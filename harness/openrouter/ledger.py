"""Independent, exact-USD accounting for one OpenRouter proof.

Every potentially billable operation, including retries and compaction, holds
the remaining proof allowance before dispatch. This is a serial accounting hold,
not a pre-request cost estimate. Only a provider receipt settles a charge;
token counts never determine cost. An unresolved dispatch survives process loss.
The database contains accounting receipts only, never request or response bodies.
"""

from __future__ import annotations

from contextlib import contextmanager
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, localcontext
import hashlib
import json
import math
from pathlib import Path
import re
import sqlite3
from typing import Any, Iterator, Mapping
from uuid import uuid4


DEFAULT_LIMIT_USD = Decimal("3")
_ACTIVE = ("reserved", "dispatched", "unknown")


PRESUMED_ZERO_POLICY = "exclusive-key-zero-audit-v1"
_PRESUMED_ZERO = "presumed_zero_recovery"
_PRE_SEND = "pre_send_failure"
_RECOVERY_TAGS = {_PRESUMED_ZERO, _PRE_SEND, "unreported_cost_nonblocking"}
_SHA256 = re.compile(r"[0-9a-f]{64}\Z")


def _sha256(value, label):
    if not isinstance(value, str) or not _SHA256.fullmatch(value):
        raise LedgerError(f"{label} requires a lowercase SHA-256 digest")
    return value


def receipt_identity(receipt: Mapping[str, Any]) -> str:
    """Optimistic pin for one complete request, without altering its evidence."""
    def plain(value):
        if isinstance(value, Decimal):
            return str(value)
        if isinstance(value, Mapping):
            return {key: plain(item) for key, item in value.items()}
        if isinstance(value, (tuple, list)):
            return [plain(item) for item in value]
        return value
    return hashlib.sha256(json.dumps(plain(receipt), sort_keys=True, separators=(",", ":"),
        ensure_ascii=True, allow_nan=False).encode()).hexdigest()


def _timestamp(value, label):
    try:
        valid = isinstance(value, str) and datetime.fromisoformat(value).utcoffset() is not None
    except ValueError:
        valid = False
    if not valid:
        raise LedgerError(f"{label} requires an aware ISO timestamp")
    return value


def _presumption(row, *, proof_id=None, model=None):
    value = row["metadata"].get(_PRESUMED_ZERO)
    if value is None:
        return None
    required = {"schema_version", "policy", "request_id", "proof_id", "model", "exclusive_key",
        "retry_used", "evidence_sha256", "key_sha256", "baseline_sha256", "receipt_sha256",
        "created_at", "status"}
    optional = {"revoked_at", "revocation_reason", "revocation_evidence_sha256", "resolved_at", "resolved_cost_usd"}
    if (not isinstance(value, dict) or not required <= value.keys() or set(value) - required - optional
            or type(value.get("schema_version")) is not int or value.get("schema_version") != 1 or value.get("policy") != PRESUMED_ZERO_POLICY
            or value.get("request_id") != row["request_id"] or value.get("exclusive_key") is not True
            or value.get("retry_used") is not True or row["dispatched_at"] is None
            or (proof_id is not None and value.get("proof_id") != proof_id)
            or (model is not None and value.get("model") != model)):
        raise LedgerError("invalid presumed-zero recovery binding")
    for name in ("proof_id", "model"):
        _label(value[name], "presumed-zero " + name)
    for name in ("evidence_sha256", "key_sha256", "baseline_sha256", "receipt_sha256"):
        _sha256(value[name], "presumed-zero " + name)
    _timestamp(value["created_at"], "presumed-zero created_at")
    status = value["status"]
    if status not in {"provisional", "revoked", "settled"}:
        raise LedgerError("invalid presumed-zero recovery status")
    revoked_fields = {"revoked_at", "revocation_reason", "revocation_evidence_sha256"}
    if ((revoked_fields & value.keys() and not revoked_fields <= value.keys())
            or (status == "revoked" and not revoked_fields <= value.keys())
            or (status != "settled" and {"resolved_at", "resolved_cost_usd"} & value.keys())):
        raise LedgerError("incomplete presumed-zero recovery history")
    if status == "settled":
        if (row["state"] != "settled" or row["cost_usd"] is None
                or _money(value.get("resolved_cost_usd"), "resolved cost") != row["cost_usd"]):
            raise LedgerError("presumed-zero resolution differs from the actual charge")
        _timestamp(value.get("resolved_at"), "presumed-zero resolved_at")
    elif row["state"] != "unknown" or row["cost_usd"] is not None:
        raise LedgerError("presumed-zero recovery must retain its unknown bill")
    if status == "provisional":
        tags = row["metadata"]
        if (row["generation_id"] is not None or row["usage"] or tags.get("output_observed") is not False
                or type(tags.get("response_headers_received")) is not bool
                or tags.get("protocol_conflict") is True or tags.get("byok_liability_unresolved") is True
                or tags.get("transport_error_category") == "protocol_error"
                or any(name in value for name in optional)):
            raise LedgerError("presumed-zero transport evidence is not eligible")
        _timestamp(tags.get("transport_finished_at"), "transport_finished_at")
    if status == "revoked" or "revoked_at" in value:
        _timestamp(value.get("revoked_at"), "presumed-zero revoked_at")
        _label(value.get("revocation_reason"), "presumed-zero revocation reason")
        _sha256(value.get("revocation_evidence_sha256"), "presumed-zero revocation evidence")
    return value


def _pre_send_failure(row):
    value = row["metadata"].get(_PRE_SEND)
    if value is None:
        return None
    if (not isinstance(value, dict) or set(value) != {"schema_version", "category", "evidence_sha256", "confirmed_at"}
            or type(value.get("schema_version")) is not int or value.get("schema_version") != 1 or value.get("category") not in {"dns_failure", "connection_refused"}
            or row["state"] != "cancelled" or row["dispatched_at"] is None or row["generation_id"] is not None
            or row["cost_usd"] is not None or row["usage"] or row["metadata"].get("request_bytes_sent") is not False
            or row["metadata"].get("response_headers_received") is not False
            or row["metadata"].get("output_observed") is not False):
        raise LedgerError("invalid proven pre-send failure binding")
    _sha256(value["evidence_sha256"], "pre-send evidence")
    _timestamp(value["confirmed_at"], "pre-send confirmed_at")
    return value


def _validate_recovery(receipts, proof_id, model):
    marked = []
    for row in receipts:
        if _presumption(row, proof_id=proof_id, model=model) is not None:
            marked.append(row)
        _pre_send_failure(row)
    if len(marked) > 1:
        raise LedgerError("only one automatic presumed-zero recovery is allowed per proof")


def _active_receipt(row):
    presumed = _presumption(row)
    if presumed is not None:
        return row["state"] in _ACTIVE and presumed["status"] != "provisional"
    # Historical provider-key enforcement can close unknown usage independently.
    return row["state"] in _ACTIVE and not (
        row["state"] == "unknown" and row["metadata"].get("unreported_cost_nonblocking") is True)


_NUMBER = re.compile(r"[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?\Z")
_PRIVATE_KEYS = {
    "prompt", "prompts", "message", "messages", "content", "body", "bodies",
    "request", "response", "headers", "header", "authorization", "secret",
    "password", "credential", "credentials", "api_key", "apikey", "access_token",
    "refresh_token", "token", "input", "output", "text", "error_message",
}
_USAGE_KEYS = {
    "cost", "cost_details", "prompt_tokens", "completion_tokens", "total_tokens",
    "input_tokens", "output_tokens", "reasoning_tokens", "cached_tokens",
    "prompt_tokens_details", "completion_tokens_details", "input_tokens_details",
    "output_tokens_details", "is_byok", "upstream_inference_cost",
    "upstream_inference_prompt_cost", "upstream_inference_completions_cost",
    "upstream_inference_input_cost", "upstream_inference_output_cost",
    "cache_write_tokens", "audio_tokens", "video_tokens", "image_tokens",
    "accepted_prediction_tokens", "rejected_prediction_tokens",
    "cache_creation_input_tokens", "cache_read_input_tokens",
}


class LedgerError(RuntimeError):
    """Invalid identity, receipt, or lifecycle transition."""


class BudgetExhausted(LedgerError):
    """A request would exceed the cap, or a permanent breach has halted work."""


class UnsettledRequest(LedgerError):
    """A previous request must be settled before another can be reserved."""


def _money(value: Any, name: str) -> Decimal:
    if isinstance(value, bool) or not isinstance(value, (str, int, float, Decimal)):
        raise LedgerError(f"{name} must be a finite nonnegative USD amount")
    raw = str(value).strip()
    if not _NUMBER.fullmatch(raw):
        raise LedgerError(f"{name} must be a finite nonnegative USD amount")
    try:
        result = Decimal(raw)
    except (InvalidOperation, ValueError) as exc:
        raise LedgerError(f"invalid {name}") from exc
    if not result.is_finite() or result < 0:
        raise LedgerError(f"{name} must be a finite nonnegative USD amount")
    return result


def _sum(values: list[Decimal]) -> Decimal:
    """Sum without the caller's Decimal context rounding a small charge away."""
    if not values:
        return Decimal("0")
    low = min(value.as_tuple().exponent for value in values)
    high = max(value.adjusted() for value in values)
    with localcontext() as context:
        context.prec = max(28, high - low + len(str(len(values))) + 3)
        return sum(values, Decimal("0"))


def _difference(left: Decimal, right: Decimal) -> Decimal:
    return _sum([left, right.copy_negate()])


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _label(value: Any, name: str, *, maximum: int = 256) -> str:
    if not isinstance(value, str) or not value.strip() or len(value) > maximum:
        raise LedgerError(f"{name} must be nonempty text of at most {maximum} characters")
    if any(ord(char) < 32 for char in value):
        raise LedgerError(f"{name} cannot contain control characters")
    # Catch accidental credential material in accounting tags and error reasons.
    lowered = value.lower()
    if "bearer " in lowered or "sk-or-" in lowered or "sk-proj-" in lowered:
        raise LedgerError(f"{name} cannot contain credentials")
    return value


def _metadata(value: Mapping[str, Any] | None) -> dict[str, Any]:
    if value is None:
        return {}
    if not isinstance(value, Mapping):
        raise LedgerError("metadata must be an accounting-tag mapping")

    def clean(item: Any, depth: int = 0) -> Any:
        if depth > 8:
            raise LedgerError("metadata is too deeply nested")
        if isinstance(item, Mapping):
            result = {}
            for key, entry in item.items():
                key = _label(key, "metadata key", maximum=80)
                normalized = key.lower().replace("-", "_")
                if normalized in _PRIVATE_KEYS or any(
                    normalized.endswith("_" + suffix)
                    for suffix in ("prompt", "body", "content", "messages", "secret", "password", "api_key", "headers")
                ):
                    raise LedgerError("metadata cannot contain prompts, bodies, or secrets")
                result[key] = clean(entry, depth + 1)
            return result
        if isinstance(item, (list, tuple)):
            return [clean(entry, depth + 1) for entry in item]
        if item is None or isinstance(item, (bool, int)):
            return item
        if isinstance(item, Decimal):
            if not item.is_finite():
                raise LedgerError("metadata numbers must be finite")
            return str(item)
        if isinstance(item, float):
            if not math.isfinite(item):
                raise LedgerError("metadata numbers must be finite")
            return item
        if isinstance(item, str):
            return _label(item, "metadata value", maximum=256) if item else ""
        raise LedgerError("metadata must contain JSON accounting tags")

    result = clean(value)
    if len(json.dumps(result)) > 8192:
        raise LedgerError("metadata is too large for accounting tags")
    return result


def _ordinary_metadata(value):
    tags = _metadata(value)
    if _RECOVERY_TAGS & tags.keys():
        raise LedgerError("recovery metadata requires its dedicated audited ledger method")
    return tags


def _merge_metadata(prior, incoming):
    result = dict(prior)
    tags = _ordinary_metadata(incoming)
    for name in ("response_headers_received", "output_observed", "protocol_conflict"):
        if name in tags:
            if type(tags[name]) is not bool or (result.get(name) is True and tags[name] is not True):
                raise LedgerError("transport evidence booleans cannot be weakened")
    if "request_bytes_sent" in tags:
        if tags["request_bytes_sent"] is not None and type(tags["request_bytes_sent"]) is not bool:
            raise LedgerError("request_bytes_sent must be a boolean or unknown")
        if result.get("request_bytes_sent") is True and tags["request_bytes_sent"] is not True:
            raise LedgerError("sent request bytes cannot become unobserved")
    result.update(tags)
    return _metadata(result)


def _usage(value: Mapping[str, Any] | None) -> dict[str, Any]:
    """Retain only numeric provider accounting fields, dropping any body data."""
    if value is None:
        return {}
    if not isinstance(value, Mapping):
        raise LedgerError("usage must be a mapping")
    result = {}
    for key, item in value.items():
        if key not in _USAGE_KEYS:
            continue
        if key == "is_byok":
            if type(item) is not bool:
                raise LedgerError("usage.is_byok must be boolean")
            result[key] = item
            continue
        if isinstance(item, Mapping):
            result[key] = _usage(item)
        elif isinstance(item, bool):
            if key == "is_byok":
                result[key] = item
        elif item is not None:
            result[key] = str(_money(item, f"usage.{key}"))
    return result


def provider_cost(usage: Mapping[str, Any]) -> tuple[Decimal, Decimal, Decimal] | None:
    """Return (total liability, OpenRouter charge, BYOK upstream charge).

    Ordinary receipts already include inference in cost. Only an explicit BYOK
    receipt adds the separately billed upstream amount. Missing BYOK evidence
    is unresolved, never a free inference receipt.
    """
    byok = usage.get("is_byok", False)
    if type(byok) is not bool:
        raise LedgerError("usage.is_byok must be boolean")
    fee = _money(usage["cost"], "usage.cost") if "cost" in usage else None
    if not byok:
        return None if fee is None else (fee, fee, Decimal("0"))
    details = usage.get("cost_details", {})
    if not isinstance(details, Mapping):
        raise LedgerError("usage.cost_details must be a mapping")
    upstream = None
    components = {}
    for source in (usage, details):
        if "upstream_inference_cost" in source:
            candidate = _money(source["upstream_inference_cost"], "upstream_inference_cost")
            if upstream is not None and candidate != upstream:
                raise LedgerError("conflicting BYOK upstream inference costs")
            upstream = candidate
        for field, component in (("upstream_inference_input_cost", "input"),
                                 ("upstream_inference_prompt_cost", "input"),
                                 ("upstream_inference_output_cost", "output"),
                                 ("upstream_inference_completions_cost", "output")):
            if field in source:
                value = _money(source[field], field)
                if component in components and components[component] != value:
                    raise LedgerError("conflicting BYOK upstream cost components")
                components[component] = value
    subtotal = _sum(list(components.values()))
    if upstream is not None and (subtotal > upstream or (len(components) == 2 and subtotal != upstream)):
        raise LedgerError("BYOK upstream components conflict with aggregate cost")
    if fee is None or upstream is None:
        return None
    return _sum([fee, upstream]), fee, upstream


_LIABILITY_FIELDS = {"cost", "is_byok", "upstream_inference_cost",
                     "upstream_inference_input_cost", "upstream_inference_output_cost",
                     "upstream_inference_prompt_cost", "upstream_inference_completions_cost"}


def _merge_usage(prior: Mapping[str, Any], incoming: Mapping[str, Any]) -> dict[str, Any]:
    result = dict(prior)
    for key, value in incoming.items():
        if key in result and isinstance(value, Mapping) and isinstance(result[key], Mapping):
            value = _merge_usage(result[key], value)
        elif key in result and key in _LIABILITY_FIELDS:
            same = (type(result[key]) is bool and type(value) is bool and result[key] == value
                    if key == "is_byok" else _money(result[key], key) == _money(value, key))
            if not same:
                raise LedgerError("conflicting provider accounting evidence")
        result[key] = value
    return result


def _cost_totals(receipts: list[dict[str, Any]]) -> dict[str, Decimal]:
    openrouter, upstream = [], []
    for row in receipts:
        if row["state"] != "settled":
            continue
        costs = provider_cost(row["usage"])
        if costs is None:
            if row["usage"].get("is_byok") is True:
                raise LedgerError("settled BYOK receipt is missing upstream liability")
            costs = (row["cost_usd"], row["cost_usd"], Decimal("0"))
        if costs[0] != row["cost_usd"]:
            raise LedgerError("stored usage.cost conflicts with actual receipt cost")
        openrouter.append(costs[1])
        upstream.append(costs[2])
    return {"openrouter_cost_usd": _sum(openrouter), "byok_upstream_cost_usd": _sum(upstream)}


class OpenRouterLedger:
    """A restart-safe ledger with immutable proof, model, and cap identity.

    Public money values are Decimals; serialize them as strings in reports.
    Reserve before sending and mark_dispatched immediately before network I/O.
    Never cancel a request after dispatch. Missing provider cost is unknown,
    including on an error response. With provider-key enforcement, a closed
    attempt can retain an unknown cost without blocking the next request.
    Metadata accepts short accounting tags, not prompts, bodies, or credentials.
    """

    def __init__(self, path: str | Path, *, proof_id: str, model: str,
                 limit_usd: Any = DEFAULT_LIMIT_USD):
        self._proof_id = _label(proof_id, "proof_id")
        self._model = _label(model, "model")
        self._limit_usd = _money(limit_usd, "limit_usd")
        if str(path) == ":memory:":
            raise LedgerError("the ledger requires a persistent database path")
        self._path = Path(path).resolve()
        self._path.parent.mkdir(parents=True, exist_ok=True)
        with self._transaction() as connection:
            connection.execute("""CREATE TABLE IF NOT EXISTS openrouter_identity (
                singleton INTEGER PRIMARY KEY CHECK (singleton = 1),
                schema_version INTEGER NOT NULL,
                proof_id TEXT NOT NULL, model TEXT NOT NULL, limit_usd TEXT NOT NULL,
                created_at TEXT NOT NULL, breach_reason TEXT, breached_at TEXT
            )""")
            connection.execute("""CREATE TABLE IF NOT EXISTS openrouter_requests (
                request_id TEXT PRIMARY KEY, pass_number INTEGER NOT NULL,
                purpose TEXT NOT NULL, state TEXT NOT NULL
                    CHECK (state IN ('reserved', 'dispatched', 'unknown', 'settled', 'cancelled')),
                reserved_usd TEXT NOT NULL, cost_usd TEXT,
                generation_id TEXT UNIQUE, created_at TEXT NOT NULL,
                dispatched_at TEXT, settled_at TEXT, cancelled_at TEXT,
                unknown_reason TEXT, usage_json TEXT NOT NULL DEFAULT '{}',
                metadata_json TEXT NOT NULL DEFAULT '{}',
                CHECK ((state = 'settled') = (cost_usd IS NOT NULL))
            )""")
            connection.execute("DROP INDEX IF EXISTS openrouter_single_active")
            connection.execute("""CREATE UNIQUE INDEX openrouter_single_active
                ON openrouter_requests ((1))
                WHERE state IN ('reserved', 'dispatched')""")
            identity = connection.execute("SELECT * FROM openrouter_identity").fetchone()
            if identity is None:
                connection.execute("""INSERT INTO openrouter_identity
                    (singleton, schema_version, proof_id, model, limit_usd, created_at)
                    VALUES (1, 1, ?, ?, ?, ?)""",
                    (self.proof_id, self.model, str(self.limit_usd), _now()))
            elif (identity["schema_version"] != 1 or identity["proof_id"] != self.proof_id
                  or identity["model"] != self.model
                  or _money(identity["limit_usd"], "stored limit_usd") != self.limit_usd):
                raise LedgerError("ledger proof, model, cap, and schema identity are immutable")

    @property
    def path(self) -> Path:
        return self._path

    @property
    def proof_id(self) -> str:
        return self._proof_id

    @property
    def model(self) -> str:
        return self._model

    @property
    def limit_usd(self) -> Decimal:
        return self._limit_usd

    @contextmanager
    def _connection(self, *, readonly: bool = False) -> Iterator[sqlite3.Connection]:
        try:
            connection = sqlite3.connect(
                self.path.as_uri() + "?mode=ro" if readonly else str(self.path),
                uri=readonly, timeout=30, isolation_level=None,
            )
            connection.row_factory = sqlite3.Row
            if readonly:
                connection.execute("PRAGMA query_only = ON")
            try:
                yield connection
            finally:
                connection.close()
        except sqlite3.Error as exc:
            raise LedgerError(f"ledger database error: {exc}") from exc

    @contextmanager
    def _transaction(self) -> Iterator[sqlite3.Connection]:
        with self._connection() as connection:
            connection.execute("BEGIN IMMEDIATE")
            try:
                yield connection
                connection.commit()
            except BaseException:
                connection.rollback()
                raise

    @staticmethod
    def _row(connection: sqlite3.Connection, request_id: str) -> sqlite3.Row:
        if not isinstance(request_id, str):
            raise LedgerError("request_id must be a ledger request identifier")
        row = connection.execute("SELECT * FROM openrouter_requests WHERE request_id = ?",
                                 (request_id,)).fetchone()
        if row is None:
            raise LedgerError("unknown ledger request_id")
        return row

    @staticmethod
    def _receipt(row: sqlite3.Row) -> dict[str, Any]:
        result = dict(row)
        result["reserved_usd"] = _money(result["reserved_usd"], "stored reserved_usd")
        result["cost_usd"] = None if result["cost_usd"] is None else _money(result["cost_usd"], "stored cost_usd")
        result["usage"] = json.loads(result.pop("usage_json"))
        result["metadata"] = json.loads(result.pop("metadata_json"))
        return result

    def _snapshot(self, connection: sqlite3.Connection) -> dict[str, Any]:
        identity = connection.execute("SELECT * FROM openrouter_identity WHERE singleton = 1").fetchone()
        receipts = [self._receipt(row) for row in connection.execute(
            "SELECT * FROM openrouter_requests ORDER BY created_at, request_id")]
        _validate_recovery(receipts, self.proof_id, self.model)
        spent = _sum([row["cost_usd"] for row in receipts if row["state"] == "settled"])
        active = [row for row in receipts if _active_receipt(row)]
        reserved = _sum([row["reserved_usd"] for row in active])
        remaining = max(Decimal("0"), _difference(self.limit_usd, _sum([spent, reserved])))
        unknown = [row for row in receipts if row["state"] == "unknown"]
        blocking_unknown = [row for row in active if row["state"] == "unknown"]
        halted = identity["breach_reason"]
        if halted is None:
            halted = ("unreconciled_provider_cost" if blocking_unknown else "request_in_flight" if active
                      else "budget_exhausted" if spent >= self.limit_usd else None)
        return {"proof_id": self.proof_id, "model": self.model, "limit_usd": self.limit_usd,
                "spent_usd": spent, **_cost_totals(receipts), "reserved_usd": reserved, "remaining_usd": remaining,
                "unknown_requests": unknown, "active_requests": active,
                "blocking_unknown_requests": blocking_unknown,
                "provisional_unknown_requests": [row for row in unknown if _presumption(row) is not None
                    and row["metadata"][_PRESUMED_ZERO]["status"] == "provisional"],
                "halted_reason": halted}

    def reserve(self, max_cost_usd: Any, *, pass_number: int,
                purpose: str = "inference", metadata: Mapping[str, Any] | None = None) -> str:
        ceiling = _money(max_cost_usd, "max_cost_usd")
        if isinstance(pass_number, bool) or not isinstance(pass_number, int) or pass_number < 1:
            raise LedgerError("pass_number must be a positive integer")
        purpose = _label(purpose, "purpose", maximum=80)
        tags = _ordinary_metadata(metadata)
        with self._transaction() as connection:
            snapshot = self._snapshot(connection)
            if snapshot["active_requests"]:
                raise UnsettledRequest("settle or reconcile the existing request before retrying")
            if snapshot["halted_reason"] not in (None, "budget_exhausted"):
                raise BudgetExhausted(f"ledger permanently halted: {snapshot['halted_reason']}")
            if _sum([snapshot["spent_usd"], ceiling]) > self.limit_usd:
                raise BudgetExhausted("request reservation would exceed the proof USD cap")
            request_id = uuid4().hex
            connection.execute("""INSERT INTO openrouter_requests
                (request_id, pass_number, purpose, state, reserved_usd, created_at, metadata_json)
                VALUES (?, ?, ?, 'reserved', ?, ?, ?)""",
                (request_id, pass_number, purpose, str(ceiling), _now(), json.dumps(tags, sort_keys=True)))
        return request_id

    def mark_dispatched(self, request_id: str) -> dict[str, Any]:
        with self._transaction() as connection:
            row = self._row(connection, request_id)
            if row["state"] not in ("reserved", "dispatched"):
                raise LedgerError("only a reserved request can be dispatched")
            if row["state"] == "reserved":
                connection.execute("""UPDATE openrouter_requests SET state = 'dispatched',
                    dispatched_at = ? WHERE request_id = ?""", (_now(), request_id))
            return self._receipt(self._row(connection, request_id))

    @staticmethod
    def _generation(connection: sqlite3.Connection, row: sqlite3.Row,
                    generation_id: str | None) -> str | None:
        if generation_id is None:
            return row["generation_id"]
        generation_id = _label(generation_id, "generation_id")
        if row["generation_id"] is not None and row["generation_id"] != generation_id:
            raise LedgerError("request generation_id is immutable")
        duplicate = connection.execute("""SELECT request_id FROM openrouter_requests
            WHERE generation_id = ? AND request_id != ?""", (generation_id, row["request_id"])).fetchone()
        if duplicate is not None:
            raise LedgerError("generation_id already belongs to another request")
        return generation_id

    def annotate(self, request_id: str, *, generation_id: str | None = None,
                 metadata: Mapping[str, Any] | None = None) -> dict[str, Any]:
        """Persist safe transport facts without inventing a cost or verdict."""
        with self._transaction() as connection:
            row = self._row(connection, request_id)
            if row["state"] not in ("dispatched", "unknown", "settled", "cancelled"):
                raise LedgerError("transport annotation requires a dispatched request")
            if row["state"] == "cancelled" and (row["dispatched_at"] is None or generation_id is not None):
                raise LedgerError("cancelled request cannot gain a generation")
            generation = self._generation(connection, row, generation_id)
            tags = _merge_metadata(json.loads(row["metadata_json"]), metadata)
            marker = tags.get(_PRESUMED_ZERO)
            if marker and marker["status"] == "provisional" and (
                    generation is not None or tags.get("output_observed") is not False
                    or tags.get("protocol_conflict") is True or tags.get("byok_liability_unresolved") is True
                    or tags.get("transport_error_category") == "protocol_error"):
                self._revoke_marker(connection, tags, reason="new_transport_evidence",
                    evidence_sha256=receipt_identity({"generation_id": generation, "metadata": tags}))
            candidate = {**self._receipt(row), "generation_id": generation, "metadata": tags}
            _presumption(candidate, proof_id=self.proof_id, model=self.model)
            _pre_send_failure(candidate)
            connection.execute("UPDATE openrouter_requests SET generation_id = ?, metadata_json = ? WHERE request_id = ?",
                (generation, json.dumps(tags, sort_keys=True), request_id))
            return self._receipt(self._row(connection, request_id))

    def attach_generation(self, request_id: str, generation_id: str) -> dict[str, Any]:
        return self.annotate(request_id, generation_id=_label(generation_id, "generation_id"))

    def presumed_zero_valid(self, request_id: str) -> bool:
        """Validate the protected provisional release, retaining its unknown bill."""
        with self._connection(readonly=True) as connection:
            receipts = [self._receipt(row) for row in connection.execute("SELECT * FROM openrouter_requests")]
            _validate_recovery(receipts, self.proof_id, self.model)
            row = self._receipt(self._row(connection, request_id))
            marker = _presumption(row, proof_id=self.proof_id, model=self.model)
            return marker is not None and marker["status"] == "provisional"

    def presume_zero(self, request_id: str, *, evidence_sha256: str, key_sha256: str,
                     baseline_sha256: str, expected_receipt_sha256: str,
                     exclusive_key: bool) -> dict[str, Any]:
        """Release one audited hold provisionally; never settle a fictitious bill.

        The host coordinator owns the exclusive-key audit. Its exact evidence,
        baseline and request pins are durable; one automatic presumption is the
        entire lifetime allowance for this proof, including across restarts.
        """
        pins = {"evidence_sha256": _sha256(evidence_sha256, "audit evidence"),
            "key_sha256": _sha256(key_sha256, "exclusive key"),
            "baseline_sha256": _sha256(baseline_sha256, "key baseline"),
            "receipt_sha256": _sha256(expected_receipt_sha256, "request receipt")}
        if exclusive_key is not True:
            raise LedgerError("presumed zero requires an explicitly exclusive run key")
        with self._transaction() as connection:
            row = self._receipt(self._row(connection, request_id))
            snapshot = self._snapshot(connection)
            marker = _presumption(row, proof_id=self.proof_id, model=self.model)
            if marker is not None and marker["status"] == "provisional" and all(marker[k] == v for k, v in pins.items()):
                return row
            receipts = [self._receipt(item) for item in connection.execute("SELECT * FROM openrouter_requests")]
            if any(_PRESUMED_ZERO in item["metadata"] for item in receipts):
                raise LedgerError("only one automatic presumed-zero recovery is allowed per proof")
            if receipt_identity(row) != expected_receipt_sha256:
                raise LedgerError("request receipt changed since the exclusive-key audit")
            if (row["state"] != "unknown" or row["dispatched_at"] is None or row["generation_id"] is not None
                    or row["usage"] or row["metadata"].get("output_observed") is not False
                    or type(row["metadata"].get("response_headers_received")) is not bool
                    or row["metadata"].get("protocol_conflict") is True or row["metadata"].get("byok_liability_unresolved") is True
                    or row["metadata"].get("transport_error_category") == "protocol_error"
                    or [item["request_id"] for item in snapshot["unknown_requests"]] != [request_id]
                    or [item["request_id"] for item in snapshot["active_requests"]] != [request_id]
                    or snapshot["halted_reason"] != "unreconciled_provider_cost"):
                raise LedgerError("request is not an eligible sole no-output unknown")
            _timestamp(row["metadata"].get("transport_finished_at"), "transport_finished_at")
            tags = dict(row["metadata"])
            tags.pop("unreported_cost_nonblocking", None)
            tags[_PRESUMED_ZERO] = {"schema_version": 1, "policy": PRESUMED_ZERO_POLICY,
                "request_id": request_id, "proof_id": self.proof_id, "model": self.model,
                "exclusive_key": True, "retry_used": True, **pins, "created_at": _now(), "status": "provisional"}
            _presumption({**row, "metadata": tags}, proof_id=self.proof_id, model=self.model)
            connection.execute("UPDATE openrouter_requests SET metadata_json = ? WHERE request_id = ?",
                (json.dumps(_metadata(tags), sort_keys=True), request_id))
            return self._receipt(self._row(connection, request_id))

    @staticmethod
    def _revoke_marker(connection, tags, *, reason, evidence_sha256):
        marker = dict(tags[_PRESUMED_ZERO])
        if marker["status"] == "provisional":
            marker.update(status="revoked", revoked_at=_now(), revocation_reason=_label(reason, "revocation reason"),
                revocation_evidence_sha256=_sha256(evidence_sha256, "revocation evidence"))
            tags[_PRESUMED_ZERO] = marker
            tags.pop("unreported_cost_nonblocking", None)
            connection.execute("""UPDATE openrouter_identity SET breach_reason = COALESCE(breach_reason, ?),
                breached_at = COALESCE(breached_at, ?) WHERE singleton = 1""",
                ("presumed_zero_recovery_revoked", _now()))

    def revoke_presumed_zero(self, request_id: str, *, evidence_sha256: str,
                            reason: str = "key_audit_discrepancy") -> dict[str, Any]:
        evidence_sha256 = _sha256(evidence_sha256, "revocation evidence")
        reason = _label(reason, "revocation reason")
        with self._transaction() as connection:
            row = self._receipt(self._row(connection, request_id))
            marker = _presumption(row, proof_id=self.proof_id, model=self.model)
            if marker is None or marker["status"] == "settled":
                raise LedgerError("only an unresolved presumed-zero request can be revoked")
            tags = dict(row["metadata"])
            self._revoke_marker(connection, tags, reason=reason, evidence_sha256=evidence_sha256)
            connection.execute("UPDATE openrouter_requests SET metadata_json = ? WHERE request_id = ?",
                (json.dumps(_metadata(tags), sort_keys=True), request_id))
            return self._receipt(self._row(connection, request_id))

    def cancel_pre_send_failure(self, request_id: str, *, category: str,
                                evidence_sha256: str | None = None) -> dict[str, Any]:
        """Close a typed connection failure proven to precede model POST bytes."""
        if category not in {"dns_failure", "connection_refused"}:
            raise LedgerError("unsupported proven pre-send transport category")
        with self._transaction() as connection:
            row = self._receipt(self._row(connection, request_id))
            if (row["state"] != "dispatched" or row["generation_id"] is not None or row["usage"]
                    or row["metadata"].get("transport_phase") != "pre_send"
                    or row["metadata"].get("request_bytes_sent") is not False
                    or row["metadata"].get("response_headers_received") is not False
                    or row["metadata"].get("output_observed") is not False):
                raise LedgerError("request lacks positive pre-send failure evidence")
            evidence = _sha256(evidence_sha256, "pre-send evidence") if evidence_sha256 is not None else receipt_identity(row)
            tags = dict(row["metadata"])
            tags[_PRE_SEND] = {"schema_version": 1, "category": category,
                "evidence_sha256": evidence, "confirmed_at": _now()}
            connection.execute("""UPDATE openrouter_requests SET state = 'cancelled', cancelled_at = ?,
                metadata_json = ? WHERE request_id = ?""", (_now(), json.dumps(_metadata(tags), sort_keys=True), request_id))
            return self._receipt(self._row(connection, request_id))

    def settle(self, request_id: str, *, cost_usd: Any, usage: Mapping[str, Any] | None = None,
               generation_id: str | None = None,
               metadata: Mapping[str, Any] | None = None) -> dict[str, Any]:
        cost = _money(cost_usd, "cost_usd")
        account_usage = _usage(usage)
        tags = _ordinary_metadata(metadata)
        with self._transaction() as connection:
            row = self._row(connection, request_id)
            if row["state"] == "cancelled":
                raise LedgerError("a cancelled request cannot be settled")
            generation = self._generation(connection, row, generation_id)
            if row["state"] == "settled" and _money(row["cost_usd"], "stored cost_usd") != cost:
                raise LedgerError("a settled provider charge is immutable")
            prior_tags = _merge_metadata(json.loads(row["metadata_json"]), tags)
            prior_tags.pop("byok_liability_unresolved", None)
            if _PRESUMED_ZERO in prior_tags:
                marker = dict(prior_tags[_PRESUMED_ZERO])
                marker.update(status="settled", resolved_cost_usd=str(cost))
                marker.setdefault("resolved_at", _now())
                prior_tags[_PRESUMED_ZERO] = marker
            prior_usage = _merge_usage(json.loads(row["usage_json"]), account_usage)
            costs = provider_cost(prior_usage)
            if costs is None and prior_usage.get("is_byok") is True:
                raise LedgerError("BYOK receipt is missing upstream liability")
            if costs is not None and costs[0] != cost:
                raise LedgerError("cost_usd conflicts with provider usage.cost and liability")
            stored_cost = row["cost_usd"] if row["state"] == "settled" else str(cost)
            if (row["state"] == "settled" and generation == row["generation_id"]
                    and prior_tags == json.loads(row["metadata_json"])
                    and prior_usage == json.loads(row["usage_json"])):
                return self._receipt(row)
            connection.execute("""UPDATE openrouter_requests SET state = 'settled', cost_usd = ?,
                generation_id = ?, settled_at = COALESCE(settled_at, ?), usage_json = ?,
                metadata_json = ? WHERE request_id = ?""",
                (stored_cost, generation, _now(), json.dumps(prior_usage, sort_keys=True),
                 json.dumps(prior_tags, sort_keys=True), request_id))
            snapshot = self._snapshot(connection)
            spent = snapshot["spent_usd"]
            breach = ("actual_cost_exceeded_reservation" if cost > _money(row["reserved_usd"], "stored reserved_usd")
                      else "actual_cost_exceeded_budget" if spent > self.limit_usd
                      else "late_cost_exceeded_reserved_allowance" if _sum([spent, snapshot["reserved_usd"]]) > self.limit_usd else None)
            if breach is not None:
                connection.execute("""UPDATE openrouter_identity SET breach_reason = COALESCE(breach_reason, ?),
                    breached_at = COALESCE(breached_at, ?) WHERE singleton = 1""", (breach, _now()))
            return self._receipt(self._row(connection, request_id))

    def cancel_before_dispatch(self, request_id: str) -> dict[str, Any]:
        with self._transaction() as connection:
            row = self._row(connection, request_id)
            if row["state"] not in ("reserved", "cancelled"):
                raise LedgerError("a dispatched or unknown request cannot release its reservation")
            if row["state"] == "reserved":
                connection.execute("""UPDATE openrouter_requests SET state = 'cancelled',
                    cancelled_at = ? WHERE request_id = ?""", (_now(), request_id))
            return self._receipt(self._row(connection, request_id))

    def mark_unknown(self, request_id: str, reason: str, *, blocks_spending: bool = True,
                     usage: Mapping[str, Any] | None = None,
                     metadata: Mapping[str, Any] | None = None) -> dict[str, Any]:
        reason = _label(reason, "unknown reason", maximum=256)
        if type(blocks_spending) is not bool:
            raise LedgerError("blocks_spending must be boolean")
        with self._transaction() as connection:
            row = self._row(connection, request_id)
            if row["state"] == "cancelled":
                raise LedgerError("a cancelled request cannot become unknown")
            if row["state"] != "settled":
                tags = _merge_metadata(json.loads(row["metadata_json"]), metadata)
                account_usage = _merge_usage(json.loads(row["usage_json"]), _usage(usage))
                # A known BYOK dispatch cannot release liability merely because
                # its upstream receipt is missing or contradictory.
                blocks_spending = (blocks_spending or account_usage.get("is_byok") is True
                                   or tags.get("byok_liability_unresolved") is True)
                if _PRESUMED_ZERO in tags and tags[_PRESUMED_ZERO]["status"] == "provisional":
                    if blocks_spending or account_usage:
                        self._revoke_marker(connection, tags, reason="new_blocking_evidence",
                            evidence_sha256=receipt_identity(self._receipt(row)))
                if blocks_spending:
                    tags.pop("unreported_cost_nonblocking", None)
                if not blocks_spending and _PRESUMED_ZERO not in tags:
                    if row["dispatched_at"] is None:
                        raise LedgerError("only a dispatched attempt can close with unreported usage")
                    tags["unreported_cost_nonblocking"] = True
                _presumption({**self._receipt(row), "state": "unknown", "metadata": tags,
                    "usage": account_usage}, proof_id=self.proof_id, model=self.model)
                connection.execute("""UPDATE openrouter_requests SET state = 'unknown',
                    unknown_reason = ?, metadata_json = ?, usage_json = ? WHERE request_id = ?""",
                    (reason, json.dumps(tags, sort_keys=True), json.dumps(account_usage, sort_keys=True), request_id))
            return self._receipt(self._row(connection, request_id))

    def snapshot(self) -> dict[str, Any]:
        """Read a consistent snapshot without changing requests or timestamps."""
        with self._connection(readonly=True) as connection:
            connection.execute("BEGIN")
            return self._snapshot(connection)

    def request(self, request_id: str) -> dict[str, Any]:
        with self._connection(readonly=True) as connection:
            return self._receipt(self._row(connection, request_id))

    def requests(self, *, pass_number: int | None = None) -> list[dict[str, Any]]:
        if pass_number is not None and (isinstance(pass_number, bool) or not isinstance(pass_number, int) or pass_number < 1):
            raise LedgerError("pass_number must be a positive integer")
        with self._connection(readonly=True) as connection:
            query = "SELECT * FROM openrouter_requests"
            arguments: tuple[Any, ...] = ()
            if pass_number is not None:
                query += " WHERE pass_number = ?"
                arguments = (pass_number,)
            query += " ORDER BY created_at, request_id"
            return [self._receipt(row) for row in connection.execute(query, arguments)]

    def pass_receipts(self, *, pass_number: int | None = None) -> list[dict[str, Any]]:
        """Return all request receipts, including unresolved and cancelled ones."""
        return self.requests(pass_number=pass_number)


def read_openrouter_receipt(path: str | Path) -> dict[str, Any]:
    """Read and validate a canonical, JSON-safe export without creating a ledger.

    The digest covers immutable identity and all stored request receipt fields;
    it excludes the location so copying an unchanged ledger preserves its hash.
    This is an integrity fingerprint, not a provider signature or cost estimate.
    """
    location = Path(path).resolve()
    try:
        connection = sqlite3.connect(location.as_uri() + "?mode=ro", uri=True, isolation_level=None)
        connection.row_factory = sqlite3.Row
        try:
            connection.execute("PRAGMA query_only = ON")
            connection.execute("BEGIN")
            identities = connection.execute("SELECT * FROM openrouter_identity").fetchall()
            if len(identities) != 1 or identities[0]["singleton"] != 1 or identities[0]["schema_version"] != 1:
                raise LedgerError("unsupported or malformed OpenRouter ledger identity")
            identity = dict(identities[0])
            identity.pop("singleton")
            _label(identity["proof_id"], "stored proof_id")
            _label(identity["model"], "stored model")
            limit = _money(identity["limit_usd"], "stored limit_usd")
            requests = [OpenRouterLedger._receipt(row) for row in connection.execute(
                "SELECT * FROM openrouter_requests ORDER BY created_at, request_id")]
        finally:
            connection.close()
    except sqlite3.Error as exc:
        raise LedgerError(f"cannot read OpenRouter ledger receipt: {exc}") from exc
    except (KeyError, TypeError, json.JSONDecodeError) as exc:
        raise LedgerError("malformed OpenRouter ledger receipt") from exc

    generations: set[str] = set()
    identifiers: set[str] = set()
    for row in requests:
        _label(row["request_id"], "stored request_id")
        if row["request_id"] in identifiers:
            raise LedgerError("duplicate request receipt")
        identifiers.add(row["request_id"])
        if (isinstance(row["pass_number"], bool) or not isinstance(row["pass_number"], int)
                or row["pass_number"] < 1):
            raise LedgerError("malformed receipt pass_number")
        if row["state"] not in (*_ACTIVE, "settled", "cancelled"):
            raise LedgerError("malformed receipt state")
        if (row["state"] == "settled") != (row["cost_usd"] is not None):
            raise LedgerError("receipt state and actual cost disagree")
        _label(row["purpose"], "stored purpose", maximum=80)
        _metadata(row["metadata"])
        usage = _usage(row["usage"])
        if usage != row["usage"]:
            raise LedgerError("stored usage contains unsupported accounting fields")
        generation = row["generation_id"]
        if generation is not None:
            if row["state"] in ("reserved", "cancelled"):
                raise LedgerError("undispatched request has a provider generation receipt")
            _label(generation, "stored generation_id")
            if generation in generations:
                raise LedgerError("duplicate provider generation receipt")
            generations.add(generation)
    _validate_recovery(requests, identity["proof_id"], identity["model"])
    active = [row for row in requests if _active_receipt(row)]
    breach = identity["breach_reason"]
    if len(active) > 1 and not (breach is not None and any(
            _presumption(row) is not None and row["metadata"][_PRESUMED_ZERO]["status"] == "revoked" for row in active)):
        raise LedgerError("multiple unsettled requests in one proof ledger")
    spent = _sum([row["cost_usd"] for row in requests if row["state"] == "settled"])
    reserved = _sum([row["reserved_usd"] for row in active])
    unknown = [row for row in requests if row["state"] == "unknown"]
    blocking_unknown = [row for row in active if row["state"] == "unknown"]
    breach = identity["breach_reason"]
    if _sum([spent, reserved]) > limit and active and breach is None:
        raise LedgerError("unsettled reservation exceeds the proof budget")
    if (spent > limit or any(row["state"] == "settled" and row["cost_usd"] > row["reserved_usd"]
                             for row in requests)) and breach is None:
        raise LedgerError("actual charge breach is missing its permanent halt marker")
    halted = breach or ("unreconciled_provider_cost" if blocking_unknown else "request_in_flight" if active
                        else "budget_exhausted" if spent >= limit else None)

    def json_safe(value: Any) -> Any:
        if isinstance(value, Decimal):
            return str(value)
        if isinstance(value, dict):
            return {key: json_safe(item) for key, item in value.items()}
        if isinstance(value, list):
            return [json_safe(item) for item in value]
        return value

    canonical = json_safe({"identity": identity, "requests": requests})
    digest = hashlib.sha256(json.dumps(canonical, sort_keys=True, separators=(",", ":"),
                                      ensure_ascii=True, allow_nan=False).encode("utf-8")).hexdigest()
    return {"provider": "openrouter", "authority": "openrouter_actual_cost_ledger",
            "ledger_path": str(location), "sha256": digest, **canonical,
            "budget": json_safe({"provider": "openrouter", "metering_enabled": True,
                                 "limit_usd": limit, "spent_usd": spent, **_cost_totals(requests), "reserved_usd": reserved,
                                 "remaining_usd": max(Decimal("0"), _difference(limit, _sum([spent, reserved]))),
                                 "unknown_requests": len(unknown), "active_requests": len(active),
                                 "blocking_unknown_requests": len(blocking_unknown),
                                 "provisional_unknown_requests": sum(_presumption(row) is not None
                                     and row["metadata"][_PRESUMED_ZERO]["status"] == "provisional" for row in unknown),
                                 "blocking_unknown_request_ids": [row["request_id"] for row in blocking_unknown],
                                 "provisional_unknown_request_ids": [row["request_id"] for row in unknown
                                     if _presumption(row) is not None and row["metadata"][_PRESUMED_ZERO]["status"] == "provisional"],
                                 "unknown_request_ids": [row["request_id"] for row in unknown],
                                 "active_request_ids": [row["request_id"] for row in active],
                                 "request_count": len(requests),
                                 "dispatched_requests": sum(row["dispatched_at"] is not None for row in requests),
                                 "completed_requests": sum(row["state"] == "settled" for row in requests),
                                 "metered_responses": sum(row["state"] == "settled" for row in requests),
                                 "halted_reason": halted})}
