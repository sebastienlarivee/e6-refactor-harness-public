"""Durable usage facts and request lifecycle for provider requests.

Amounts are exact decimal USD, stored as text in SQLite. Every request is
recorded before dispatch; all callers in an episode use the same database and
episode ID. Request lifecycle transitions are atomic across processes.
Prices are supplied by the caller in USD per million tokens. The native relay
uses zero-dollar markers, not pessimistic reservations; its serial admission
policy is separate from these accounting facts.
"""

from __future__ import annotations

import json
import hashlib
import shutil
import sqlite3
from contextlib import contextmanager
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, localcontext
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import Any, Iterator, Mapping


def _decimal(value: Any, field: str) -> Decimal:
    if isinstance(value, bool):
        raise ValueError(f"{field} must be a finite nonnegative decimal")
    try:
        result = Decimal(str(value))
    except (InvalidOperation, ValueError, TypeError) as exc:
        raise ValueError(f"{field} must be a finite nonnegative decimal") from exc
    if not result.is_finite() or result < 0:
        raise ValueError(f"{field} must be a finite nonnegative decimal")
    return result


def _money(value: Decimal) -> str:
    if not value:
        return "0"
    text = format(value, "f")
    return text.rstrip("0").rstrip(".") if "." in text else text


def _sum(values: list[Decimal]) -> Decimal:
    if not values:
        return Decimal(0)
    # Avoid the process's Decimal context rounding either costs or their sum.
    least_exponent = min(value.as_tuple().exponent for value in values)
    largest_place = max(value.adjusted() for value in values)
    with localcontext() as context:
        context.prec = max(28, largest_place - least_exponent + len(str(len(values))) + 2)
        return sum(values, Decimal(0))


def _tokens(value: Any, field: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or not 0 <= value < 2**63:
        raise ValueError(f"{field} must be a nonnegative integer below 2**63")
    return value


def _json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _prices(prices: Mapping[str, Any]) -> dict[str, str]:
    result = {key: _money(_decimal(prices[key], f"prices.{key}"))
              for key in ("input", "cache_read", "output")}
    if "cache_write" in prices:
        result["cache_write"] = _money(_decimal(prices["cache_write"], "prices.cache_write"))
    return result


def _covers_cache_writes(prices: Mapping[str, str], metadata: Any) -> bool:
    key = "unclassified_input_rate_covers_cache_writes"
    if not isinstance(metadata, Mapping) or key not in metadata:
        return False
    flag = metadata[key]
    if not isinstance(flag, bool):
        raise ValueError(f"metadata.{key} must be a boolean")
    if flag and ("cache_write" not in prices
                 or Decimal(prices["input"]) < Decimal(prices["cache_write"])):
        raise ValueError("cache-write coverage requires a cache_write price at most the input price")
    return flag


def _cost(input_tokens: int, cached_tokens: int, output_tokens: int,
          prices: Mapping[str, str], cache_write_tokens: int = 0) -> Decimal:
    terms = []
    counts = [(input_tokens - cached_tokens - cache_write_tokens, "input"),
              (cached_tokens, "cache_read"), (output_tokens, "output")]
    if cache_write_tokens:
        counts.append((cache_write_tokens, "cache_write"))
    for count, key in counts:
        price = Decimal(prices[key])
        with localcontext() as context:
            context.prec = max(28, len(price.as_tuple().digits) + len(str(count)) + 2)
            terms.append((price * count).scaleb(-6))
    return _sum(terms)


def normalize_usage(usage: Mapping[str, Any]) -> dict[str, Any]:
    """Normalize Responses usage; reasoning is already part of output_tokens.

    Missing billing counters are unknown, never silently converted to zero.
    Flat normalized counters are accepted as well as Responses detail objects.
    Reasoning detail is optional because its absence does not affect the bill.
    """
    if not isinstance(usage, Mapping):
        raise ValueError("usage must be a mapping")
    input_tokens = _tokens(usage.get("input_tokens"), "usage.input_tokens")
    output_tokens = _tokens(usage.get("output_tokens"), "usage.output_tokens")
    details = usage.get("input_tokens_details")
    nested_cached = details.get("cached_tokens") if isinstance(details, Mapping) else None
    cached = usage.get("cached_input_tokens", nested_cached)
    cached = _tokens(cached, "usage.cached_input_tokens")
    if nested_cached is not None and cached != _tokens(nested_cached, "usage.cached_input_tokens"):
        raise ValueError("conflicting cached input counters")
    if cached > input_tokens:
        raise ValueError("cached input tokens exceed total input tokens")
    nested_write = details.get("cache_write_tokens") if isinstance(details, Mapping) else None
    cache_write = usage.get("cache_write_input_tokens", nested_write)
    if cache_write is not None:
        cache_write = _tokens(cache_write, "usage.cache_write_input_tokens")
        if nested_write is not None and cache_write != _tokens(nested_write, "usage.cache_write_input_tokens"):
            raise ValueError("conflicting cache write input counters")
        if cached + cache_write > input_tokens:
            raise ValueError("cached input and cache write tokens exceed total input tokens")
    if "total_tokens" in usage and _tokens(usage["total_tokens"], "usage.total_tokens") != input_tokens + output_tokens:
        raise ValueError("total_tokens does not equal input_tokens + output_tokens")
    output_details = usage.get("output_tokens_details")
    nested_reasoning = output_details.get("reasoning_tokens") if isinstance(output_details, Mapping) else None
    reasoning = usage.get("reasoning_output_tokens", nested_reasoning)
    if reasoning is not None:
        reasoning = _tokens(reasoning, "usage.reasoning_output_tokens")
        if nested_reasoning is not None and reasoning != _tokens(nested_reasoning, "usage.reasoning_output_tokens"):
            raise ValueError("conflicting reasoning output counters")
        if reasoning > output_tokens:
            raise ValueError("reasoning output tokens exceed total output tokens")
    return {
        "input_tokens": input_tokens,
        "uncached_input_tokens": input_tokens - cached - cache_write if cache_write is not None else None,
        "cached_input_tokens": cached,
        "cache_write_input_tokens": cache_write,
        "output_tokens": output_tokens,
        "reasoning_output_tokens": reasoning,
        "total_tokens": input_tokens + output_tokens,
    }


class BudgetLedger:
    """One durable SQLite accounting authority; admission belongs to callers."""

    def __init__(self, path: str | Path, *, readonly: bool = False):
        if str(path) == ":memory:":
            raise ValueError("a shared budget ledger requires a durable database path")
        self.path = Path(path).resolve()
        self.readonly = readonly
        if readonly:
            # Export may inspect old schemas, but must never initialize,
            # migrate, checkpoint or otherwise rewrite an archived ledger.
            return
        self.path.parent.mkdir(parents=True, exist_ok=True)
        connection = self._connect()
        try:
            connection.execute("PRAGMA journal_mode=WAL")
            connection.executescript("""
                BEGIN IMMEDIATE;
                CREATE TABLE IF NOT EXISTS episodes (
                    episode_id TEXT PRIMARY KEY, limit_usd TEXT NOT NULL,
                    created_at TEXT NOT NULL
                );
                CREATE TABLE IF NOT EXISTS requests (
                    request_id TEXT PRIMARY KEY,
                    episode_id TEXT NOT NULL REFERENCES episodes(episode_id),
                    model TEXT NOT NULL, input_tokens INTEGER NOT NULL,
                    max_output_tokens INTEGER NOT NULL, prices_json TEXT NOT NULL,
                    metadata_json TEXT NOT NULL, reserved_usd TEXT NOT NULL,
                    hold_usd TEXT NOT NULL, actual_usd TEXT,
                    status TEXT NOT NULL, usage_json TEXT, error_json TEXT,
                    completion_json TEXT, created_at TEXT NOT NULL,
                    updated_at TEXT NOT NULL
                );
                CREATE INDEX IF NOT EXISTS requests_episode ON requests(episode_id);
                CREATE TABLE IF NOT EXISTS events (
                    sequence INTEGER PRIMARY KEY AUTOINCREMENT,
                    episode_id TEXT NOT NULL REFERENCES episodes(episode_id),
                    request_id TEXT, kind TEXT NOT NULL, timestamp TEXT NOT NULL,
                    data_json TEXT NOT NULL
                );
                CREATE INDEX IF NOT EXISTS events_episode ON events(episode_id);
                CREATE TABLE IF NOT EXISTS relay_state (
                    episode_id TEXT PRIMARY KEY REFERENCES episodes(episode_id),
                    limit_usd TEXT NOT NULL, stop_reason TEXT, last_error TEXT,
                    last_error_phase TEXT
                );
                CREATE INDEX IF NOT EXISTS e6_unbilled_requests
                ON events(episode_id,request_id) WHERE kind='request_not_dispatched';
                COMMIT;
            """)
        finally:
            connection.close()

    def _connect(self) -> sqlite3.Connection:
        target = self.path.as_uri() + "?mode=ro" if self.readonly else self.path
        connection = sqlite3.connect(target, uri=self.readonly, timeout=30, isolation_level=None)
        connection.row_factory = sqlite3.Row
        connection.execute("PRAGMA foreign_keys=ON")
        if not self.readonly:
            connection.execute("PRAGMA synchronous=FULL")
        return connection

    @contextmanager
    def _transaction(self, *, write: bool = True) -> Iterator[sqlite3.Connection]:
        if write and self.readonly:
            raise ValueError("This ledger was opened for read-only verification")
        connection = self._connect()
        try:
            connection.execute("BEGIN IMMEDIATE" if write else "BEGIN")
            yield connection
            connection.commit()
        except BaseException:
            connection.rollback()
            raise
        finally:
            connection.close()

    @staticmethod
    def _now() -> str:
        return datetime.now(timezone.utc).isoformat()

    def _event(self, connection: sqlite3.Connection, episode_id: str,
               request_id: str | None, kind: str, data: Any) -> None:
        connection.execute(
            "INSERT INTO events(episode_id,request_id,kind,timestamp,data_json) VALUES(?,?,?,?,?)",
            (episode_id, request_id, kind, self._now(), _json(data)),
        )

    @staticmethod
    def _request(row: sqlite3.Row) -> dict[str, Any]:
        prices = json.loads(row["prices_json"])
        metadata = json.loads(row["metadata_json"])
        usage = json.loads(row["usage_json"]) if row["usage_json"] else None
        reported_cost = isinstance(metadata, Mapping) and metadata.get("billing_basis") == "provider_reported_cost"
        bounded_input = (not reported_cost and usage is not None and usage["cache_write_input_tokens"] is None
                         and _covers_cache_writes(prices, metadata))
        result = {
            "request_id": row["request_id"], "episode_id": row["episode_id"],
            "model": row["model"], "status": row["status"],
            "input_tokens": row["input_tokens"], "max_output_tokens": row["max_output_tokens"],
            "reserved_usd": row["reserved_usd"], "hold_usd": row["hold_usd"],
            "actual_usd": row["actual_usd"], "prices": prices,
            "metadata": metadata, "usage": usage,
            "cost_basis": ("unknown" if row["actual_usd"] is None else
                           "provider_reported_cost" if reported_cost else
                           "unclassified_input_upper_bound" if bounded_input else "reported_usage"),
            "error": json.loads(row["error_json"]) if row["error_json"] else None,
            # Historical event receipts retain this field for schema compatibility.
            "reservation_exceeded": (row["actual_usd"] is not None
                                     and Decimal(row["actual_usd"]) > Decimal(row["reserved_usd"])),
        }
        if reported_cost:
            result["reported_accounting"] = (json.loads(row["completion_json"]).get("reported_accounting")
                                             if row["completion_json"] else None)
        return result

    def create_episode(self, episode_id: str, limit_usd: Any = "3") -> dict[str, Any]:
        if not isinstance(episode_id, str) or not episode_id:
            raise ValueError("episode_id must be a nonempty string")
        limit = _money(_decimal(limit_usd, "limit_usd"))
        with self._transaction() as connection:
            existing = connection.execute("SELECT * FROM episodes WHERE episode_id=?", (episode_id,)).fetchone()
            if existing:
                if existing["limit_usd"] != limit:
                    raise ValueError("episode already exists with a different limit")
            else:
                connection.execute("INSERT INTO episodes VALUES(?,?,?)", (episode_id, limit, self._now()))
                self._event(connection, episode_id, None, "episode_created", {"limit_usd": limit})
            return self._status(connection, episode_id)

    def initialize_relay_control(self, episode_id: str, limit_usd: Any) -> dict[str, Any]:
        """Restore durable relay decisions; monitor snapshots are expendable."""
        limit = _money(_decimal(limit_usd, "limit_usd"))
        with self._transaction() as connection:
            self._status(connection, episode_id)
            saved = connection.execute("SELECT * FROM relay_state WHERE episode_id=?", (episode_id,)).fetchone()
            if saved is None:
                connection.execute("INSERT INTO relay_state(episode_id,limit_usd) VALUES(?,?)", (episode_id, limit))
                return {"stop_reason": None, "last_error": None, "last_error_phase": None}
            if Decimal(saved["limit_usd"]) != Decimal(limit):
                raise ValueError("Saved public spend threshold differs from this run")
            return {key: saved[key] for key in ("stop_reason", "last_error", "last_error_phase")}

    def update_relay_control(self, episode_id: str, *, stop_reason: str | None,
                             last_error: str | None, last_error_phase: str | None) -> None:
        with self._transaction() as connection:
            cursor = connection.execute(
                "UPDATE relay_state SET stop_reason=?,last_error=?,last_error_phase=? WHERE episode_id=?",
                (stop_reason, last_error, last_error_phase, episode_id))
            if cursor.rowcount != 1:
                raise KeyError(f"uninitialized relay control for {episode_id!r}")

    def begin_request(self, episode_id: str, request_id: str, model: str,
                      prices: Mapping[str, Any], metadata: Any = None) -> dict[str, Any]:
        """Record a durable in-flight marker without imposing an admission cap.

        Token counters in this historical schema are placeholders. Reported
        terminal usage is the only source of the native relay's dollar amount.
        The caller serializes admission and decides whether another request may
        begin; this operation deliberately admits even above the episode limit.
        """
        if not isinstance(request_id, str) or not request_id:
            raise ValueError("request_id must be a nonempty string")
        if not isinstance(model, str) or not model:
            raise ValueError("model must be a nonempty string")
        normalized_prices = _prices(prices)
        _covers_cache_writes(normalized_prices, metadata)
        prices_json, metadata_json = _json(normalized_prices), _json(metadata)
        with self._transaction() as connection:
            self._status(connection, episode_id)
            existing = connection.execute("SELECT * FROM requests WHERE request_id=?", (request_id,)).fetchone()
            if existing is not None:
                expected = (episode_id, model, 0, 0, prices_json, metadata_json, "0")
                actual = tuple(existing[key] for key in (
                    "episode_id", "model", "input_tokens", "max_output_tokens", "prices_json", "metadata_json", "reserved_usd"))
                if actual != expected:
                    raise ValueError("request_id already exists with different request facts")
                return self._request(existing)
            now = self._now()
            connection.execute("""
                INSERT INTO requests(request_id,episode_id,model,input_tokens,max_output_tokens,
                    prices_json,metadata_json,reserved_usd,hold_usd,status,created_at,updated_at)
                VALUES(?,?,?,0,0,?,?,'0','0','reserved',?,?)
            """, (request_id, episode_id, model, prices_json, metadata_json, now, now))
            row = connection.execute("SELECT * FROM requests WHERE request_id=?", (request_id,)).fetchone()
            result = self._request(row)
            self._event(connection, episode_id, request_id, "request_reserved", result)
            return result


    def settle_request(self, request_id: str, usage: Any, failure: Any = None, *,
                       reported_terminal: bool = False) -> dict[str, Any]:
        """Atomically settle usage and preserve a reported terminal failure.

        A model's unsuccessful terminal response can still contain authoritative
        billing counters. A transport interruption cannot establish complete
        usage and remains unknown. Neither fact decides research eligibility.
        """
        return self._settle(request_id, usage,
                              None if reported_terminal else failure,
                              reported_failure=failure if reported_terminal else None)

    def settle_reported_cost(self, request_id: str, usage: Any, *,
                             provider: str | None = None, model: str | None = None,
                             failure: Any = None, not_dispatched_phase: str | None = None) -> dict[str, Any]:
        """Settle an explicit provider bill, preserving its raw token counters.

        The authoritative dollar amount is usage.cost. No catalog rate or
        invented token partition is used for this accounting mode. Missing or
        invalid cost remains unknown even when a response contains token usage.
        """
        amount = None
        accounting_error = None
        try:
            if not isinstance(usage, Mapping) or "cost" not in usage:
                raise ValueError("missing_usage.cost")
            amount = _money(_decimal(usage["cost"], "usage.cost"))
            _json(usage)
        except (ValueError, TypeError) as exc:
            accounting_error = str(exc)
        accounting = {"provider": provider, "model": model, "reported_cost_usd": amount}
        completion_data = {"usage": usage, "reported_accounting": accounting,
                           "accounting_error": accounting_error, "reported_failure": failure}
        if not_dispatched_phase is not None:
            completion_data["not_dispatched_phase"] = not_dispatched_phase
        completion = _json(completion_data)
        with self._transaction() as connection:
            row = connection.execute("SELECT * FROM requests WHERE request_id=?", (request_id,)).fetchone()
            if row is None:
                raise KeyError(f"unknown request_id {request_id!r}")
            metadata = json.loads(row["metadata_json"])
            if not isinstance(metadata, Mapping) or metadata.get("billing_basis") != "provider_reported_cost":
                raise ValueError("Request was not begun in provider-reported-cost mode")
            if row["completion_json"] == completion:
                return self._request(row)
            if row["status"] == "completed":
                raise ValueError("request already completed with different reported cost")
            errors = {"provider_error": failure, "accounting_error": accounting_error}
            connection.execute("""
                UPDATE requests SET actual_usd=?,hold_usd='0',status=?,usage_json=?,error_json=?,
                    completion_json=?,updated_at=? WHERE request_id=?
            """, (amount, "completed" if accounting_error is None else "unknown",
                  _json(usage) if usage is not None else None,
                  _json(errors) if failure is not None or accounting_error else None,
                  completion, self._now(), request_id))
            updated = connection.execute("SELECT * FROM requests WHERE request_id=?", (request_id,)).fetchone()
            result = self._request(updated)
            self._event(connection, row["episode_id"], request_id,
                        "request_completed" if accounting_error is None else "request_unknown", result)
            if failure is not None and accounting_error is None:
                self._event(connection, row["episode_id"], request_id,
                            "response_failed_with_reported_usage", failure)
            if not_dispatched_phase is not None:
                if amount != "0":
                    raise ValueError("An undispatched request must have zero reported cost")
                self._event(connection, row["episode_id"], request_id,
                            "request_not_dispatched", {"phase": not_dispatched_phase})
            return result

    def cancel_request(self, request_id: str, phase: str) -> dict[str, Any]:
        """Settle at zero only when upstream transport was never invoked."""
        with self._transaction(write=False) as connection:
            row = connection.execute("SELECT metadata_json FROM requests WHERE request_id=?", (request_id,)).fetchone()
            metadata = json.loads(row["metadata_json"]) if row is not None else None
        if isinstance(metadata, Mapping) and metadata.get("billing_basis") == "provider_reported_cost":
            return self.settle_reported_cost(request_id, {"cost": "0"}, not_dispatched_phase=phase)
        return self._settle(request_id,
                              {"input_tokens": 0, "output_tokens": 0, "cached_input_tokens": 0},
                              not_dispatched_phase=phase)

    def _settle(self, request_id: str, usage: Any, error: Any = None, *,
                  reported_failure: Any = None, not_dispatched_phase: str | None = None) -> dict[str, Any]:
        normalized = None
        accounting_error = None
        if usage is None:
            accounting_error = "missing_usage"
        else:
            try:
                normalized = normalize_usage(usage)
            except ValueError as exc:
                accounting_error = f"invalid_usage: {exc}"
        with self._transaction() as connection:
            row = connection.execute("SELECT * FROM requests WHERE request_id=?", (request_id,)).fetchone()
            if row is None:
                raise KeyError(f"unknown request_id {request_id!r}")
            prices = json.loads(row["prices_json"])
            covers_cache_writes = _covers_cache_writes(prices, json.loads(row["metadata_json"]))
            if normalized is not None:
                write_tokens = normalized["cache_write_input_tokens"]
                if write_tokens is None and "cache_write" in prices and not covers_cache_writes:
                    accounting_error = "missing_usage.cache_write_input_tokens"
                elif write_tokens and "cache_write" not in prices:
                    accounting_error = "unpriced_usage.cache_write_input_tokens"
            completion_data = {"usage": normalized, "error": error, "accounting_error": accounting_error}
            if reported_failure is not None:
                completion_data["reported_failure"] = reported_failure
            if not_dispatched_phase is not None:
                completion_data["not_dispatched_phase"] = not_dispatched_phase
            completion = _json(completion_data)
            if row["completion_json"] == completion:
                return self._request(row)
            if row["status"] == "completed":
                raise ValueError("request already completed with different usage or error")
            if normalized is not None and accounting_error is None and row["usage_json"] is not None:
                if _json(normalized) != row["usage_json"]:
                    raise ValueError("request already has different known usage")
            actual_usd = row["actual_usd"]
            usage_json = row["usage_json"]
            if normalized is not None and accounting_error is None:
                # For an unknown write partition, allocate noncached input to
                # the covering input rate without inventing a zero usage count.
                actual_usd = _money(_cost(normalized["input_tokens"], normalized["cached_input_tokens"],
                                         normalized["output_tokens"], prices,
                                         normalized["cache_write_input_tokens"] or 0))
                usage_json = _json(normalized)
            known_success = normalized is not None and error is None and accounting_error is None
            hold = Decimal(0) if known_success else max(
                Decimal(0), _sum([Decimal(row["reserved_usd"]), Decimal(actual_usd or "0").copy_negate()]))
            errors = {"provider_error": error, "accounting_error": accounting_error}
            connection.execute("""
                UPDATE requests SET actual_usd=?,hold_usd=?,status=?,usage_json=?,error_json=?,
                    completion_json=?,updated_at=? WHERE request_id=?
            """, (actual_usd, _money(hold), "completed" if known_success else "unknown",
                  usage_json, _json(errors) if error is not None or accounting_error else None,
                  completion, self._now(), request_id))
            updated = connection.execute("SELECT * FROM requests WHERE request_id=?", (request_id,)).fetchone()
            result = self._request(updated)
            self._event(connection, row["episode_id"], request_id,
                        "request_completed" if known_success else "request_unknown", result)
            if reported_failure is not None and known_success:
                self._event(connection, row["episode_id"], request_id,
                            "response_failed_with_reported_usage", reported_failure)
            if not_dispatched_phase is not None:
                self._event(connection, row["episode_id"], request_id,
                            "request_not_dispatched", {"phase": not_dispatched_phase})
            return result

    def _status(self, connection: sqlite3.Connection, episode_id: str) -> dict[str, Any]:
        episode = connection.execute("SELECT * FROM episodes WHERE episode_id=?", (episode_id,)).fetchone()
        if episode is None:
            raise KeyError(f"unknown episode_id {episode_id!r}")
        rows = connection.execute("SELECT * FROM requests WHERE episode_id=?", (episode_id,)).fetchall()
        spent = _sum([Decimal(row["actual_usd"]) for row in rows if row["actual_usd"] is not None])
        selector_rows = [row for row in rows if isinstance(json.loads(row["metadata_json"]), dict)
                         and json.loads(row["metadata_json"]).get("kind") == "decision_rerank"]
        selector_spent = _sum([Decimal(row["actual_usd"]) for row in selector_rows if row["actual_usd"] is not None])
        reserved = _sum([Decimal(row["hold_usd"]) for row in rows])
        unknown = [row for row in rows if row["status"] == "unknown"]
        not_dispatched = {row[0] for row in connection.execute(
            "SELECT request_id FROM events WHERE episode_id=? AND kind='request_not_dispatched'", (episode_id,))}
        remaining = _sum([Decimal(episode["limit_usd"]), spent.copy_negate(), reserved.copy_negate()])
        return {
            "episode_id": episode_id, "limit_usd": episode["limit_usd"],
            "spent_usd": _money(spent), "reserved_usd": _money(reserved),
            "selector_spent_usd": _money(selector_spent), "selector_requests": len(selector_rows),
            "committed_usd": _money(_sum([spent, reserved])), "remaining_usd": _money(remaining),
            "unknown_requests": len(unknown),
            "unknown_usd": _money(_sum([Decimal(row["hold_usd"]) for row in unknown])),
            "active_requests": sum(row["status"] == "reserved" for row in rows),
            "completed_requests": sum(row["status"] == "completed" for row in rows),
            "metered_responses": sum(row["status"] == "completed" and row["request_id"] not in not_dispatched
                                     for row in rows),
            "request_count": len(rows), "over_limit": remaining < 0,
        }

    def status(self, episode_id: str) -> dict[str, Any]:
        with self._transaction(write=False) as connection:
            return self._status(connection, episode_id)

    def export_events(self, episode_id: str) -> list[dict[str, Any]]:
        """Return the episode's durable audit trail in transaction order."""
        with self._transaction(write=False) as connection:
            self._status(connection, episode_id)
            rows = connection.execute("SELECT * FROM events WHERE episode_id=? ORDER BY sequence", (episode_id,)).fetchall()
            return [{"sequence": row["sequence"], "episode_id": row["episode_id"],
                     "request_id": row["request_id"], "kind": row["kind"],
                     "timestamp": row["timestamp"], "data": json.loads(row["data_json"])}
                    for row in rows]

    def receipt(self, episode_id: str) -> dict[str, Any]:
        """Read one consistent, independently checked snapshot of usage facts.

        Historical request/event schemas are supported without modifying them.
        Token-rate totals are recomputed from normalized reported counters and
        stored prices. Explicit provider bills are checked against raw usage.cost
        and their durable settlement event, without applying token-rate prices.
        A logical digest covers rows and events, including WAL-resident changes.
        """
        with self._transaction(write=False) as connection:
            budget = self._status(connection, episode_id)
            rows = connection.execute(
                "SELECT * FROM requests WHERE episode_id=? ORDER BY created_at,request_id", (episode_id,)).fetchall()
            events = [{"sequence": row["sequence"], "episode_id": row["episode_id"],
                       "request_id": row["request_id"], "kind": row["kind"],
                       "timestamp": row["timestamp"], "data": json.loads(row["data_json"])}
                      for row in connection.execute(
                          "SELECT * FROM events WHERE episode_id=? ORDER BY sequence", (episode_id,))]
            tables = {row[0] for row in connection.execute("SELECT name FROM sqlite_master WHERE type='table'")}
            control_row = (connection.execute("SELECT * FROM relay_state WHERE episode_id=?", (episode_id,)).fetchone()
                           if "relay_state" in tables else None)
            control = dict(control_row) if control_row is not None else None
            requests = []
            for row in rows:
                fact = self._request(row)
                request_events = [event for event in events if event["request_id"] == row["request_id"]]
                reserved = [event for event in request_events if event["kind"] == "request_reserved"]
                if len(reserved) != 1:
                    raise ValueError("Request lacks a unique durable begin event")
                for key in ("model", "prices", "metadata", "reserved_usd"):
                    if reserved[0]["data"].get(key) != fact[key]:
                        raise ValueError(f"Request begin event disagrees on {key}")
                if row["actual_usd"] is not None and fact["cost_basis"] == "provider_reported_cost":
                    amount = _decimal(fact["usage"]["cost"], "usage.cost")
                    reported = fact["reported_accounting"]
                    if not isinstance(reported, Mapping) or _decimal(reported["reported_cost_usd"], "reported_cost_usd") != amount:
                        raise ValueError("Stored provider-reported cost disagrees with raw usage")
                    if _decimal(row["actual_usd"], "actual_usd") != amount:
                        raise ValueError("Stored request cost differs from provider-reported cost")
                elif row["actual_usd"] is not None:
                    usage = normalize_usage(fact["usage"])
                    if fact["usage"] != usage:
                        raise ValueError("Stored usage is not normalized")
                    writes = usage["cache_write_input_tokens"]
                    if writes is None and "cache_write" in fact["prices"] and not _covers_cache_writes(
                            fact["prices"], fact["metadata"]):
                        raise ValueError("Stored usage has an uncovered unknown cache-write partition")
                    if writes and "cache_write" not in fact["prices"]:
                        raise ValueError("Stored usage contains unpriced cache-write tokens")
                    amount = _cost(usage["input_tokens"], usage["cached_input_tokens"],
                                   usage["output_tokens"], fact["prices"], writes or 0)
                    if _decimal(row["actual_usd"], "actual_usd") != amount:
                        raise ValueError("Stored request cost differs from reported usage")
                terminal_kind = "request_completed" if row["status"] == "completed" else "request_unknown"
                if row["status"] != "reserved":
                    settled = [event for event in request_events if event["kind"] == terminal_kind]
                    if not settled or settled[-1]["data"] != fact:
                        raise ValueError("Request settlement differs from its durable event")
                no_dispatch = [event for event in request_events if event["kind"] == "request_not_dispatched"]
                if len(no_dispatch) > 1 or no_dispatch and (row["status"] != "completed" or Decimal(row["actual_usd"]) != 0):
                    raise ValueError("Invalid undispatched request settlement")
                failures = [event["data"] for event in request_events if event["kind"] == "response_failed_with_reported_usage"]
                fact.update(not_dispatched=bool(no_dispatch), reported_terminal_failure=failures[-1] if failures else None)
                requests.append(fact)
            evidence = {"schema_version": 1, "episode_id": episode_id, "budget": budget,
                        "requests": requests, "events": events, "control": control}
            return {**evidence, "authority": "billing.sqlite", "ledger_path": str(self.path),
                    "sha256": hashlib.sha256(_json(evidence).encode("utf-8")).hexdigest()}


def read_ledger_receipt(path: str | Path, episode_id: str = "serial-sol61") -> dict[str, Any]:
    """Verify a finished ledger without creating sidecars in its run directory.

    SQLite's mode=ro can still create WAL/shm sidecars. Copy the durable database
    and any WAL to disposable storage, check that the copies match stable source
    bytes, then inspect them. Uncheckpointed WAL usage remains authoritative.
    """
    path = Path(path).resolve()
    wal = path.with_name(path.name + "-wal")

    def digest(source: Path) -> str:
        with source.open("rb") as stream:
            return hashlib.file_digest(stream, "sha256").hexdigest()

    with TemporaryDirectory(prefix="e6-ledger-receipt-") as directory:
        sources = [path, *([wal] if wal.exists() else [])]
        before = {source: digest(source) for source in sources}
        for source in sources:
            copied = Path(directory) / source.name
            shutil.copyfile(source, copied)
            if digest(copied) != before[source]:
                raise ValueError("Billing ledger changed while copying verification evidence")
        if (wal.exists() != (wal in sources)
                or any(digest(source) != before[source] for source in sources)):
            raise ValueError("Billing ledger changed while copying verification evidence")
        receipt = BudgetLedger(Path(directory) / path.name, readonly=True).receipt(episode_id)
        return {**receipt, "ledger_path": str(path)}


def receipt_budget(receipt: Mapping[str, Any], through_pass: int | None = None) -> dict[str, Any]:
    """Derive cumulative usage facts from request pass metadata.

    This describes accounting only. The frozen experiment specification owns
    admission and whole-pass research eligibility.
    """
    if through_pass is not None and (type(through_pass) is not int or through_pass < 0):
        raise ValueError("through_pass must be a nonnegative integer")
    rows = []
    for request in receipt["requests"]:
        number = request["metadata"].get("pass") if isinstance(request["metadata"], Mapping) else None
        if type(number) is not int or number < 1:
            raise ValueError("Ledger request lacks valid pass metadata")
        if through_pass is None or number <= through_pass:
            rows.append(request)
    return {"spent_usd": _money(_sum([Decimal(row["actual_usd"]) for row in rows if row["actual_usd"] is not None])),
            "unknown_requests": sum(row["status"] == "unknown" for row in rows),
            "active_requests": sum(row["status"] == "reserved" for row in rows),
            "completed_requests": sum(row["status"] == "completed" for row in rows),
            "request_count": len(rows),
            "metered_responses": sum(row["status"] == "completed" and not row["not_dispatched"] for row in rows)}
