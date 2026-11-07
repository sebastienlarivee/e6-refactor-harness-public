"""Host-only Responses relay with frozen per-proof spending policies.

Native Codex owns context, compaction and reasoning. The relay serializes HTTP
attempts and records exact provider receipts. Shared ordinary keys use a local
reported-cost threshold, an endpoint output ceiling, and blocking unknown bills.
Legacy dedicated keys retain their provider backstop and recovery policy.
"""
from __future__ import annotations

from contextlib import contextmanager
from decimal import Decimal, InvalidOperation, localcontext
from datetime import datetime, timezone
import http.client
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import hashlib
import math
import os
import re
from pathlib import Path
import secrets
import socket
import threading
import time
from typing import Any
from urllib import error, parse, request

from .config import OpenRouterSettings
from .ledger import (BudgetExhausted, LedgerError, OpenRouterLedger,
                                UnsettledRequest, provider_cost)


UPSTREAM_URL = "https://openrouter.ai/api/v1/responses"
GENERATION_URL = "https://openrouter.ai/api/v1/generation"
MAX_BODY_BYTES = 32 * 1024 * 1024
MAX_EVENT_BYTES = 16 * 1024 * 1024
ROUTING_REJECTION_MESSAGE = (
    "No endpoints found that can handle the requested parameters. To learn more about provider routing, visit: "
    "https://openrouter.ai/docs/guides/routing/provider-selection")
ROUTING_REJECTION_MESSAGES = {
    "No endpoints found that can handle the requested parameters.", ROUTING_REJECTION_MESSAGE}
ROUTING_REJECTION_POLICY_URL = "https://openrouter.ai/pricing"
AFFORDABLE_OUTPUT_REJECTION = re.compile(
    r"This request requires more credits, or fewer max_tokens\. "
    r"You requested up to ([0-9]+) tokens, but can only afford ([0-9]+)\."
    r"(?: To increase, visit https://openrouter\.ai/"
    r"(settings/(?:keys|credits)|workspaces/[A-Za-z0-9_-]+/keys/[a-f0-9]+)"
    r" and (?:adjust the key's total limit|add more credits)\.?)?")
TERMINAL_EVENTS = {"response.completed", "response.failed", "response.incomplete"}
# Verified native Responses fields only. Unknown extensions could enable paid
# server tools, hidden conversation state, multiple generations, or auto routers.
REQUEST_FIELDS = {
    "model", "instructions", "input", "tools", "additional_tools", "tool_choice",
    "parallel_tool_calls", "reasoning", "store", "stream", "include", "service_tier",
    "max_output_tokens", "temperature", "top_p", "text", "metadata", "truncation",
    "user", "provider", "previous_response_id", "background", "context_management",
    "stream_options", "prompt_cache_key", "prompt_cache_retention", "safety_identifier",
    "client_metadata",
}


class RelayRejected(ValueError):
    def __init__(self, code: str, message: str, status: int = 400):
        super().__init__(message)
        self.code, self.status = code, status


class ProtocolAccountingError(RuntimeError):
    """Contradictory provider accounting or generation identity evidence."""


class PreSendTransportError(RuntimeError):
    """Our HTTPS connector proved the model POST had not yet been sent."""
    def __init__(self, category: str):
        if category not in {"dns_failure", "connection_refused"}:
            raise ValueError("Unknown pre-send transport failure category")
        self.category = category
        super().__init__("Upstream connection failed before the model request was sent")


class _PreSendHTTPSConnection(http.client.HTTPSConnection):
    def connect(self):
        # Connect/HTTPS tunnel/TLS setup precede the model request's send().
        # Never classify errors from sending or receiving as provably unbilled.
        try:
            return super().connect()
        except socket.gaierror:
            raise PreSendTransportError("dns_failure") from None
        except ConnectionRefusedError:
            raise PreSendTransportError("connection_refused") from None


class _PreSendHTTPSHandler(request.HTTPSHandler):
    def https_open(self, req):
        return self.do_open(_PreSendHTTPSConnection, req, context=self._context)


class _NoRedirect(request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


class OpenRouterTransport:
    """One-shot stdlib HTTPS transport. Credentials cannot follow redirects."""
    def __init__(self):
        self._opener = request.build_opener(_NoRedirect(), _PreSendHTTPSHandler())

    @contextmanager
    def open_response(self, payload: dict, *, api_key: str, timeout: float):
        req = request.Request(UPSTREAM_URL, data=json.dumps(payload, allow_nan=False).encode(),
                              headers={"Authorization": "Bearer " + api_key,
                                       "Content-Type": "application/json",
                                       "Accept": "text/event-stream" if payload.get("stream") else "application/json"},
                              method="POST")
        try:
            response = self._opener.open(req, timeout=timeout)
        except error.HTTPError as exc:
            response = exc
        with response:
            yield response

    def get_generation(self, generation_id: str, *, api_key: str, timeout: float) -> dict:
        req = request.Request(GENERATION_URL + "?" + parse.urlencode({"id": generation_id}),
                              headers={"Authorization": "Bearer " + api_key}, method="GET")
        with self._opener.open(req, timeout=timeout) as response:
            raw = response.read(MAX_BODY_BYTES + 1)
            if len(raw) > MAX_BODY_BYTES:
                raise ValueError("generation response too large")
            result = _load_json(raw)
            if not isinstance(result, dict):
                raise ValueError("invalid generation response")
            return result


def _reject_constant(value: str):
    raise ValueError("non-finite JSON number")


def _load_json(raw: bytes | str):
    return json.loads(raw, parse_float=Decimal, parse_constant=_reject_constant)


def _money(value: Any) -> Decimal | None:
    if isinstance(value, bool) or value is None:
        return None
    try:
        result = value if isinstance(value, Decimal) else Decimal(str(value))
    except (InvalidOperation, ValueError, TypeError):
        return None
    return result if result.is_finite() and result >= 0 else None


def _sum_money(values: list[Decimal]) -> Decimal:
    if not values:
        return Decimal(0)
    low = min(value.as_tuple().exponent for value in values)
    high = max(value.adjusted() for value in values)
    with localcontext() as context:
        context.prec = max(28, high - low + len(str(len(values))) + 3)
        return sum(values, Decimal(0))


def _jsonable(value: Any):
    if isinstance(value, Decimal):
        return str(value)
    if isinstance(value, dict):
        return {str(k): _jsonable(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [_jsonable(v) for v in value]
    return value


def _redact(value: Any, secret: str):
    if isinstance(value, str):
        return value.replace(secret, "[REDACTED]") if secret else value
    if isinstance(value, dict):
        return {_redact(k, secret): _redact(v, secret) for k, v in value.items()}
    if isinstance(value, list):
        return [_redact(v, secret) for v in value]
    return value


class _SSEObserver:
    """Observe JSON event data without changing the forwarded SSE wire bytes."""
    def __init__(self, observe):
        self.pending = bytearray()
        self.lines: list[bytes] = []
        self.size = 0
        self.observe = observe

    def feed(self, chunk: bytes):
        self.pending.extend(chunk)
        while b"\n" in self.pending:
            line, _, tail = self.pending.partition(b"\n")
            self.pending = bytearray(tail)
            line = bytes(line).rstrip(b"\r")
            self.size += len(line) + 1
            if self.size > MAX_EVENT_BYTES:
                raise ValueError("upstream event too large")
            if line:
                self.lines.append(line)
            else:
                data = b"\n".join(x[5:].lstrip(b" ") for x in self.lines if x.startswith(b"data:"))
                if data and data != b"[DONE]":
                    event = _load_json(data)
                    if not isinstance(event, dict):
                        raise ValueError("malformed event")
                    self.observe(event)
                self.lines, self.size = [], 0
        if self.size + len(self.pending) > MAX_EVENT_BYTES:
            raise ValueError("upstream event too large")

    def finish(self):
        if self.pending or self.lines:
            raise ValueError("upstream event truncated")


class _WireRedactor:
    """Protect the host key even when a malicious upstream splits it in chunks."""
    def __init__(self, key: str):
        self.key = key.encode()
        self.pending = b""

    def feed(self, chunk: bytes, *, final=False) -> bytes:
        data = self.pending + chunk
        if final or not self.key:
            self.pending = b""
            return data.replace(self.key, b"[REDACTED]") if self.key else data
        # Retain a suffix which could become the start of a split secret.
        keep = min(len(self.key) - 1, len(data))
        for size in range(keep, 0, -1):
            if data.endswith(self.key[:size]):
                self.pending = data[-size:]
                return data[:-size].replace(self.key, b"[REDACTED]")
        self.pending = b""
        return data.replace(self.key, b"[REDACTED]")


def _native_tools(tools: Any):
    if not isinstance(tools, list):
        raise RelayRejected("unsupported_tool", "Tools must be native function, custom, or namespace definitions")
    for tool in tools:
        if not isinstance(tool, dict) or tool.get("type") not in {"function", "custom", "namespace"}:
            raise RelayRejected("unsupported_tool", "Paid hosted tools are outside this relay's token-only scope")
        if tool["type"] == "namespace":
            _native_tools(tool.get("tools", []))


def _text_only(value: Any):
    if isinstance(value, dict):
        kind = value.get("type", "")
        if isinstance(kind, str) and (any(word in kind.lower() for word in ("image", "audio", "video"))
                                      or kind in {"input_file", "file", "computer_screenshot"}):
            raise RelayRejected("unsupported_modality", "Only text and native tool messages are admitted")
        if any(key in value for key in ("image_url", "audio_url", "video_url", "file_data", "file_id")):
            raise RelayRejected("unsupported_modality", "Only text and native tool messages are admitted")
        for child in value.values():
            _text_only(child)
    elif isinstance(value, list):
        for child in value:
            _text_only(child)


def _rejection_tags(message: str, digest: str, evidence_kind: str) -> dict:
    return {"billing_basis": "openrouter_routing_rejection",
            "routing_rejection_code": "no_compatible_endpoints",
            "routing_rejection_http_status": 404, "routing_rejection_error_code": 404,
            "routing_rejection_error_message": message,
            "routing_rejection_evidence_kind": evidence_kind,
            "routing_rejection_sha256": digest,
            "routing_rejection_policy_url": ROUTING_REJECTION_POLICY_URL}


def routing_rejection_metadata(http_status: int, raw_body: bytes) -> dict | None:
    """Recognize only OpenRouter's exact pre-provider routing rejection.

    This is a separate documented no-charge basis, never invented usage.cost.
    OpenRouter's pricing FAQ excludes failed model attempts and we prohibit all
    auxiliary services. Broad HTTP errors, partial responses, provider metadata,
    generation IDs, and missing usage are deliberately outside this exception.
    """
    if http_status != 404 or not isinstance(raw_body, bytes) or len(raw_body) > MAX_BODY_BYTES:
        return None
    try:
        document = _load_json(raw_body)
    except (ValueError, UnicodeError):
        return None
    if not isinstance(document, dict) or set(document) - {"error", "user_id"}:
        return None
    failure = document.get("error")
    if not isinstance(failure, dict) or set(failure) - {"code", "message", "type", "metadata"}:
        return None
    if (type(failure.get("code")) is not int or failure["code"] != 404
            or not isinstance(failure.get("message"), str)
            or failure["message"] not in ROUTING_REJECTION_MESSAGES):
        return None
    if failure.get("metadata") not in (None, {}) or failure.get("type") not in (None, "not_found"):
        return None
    return _rejection_tags(failure["message"], hashlib.sha256(raw_body).hexdigest(), "raw_response")


def credit_rejection_metadata(http_status: int, raw_body: bytes) -> dict | None:
    """Recognize documented OpenRouter pre-provider credit/budget rejections.

    Generic 402/403 responses, upstream errors and generations with missing cost
    remain unknown. Recognize structured limit_source and the exact legacy
    affordable-output rejection observed from the router.
    See https://openrouter.ai/docs/api_reference/limits.
    """
    sources = {
        402: {"openrouter_key_limit", "openrouter_credits", "openrouter_in_flight_budget"},
        403: {"openrouter_key_limit", "openrouter_guardrail_budget", "openrouter_workspace_budget"},
    }
    if http_status not in sources or len(raw_body) > MAX_BODY_BYTES:
        return None
    try:
        document = _load_json(raw_body)
    except (ValueError, UnicodeError):
        return None
    if not isinstance(document, dict) or set(document) - {"error", "user_id"}:
        return None
    failure = document.get("error")
    if (not isinstance(failure, dict) or set(failure) - {"code", "message", "metadata"}
            or type(failure.get("code")) is not int or failure["code"] != http_status):
        return None
    metadata = failure.get("metadata")
    hint = AFFORDABLE_OUTPUT_REJECTION.fullmatch(failure.get("message", "")) if isinstance(failure.get("message"), str) else None
    extra = {}
    if http_status == 402 and hint and metadata in (None, {}, {"provider_name": None}):
        requested, affordable = int(hint[1]), int(hint[2])
        if not 0 <= affordable < requested:
            return None
        source = "openrouter_key_limit" if "keys" in (hint[3] or "") else "openrouter_credits"
        extra = {"provider_requested_output_tokens": requested, "provider_affordable_output_tokens": affordable}
    else:
        if (not isinstance(metadata, dict)
                or set(metadata) - {"limit_source", "reason", "remedy_hint", "scope", "guardrail_id",
                                    "budget_id", "limit_usd", "spend_usd", "resets_at", "provider_name"}
                or metadata.get("provider_name") is not None
                or not isinstance(metadata.get("limit_source"), str)
                or metadata.get("limit_source") not in sources[http_status]):
            return None
        source = metadata["limit_source"]
        if http_status == 402 and hint and 0 <= int(hint[2]) < int(hint[1]):
            extra = {"provider_requested_output_tokens": int(hint[1]), "provider_affordable_output_tokens": int(hint[2])}
    return {"billing_basis": "openrouter_credit_rejection", "limit_source": source, **extra,
            "credit_rejection_http_status": http_status,
            "credit_rejection_sha256": hashlib.sha256(raw_body).hexdigest(),
            "credit_rejection_policy_url": "https://openrouter.ai/docs/api_reference/limits"}


class OpenRouterRelay:
    def __init__(self, root: str | Path, auth_path: str | Path | None = None, *,
                 settings: OpenRouterSettings | None = None, spec=None, model: str | None = None,
                 credential_provider=None, transport=None, request_timeout: float = 600,
                 proof_id: str | None = None, budget_policy: str = "provider-key-v1",
                 recovery_policy: str = "none", recovery_backoff=(0, 2, 10), recovery_sleep=None):
        if recovery_policy not in {"none", "generation-v1", "exclusive-key-v1"}:
            raise ValueError("Unknown frozen OpenRouter recovery policy")
        if (not isinstance(recovery_backoff, (list, tuple)) or not 1 <= len(recovery_backoff) <= 3
                or any(type(delay) not in (int, float) or not math.isfinite(delay) or not 0 <= delay <= 30
                       for delay in recovery_backoff)):
            raise ValueError("Recovery backoff requires one to three bounded nonnegative delays")
        if recovery_sleep is not None and not callable(recovery_sleep):
            raise ValueError("Recovery sleeper must be callable")
        self.recovery_policy = recovery_policy
        self._recovery_backoff = tuple(recovery_backoff)
        self._recovery_sleep = recovery_sleep or time.sleep
        if budget_policy not in ("local-actual-cost-v1", "provider-key-v1"):
            raise ValueError("Unknown frozen OpenRouter budget policy")
        self.budget_policy = budget_policy
        self._local_budget = budget_policy == "local-actual-cost-v1"
        self.root = Path(root)
        self.root.mkdir(parents=True, exist_ok=True)
        self.settings = settings or getattr(spec, "openrouter", None)
        if not isinstance(self.settings, OpenRouterSettings):
            raise ValueError("Frozen OpenRouterSettings are required")
        if (self.settings.model_id.startswith("openrouter/")
                or self.settings.model_id.endswith((":online", ":nitro", ":floor", ":exacto"))):
            raise ValueError("OpenRouter auto routers and paid model transformations are not admitted")
        if model is not None and model != self.settings.model_id:
            raise ValueError("Relay model differs from frozen OpenRouter settings")
        settings_path = self.root / "relay-settings.json"
        frozen_settings = self.settings.to_dict()
        try:
            with settings_path.open("x", encoding="utf-8") as source:
                source.write(json.dumps(frozen_settings, sort_keys=True, indent=2) + "\n")
        except FileExistsError:
            try:
                prior = json.loads(settings_path.read_text(encoding="utf-8"))
            except (OSError, ValueError, UnicodeError):
                raise ValueError("Cannot read the frozen relay settings") from None
            if prior != frozen_settings:
                raise ValueError("OpenRouter relay settings are immutable across proof resumes")
        if isinstance(request_timeout, bool) or not math.isfinite(request_timeout) or request_timeout <= 0:
            raise ValueError("request_timeout must be positive and finite")
        self.request_timeout = request_timeout
        self.auth_path = Path(auth_path).expanduser().resolve() if auth_path is not None else None
        if self.auth_path is not None and self.auth_path.is_relative_to(self.root.parent.resolve()):
            raise ValueError("Credential file must remain outside the proof/agent tree")
        self.credential_provider = credential_provider
        self._request_metadata = None
        self.transport = transport if transport is not None else OpenRouterTransport()
        policy_path = self.root / "relay-budget-policy.json"
        policy = {"schema_version": 1, "budget_policy": budget_policy}
        try:
            prior_policy = json.loads(policy_path.read_text(encoding="utf-8"))
        except FileNotFoundError:
            # An old ledger has the provider-key contract, even if it has not
            # dispatched yet. A new CLI default must not alter its recovery.
            if self._local_budget and (self.root / "openrouter.sqlite").exists():
                raise ValueError("Existing ledger has no frozen local budget policy") from None
            with policy_path.open("x", encoding="utf-8") as destination:
                destination.write(json.dumps(policy, sort_keys=True) + "\n")
                destination.flush()
                os.fsync(destination.fileno())
            descriptor = os.open(self.root, os.O_DIRECTORY)
            try:
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
        else:
            if prior_policy != policy:
                raise ValueError("OpenRouter budget policy is immutable across proof resumes")
        recovery_path = self.root / "relay-recovery-policy.json"
        recovery = {"schema_version": 1, "recovery_policy": recovery_policy}
        if recovery_path.exists():
            if json.loads(recovery_path.read_text(encoding="utf-8")) != recovery:
                raise ValueError("OpenRouter recovery policy is immutable across proof resumes")
        else:
            if recovery_policy != "none" and (self.root / "openrouter.sqlite").exists():
                raise ValueError("Existing ledger has no frozen recovery policy")
            with recovery_path.open("x", encoding="utf-8") as destination:
                destination.write(json.dumps(recovery, sort_keys=True) + "\n")
                destination.flush()
                os.fsync(destination.fileno())
            descriptor = os.open(self.root, os.O_DIRECTORY)
            try:
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
        self.ledger = OpenRouterLedger(self.root / "openrouter.sqlite", proof_id=proof_id or str(self.root.parent.resolve()),
                                      model=self.settings.model_id, limit_usd=self.settings.budget_usd)
        if self._local_budget:
            for receipt in self.ledger.requests():
                if receipt["state"] == "unknown" and (receipt["metadata"].get("unreported_cost_nonblocking") is True
                        or receipt["metadata"].get("presumed_zero_recovery") is not None):
                    if not self._valid_presumed_zero(receipt):
                        self.ledger.mark_unknown(receipt["request_id"], receipt["unknown_reason"], blocks_spending=True)
        self.token = secrets.token_urlsafe(32)
        self.url: str | None = None
        self.pass_number: int | None = None
        self._state = threading.RLock()
        self._idle = threading.Condition(self._state)
        self._admission = threading.Lock()
        self._active: set[str] = set()
        self._closed = False
        self._server = self._thread = None
        self._stop_reason: str | None = None
        self._last_error: str | None = None
        self._budget_failure_code: str | None = None
        stop_path = self.root / "relay-stop.json"
        if stop_path.exists():
            try:
                code = json.loads(stop_path.read_text(encoding="utf-8"))["code"]
                if code not in {"budget_reached", "unknown_usage", "account_error", "upstream_http_error", "accounting_error", "routing_rejected"}:
                    raise ValueError("invalid stop reason")
                self._stop_reason = self._budget_failure_code = code
                self._last_error = "A durable relay stop is recorded for this proof"
            except (OSError, ValueError, UnicodeError, KeyError, TypeError):
                raise ValueError("Cannot read the durable relay stop") from None
        self._write_status()

    def _credential(self) -> str:
        try:
            if self.credential_provider is not None:
                key = self.credential_provider()
            else:
                if self.auth_path is None:
                    raise ValueError("explicit host credential source required")
                key = self.auth_path.read_text(encoding="utf-8").strip()
            if not isinstance(key, str) or not key.strip() or any(ord(x) < 33 or ord(x) == 127 for x in key):
                raise ValueError("invalid credential")
            key = key.strip()
            fingerprint = hashlib.sha256(key.encode()).hexdigest()
            identity_path = self.root / "relay-key-identity.json"
            identity = {"schema_version": 1, "key_sha256": fingerprint}
            try:
                with identity_path.open("x", encoding="utf-8") as destination:
                    destination.write(json.dumps(identity, sort_keys=True) + "\n")
                    destination.flush()
                    os.fsync(destination.fileno())
                descriptor = os.open(self.root, os.O_DIRECTORY)
                try:
                    os.fsync(descriptor)
                finally:
                    os.close(descriptor)
            except FileExistsError:
                if json.loads(identity_path.read_text(encoding="utf-8")) != identity:
                    raise ValueError("Proof credential identity is immutable")
            return key
        except Exception:
            raise RelayRejected("credential_unavailable", "Host OpenRouter credential is unavailable", 503) from None

    def start_pass(self, number: int):
        if isinstance(number, bool) or not isinstance(number, int) or number < 1:
            raise ValueError("pass number must be a positive integer")
        with self._state:
            if self._active:
                raise RuntimeError("Cannot change pass while a request is active")
            self.pass_number = number
            self._request_metadata = None
        self._write_status()

    set_pass = start_pass

    def status(self) -> dict:
        with self._state:
            snapshot = _jsonable(self.ledger.snapshot())
            active = snapshot.get("active_requests", [])
            unknown = snapshot.get("unknown_requests", [])
            receipts = _jsonable(self.ledger.pass_receipts())
            current = self.pass_number
            pass_amounts: dict[str, list[Decimal]] = {}
            for item in receipts:
                if item.get("cost_usd") is not None:
                    pass_amounts.setdefault(str(item["pass_number"]), []).append(Decimal(item["cost_usd"]))
            pass_costs = {number: _sum_money(amounts) for number, amounts in pass_amounts.items()}
            spent = pass_costs.get(str(current), Decimal(0))
            reason = self._stop_reason or snapshot.get("halted_reason")
            over_budget = max(Decimal(0), _sum_money([
                Decimal(snapshot["spent_usd"]), Decimal(snapshot["limit_usd"]).copy_negate()]))
            if (over_budget > 0 and reason in {"actual_cost_exceeded_reservation", "actual_cost_exceeded_budget"}):
                # A provider can settle its last admitted request above the key
                # limit. Stop normally, while keeping the breach and exact cost
                # in the ledger and report; this is not an unknown charge.
                reason = "budget_reached"
            if reason == "request_in_flight":
                reason = None if self._active else "unknown_usage"
            elif reason == "unreconciled_provider_cost" and self._stop_reason is None:
                # BYOK evidence is durably unknown before its charge settles.
                # Let the owning HTTP handler finish before treating that state
                # as a native-agent stop. The ledger reservation and admission
                # lock still block spending; unowned liabilities remain stops.
                if all(item["request_id"] in self._active for item in active if item["state"] == "unknown"):
                    reason = None
            elif reason == "budget_exhausted":
                # Settling the last admitted response must not interrupt its
                # native finalization. The next admission gate records the cap.
                reason = None
            return {**snapshot, "provider": "openrouter", "model": self.settings.model_id,
                    "endpoint_provider": self.settings.provider, "pass": current,
                    "pass_spent_usd": str(spent), "pass_receipts": receipts,
                    "active_request_ids": [x["request_id"] for x in active],
                    "unknown_request_ids": [x["request_id"] for x in unknown],
                    "pass_costs_usd": _jsonable(pass_costs), "metering_enabled": True,
                    "request_count": len(receipts),
                    "dispatched_requests": sum(x.get("dispatched_at") is not None for x in receipts),
                    "completed_requests": sum(x["state"] == "settled" for x in receipts),
                    "metered_responses": sum(x["state"] == "settled" and x.get("metadata", {}).get("billing_basis") not in {"openrouter_routing_rejection", "openrouter_credit_rejection"} for x in receipts),
                    "routing_rejected_requests": sum(x.get("metadata", {}).get("billing_basis") == "openrouter_routing_rejection" for x in receipts),
                    "credit_rejected_requests": sum(x.get("metadata", {}).get("billing_basis") == "openrouter_credit_rejection" for x in receipts),
                    "active_requests": len(active), "unknown_requests": len(unknown),
                    "blocking_unknown_requests": len(snapshot.get("blocking_unknown_requests",
                        [row for row in unknown if row["request_id"] in {item["request_id"] for item in active}])),
                    "provisional_unknown_requests": len(snapshot.get("provisional_unknown_requests", [])),
                    "cost_reporting_complete": not unknown,
                    "over_budget_usd": str(over_budget),
                    "stop_reason": reason, "budget_failure_code": self._budget_failure_code,
                    "last_error": self._last_error, "closed": self._closed,
                    "budget_policy": self.budget_policy, "recovery_policy": self.recovery_policy,
                    "provider_budget_is_per_proof": not self._local_budget,
                    "admission_policy": "local_actual_cost" if self._local_budget else "provider_key_limit_and_actual_cost",
                    "strict_dollar_cap_claimed": False,
                    "context_management": "native_codex",
                    "context_admission_enabled": False,
                    "reservation_policy": "hold_remaining_allowance_during_http_attempt",
                    "last_request_policy": self._request_metadata,
                    "accounting_authority": "openrouter.sqlite",
                    "billing_basis": ("openrouter_byok_fee_plus_upstream" if any(
                        x["usage"].get("is_byok") is True for x in receipts)
                        else "openrouter_reported_usage_cost"),
                    "output_cap_tokens": self.settings.max_output_tokens if self._local_budget else None,
                    "output_policy": "endpoint_ceiling_with_provider_rejection_hint" if self._local_budget else "native_passthrough_with_provider_rejection_hint",
                    "unreported_cost_policy": "block_proof" if self._local_budget else "provider_key_backstop",
                    "prompt_cache_policy": "anthropic_ephemeral" if self.settings.automatic_prompt_cache else "native_provider_default",
                    "minimum_request_reservation_usd": None,
                    "input_price_per_million": str(self.settings.input_price_per_million),
                    "output_price_per_million": str(self.settings.output_price_per_million),
                    "context_length": self.settings.context_length}

    @property
    def metering_enabled(self) -> bool:
        return True

    @property
    def stop_reason(self):
        return self.status()["stop_reason"]

    def gate_request(self) -> bool:
        status = self.status()
        if (status["closed"] or status["stop_reason"] or status["active_requests"]
                or self._active):
            return False
        if Decimal(status["remaining_usd"]) <= 0:
            self._stop("budget_reached", "Reported charges exhausted the proof allowance")
            return False
        return True

    def _write_status(self):
        try:
            status = self.status()
            target = self.root / "status.json"
            temporary = self.root / (".status-" + secrets.token_hex(6) + ".tmp")
            temporary.write_text(json.dumps(status, indent=2, allow_nan=False) + "\n", encoding="utf-8")
            temporary.replace(target)
        except OSError:
            # The SQLite ledger remains authoritative if an expendable snapshot
            # cannot be written; no admission decision depends on status.json.
            pass

    def _stop(self, code: str, message: str):
        with self._state:
            self._stop_reason = self._stop_reason or code
            self._last_error = message
            self._budget_failure_code = code
            target = self.root / "relay-stop.json"
            temporary = self.root / (".stop-" + secrets.token_hex(6) + ".tmp")
            try:
                temporary.write_text(json.dumps({"code": self._stop_reason}) + "\n", encoding="utf-8")
                temporary.replace(target)
            except OSError:
                # Ledger unknown/breach markers remain authoritative; a failed
                # control receipt also prevents admission in this process.
                self._stop_reason = "accounting_error"
        self._write_status()

    def _prepare(self, payload: Any) -> tuple[dict, Decimal]:
        if not isinstance(payload, dict):
            raise RelayRejected("invalid_request", "Responses request must be a JSON object")
        frozen = self.settings
        if set(payload) - REQUEST_FIELDS:
            raise RelayRejected("unsupported_request", "Unverified Responses extensions are not admitted")
        if payload.get("model", frozen.model_id) != frozen.model_id:
            raise RelayRejected("model_mismatch", "Requested model differs from the frozen model")
        if any(key in payload for key in ("models", "route", "plugins", "web_search_options", "modalities", "audio", "image", "images")):
            raise RelayRejected("unsupported_request", "Model fallback, plugins, and multimodal requests are not admitted")
        if payload.get("previous_response_id") is not None:
            raise RelayRejected("unsupported_state", "previous_response_id is not admitted; send native history explicitly")
        if payload.get("background"):
            raise RelayRejected("unsupported_state", "Background Responses requests are not admitted")
        if payload.get("context_management"):
            raise RelayRejected("unsupported_state", "Send native compaction as an explicit bounded request")
        for key in ("tools", "additional_tools"):
            if key in payload:
                _native_tools(payload[key])
        # Schemas and custom tool text may legitimately mention images. Only
        # actual input/history structures are inspected for paid modalities.
        _text_only(payload.get("input", []))
        requested_cap = payload.get("max_output_tokens")
        if requested_cap is not None and (type(requested_cap) is not int or requested_cap <= 0):
            raise RelayRejected("invalid_output_cap", "max_output_tokens must be a positive integer")
        # Shared keys have an explicit endpoint ceiling, not an affordability
        # estimate. Legacy keys preserve omitted native output limits.
        prepared = dict(payload)
        if self._local_budget:
            prepared["max_output_tokens"] = min(requested_cap or frozen.max_output_tokens, frozen.max_output_tokens)
        prepared.update({"model": frozen.model_id, "store": False,
                         "provider": {"only": [frozen.provider], "allow_fallbacks": False,
                                      "require_parameters": True,
                                      "max_price": {"prompt": str(frozen.input_price_per_million),
                                                    "completion": str(frozen.output_price_per_million),
                                                    "request": "0", "image": "0"}}})
        prepared.pop("previous_response_id", None)
        prepared.pop("service_tier", None)
        if frozen.automatic_prompt_cache:
            prepared["cache_control"] = {"type": "ephemeral"}
        # Codex's true value is an optional permission hint. DeepSeek advertises
        # tools, but not parallel_tool_calls; require_parameters must stay true.
        # Preserve false, which expresses a meaningful serial-only constraint.
        if prepared.get("parallel_tool_calls") is True and not frozen.supports_parallel_tool_calls:
            prepared.pop("parallel_tool_calls")
        remaining = self.ledger.snapshot()["remaining_usd"]
        self._request_metadata = {
            "budget_policy": self.budget_policy,
            "admission_policy": "local_actual_cost" if self._local_budget else "provider_key_limit_and_actual_cost",
            "reservation_policy": "hold_remaining_allowance_during_http_attempt",
            "output_cap_tokens": prepared.get("max_output_tokens"),
            "context_admission_enabled": False,
        }
        return prepared, remaining

    def _receipt_cost(self, request_id: str, usage: dict, key: str):
        # Persist explicit BYOK liability before inspecting its possibly missing
        # or malformed amount. A restart must not turn this into a zero charge.
        prior_receipt = self.ledger.request(request_id)
        prior = prior_receipt["usage"]
        if (prior_receipt["metadata"].get("byok_liability_unresolved") is True
                and "is_byok" not in usage):
            return None
        if "is_byok" in usage and type(usage["is_byok"]) is not bool:
            self.ledger.mark_unknown(request_id, "Invalid provider BYOK accounting indicator",
                                     metadata={"byok_liability_unresolved": True})
            raise LedgerError("usage.is_byok must be boolean")
        if usage.get("is_byok") is True or prior.get("is_byok") is True:
            self.ledger.mark_unknown(request_id, "Awaiting complete BYOK provider liability",
                                     usage={"is_byok": True})
            receipt = self.ledger.mark_unknown(request_id, "Awaiting complete BYOK provider liability",
                                               usage=_redact(usage, key))
            return provider_cost(receipt["usage"])
        # Keep ordinary missing/invalid receipt handling unchanged: the key
        # backstop permits native retries while their unknown bill stays visible.
        if _money(usage.get("cost")) is None:
            return None
        return provider_cost(usage)

    def _settle(self, request_id: str, receipt: dict, key: str) -> bool:
        response = receipt.get("response")
        response = response if isinstance(response, dict) else receipt
        usage = response.get("usage")
        if not isinstance(usage, dict):
            return False
        costs = self._receipt_cost(request_id, usage, key)
        if costs is None:
            return False
        tags = self._metadata(response)
        if usage.get("is_byok") is True:
            tags["billing_basis"] = "openrouter_byok_fee_plus_upstream"
        self.ledger.settle(request_id, cost_usd=costs[0], usage=_redact(usage, key),
                           generation_id=response.get("id"), metadata=_redact(tags, key))
        return True

    @staticmethod
    def _metadata(response: dict) -> dict:
        result = {k: response[k] for k in ("id", "model", "status", "finish_reason", "native_finish_reason")
                  if isinstance(response.get(k), str) and len(response[k]) <= 256}
        incomplete = response.get("incomplete_details")
        if (response.get("status") == "incomplete" and isinstance(incomplete, dict)
                and incomplete.get("reason") in ("max_output_tokens", "content_filter")):
            result["incomplete_reason"] = incomplete["reason"]
        for key in ("provider", "provider_name"):
            if isinstance(response.get(key), str) and len(response[key]) <= 256:
                result["reported_" + key] = response[key]
        return result

    def _valid_presumed_zero(self, receipt: dict) -> bool:
        if self.recovery_policy != "exclusive-key-v1":
            return False
        try:
            if not self.ledger.presumed_zero_valid(receipt["request_id"]):
                return False
            marker = receipt["metadata"]["presumed_zero_recovery"]
            identity = json.loads((self.root / "relay-key-identity.json").read_text(encoding="utf-8"))
            return identity == {"schema_version": 1, "key_sha256": marker["key_sha256"]}
        except (LedgerError, OSError, ValueError, KeyError, TypeError):
            return False

    def _annotate_transport(self, request_id: str, **tags):
        allowed = {"response_headers_received", "output_observed", "request_bytes_sent", "transport_phase",
            "transport_failure", "transport_error_category", "transport_finished_at", "retry_exhausted",
            "protocol_conflict", "client_disconnected", "generation_id_header_observed", "generation_id_body_observed"}
        if set(tags) - allowed:
            raise ValueError("Unverified transport metadata field")
        booleans = allowed - {"request_bytes_sent", "transport_phase", "transport_error_category", "transport_finished_at"}
        if any(type(value) is not bool for name, value in tags.items() if name in booleans):
            raise ValueError("Transport evidence flags must be boolean")
        if ("request_bytes_sent" in tags and tags["request_bytes_sent"] is not None
                and type(tags["request_bytes_sent"]) is not bool):
            raise ValueError("Sent-byte evidence must be boolean or unknown")
        if tags.get("transport_phase", "dispatch") not in {"dispatch", "headers_received", "body_received", "pre_send", "completed", "failed"}:
            raise ValueError("Unverified transport phase")
        if tags.get("transport_error_category", "transport_error") not in {
                "dns_failure", "connection_refused", "timeout", "connection_lost", "incomplete_response",
                "invalid_response", "upstream_http_error", "transport_error", "protocol_error"}:
            raise ValueError("Unverified transport error category")
        if "transport_finished_at" in tags:
            stamp = tags["transport_finished_at"]
            if not isinstance(stamp, str) or len(stamp) > 64 or datetime.fromisoformat(stamp).utcoffset() is None:
                raise ValueError("Transport completion requires a bounded UTC timestamp")
        return self.ledger.annotate(request_id, metadata=tags)

    def _record_transport_failure(self, request_id: str | None, category: str, *, protocol=False):
        if request_id is None:
            return
        try:
            prior = self.ledger.request(request_id)["metadata"]
            if prior.get("transport_failure") is True and not protocol:
                return
            self._annotate_transport(request_id, transport_failure=True,
                transport_error_category=category, **({"protocol_conflict": True} if protocol else {}))
        except Exception:
            self._stop("accounting_error", "Transport evidence could not be durably recorded")

    @staticmethod
    def _transport_category(error: BaseException) -> str:
        if isinstance(error, TimeoutError):
            return "timeout"
        if isinstance(error, http.client.IncompleteRead):
            return "incomplete_response"
        if isinstance(error, (ConnectionError, OSError)):
            return "connection_lost"
        if isinstance(error, (ValueError, UnicodeError)):
            return "invalid_response"
        return "transport_error"

    def _poll_generation(self, request_id: str, generation_id: str | None, key: str) -> bool:
        if self.recovery_policy == "none":
            return self._reconcile(request_id, generation_id, key)
        if not generation_id:
            return False
        for delay in self._recovery_backoff:
            if delay:
                self._recovery_sleep(delay)
            if self._reconcile(request_id, generation_id, key):
                return True
            if self._stop_reason == "accounting_error":
                return False
        return False

    def _reconcile(self, request_id: str, generation_id: str | None, key: str) -> bool:
        if not generation_id or not hasattr(self.transport, "get_generation"):
            return False
        try:
            result = self.transport.get_generation(generation_id, api_key=key,
                                                    timeout=min(self.request_timeout, 30))
            data = result.get("data", result) if isinstance(result, dict) else None
            if not isinstance(data, dict) or data.get("id") is None:
                return False
            if data["id"] != generation_id:
                raise ProtocolAccountingError("generation lookup returned a conflicting identity")
            final = (data.get("status") in {"completed", "failed", "incomplete", "cancelled"}
                     or data.get("cancelled") is True
                     or any(isinstance(data.get(k), str) and bool(data[k])
                            for k in ("finish_reason", "native_finish_reason")))
            if not final:
                # A generation lookup can race provider finalization. A
                # provisional total_cost (especially zero) is not a final bill.
                return False
            usage = dict(data["usage"]) if isinstance(data.get("usage"), dict) else {}
            if (("is_byok" in data and type(data["is_byok"]) is not bool)
                    or ("is_byok" in usage and type(usage["is_byok"]) is not bool)):
                self.ledger.mark_unknown(request_id, "Invalid provider BYOK accounting indicator",
                                         metadata={"byok_liability_unresolved": True})
                return False
            if data.get("is_byok") is True or usage.get("is_byok") is True:
                self.ledger.mark_unknown(request_id, "Awaiting complete BYOK provider liability",
                                         usage={"is_byok": True})
            # The generation endpoint reports BYOK accounting at top level;
            # usage may be a scalar rather than a token-detail mapping. Preserve original amounts.
            for field in ("is_byok", "upstream_inference_cost", "upstream_inference_input_cost",
                          "upstream_inference_output_cost", "upstream_inference_prompt_cost",
                          "upstream_inference_completions_cost"):
                if field in data:
                    if field in usage:
                        same = (usage[field] == data[field] if field == "is_byok" else
                                _money(usage[field]) == _money(data[field]))
                        if not same:
                            raise LedgerError("conflicting generation accounting evidence")
                    usage[field] = data[field]
            if "total_cost" in data:
                if "cost" in usage and _money(usage["cost"]) != _money(data["total_cost"]):
                    raise LedgerError("generation total_cost conflicts with usage.cost")
                usage["cost"] = data["total_cost"]
            costs = self._receipt_cost(request_id, usage, key)
            if costs is None:
                return False
            tags = {**_redact(self._metadata(data), key), "reconciled": True}
            if "total_cost" in data:
                tags["generation_total_cost"] = str(data["total_cost"])
            if self.ledger.request(request_id)["usage"].get("is_byok") is True or usage.get("is_byok") is True:
                tags["billing_basis"] = "openrouter_byok_fee_plus_upstream"
            self.ledger.settle(request_id, cost_usd=costs[0], generation_id=generation_id,
                               usage=_redact(usage, key), metadata=tags)
            return True
        except (LedgerError, ProtocolAccountingError):
            self._record_transport_failure(request_id, "protocol_error", protocol=True)
            self._stop("accounting_error", "Conflicting or invalid provider accounting evidence")
            return False
        except Exception:
            return False

    def reconcile_pending(self) -> dict:
        """Reconcile persisted dispatches by final generation cost, never account totals."""
        if not self._admission.acquire(blocking=False):
            raise RuntimeError("Cannot reconcile an active request")
        try:
            for receipt in self.ledger.requests():
                if receipt["state"] == "reserved":
                    self.ledger.cancel_before_dispatch(receipt["request_id"])
                elif receipt["state"] in {"dispatched", "unknown"}:
                    if self._valid_presumed_zero(receipt):
                        continue
                    key = self._credential()
                    if (not self._poll_generation(receipt["request_id"], receipt["generation_id"], key)
                            and (self._local_budget or not (receipt["state"] == "unknown"
                                     and receipt["metadata"].get("unreported_cost_nonblocking") is True))):
                        self.ledger.mark_unknown(receipt["request_id"], "Awaiting authoritative final generation receipt",
                                                 blocks_spending=self._local_budget)
            snapshot = self.ledger.snapshot()
            if not snapshot["active_requests"] and snapshot["halted_reason"] is None and self._stop_reason in {"unknown_usage", "upstream_http_error"}:
                (self.root / "relay-stop.json").unlink(missing_ok=True)
                self._stop_reason = self._budget_failure_code = self._last_error = None
            self._write_status()
            return self.status()
        finally:
            self._admission.release()

    def _save_rejection_evidence(self, request_id: str, document: dict, *, suffix: str) -> str:
        directory = self.root / "routing-rejections"
        directory.mkdir(exist_ok=True)
        target = directory / (request_id + "-" + suffix + ".json")
        raw = json.dumps(_jsonable(document), indent=2, sort_keys=True, allow_nan=False).encode() + b"\n"
        try:
            with target.open("xb") as destination:
                destination.write(raw)
        except FileExistsError:
            if target.read_bytes() != raw:
                raise ValueError("routing evidence is immutable") from None
        return str(target.relative_to(self.root))

    def _settle_routing_rejection(self, request_id: str, raw_body: bytes, http_status: int, key: str) -> bool:
        tags = routing_rejection_metadata(http_status, raw_body)
        if (tags is None or self.ledger.request(request_id).get("generation_id") is not None
                or (key and (key.encode() in raw_body or _redact(_load_json(raw_body), key) != _load_json(raw_body)))):
            return False
        directory = self.root / "routing-rejections"
        directory.mkdir(exist_ok=True)
        target = directory / (request_id + "-raw-response.json")
        try:
            with target.open("xb") as destination:
                destination.write(raw_body)
        except FileExistsError:
            if target.read_bytes() != raw_body:
                raise ValueError("Original routing response is immutable") from None
        tags["routing_rejection_evidence_file"] = str(target.relative_to(self.root))
        self.ledger.settle(request_id, cost_usd=Decimal(0), metadata=tags)
        return True

    def _settle_credit_rejection(self, request_id: str, raw_body: bytes, http_status: int, key: str) -> dict | None:
        tags = credit_rejection_metadata(http_status, raw_body)
        if (tags is None or self.ledger.request(request_id).get("generation_id") is not None
                or (key and (key.encode() in raw_body or _redact(_load_json(raw_body), key) != _load_json(raw_body)))):
            return None
        directory = self.root / "credit-rejections"
        directory.mkdir(exist_ok=True)
        target = directory / (request_id + "-raw-response.json")
        with target.open("xb") as destination:
            destination.write(raw_body)
        tags["credit_rejection_evidence_file"] = str(target.relative_to(self.root))
        self.ledger.settle(request_id, cost_usd=Decimal(0), metadata=tags)
        return tags

    def _handle(self, handler: BaseHTTPRequestHandler):
        if handler.headers.get("Authorization") != "Bearer " + self.token:
            self._error(handler, RelayRejected("unauthorized", "Invalid local relay capability", 401))
            return
        if handler.path not in {"/v1/responses", "/responses"}:
            self._error(handler, RelayRejected("unsupported_route", "Only Responses requests are admitted", 404))
            return
        if not self._admission.acquire(blocking=False):
            self._error(handler, RelayRejected("request_in_flight", "A proof request is already in flight", 409))
            return
        request_id = None
        dispatched = settled = headers_sent = False
        generation_id = None
        terminal = None
        key = ""
        response_headers_received = output_observed = accounting_failed = False
        upstream_code = None
        try:
            if not self.gate_request():
                raise RelayRejected("spending_stopped", "OpenRouter spending is stopped for this proof", 402)
            if self.pass_number is None:
                raise RelayRejected("pass_not_started", "Start a proof pass before requesting inference", 409)
            length = handler.headers.get("Content-Length")
            if length is None or not length.isdigit() or not 0 < int(length) <= MAX_BODY_BYTES:
                raise RelayRejected("invalid_request", "A bounded Content-Length is required", 413)
            raw = handler.rfile.read(int(length))
            if len(raw) != int(length):
                raise RelayRejected("invalid_request", "Truncated request body")
            try:
                payload = json.loads(raw, parse_constant=_reject_constant)
            except (ValueError, UnicodeError):
                raise RelayRejected("invalid_request", "Malformed JSON request") from None
            prepared, reservation = self._prepare(payload)
            key = self._credential()
            for attempt in range(3):
                try:
                    with self._idle:
                        if self._closed:
                            raise RelayRejected("spending_stopped", "Relay closed before dispatch", 503)
                        request_id = self.ledger.reserve(reservation, pass_number=self.pass_number,
                                                         metadata={"provider": self.settings.provider,
                                                                   "frozen_provider": self.settings.provider,
                                                                   **self._request_metadata,
                                                                   "response_headers_received": False,
                                                                   "output_observed": False, "request_bytes_sent": None,
                                                                   "transport_phase": "dispatch", "protocol_conflict": False,
                                                                   "retry_exhausted": False})
                        self._active.add(request_id)
                except BudgetExhausted:
                    self._stop("budget_reached", "Proof allowance is exhausted or permanently halted")
                    raise RelayRejected("budget_reached", "Proof allowance is exhausted or permanently halted", 402) from None
                except UnsettledRequest:
                    self._stop("unknown_usage", "An earlier request has unsettled provider usage")
                    raise RelayRejected("unknown_usage", "An earlier request has unsettled provider usage", 402) from None
                self._write_status()
                self.ledger.mark_dispatched(request_id)
                dispatched = True
                response_headers_received = output_observed = False
                upstream_code = None
                def bind_generation(candidate, *, from_header=False):
                    nonlocal generation_id
                    if (not isinstance(candidate, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.:-]{0,255}", candidate)
                            or (key and key in candidate)):
                        raise ProtocolAccountingError("invalid upstream generation identity")
                    if generation_id is not None and generation_id != candidate:
                        raise ProtocolAccountingError("conflicting upstream generation identities")
                    tags = {"generation_id_header_observed" if from_header else "generation_id_body_observed": True}
                    if from_header:
                        tags.update(response_headers_received=True, request_bytes_sent=True,
                                    transport_phase="headers_received")
                    self.ledger.annotate(request_id, generation_id=candidate, metadata=tags)
                    generation_id = candidate
                def observe(event):
                    nonlocal terminal, generation_id, settled
                    response = event.get("response", event)
                    if isinstance(response, dict):
                        candidate = response.get("id")
                        if candidate is not None:
                            bind_generation(candidate)
                    if event.get("type") in TERMINAL_EVENTS:
                        if terminal is not None:
                            if terminal == event:
                                return
                            raise ProtocolAccountingError("conflicting terminal response events")
                        terminal = event
                        # Durably record the authoritative charge before native
                        # Codex observes completion and can begin another request.
                        # The admission lock remains held until the stream drains.
                        settled = self._settle(request_id, event, key)
                try:
                    with self.transport.open_response(prepared, api_key=key, timeout=self.request_timeout) as upstream:
                        # Header identity and explicit transport facts are durable
                        # before status handling or the first potentially failing read.
                        response_headers_received = True
                        headers = getattr(upstream, "headers", None) or {}
                        header_ids = (headers.get_all("X-Generation-Id", []) if hasattr(headers, "get_all") else
                            [value for name, value in headers.items() if str(name).lower() == "x-generation-id"])
                        if header_ids:
                            for header_id in header_ids:
                                bind_generation(header_id, from_header=True)
                        else:
                            self._annotate_transport(request_id, response_headers_received=True,
                                request_bytes_sent=True, transport_phase="headers_received")
                        code = upstream_code = getattr(upstream, "status", getattr(upstream, "code", 200))
                        if not 200 <= code < 300:
                            # Even an HTTP error may follow paid inference. Never infer
                            # zero spend from a status code or forward provider prose.
                            self._record_transport_failure(request_id, "upstream_http_error")
                            raw_error = upstream.read(MAX_BODY_BYTES + 1)
                            if raw_error.strip():
                                output_observed = True
                                self._annotate_transport(request_id, output_observed=True, transport_phase="body_received")
                            try:
                                document = _load_json(raw_error)
                                if isinstance(document, dict):
                                    observe(document)
                                    settled = self._settle(request_id, document, key)
                            except (ValueError, UnicodeError):
                                pass
                            if not settled and self._settle_routing_rejection(request_id, raw_error, code, key):
                                settled = True
                                self._stop("routing_rejected", "OpenRouter could not select a compatible endpoint")
                                raise RelayRejected("no_compatible_endpoints", "OpenRouter could not select a compatible endpoint", 404)
                            credit = None
                            if not settled:
                                credit = self._settle_credit_rejection(request_id, raw_error, code, key)
                                settled = credit is not None
                            credit_source = credit.get("limit_source") if credit else None
                            affordable = credit.get("provider_affordable_output_tokens") if credit else None
                            current_cap = prepared.get("max_output_tokens")
                            if (affordable is not None and affordable > 0 and attempt < 2
                                    and (current_cap is None or affordable < current_cap)):
                                # This is the provider's explicit response to an uncharged
                                # rejection, never a local token-price prediction. Retry
                                # the same history/tools/reasoning with that allowance.
                                prepared = {**prepared, "max_output_tokens": affordable}
                                self._request_metadata = {**self._request_metadata,
                                    "output_cap_tokens": affordable,
                                    "provider_advertised_output_cap": True}
                                with self._idle:
                                    self._active.discard(request_id)
                                request_id = None
                                dispatched = settled = False
                                generation_id = terminal = None
                                response_headers_received = output_observed = False
                                continue
                            account = code in {401, 402, 403}
                            if credit_source == "openrouter_key_limit" and not self._local_budget:
                                self._stop("budget_reached", "OpenRouter rejected the proof key's spending limit")
                            elif credit_source == "openrouter_in_flight_budget":
                                # Transient router hold. Forward Retry-After unchanged;
                                # native Codex owns retries and retains the same context.
                                pass
                            elif account:
                                self._stop("account_error", "OpenRouter account rejected the request")
                            handler.send_response(code)
                            handler.send_header("Content-Type", "application/json")
                            handler.send_header("Connection", "close")
                            for name in ("Retry-After", "X-Request-ID", "X-RateLimit-Remaining", "X-RateLimit-Reset"):
                                value = upstream.headers.get(name) if hasattr(upstream, "headers") else None
                                if value:
                                    handler.send_header(name, _redact(str(value), key))
                            handler.end_headers()
                            headers_sent = True
                            wire = _WireRedactor(key).feed(raw_error[:MAX_BODY_BYTES], final=True)
                            handler.wfile.write(wire)
                            return
                        handler.send_response(200)
                        handler.send_header("Content-Type", "text/event-stream" if prepared.get("stream") else "application/json")
                        handler.send_header("Connection", "close")
                        handler.end_headers()
                        headers_sent = True
                        redactor = _WireRedactor(key)
                        observer = _SSEObserver(observe) if prepared.get("stream") else None
                        body = bytearray()
                        disconnected = False
                        # HTTPResponse.read(size) may wait for the whole size. read1
                        # forwards available SSE bytes promptly, including tool calls.
                        read_chunk = getattr(upstream, "read1", upstream.read)
                        while True:
                            chunk = read_chunk(64 * 1024)
                            if not chunk:
                                break
                            if not output_observed and chunk.strip():
                                output_observed = True
                                self._annotate_transport(request_id, output_observed=True, transport_phase="body_received")
                            if observer:
                                observer.feed(chunk)
                            else:
                                body.extend(chunk)
                                if len(body) > MAX_BODY_BYTES:
                                    raise ValueError("upstream response too large")
                            wire = redactor.feed(chunk)
                            if wire and not disconnected:
                                try:
                                    handler.wfile.write(wire)
                                    handler.wfile.flush()
                                except (OSError, ValueError):
                                    disconnected = True
                                    self._annotate_transport(request_id, client_disconnected=True)
                        if observer:
                            observer.finish()
                        else:
                            document = _load_json(bytes(body))
                            if not isinstance(document, dict):
                                raise ValueError("malformed response")
                            observe(document)
                            terminal = document
                        tail = redactor.feed(b"", final=True)
                        if tail and not disconnected:
                            try:
                                handler.wfile.write(tail)
                                handler.wfile.flush()
                            except (OSError, ValueError):
                                pass
                        if terminal is not None:
                            settled = self._settle(request_id, terminal, key)
                except PreSendTransportError as error:
                    if response_headers_received or output_observed or generation_id is not None:
                        raise ProtocolAccountingError("pre-send evidence contradicts an upstream response") from None
                    self._annotate_transport(request_id, transport_phase="pre_send", request_bytes_sent=False,
                        response_headers_received=False, output_observed=False, transport_failure=True,
                        transport_error_category=error.category, retry_exhausted=attempt == 2,
                        transport_finished_at=datetime.now(timezone.utc).isoformat())
                    if self.recovery_policy == "none":
                        raise
                    self.ledger.cancel_pre_send_failure(request_id, category=error.category)
                    dispatched = False
                    if attempt < 2:
                        with self._idle:
                            self._active.discard(request_id)
                        request_id = None
                        generation_id = terminal = None
                        continue
                    raise RelayRejected("upstream_unavailable", "Upstream connection failed before dispatch", 503) from None
                break
        except RelayRejected as exc:
            if not headers_sent:
                self._error(handler, exc)
        except (LedgerError, ProtocolAccountingError):
            accounting_failed = True
            if request_id is not None:
                try:
                    self._annotate_transport(request_id, response_headers_received=response_headers_received,
                                             output_observed=output_observed)
                except Exception:
                    pass
            self._record_transport_failure(request_id, "protocol_error", protocol=True)
            self._stop("accounting_error", "Conflicting or invalid provider accounting evidence")
            if not headers_sent:
                self._error(handler, RelayRejected("accounting_error", "Provider accounting requires host review", 502))
        except Exception as error:
            self._record_transport_failure(request_id, self._transport_category(error))
            # Provider exceptions and error bodies may contain host secrets.
            # Diagnostics use fixed categories, never str(exception).
            if not headers_sent:
                self._error(handler, RelayRejected("upstream_error", "OpenRouter transport or accounting failed", 502))
        finally:
            try:
                if request_id is not None:
                    if dispatched and terminal is None and upstream_code is not None and 200 <= upstream_code < 300:
                        self._record_transport_failure(request_id, "incomplete_response")
                    self._annotate_transport(request_id, transport_finished_at=datetime.now(timezone.utc).isoformat())
                    if not settled:
                        if not dispatched:
                            self.ledger.cancel_before_dispatch(request_id)
                        elif not accounting_failed and terminal is not None and self._settle(request_id, terminal, key):
                            settled = True
                        elif (not accounting_failed and self.recovery_policy != "none"
                                and self._poll_generation(request_id, generation_id, key)):
                            settled = True
                        else:
                            self.ledger.mark_unknown(request_id, "HTTP attempt ended without an itemized provider cost",
                                                     blocks_spending=self._local_budget)
            except Exception:
                self._stop("accounting_error", "Provider usage could not be durably settled")
            finally:
                with self._idle:
                    if request_id is not None:
                        self._active.discard(request_id)
                    self._idle.notify_all()
                self._admission.release()
                self._write_status()
                handler.close_connection = True

    @staticmethod
    def _error(handler, exc: RelayRejected):
        raw = json.dumps({"error": {"type": "openrouter_relay_error", "code": exc.code,
                                    "message": str(exc)}}).encode()
        try:
            handler.send_response(exc.status)
            handler.send_header("Content-Type", "application/json")
            handler.send_header("Content-Length", str(len(raw)))
            handler.send_header("Connection", "close")
            handler.end_headers()
            handler.wfile.write(raw)
        except (OSError, ValueError):
            pass
        handler.close_connection = True

    def __enter__(self):
        relay = self
        class Handler(BaseHTTPRequestHandler):
            def do_POST(self):
                relay._handle(self)
            def do_GET(self):
                relay._error(self, RelayRejected("unsupported_route", "Only Responses requests are admitted", 404))
            def log_message(self, *args):
                pass
        self._server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self._server.daemon_threads = True
        self._server.block_on_close = False
        self.url = f"http://127.0.0.1:{self._server.server_port}/v1"
        self._thread = threading.Thread(target=self._server.serve_forever, daemon=True)
        self._thread.start()
        return self

    def wait_for_idle(self, timeout: float | None = None) -> bool:
        deadline = None if timeout is None else time.monotonic() + max(0, timeout)
        with self._idle:
            while self._active:
                remaining = None if deadline is None else deadline - time.monotonic()
                if remaining is not None and remaining <= 0:
                    return False
                self._idle.wait(remaining)
            return True

    def drain_pending(self, timeout: float | None = None, **kwargs) -> dict:
        before = self.status()
        idle = self.wait_for_idle(timeout)
        after = self.status()
        return {"status": "settled" if idle else "timed_out", "budget": after,
                "active_requests_before": before["active_requests"],
                "newly_completed_requests": after["completed_requests"] - before["completed_requests"],
                "newly_metered_responses": after["metered_responses"] - before["metered_responses"],
                "settled_cost_usd": str(_sum_money([Decimal(after["spent_usd"]), Decimal(before["spent_usd"]).copy_negate()]))}

    def close(self):
        with self._idle:
            if self._closed:
                return
            self._closed = True
            self._idle.notify_all()
        # Existing HTTP handlers continue draining and settling upstream usage.
        # Closing never cancels a reservation while its HTTP handler is active.
        if self._server is not None:
            self._server.shutdown()
            self._server.server_close()
        if self._thread is not None:
            self._thread.join(timeout=5)
        self._write_status()

    def __exit__(self, *args):
        self.close()
