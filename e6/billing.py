"""A host-only billing relay for serial native Codex or Pi proof passes.

The native CLI owns its tools/session; this relay only admits and accounts for
Responses requests. One persistent API-equivalent dollar ledger spans every
fresh pass. Requests are admitted serially while reported spend is below the
threshold; a successful response may cross it once, after which inference stops.
Durable zero-dollar request markers track in-flight and unknown requests without
guessing provider token counts or reserving future spend. Interrupted or missing
usage stops the entire serial experiment. Predispatch failures and unsuccessful
terminal responses with fully reported usage can be retried.

With metering disabled, the relay tracks transport lifecycle and retains raw
provider usage as host telemetry. Usage cannot block or exclude research work.
"""
from __future__ import annotations

from decimal import Decimal
from dataclasses import replace
from contextlib import contextmanager
from collections import deque
from http.client import IncompleteRead
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import math
from pathlib import Path
import re
import secrets
import threading
import time
from typing import Any
from uuid import uuid4

from transport.auth import AuthError, load_reloadable_credentials
from transport.budget import BudgetLedger, normalize_usage
from transport.responses import (ResponsesTransport, UpstreamError, UpstreamPreparationError,
                                 safe_exception_metadata, safe_response_metadata, sse_events)
from .experiment import DEFAULT_SPEC, ExperimentSpec

from .pi_auth import PiAuthResolver, PiResponsesTransport


MODEL = DEFAULT_SPEC.model
# Fixed experiment accounting policy, not a subscription charge. Unknown
# cache-write partitions are covered by the upper input rate as in Prime.
RATES = DEFAULT_SPEC.rates()
STATUS_WRITE_ATTEMPTS = 4
STATUS_RETRY_SECONDS = .02
NO_DISPATCH_USAGE = {"input_tokens": 0, "output_tokens": 0, "cached_input_tokens": 0}
# Preserve native retry/compaction classification without retaining arbitrary
# provider prose, which can echo prompts, schemas or secret credentials.
SAFE_RESPONSE_ERRORS = {
    "rate_limit_exceeded": "Rate limit exceeded",
    "server_error": "Upstream server error",
    "internal_error": "Upstream internal error",
    "server_busy": "Upstream server busy",
    "service_unavailable": "Upstream service unavailable",
    "overloaded_error": "Upstream overloaded",
    "subscription_sharing_usage_unavailable": "Subscription usage temporarily unavailable",
    "subscription_sharing_user_unavailable": "Subscription user temporarily unavailable",
    "subscription_sharing_usage_limit_exceeded": "Subscription usage limit exceeded",
    "insufficient_quota": "Insufficient quota",
    "context_length_exceeded": "Context length exceeded",
    "invalid_request_error": "Invalid upstream request",
    "invalid_api_key": "Invalid upstream authentication",
    "authentication_error": "Invalid upstream authentication",
    "permission_denied": "Upstream permission denied",
    "model_not_found": "Upstream model unavailable",
    "token_expired": "Upstream authentication expired",
}


class RelayRejected(ValueError):
    pass


class BudgetReached(RelayRejected):
    pass


def _safe_response_error(event: dict[str, Any]) -> dict[str, Any]:
    candidates = [event]
    response = event.get("response")
    if isinstance(response, dict):
        candidates.append(response.get("error"))
    candidates.append(event.get("error"))
    for candidate in candidates:
        if not isinstance(candidate, dict):
            continue
        for key in ("code", "type"):
            value = candidate.get(key)
            if isinstance(value, str) and value in SAFE_RESPONSE_ERRORS:
                safe = {"code": value, "message": SAFE_RESPONSE_ERRORS[value]}
                break
        else:
            continue
        break
    else:
        safe = {"code": "upstream_error", "message": "Upstream response failed"}
    if event.get("type") == "response.failed":
        # Codex reads failures from response.error. Flattening this terminal
        # event into type=error hides its classification and produces the
        # misleading "stream closed before response.completed" diagnostic.
        # Preserve the protocol envelope, without copying arbitrary response
        # fields or provider prose that can echo host credentials/prompts.
        return {"type": "response.failed", "response": {"status": "failed", "error": safe}}
    return {"type": "error", **safe}


_RETRYABLE_NATIVE_ERRORS = {"server_error", "internal_error", "server_busy",
                            "service_unavailable", "overloaded_error"}
_NATIVE_RECONNECT = re.compile(r"Reconnecting[.][.][.][ ]+([0-9]+)/([0-9]+)[ ]+[(]")


def classify_retryable_native_failure(capsule: Path, billing_root: Path,
                                     pass_number: int) -> dict[str, Any] | None:
    """Prove native retry exhaustion from terminal host receipts, not EOF prose.

    The caller must additionally require a nonzero native return code and healthy
    host validation. Quota, authentication, unknown transport failures, missing
    evidence and mixed failure tails never authorize fresh-pass recovery.
    """
    events_path = Path(capsule) / "codex-events.jsonl"
    usage_path = Path(billing_root) / "usage.jsonl"
    final_event = None
    exhausted_retries = None
    recent = deque(maxlen=64)
    try:
        with events_path.open(encoding="utf-8") as source:
            for line in source:
                event = json.loads(line)
                if not isinstance(event, dict):
                    return None
                final_event = event
                if (event.get("type") == "error" and isinstance(event.get("message"), str)
                        and len(event["message"]) <= 2048):
                    match = _NATIVE_RECONNECT.match(event["message"])
                    if match and match[1] == match[2] and 0 < int(match[2]) < 64:
                        exhausted_retries = int(match[2])
        with usage_path.open(encoding="utf-8") as source:
            for line in source:
                receipt = json.loads(line)
                if not isinstance(receipt, dict):
                    return None
                if receipt.get("pass") == pass_number and receipt.get("kind") == "native_responses":
                    recent.append(receipt)
    except (OSError, ValueError, UnicodeError, RecursionError):
        return None
    if not final_event or final_event.get("type") != "turn.failed" or exhausted_retries is None:
        return None
    required = exhausted_retries + 1
    if len(recent) < required:
        return None
    codes = set()
    for receipt in list(recent)[-required:]:
        observed = receipt.get("observations")
        failure = receipt.get("failure")
        if not isinstance(observed, dict) or not isinstance(failure, dict):
            return None
        upstream = observed.get("upstream")
        provider_error = observed.get("upstream_error")
        if not isinstance(upstream, dict) or not isinstance(provider_error, dict):
            return None
        code = provider_error.get("code", provider_error.get("type"))
        relay_close = observed.get("relay_close")
        transport_close = upstream.get("transport_close")
        if not isinstance(relay_close, dict) or not isinstance(transport_close, dict):
            return None
        if (not isinstance(code, str) or receipt.get("metering_enabled") is not False
                or receipt.get("dispatched") is not True
                or receipt.get("terminal_seen") is not True
                or failure.get("kind") != "upstream_response_error"
                or observed.get("terminal_seen") is not True
                or observed.get("last_event_type") != "response.failed"
                or code not in _RETRYABLE_NATIVE_ERRORS
                or upstream.get("status") != 200 or upstream.get("category") != "http_success"
                or observed.get("exception") or observed.get("downstream_disconnect")
                or relay_close.get("begun") is not False
                or transport_close.get("begun") is not False
                or upstream.get("read_failure")):
            return None
        codes.add(code)
    return {"kind": "upstream_transient_failure", "codes": sorted(codes),
            "failed_request_count": required, "native_stream_retries": exhausted_retries,
            "native_retry_exhausted": True, "terminal_seen": True,
            "evidence": {"native_events": str(events_path), "host_usage": str(usage_path)}}


def _usd(amount: Decimal) -> str:
    result = format(amount, "f")
    return result.rstrip("0").rstrip(".") if "." in result else result


NATIVE_HEADERS = {"x-codex-beta-features", "x-openai-internal-codex-responses-lite", "originator", "user-agent",
                  "session-id", "thread-id", "x-client-request-id", "x-codex-turn-metadata", "x-codex-window-id"}

# Event names and IDs are protocol facts; arbitrary event fields can contain
# prompts, tool arguments, model output or provider messages and are not logged.
_EVENT_TYPES = {"error", "response.created", "response.queued", "response.in_progress", "response.done",
                "response.completed", "response.incomplete", "response.failed", "response.output_item.added",
                "response.output_item.done", "response.content_part.added", "response.content_part.done",
                "response.output_text.delta", "response.output_text.done", "response.refusal.delta",
                "response.refusal.done", "response.function_call_arguments.delta", "response.function_call_arguments.done",
                "response.custom_tool_call_input.delta", "response.custom_tool_call_input.done",
                "response.reasoning_summary_part.added", "response.reasoning_summary_part.done",
                "response.reasoning_summary_text.delta", "response.reasoning_summary_text.done",
                "response.reasoning_text.delta", "response.reasoning_text.done"}
_RESPONSE_ID = re.compile(r"resp_[A-Za-z0-9]{8,128}\Z")
_ERROR_TYPES = {"TimeoutError", "OSError", "BrokenPipeError", "ConnectionResetError", "ConnectionAbortedError",
                "PermissionError", "IncompleteRead", "JSONDecodeError", "UnicodeDecodeError", "ValueError",
                "TypeError", "AttributeError", "RuntimeError", "RelayRejected", "AuthError", "UpstreamError",
                "UpstreamPreparationError"}


def _error_type(exc: Exception) -> str:
    name = type(exc).__name__
    return name if name in _ERROR_TYPES else "Exception"


def _observe_event(observations: dict[str, Any], event: dict[str, Any]) -> None:
    kind = event.get("type")
    if isinstance(kind, str) and len(kind) <= 128 and kind in _EVENT_TYPES:
        observations["last_event_type"] = kind
    else:
        observations["last_event_type"] = "unclassified"
    response = event.get("response")
    if isinstance(response, dict):
        identifier = response.get("id")
        if isinstance(identifier, str) and len(identifier) <= 133 and _RESPONSE_ID.fullmatch(identifier):
            observations.setdefault("response_id", identifier)
        observations["usage_present"] = observations["usage_present"] or response.get("usage") is not None
        provider_error = response.get("error")
    else:
        provider_error = None
    for supplied in (event if kind == "error" else None, provider_error):
        if isinstance(supplied, dict):
            details = safe_response_metadata({key: supplied.get(key) for key in ("code", "type")})
            if details:
                observations["upstream_error"] = details


class _NativeCredentials:
    """Keep host authentication, with narrowly allowlisted native wire metadata."""
    def __init__(self, credentials):
        self._original = credentials
        self.native_headers: dict[str, str] = {}

    def __getattr__(self, name):
        return getattr(self._original, name)

    def headers(self):
        headers = self._original.headers()
        headers = {key: value for key, value in headers.items()
                   if key.lower() != "openai-beta" and key.lower() not in self.native_headers}
        headers.update(self.native_headers)
        return headers


class NativeResponsesTransport(ResponsesTransport):
    def __init__(self, credentials):
        super().__init__(_NativeCredentials(credentials))

    def set_native_headers(self, supplied):
        native = {}
        for key in NATIVE_HEADERS:
            values = supplied.get_all(key, []) if hasattr(supplied, "get_all") else (
                [value for name, value in supplied.items() if name.lower() == key])
            if not values:
                continue
            if (len(values) != 1 or not isinstance(values[0], str)
                    or any(char in values[0] for char in "\r\n\0")):
                raise RelayRejected("Invalid native protocol metadata header")
            native[key] = values[0]
        # A missing header on the next call must not inherit prior-pass metadata.
        self.credentials.native_headers = native


def _tools(tools: Any) -> None:
    pending = [tools]
    while pending:
        definitions = pending.pop()
        if not isinstance(definitions, list):
            raise RelayRejected("Invalid local tool definitions")
        for tool in definitions:
            if not isinstance(tool, dict):
                raise RelayRejected("Invalid local tool definition")
            if tool.get("type") == "namespace":
                pending.append(tool.get("tools"))
            elif tool.get("type") not in {"function", "custom"}:
                raise RelayRejected("Only native locally executed tools are permitted")


def _text_parts(content: Any) -> None:
    if isinstance(content, str):
        return
    if not isinstance(content, list):
        raise RelayRejected("Only text content is permitted")
    for part in content:
        if (not isinstance(part, dict) or part.get("type") not in {"input_text", "output_text", "summary_text"}
                or not isinstance(part.get("text"), str)):
            raise RelayRejected("Only text content is permitted")


def validate_native_payload(payload: Any, model: str = MODEL) -> dict[str, Any]:
    """Keep normal Codex custom/namespace tool definitions and call continuity.

    No external providers, attachments, server-side references or paid hosted
    tools are admitted. HTTP routes other than Responses are accounted nowhere
    and are refused. This deliberately does not use Prime's function-only schema.
    """
    if not isinstance(payload, dict) or payload.get("model") != model:
        raise RelayRejected("Only the pinned Sol 6.1 model is permitted")
    if payload.get("stream") is not True or payload.get("store") is not False:
        raise RelayRejected("Responses requires stream=true and store=false")
    if payload.get("background", False) is not False:
        raise RelayRejected("Background responses are forbidden")
    if payload.get("service_tier", "default") not in {"auto", "default"}:
        raise RelayRejected("Only the default service tier is permitted")
    if any(key in payload for key in ("previous_response_id", "conversation", "attachments")):
        raise RelayRejected("Server-side history and attachments are forbidden")
    if not isinstance(payload.get("instructions", ""), str):
        raise RelayRejected("Instructions must be text")
    _tools(payload.get("tools", []))
    items = payload.get("input")
    if isinstance(items, str):
        pass
    elif isinstance(items, list):
        for item in items:
            if not isinstance(item, dict):
                raise RelayRejected("Input items must be objects")
            kind = item.get("type", "message")
            if kind == "message":
                _text_parts(item.get("content"))
            elif kind == "reasoning":
                if not isinstance(item.get("encrypted_content", ""), str):
                    raise RelayRejected("Invalid opaque reasoning")
                _text_parts(item.get("summary", []))
            elif kind == "additional_tools":
                # Native Sol catalog schemas use history-scoped definitions.
                # Keep this item in place, including its id/role, and apply the
                # same hosted-tool prohibition as top-level tool definitions.
                _tools(item.get("tools"))
            elif kind in {"function_call", "custom_tool_call"}:
                field = "arguments" if kind == "function_call" else "input"
                if any(not isinstance(item.get(key), str) for key in ("call_id", "name", field)):
                    raise RelayRejected("Invalid native tool call")
            elif kind in {"function_call_output", "custom_tool_call_output"}:
                if not isinstance(item.get("call_id"), str):
                    raise RelayRejected("Invalid native tool result")
                _text_parts(item.get("output"))
            else:
                raise RelayRejected("Unsupported server-side or nontext input item")
    else:
        raise RelayRejected("Complete input history is required")
    result = dict(payload)
    result["service_tier"] = "default"
    return result


def validate_pi_payload(payload: Any, model: str = MODEL) -> dict[str, Any]:
    """Keep Pi's complete text/local-tool history on the public Responses API.

    Standard metadata, structured text options and cache keys survive. Native
    Pi's SIWC builder omits unsupported sampling/output-cap fields; a local
    custom provider cannot detect account auth, so the host applies that rule.
    Remote tools, history references, classifier models and premium tiers are
    rejected by the same admission checks used by the Codex backend.
    """
    result = validate_native_payload(payload, model)
    allowed = {"model", "input", "instructions", "reasoning", "tools", "tool_choice",
               "parallel_tool_calls", "stream", "store", "text", "temperature", "top_p",
               "max_output_tokens", "prompt_cache_key", "prompt_cache_retention", "prompt_cache_options",
               "include", "service_tier", "background", "metadata", "user", "safety_identifier",
               "truncation"}
    if any(key not in allowed for key in result):
        raise RelayRejected("Unsupported Pi Responses request field")
    if result.get("truncation", "disabled") != "disabled":
        raise RelayRejected("Complete Pi input history is required")
    choice = result.get("tool_choice", "auto")
    if isinstance(choice, dict):
        if choice.get("type") not in {"function", "custom", "allowed_tools"}:
            raise RelayRejected("Only local Pi tool selection is permitted")
        if choice.get("type") == "allowed_tools":
            _tools(choice.get("tools"))
    elif not isinstance(choice, str) or choice not in {"auto", "none", "required"}:
        raise RelayRejected("Only local Pi tool selection is permitted")
    for key in ("max_output_tokens", "prompt_cache_retention", "prompt_cache_options", "temperature"):
        result.pop(key, None)
    return result


class BudgetRelay:
    def __init__(self, root: str | Path, auth_path: str | Path | None = None, cap: Any = None, *,
                 transport: Any = None, request_timeout: float | None = None,
                 spec: ExperimentSpec | None = None, backend: str = "codex", pi_runtime: Any = None,
                 metering: bool = True):
        if backend not in {"codex", "pi"}:
            raise ValueError("Unsupported native agent backend")
        if type(metering) is not bool:
            raise ValueError("metering must be a boolean")
        self.backend = backend
        self.metering_enabled = metering
        spec = DEFAULT_SPEC if spec is None else spec
        if backend == "pi":
            from . import pi
            pi.validate_settings(spec.proof_settings())
        self.root = Path(root).resolve()
        self.root.mkdir(parents=True, exist_ok=True)
        self.spec = spec
        self.episode = "serial-sol61"
        self.limit = self.ledger = None
        self._stop_reason = None
        self.last_error = self.last_error_phase = None
        self._request_count = self._dispatched_requests = self._completed_requests = 0
        self._selector_requests = self._selector_dispatched_requests = self._selector_completed_requests = 0
        self._unmetered_metadata: dict[str, dict[str, Any]] = {}
        self._telemetry_write_failures = 0
        saved = {"stop_reason": None}
        if metering:
            amount = spec.cumulative_budget_usd if cap is None else Decimal(str(cap))
            if not amount.is_finite() or not 0 < amount <= spec.cumulative_budget_usd:
                raise ValueError("The cumulative dollar threshold must be positive and at most the frozen experiment threshold")
            self.spec = replace(spec, cumulative_budget_usd=amount)
            self.limit = amount
            self.ledger = BudgetLedger(self.root / "billing.sqlite")
            self.episode = "serial-sol61"
            previous = self.ledger.create_episode(self.episode, amount)
            self._stop_reason = (
                "unknown_usage" if previous["unknown_requests"] or previous["active_requests"] else
                "budget_reached" if Decimal(previous["spent_usd"]) >= amount else None)
            # Monitor snapshots are expendable. Persist relay controls alongside the
            # authoritative request ledger so missing, stale or locked status.json
            # files cannot change accounting or restart admission.
            # Keep the backend pin alongside the ledger's reusable relay controls.
            # A legacy control row without a pin belongs to the Codex backend.
            with self.ledger._transaction() as database:
                columns = {row[1] for row in database.execute("PRAGMA table_info(relay_state)")}
                if "backend" not in columns:
                    database.execute("ALTER TABLE relay_state ADD COLUMN backend TEXT NOT NULL DEFAULT 'codex'")
                saved_backend = database.execute("SELECT backend FROM relay_state WHERE episode_id=?",
                                                 (self.episode,)).fetchone()
                if saved_backend is not None and saved_backend["backend"] != backend:
                    raise ValueError("Saved native agent backend differs from this run")
                if saved_backend is None:
                    database.execute("INSERT INTO relay_state(episode_id,limit_usd,backend) VALUES(?,?,?)",
                                     (self.episode, _usd(amount), backend))
            saved = self.ledger.initialize_relay_control(self.episode, amount)
            self._stop_reason = self._stop_reason or saved["stop_reason"]
            self.last_error, self.last_error_phase = saved["last_error"], saved["last_error_phase"]
            if self._stop_reason and not saved["stop_reason"]:
                # An earlier recoverable error is not the cause of a newly inferred
                # stop after a crash. Durable stop diagnoses are restored as-is.
                self.last_error = ("Unsettled upstream request found during restart" if self._stop_reason == "unknown_usage"
                                   else "Cumulative reported API-equivalent spend threshold reached")
                self.last_error_phase = "restart"
        if transport is not None:
            self.transport = transport
        elif backend == "pi":
            selected_auth = auth_path if auth_path is not None else Path.home() / ".pi/agent/auth.json"
            self.transport = PiResponsesTransport(PiAuthResolver(selected_auth, pi_runtime or {}))
        else:
            self.transport = NativeResponsesTransport(load_reloadable_credentials(codex_auth_path=auth_path))
        self.token = secrets.token_urlsafe(32)
        self.request_timeout = None if request_timeout is None else float(request_timeout)
        if self.request_timeout is not None and (isinstance(request_timeout, bool)
                or not math.isfinite(self.request_timeout) or self.request_timeout <= 0):
            raise ValueError("request_timeout must be positive and finite, or None")
        self.pass_number: int | None = None
        self.deadline_epoch: float | None = None
        self.last_request_phase: str | None = None
        self._snapshot_failures = 0
        self._snapshot_error: dict[str, Any] | None = None
        self._state = threading.RLock()
        self._settlement = threading.Condition(self._state)
        self._admission = threading.Lock()
        self._inflight: set[str] = set()
        self._draining = False
        self._closed = False
        self._close_started: float | None = None
        self._server: ThreadingHTTPServer | None = None
        self._thread: threading.Thread | None = None
        self.url: str | None = None
        if self._stop_reason and not saved["stop_reason"]:
            self._persist_control()
        self._write_status("initialization")

    @property
    def stop_reason(self):
        with self._state:
            return self._stop_reason

    def _persist_control(self) -> None:
        if not self.metering_enabled:
            return
        self.ledger.update_relay_control(self.episode, stop_reason=self._stop_reason,
                                         last_error=self.last_error, last_error_phase=self.last_error_phase)

    def _phase(self, phase: str) -> None:
        with self._state:
            self.last_request_phase = phase

    def _diagnose(self, diagnostic: str, phase: str) -> None:
        with self._state:
            if self._stop_reason is None:
                self.last_error, self.last_error_phase = diagnostic, phase
            self._persist_control()
        self._write_status(phase)

    def _stop(self, reason: str, diagnostic: str | None = None, *, phase: str = "stop") -> None:
        with self._state:
            if not self.metering_enabled:
                if diagnostic is not None:
                    self.last_error, self.last_error_phase = diagnostic, phase
            elif self._stop_reason is None:
                self._stop_reason = reason
                self.last_error, self.last_error_phase = diagnostic, phase
            elif self.last_error is None and diagnostic is not None:
                self.last_error, self.last_error_phase = diagnostic, phase
            self._persist_control()
        self._write_status(phase)

    def status(self) -> dict[str, Any]:
        with self._state:
            if not self.metering_enabled:
                return {"episode_id": self.episode, "metering_enabled": False,
                        "limit_usd": None, "spent_usd": None, "reserved_usd": None,
                        "committed_usd": None, "remaining_usd": None, "unknown_usd": None,
                        "overshoot_usd": None, "over_limit": False, "threshold_reached": False,
                        "request_count": self._request_count,
                        "dispatched_requests": self._dispatched_requests,
                        "completed_requests": self._completed_requests,
                        "active_requests": len(self._inflight), "unknown_requests": 0,
                        "metered_responses": 0,
                        "selector_requests": self._selector_requests,
                        "selector_dispatched_requests": self._selector_dispatched_requests,
                        "selector_completed_requests": self._selector_completed_requests,
                        "selector_spent_usd": None, "stop_reason": None,
                        "admission_policy": "serial_transport_only", "reservation_policy": "none",
                        "pass": self.pass_number, "deadline_epoch": self.deadline_epoch,
                        "last_error": self.last_error, "last_error_phase": self.last_error_phase,
                        "last_request_phase": self.last_request_phase,
                        "status_snapshot_write_failures": self._snapshot_failures,
                        "status_snapshot_pending": self._snapshot_error is not None,
                        "status_snapshot_error": self._snapshot_error,
                        "accounting_authority": None, "billing_basis": None,
                        "usage_telemetry": "usage.jsonl",
                        "usage_telemetry_write_failures": self._telemetry_write_failures,
                        "model": self.spec.model, "output_cap_tokens": None,
                        "request_timeout_seconds": self.request_timeout,
                        "pending_usage_settlement_seconds": self.spec.pending_usage_settlement_seconds,
                        "settlement_draining": self._draining, "request_body_limit_bytes": None,
                        "agent_backend": self.backend, "context_management": "native_" + self.backend,
                        "context_admission_enabled": False, "context_admission_limit_tokens": None}
            accounting = self.ledger.status(self.episode)
            spent = Decimal(accounting["spent_usd"])
            return {**accounting, "metering_enabled": True, "limit_usd": _usd(self.limit),
                    "unknown_usd": None if accounting["unknown_requests"] else "0",
                    "committed_usd": None if accounting["unknown_requests"] else accounting["spent_usd"],
                    "remaining_usd": _usd(max(Decimal(0), self.limit - spent)),
                    "overshoot_usd": _usd(max(Decimal(0), spent - self.limit)),
                    "over_limit": spent > self.limit, "threshold_reached": spent >= self.limit,
                    "admission_policy": self.spec.budget_policy,
                    "reservation_policy": "none_durable_inflight_markers",
                    "pass": self.pass_number,
                    "deadline_epoch": self.deadline_epoch, "stop_reason": self._stop_reason,
                    "last_error": self.last_error,
                    "last_error_phase": self.last_error_phase, "last_request_phase": self.last_request_phase,
                    "status_snapshot_write_failures": self._snapshot_failures,
                    "status_snapshot_pending": self._snapshot_error is not None,
                    "status_snapshot_error": self._snapshot_error,
                    "accounting_authority": "billing.sqlite",
                    "model": self.spec.model, "output_cap_tokens": None,
                    "request_timeout_seconds": self.request_timeout,
                    "pending_usage_settlement_seconds": self.spec.pending_usage_settlement_seconds,
                    "settlement_draining": self._draining,
                    "request_body_limit_bytes": None,
                    "agent_backend": self.backend,
                    "context_management": "native_" + self.backend,
                    "context_admission_enabled": False,
                    "context_admission_limit_tokens": None,
                    "billing_basis": ("fixed catalog API-equivalent plus selector provider-reported usage.cost"
                                      if self.spec.rerank_config is not None or accounting["selector_requests"] else
                                      "fixed catalog API-equivalent; covering input rate")}

    def _write_status(self, phase: str = "status") -> bool:
        """Publish an atomic, best-effort monitor snapshot without affecting billing.

        Windows readers can briefly deny replacement of status.json. Each retry
        uses its own temporary file; filesystem errors stay in safe diagnostics
        and never enter the request handler's upstream-failure accounting path.
        Ledger reads intentionally stay outside the filesystem exception block.
        """
        with self._state:
            for attempt in range(STATUS_WRITE_ATTEMPTS):
                snapshot = self.status()
                # A successful replacement clears the pending snapshot error.
                snapshot["status_snapshot_pending"] = False
                snapshot["status_snapshot_error"] = None
                serialized = json.dumps(snapshot, indent=2) + "\n"
                temporary = self.root / ("billing-status-" + uuid4().hex + ".tmp")
                try:
                    with temporary.open("x", encoding="utf-8") as output:
                        output.write(serialized)
                    temporary.replace(self.root / "status.json")
                except OSError as exc:
                    self._snapshot_failures += 1
                    # Do not retain exception text: it can contain paths or
                    # arbitrary provider/request material under test doubles.
                    self._snapshot_error = {"error_type": type(exc).__name__, "phase": phase}
                else:
                    self._snapshot_error = None
                    return True
                finally:
                    try:
                        temporary.unlink(missing_ok=True)
                    except OSError:
                        pass
                if attempt + 1 < STATUS_WRITE_ATTEMPTS:
                    time.sleep(STATUS_RETRY_SECONDS)
            return False

    def set_pass(self, number: int, deadline_epoch: float | None = None):
        if type(number) is not int or number < 1:
            raise ValueError("Pass number must be positive")
        if deadline_epoch is not None and (isinstance(deadline_epoch, bool)
                or not isinstance(deadline_epoch, (int, float)) or not math.isfinite(deadline_epoch)):
            raise ValueError("Pass deadline must be finite")
        with self._state:
            if self._inflight or self._admission.locked():
                raise RuntimeError("Cannot change passes with a request in flight")
            if self._closed or self._stop_reason:
                raise RuntimeError("The cumulative billing experiment is stopped")
            if self.pass_number is not None and number <= self.pass_number:
                raise ValueError("Pass numbers must strictly increase")
            self.pass_number = number
            self._draining = False
            self.deadline_epoch = None if deadline_epoch is None else float(deadline_epoch)
            self._write_status("pass_configured")

    def _remaining(self):
        with self._state:
            if self._draining:
                raise RelayRejected("Native pass ended; pending usage is being settled")
            return self._stream_remaining()

    def _stream_remaining(self):
        """Keep reading an admitted request while a retired client is draining."""
        with self._state:
            if self._stop_reason == "budget_reached":
                raise BudgetReached("Cumulative reported API-equivalent spend threshold reached")
            if self._closed or self._stop_reason:
                raise RelayRejected("The cumulative billing experiment is stopped")
            if self.pass_number is None:
                raise RelayRejected("A pass must be configured before inference")
            remaining = None if self.deadline_epoch is None else self.deadline_epoch - time.time()
            if remaining is not None and remaining <= 0:
                raise TimeoutError("Pass inference deadline expired")
            bounds = [bound for bound in (self.request_timeout, remaining) if bound is not None]
            return min(bounds) if bounds else None

    def _settle(self, request_id: str, usage: Any, failure: Any, *, terminal: bool = False,
                observations: dict[str, Any] | None = None) -> dict[str, Any] | None:
        """Commit usage and terminal state before forwarding terminal output.

        The serial admission lock stays held throughout settlement and response
        forwarding. A threshold stop therefore has no active request and no
        later request can race ahead of its authoritative reported total.
        """
        with self._state:
            if request_id not in self._inflight:
                return None
            if not self.metering_enabled:
                self._record_usage(request_id, usage, failure, terminal=terminal, observations=observations)
                self._inflight.remove(request_id)
                self._completed_requests += int(terminal)
                self._settlement.notify_all()
                if failure:
                    self.last_error = "Upstream response did not complete successfully"
                    self.last_error_phase = self.last_error_phase or "settlement"
                self._write_status("request_finished")
                return None
            if observations is not None:
                # Successful accounting receives exactly the same failure=None
                # as before. Attach observations only when usage is already
                # invalid/missing or a provider/relay failure already exists.
                if failure is None:
                    try:
                        normalize_usage(usage)
                    except ValueError:
                        failure = {"kind": "invalid_terminal_usage" if usage is not None else "missing_terminal_usage"}
                if isinstance(failure, dict):
                    failure = {**failure, "observations": observations}
            terminal_failure = (isinstance(failure, dict) and failure.get("kind") in {
                "unsuccessful_response", "upstream_response_error"})
            # A terminal model failure does not make its reported bill unknown.
            # Prime's general ledger retains unknown holds for provider errors;
            # E6 records the failure separately and accounts valid counters.
            settled = self.ledger.settle_request(request_id, usage, failure, reported_terminal=terminal_failure)
            self._inflight.remove(request_id)
            self._settlement.notify_all()
            if settled["status"] != "completed":
                if self._stop_reason is None:
                    self._stop_reason = "unknown_usage"
                    self.last_error = "Upstream response omitted valid successful usage"
                    self.last_error_phase = "settlement"
            elif Decimal(self.ledger.status(self.episode)["spent_usd"]) >= self.limit:
                if self._stop_reason is None:
                    self._stop_reason = "budget_reached"
                    self.last_error = "Cumulative reported API-equivalent spend threshold reached"
                    self.last_error_phase = "settlement"
            if terminal_failure and settled["status"] == "completed" and self._stop_reason is None:
                self.last_error = "Upstream response ended unsuccessfully with fully accounted usage"
                self.last_error_phase = "settlement"
            self._persist_control()
            self._write_status("settlement")
            return settled

    def _cancel_before_dispatch(self, request_id: str, phase: str) -> None:
        """Retire a request marker when transport was never invoked."""
        with self._state:
            if request_id not in self._inflight:
                return
            if self.metering_enabled:
                self.ledger.cancel_request(request_id, phase)
            else:
                self._record_usage(request_id, None, {"kind": "request_not_dispatched", "phase": phase})
            self._inflight.remove(request_id)
            self._settlement.notify_all()
            self._write_status("before_dispatch")

    def _record_usage(self, request_id: str, usage: Any, failure: Any, *, terminal: bool = False,
                      observations: dict[str, Any] | None = None, extra: dict[str, Any] | None = None) -> None:
        """Append expendable host telemetry; this is never an accounting authority.

        Only provider usage, protocol observations and already-sanitized selector
        facts enter the file. Credentials, native prompts and response prose do
        not. A failed telemetry write cannot change admission or settlement.
        """
        metadata = self._unmetered_metadata.pop(request_id, {})
        event = {"schema_version": 1, "episode_id": self.episode, "request_id": request_id,
                 "metering_enabled": False, **metadata, "terminal_seen": terminal,
                 "usage": usage, "failure": failure,
                 **({"observations": observations} if observations is not None else {}),
                 **(extra or {})}
        try:
            serialized = json.dumps(event, ensure_ascii=False, separators=(",", ":"), allow_nan=False) + "\n"
            with (self.root / "usage.jsonl").open("a", encoding="utf-8") as output:
                output.write(serialized)
        except (OSError, ValueError, TypeError):
            self._telemetry_write_failures += 1

    def selector_timeout(self, timeout: float) -> float:
        """Bound each selector dispatch by the relay and current pass deadlines."""
        with self._state:
            remaining = self._remaining()
            return min(timeout, remaining) if remaining is not None else timeout

    @contextmanager
    def selector_admission(self, timeout: float):
        """Serialize selector calls with native inference, including settlement.

        Wait for the native terminal response to finish forwarding. Tool
        execution can begin during that short interval, so a selector must not
        interpret the existing native admission lease as a billing failure.
        """
        if not self._admission.acquire(timeout=self.selector_timeout(timeout)):
            raise RelayRejected("Inference admission is busy")
        try:
            self._remaining()
            yield
        finally:
            with self._state:
                self._admission.release()
                self._settlement.notify_all()

    def begin_selector_call(self, request: dict[str, Any], binding: dict[str, Any]) -> str:
        """Track provider dispatch under the frozen host billing policy."""
        with self._state:
            self._remaining()
            if not self.metering_enabled:
                request_id = uuid4().hex
                self._request_count += 1
                self._selector_requests += 1
                self._unmetered_metadata[request_id] = {
                    "pass": self.pass_number, "route": "/rerank", "kind": "decision_rerank",
                    "request_sha256": request.get("request_sha256"),
                    "request_body_bytes": request.get("request_bytes"), "binding": dict(binding)}
                self._inflight.add(request_id)
                return request_id
            status = self.ledger.status(self.episode)
            if status["active_requests"] or status["unknown_requests"]:
                raise RelayRejected("Unsettled usage prevents further inference")
            if Decimal(status["spent_usd"]) >= self.limit:
                self._stop("budget_reached")
                raise BudgetReached("Cumulative reported spend threshold reached")
            request_id = uuid4().hex
            self.ledger.begin_request(self.episode, request_id,
                request.get("config", {}).get("model", "decision-selector"),
                {"input": "0", "cache_read": "0", "output": "0"}, metadata={
                    "pass": self.pass_number, "route": "/rerank", "kind": "decision_rerank",
                    "billing_basis": "provider_reported_cost", "request_tracking": "zero_dollar_inflight_marker",
                    "request_sha256": request.get("request_sha256"),
                    "request_body_bytes": request.get("request_bytes"), "binding": binding})
            self._inflight.add(request_id)
            # Return the marker identity before any expendable monitor write:
            # the caller must retain it if a later local step fails.
            return request_id

    def settle_selector_call(self, request_id: str, call: dict[str, Any]) -> dict[str, Any] | None:
        """Commit each provider charge before another selector chunk is admitted."""
        with self._state:
            if request_id not in self._inflight:
                return None
            if not self.metering_enabled:
                dispatched = bool(call.get("dispatched"))
                terminal = dispatched and call.get("http_status") is not None
                self._dispatched_requests += int(dispatched)
                self._selector_dispatched_requests += int(dispatched)
                self._completed_requests += int(terminal)
                self._selector_completed_requests += int(terminal)
                self._record_usage(request_id, call.get("usage"), call.get("error"), terminal=terminal,
                    extra={"dispatched": dispatched, **{key: call[key] for key in (
                        "provider", "model", "id", "http_status", "status", "latency_seconds",
                        "response_bytes", "response_sha256") if key in call}})
                self._inflight.remove(request_id)
                self._settlement.notify_all()
                self._write_status("selector_settlement")
                return None
            if not call.get("dispatched"):
                settled = self.ledger.cancel_request(request_id, "selector_before_dispatch")
            else:
                settled = self.ledger.settle_reported_cost(request_id, call.get("usage"),
                    provider=call.get("provider"), model=call.get("model"), failure=call.get("error"))
            self._inflight.remove(request_id)
            self._settlement.notify_all()
            if settled["status"] != "completed":
                self._stop("unknown_usage", "Selector response omitted a valid provider-reported cost", phase="selector_settlement")
            elif Decimal(self.ledger.status(self.episode)["spent_usd"]) >= self.limit:
                self._stop("budget_reached", "Cumulative reported spend threshold reached", phase="selector_settlement")
            self._persist_control()
            self._write_status("selector_settlement")
            return settled

    def _close_observations(self, *, active_transport_only: bool = False) -> dict[str, Any]:
        # Called under relay state lock, before sampling transport metadata.
        # The transport snapshot lock is held only while copying fixed facts.
        local = {"begun": self._closed}
        if self._close_started is not None:
            local["age_seconds"] = round(max(0, time.monotonic() - self._close_started), 6)
        snapshot = getattr(self.transport, "diagnostic_snapshot", None)
        if isinstance(self.transport, ResponsesTransport):
            supplied = snapshot(active_only=active_transport_only)
        elif active_transport_only:
            supplied = None  # A custom transport cannot prove request attribution.
        else:
            supplied = snapshot() if callable(snapshot) else getattr(self.transport, "last_response_metadata", None)
        metadata = safe_response_metadata(supplied)
        return {"relay_close": local, **({"upstream": metadata} if metadata else {})}

    def __enter__(self):
        if self._server is not None:
            raise RuntimeError("Relay already started")
        owner = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def log_message(self, *args):
                pass

            def _json(self, status, value):
                # Drain an explicitly sized body before closing.
                # Unread POST bytes can make Windows reset the connection and
                # hide a 402/429 response from the native CLI.
                lengths = self.headers.get_all("Content-Length", [])
                if (not getattr(self, "_body_read", False) and len(lengths) == 1
                        and lengths[0].isdigit() and 0 < int(lengths[0])):
                    self.rfile.read(int(lengths[0]))
                    self._body_read = True
                data = json.dumps(value, separators=(",", ":")).encode()
                self.send_response(status)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(data)))
                self.send_header("Connection", "close")
                self.end_headers()
                self.close_connection = True
                self.wfile.write(data)

            def _authenticate(self):
                supplied = self.headers.get("Authorization", "")
                return (not self.headers.get("Origin") and not self.headers.get("Sec-Fetch-Site")
                        and secrets.compare_digest(supplied, "Bearer " + owner.token))

            def do_GET(self):
                if not self._authenticate():
                    self._json(401, {"error": "Unauthorized"})
                elif self.path == "/status":
                    self._json(200, owner.status())
                else:
                    self._json(404, {"error": "Unaccounted route is forbidden"})

            def do_POST(self):
                if not self._authenticate():
                    self._json(401, {"error": "Unauthorized"})
                    return
                if self.path != "/v1/responses":
                    message = "Unaccounted route, including remote compaction, is forbidden"
                    owner._diagnose(message, "route")
                    self._json(400, {"error": message})
                    return
                with owner._state:
                    draining = owner._draining or owner._closed
                    admitted = not draining and owner._admission.acquire(blocking=False)
                if draining:
                    self._json(409, {"error": "Native pass ended; no further inference is admitted"})
                    return
                if not admitted:
                    self._json(429, {"error": "Only one model request may be active"})
                    return
                request_id = None
                usage = None
                failure = None
                streaming = False
                dispatch_started = False
                phase = "admission"
                stage = "local_control"
                observations: dict[str, Any] = {"byte_count": 0, "event_count": 0,
                                                "terminal_seen": False, "usage_present": False}
                downstream_disconnected = False
                terminal = False

                def forward(data: bytes) -> None:
                    nonlocal downstream_disconnected, stage
                    # Accounting belongs to the upstream reader, independent of
                    # whether the native client can still receive its response.
                    with owner._state:
                        retired = owner._draining or owner._closed
                    if downstream_disconnected or retired:
                        return
                    stage = "client_forward"
                    try:
                        self.wfile.write(data)
                        self.wfile.flush()
                    except OSError as exc:
                        downstream_disconnected = True
                        observations["downstream_disconnect"] = {"error_type": _error_type(exc)}

                def observed_failure(exc: Exception | None = None) -> dict[str, Any]:
                    with owner._state:
                        details = {**observations, "phase": phase, "stage": stage, **owner._close_observations()}
                    metadata = details.get("upstream", {})
                    if isinstance(exc, UpstreamError):
                        supplied = safe_response_metadata(exc.metadata)
                        # A snapshot carried by an exception can predate a
                        # concurrent close; retain freshly sampled lifecycle
                        # and elapsed timing from the transport instead.
                        for key in ("transport_close", "timing"):
                            if key in metadata:
                                supplied.pop(key, None)
                        metadata.update(supplied)
                    if exc is not None:
                        details["exception"] = safe_exception_metadata(exc)
                    if isinstance(exc, IncompleteRead) and isinstance(exc.partial, bytes):
                        # Partial read bytes were not yielded to the decoder.
                        details["partial_byte_count"] = len(exc.partial)
                    if metadata:
                        details["upstream"] = metadata
                    return details

                try:
                    owner._phase(phase)
                    owner._remaining()
                    if (self.headers.get("Transfer-Encoding") or self.headers.get("Content-Encoding", "identity") != "identity"
                            or self.headers.get_content_type() != "application/json"):
                        raise RelayRejected("Only uncompressed JSON requests are supported")
                    lengths = self.headers.get_all("Content-Length", [])
                    if len(lengths) != 1 or not lengths[0].isdigit() or not 0 < int(lengths[0]):
                        raise RelayRejected("Request body must have one positive Content-Length")
                    raw = self.rfile.read(int(lengths[0]))
                    self._body_read = True
                    if len(raw) != int(lengths[0]):
                        raise RelayRejected("Incomplete request body")
                    validator = validate_pi_payload if owner.backend == "pi" else validate_native_payload
                    payload = validator(json.loads(raw), owner.spec.model)
                    if not bool(getattr(owner.transport, "supports_output_cap", False)):
                        # Native Codex already builds its own instructions and
                        # developer messages. Preserve their priority/ordering;
                        # only remove fields this OAuth endpoint cannot accept.
                        payload.pop("max_output_tokens", None)
                        payload.pop("prompt_cache_retention", None)
                    encoded = json.dumps(payload, ensure_ascii=False, separators=(",", ":"), allow_nan=False).encode()
                    phase = "native_headers"
                    owner._phase(phase)
                    if hasattr(owner.transport, "set_native_headers"):
                        owner.transport.set_native_headers(self.headers)
                    phase = "inflight_record"
                    owner._phase(phase)
                    with owner._state:
                        owner._remaining()
                        if owner.metering_enabled and Decimal(owner.ledger.status(owner.episode)["spent_usd"]) >= owner.limit:
                            owner._stop("budget_reached")
                            raise BudgetReached("Cumulative reported API-equivalent spend threshold reached")
                        request_id = uuid4().hex
                        if owner.metering_enabled:
                            # Zero input/output are tracking placeholders, never provider estimates.
                            owner.ledger.begin_request(owner.episode, request_id, owner.spec.model, owner.spec.rates(), metadata={
                                "pass": owner.pass_number, "route": "/v1/responses",
                                "unclassified_input_rate_covers_cache_writes": True,
                                "request_tracking": "zero_dollar_inflight_marker",
                                "request_body_bytes": len(encoded), "relay_output_cap_enforced": False})
                        else:
                            owner._request_count += 1
                            owner._unmetered_metadata[request_id] = {
                                "pass": owner.pass_number, "route": "/v1/responses",
                                "kind": "native_responses", "request_body_bytes": len(encoded), "dispatched": False}
                        owner._inflight.add(request_id)
                        owner._write_status("inflight_record")
                    phase = "before_dispatch"
                    owner._phase(phase)
                    timeout = owner._remaining()
                    if hasattr(owner.transport, "prepare_request"):
                        # Token refresh is host authentication work, not model
                        # dispatch. Failure settles the durable marker at zero.
                        phase = "authentication"
                        owner._phase(phase)
                        owner.transport.prepare_request(timeout)
                    timeout = owner._remaining()
                    started = time.monotonic()
                    terminal = False
                    phase = "dispatch"
                    stage = "dispatch"
                    owner._phase(phase)
                    # Calling the upstream transport is the ambiguity boundary:
                    # failures from this point may have incurred provider usage.
                    dispatch_started = True
                    if not owner.metering_enabled:
                        with owner._state:
                            owner._dispatched_requests += 1
                            owner._unmetered_metadata[request_id]["dispatched"] = True
                    with owner.transport.open_response(payload, timeout) as chunks:
                        phase = "upstream_stream"
                        owner._phase(phase)
                        stage = "client_forward"
                        streaming = True
                        self.close_connection = True
                        with owner._state:
                            retired = owner._draining or owner._closed
                        if not retired:
                            try:
                                self.send_response(200)
                                self.send_header("Content-Type", "text/event-stream")
                                self.send_header("Cache-Control", "no-store")
                                self.send_header("Connection", "close")
                                self.end_headers()
                            except OSError as exc:
                                downstream_disconnected = True
                                observations["downstream_disconnect"] = {"error_type": _error_type(exc)}

                        def live_chunks():
                            nonlocal stage
                            # The accounting decoder skips SSE comments. Relay
                            # actual upstream activity promptly so native idle
                            # handling also sees comments and fragmented events.
                            # This emits nothing while upstream is silent and
                            # forwards no arbitrary provider comment contents.
                            iterator = iter(chunks)
                            while True:
                                stage = "upstream_read"
                                try:
                                    chunk = next(iterator)
                                except StopIteration:
                                    return
                                if isinstance(chunk, bytes):
                                    observations["byte_count"] += len(chunk)
                                stage = "local_control"
                                owner._stream_remaining()
                                if isinstance(chunk, bytes) and chunk:
                                    stage = "client_forward"
                                    forward(b": upstream activity\n\n")
                                stage = "upstream_decode"
                                yield chunk

                        for data in sse_events(live_chunks(), max_event_bytes=None, max_stream_bytes=None):
                            stage = "upstream_decode"
                            observations["event_count"] += 1
                            owner._stream_remaining()
                            if timeout is not None and time.monotonic() - started >= timeout:
                                raise TimeoutError("Upstream request deadline expired")
                            if data == b"[DONE]":
                                break
                            event = json.loads(data)
                            if not isinstance(event, dict):
                                raise RelayRejected("Invalid upstream SSE event")
                            _observe_event(observations, event)
                            kind = event.get("type")
                            if kind in {"response.done", "response.completed", "response.incomplete", "response.failed"}:
                                terminal = True
                                observations["terminal_seen"] = True
                                response = event.get("response", {})
                                usage = response.get("usage") if isinstance(response, dict) else None
                                if (kind in {"response.failed", "response.incomplete"}
                                        or not isinstance(response, dict) or response.get("status") != "completed"):
                                    failure = {"kind": "unsuccessful_response"}
                            if kind in {"error", "response.failed"}:
                                failure = {"kind": "upstream_response_error"}
                                # Fixed allowlisted classifications let native
                                # Pi/Codex retry transient errors without ever
                                # propagating arbitrary echoed provider prose.
                                event = _safe_response_error(event)
                            if terminal:
                                phase = "settlement"
                                stage = "settlement"
                                owner._phase(phase)
                                owner._settle(request_id, usage, failure, terminal=True, observations=observed_failure())
                                phase = "forward_terminal"
                                owner._phase(phase)
                            stage = "client_forward"
                            forward(b"data: " + json.dumps(event, ensure_ascii=False, separators=(",", ":")).encode() + b"\n\n")
                            if terminal:
                                break
                    if not terminal:
                        failure = failure or {"kind": "missing_terminal_usage", "phase": phase}
                    else:
                        owner._phase("completed")
                except BudgetReached as exc:
                    self._json(402, {"error": str(exc)})
                except UpstreamPreparationError as exc:
                    # Only this transport type proves that the HTTP opener was
                    # never invoked. HTTP rejections and connection errors do
                    # not provide that proof and retain unknown usage.
                    if dispatch_started and not owner.metering_enabled:
                        with owner._state:
                            owner._dispatched_requests -= 1
                            if request_id in owner._unmetered_metadata:
                                owner._unmetered_metadata[request_id]["dispatched"] = False
                    dispatch_started = False
                    phase = "transport_preparation"
                    owner._phase(phase)
                    failure = {"kind": "request_not_dispatched", "phase": phase,
                               "dispatch_started": False, "error_type": _error_type(exc)}
                    if request_id is not None:
                        owner._cancel_before_dispatch(request_id, phase)
                    owner._diagnose(str(exc), phase)
                    if not streaming:
                        self._json(502, {"error": str(exc)})
                except (TimeoutError, OSError) as exc:
                    failure = {"kind": "deadline_or_disconnect", "phase": phase,
                               "dispatch_started": dispatch_started, "error_type": _error_type(exc),
                               "observations": observed_failure(exc)}
                    if not dispatch_started:
                        if request_id is not None:
                            owner._cancel_before_dispatch(request_id, phase)
                        owner._diagnose("Pass deadline or connection expired before upstream dispatch", phase)
                        if not streaming:
                            self._json(408, {"error": "Pass deadline or connection expired"})
                    elif request_id not in owner._inflight:
                        # Billing has already committed authoritative usage.
                        # A local delivery failure must not replace that result
                        # with an unknown reservation or meter the request again.
                        owner._diagnose("Client response forwarding failed after billing settlement", phase)
                    else:
                        owner._stop("unknown_usage", "Pass deadline or connection expired after upstream dispatch", phase=phase)
                        if not owner.metering_enabled and request_id is not None:
                            owner._settle(request_id, usage, failure, terminal=terminal, observations=observed_failure(exc))
                        if not streaming:
                            self._json(504 if isinstance(exc, TimeoutError) else 502,
                                       {"error": "Upstream deadline or connection expired"})
                except Exception as exc:
                    failure = {"kind": "truncated_upstream_stream" if isinstance(exc, IncompleteRead) else "relay_failure",
                               "error_type": _error_type(exc), "phase": phase, "dispatch_started": dispatch_started,
                               "observations": observed_failure(exc)}
                    safe_error = ("Upstream stream was truncated (IncompleteRead)" if isinstance(exc, IncompleteRead)
                                  else str(exc) if isinstance(exc, (RelayRejected, AuthError, UpstreamError))
                                  else "Billing relay could not complete the request")
                    if dispatch_started and request_id in owner._inflight:
                        owner._stop("unknown_usage", safe_error, phase=phase)
                    else:
                        owner._diagnose(safe_error, phase)
                    if request_id is not None:
                        if not dispatch_started:
                            owner._cancel_before_dispatch(request_id, phase)
                        elif not owner.metering_enabled:
                            owner._settle(request_id, usage, failure, terminal=terminal, observations=observed_failure(exc))
                    if not streaming:
                        self._json(400 if isinstance(exc, (RelayRejected, ValueError)) else 502,
                                   {"error": safe_error})
                finally:
                    try:
                        if request_id is not None:
                            if dispatch_started:
                                # Prefer the exception snapshot: its typed
                                # metadata can include the framing diagnosis.
                                details = failure.get("observations") if isinstance(failure, dict) else None
                                owner._settle(request_id, usage, failure, terminal=terminal, observations=details or observed_failure())
                            else:
                                owner._cancel_before_dispatch(request_id, phase)
                    except Exception:
                        owner._stop("unknown_usage", "Billing settlement failed", phase="settlement")
                    finally:
                        with owner._state:
                            owner._admission.release()
                            owner._settlement.notify_all()

        class Server(ThreadingHTTPServer):
            daemon_threads = True
            block_on_close = False

            def handle_error(self, request, address):
                # Default HTTP tracebacks can retain request details.
                pass

        self._server = Server(("127.0.0.1", 0), Handler)
        self.url = "http://127.0.0.1:" + str(self._server.server_address[1]) + "/v1"
        self._thread = threading.Thread(target=self._server.serve_forever, daemon=True)
        self._thread.start()
        return self

    def drain_pending(self, seconds: float | None = None) -> dict[str, Any]:
        """Retire the client, then allow bounded upstream-only usage settlement.

        New passes remain blocked until this handler releases serial admission.
        A grace expiry atomically marks pending usage unknown before interrupting
        the transport; a racing terminal receipt can therefore never charge twice.
        Explicit close remains immediate, including exception/interrupt cleanup.
        """
        grace = self.spec.pending_usage_settlement_seconds if seconds is None else seconds
        if isinstance(grace, bool) or not isinstance(grace, (int, float)) or not math.isfinite(grace) or grace < 0:
            raise ValueError("Settlement grace must be nonnegative and finite")
        started = time.monotonic()
        expired = False
        with self._settlement:
            before = self.status()
            pending = bool(self._inflight or self._admission.locked())
            self._draining = True
            self._write_status("settlement_drain")
            while (self._inflight or self._admission.locked()) and not self._closed:
                remaining = grace - (time.monotonic() - started)
                if remaining <= 0:
                    expired = True
                    self._stop("unknown_usage", "Pending usage did not settle before the native-exit grace expired",
                               phase="settlement_drain")
                    for request_id in list(self._inflight):
                        self._settle(request_id, None, {"kind": "settlement_grace_expired",
                            "observations": self._close_observations(active_transport_only=True)})
                    break
                self._settlement.wait(remaining)
            after = self.status()
        if expired and hasattr(self.transport, "close"):
            self.transport.close()
        return {"status": "timed_out" if expired else "stopped" if self._closed else "settled" if pending else "no_pending",
                "active_requests_before": before["active_requests"], "grace_seconds": grace,
                "elapsed_seconds": round(time.monotonic() - started, 6),
                "newly_completed_requests": after["completed_requests"] - before["completed_requests"],
                "newly_metered_responses": after["metered_responses"] - before["metered_responses"],
                "settled_cost_usd": (_usd(Decimal(after["spent_usd"]) - Decimal(before["spent_usd"]))
                                     if self.metering_enabled else None),
                "budget": after}

    def close(self):
        with self._state:
            if self._closed:
                return
            self._close_started = time.monotonic()
            self._closed = True
            self._settlement.notify_all()
            pending = list(self._inflight)
            self._inflight.clear()
            for request_id in pending:
                failure = {"kind": "relay_closed", "observations": self._close_observations(active_transport_only=True)}
                if self.metering_enabled:
                    self.ledger.settle_request(request_id, None, failure=failure)
                else:
                    self._record_usage(request_id, None, failure)
            if pending:
                if self.metering_enabled and self._stop_reason is None:
                    self._stop_reason = "unknown_usage"
                self.last_error = "Relay closed before upstream usage was settled"
                self.last_error_phase = "closed"
            self._persist_control()
            self._write_status("closed")
        if hasattr(self.transport, "close"):
            self.transport.close()
        if self._server is not None:
            self._server.shutdown()
            self._server.server_close()
        if self._thread is not None:
            self._thread.join(timeout=5)

    def __exit__(self, *args):
        self.close()
