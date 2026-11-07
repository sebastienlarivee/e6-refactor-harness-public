"""One source-bound client for the existing resident Lean broker protocol.

Only the broker's existing validate, observe, goals and prewarm operations are
supported. Quick feedback carries one request deadline even when the resident
broker otherwise uses historical compile-only budgets.
"""

from __future__ import annotations

import hashlib
import json
import math
import socket
import struct
import time
from dataclasses import dataclass
from typing import Any

from lean_tools.measurement_policy import LEGACY_POLICY, resolve_scoring_policy
from lean_tools import check_budget

ENDPOINT_ENV = "LEAN_REFACTOR_QUICK_BROKER"
TOKEN_ENV = "LEAN_REFACTOR_QUICK_BROKER_TOKEN"
PROJECT_ROOT_ENV = "LEAN_REFACTOR_QUICK_BROKER_PROJECT_ROOT"
MAX_MESSAGE_BYTES = 16 * 1024 * 1024
OPERATIONS = frozenset({"validate", "observe", "goals", "prewarm"})


class BrokerClientError(RuntimeError):
    """Transport/protocol failure; candidate Lean errors remain normal replies."""

    def __init__(
        self, code: str, message: str, *, result: dict[str, Any] | None = None,
        retryable: bool = False,
    ) -> None:
        super().__init__(message)
        self.code = code
        self.result = result
        # Only a proven failure before dispatch permits an automatic cold retry.
        self.retryable = retryable


@dataclass(frozen=True)
class SourceRequest:
    source: str
    timeout_seconds: float
    operation: str = "validate"
    position: dict[str, int] | None = None
    target_start_line: int | None = None
    scoring_policy: str | None = None

    def __post_init__(self) -> None:
        # A request retains its policy even if the sender later changes scopes.
        object.__setattr__(self, "scoring_policy", resolve_scoring_policy(self.scoring_policy))

    def validate_timeout(self) -> None:
        timeout = self.timeout_seconds
        if (
            isinstance(timeout, bool)
            or not isinstance(timeout, (int, float))
            or not math.isfinite(timeout)
            or timeout <= 0
        ):
            raise BrokerClientError("invalid_timeout", "timeout must be positive and finite")

    @property
    def source_sha256(self) -> str:
        return hashlib.sha256(self.source.encode("utf-8")).hexdigest()

    def payload(self, token: str, timeout_scope: str) -> dict[str, Any]:
        result: dict[str, Any] = {
            "token": token,
            "source": self.source,
            "source_sha256": self.source_sha256,
            "operation": self.operation,
            "timeout_seconds": self.timeout_seconds,
            "position": self.position,
            "target_start_line": self.target_start_line,
        }
        # Missing wire policy means legacy, preserving historical requests.
        if self.scoring_policy != LEGACY_POLICY:
            result["scoring_policy"] = self.scoring_policy
        if timeout_scope == "compile":
            result["timeout_scope"] = "compile"
        else:
            result["deadline_unix"] = time.time() + self.timeout_seconds
        return result


def remaining_seconds(deadline: float) -> float:
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise TimeoutError("broker request deadline expired")
    return remaining


def receive_bytes(
    connection: socket.socket, size: int, deadline: float | None = None
) -> bytes:
    chunks: list[bytes] = []
    while size:
        if deadline is not None:
            connection.settimeout(remaining_seconds(deadline))
        chunk = connection.recv(size)
        if not chunk:
            raise BrokerClientError(
                "truncated_response", "broker closed a truncated response"
            )
        chunks.append(chunk)
        size -= len(chunk)
    return b"".join(chunks)


def validate_response(value: Any, request: SourceRequest) -> dict[str, Any]:
    """Require the reply to identify the source and resident document version."""
    if not isinstance(value, dict) or not isinstance(value.get("ok"), bool):
        raise BrokerClientError(
            "malformed_response", "broker returned a malformed response",
            result=value if isinstance(value, dict) else None,
        )
    if not value["ok"]:
        if value.get("source_sha256") not in (None, request.source_sha256):
            raise BrokerClientError("source_mismatch", "broker failure does not match the requested source", result=value)
        raise BrokerClientError(
            value.get("failure_kind", "infrastructure_failure"),
            "broker infrastructure failure: " + str(value.get("error", "unknown error")),
            result=value,
        )
    if value.get("scoring_policy", LEGACY_POLICY) != request.scoring_policy:
        raise BrokerClientError("scoring_policy_mismatch", "broker response does not match the requested scoring policy")
    if value.get("source_sha256") != request.source_sha256:
        raise BrokerClientError(
            "source_mismatch", "broker response does not match the requested source"
        )
    if type(value.get("document_version")) is not int or value["document_version"] <= 0:
        raise BrokerClientError(
            "document_version_missing", "broker response omitted its document version"
        )
    if not isinstance(value.get("valid"), bool):
        raise BrokerClientError(
            "validity_missing", "broker omitted candidate validity"
        )
    diagnostics = value.get("diagnostics")
    if not isinstance(diagnostics, list) or not all(
        isinstance(item, dict) for item in diagnostics
    ):
        raise BrokerClientError(
            "diagnostics_malformed", "broker returned malformed diagnostics"
        )
    return value


def request_to(
    endpoint: str, token: str, request: SourceRequest, *, timeout_scope: str
) -> dict[str, Any]:
    """Exchange one existing operation and return a validated source-bound reply."""
    request.validate_timeout()
    timeout = check_budget.remaining(request.timeout_seconds)
    host, separator, port_text = endpoint.rpartition(":")
    if separator != ":" or host != "127.0.0.1":
        raise BrokerClientError(
            "invalid_endpoint", "broker must use a loopback IPv4 endpoint"
        )
    try:
        port = int(port_text)
    except ValueError as error:
        raise BrokerClientError("invalid_port", "broker port is invalid") from error
    if not 0 < port < 65536:
        raise BrokerClientError("invalid_port", "broker port is invalid")
    started = time.perf_counter()
    deadline = time.monotonic() + timeout
    encoded = json.dumps(
        request.payload(token, timeout_scope), ensure_ascii=False, separators=(",", ":")
    ).encode("utf-8")
    if len(encoded) > MAX_MESSAGE_BYTES:
        raise BrokerClientError("request_too_large", "request exceeds the message limit")
    compile_scope = timeout_scope == "compile" and check_budget.current() is None
    # A quick request always carries its remaining whole-request allowance,
    # independently of the long-lived broker process's environment setting.
    if not compile_scope:
        payload = request.payload(token, "request")
        payload["timeout_seconds"] = timeout
        payload["deadline_unix"] = time.time() + timeout
        encoded = json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    sent = False
    try:
        with socket.create_connection(
            (host, port), timeout=remaining_seconds(deadline)
        ) as connection:
            connection.settimeout(remaining_seconds(deadline))
            sent = True  # A partial send is ambiguous and must never be replayed.
            connection.sendall(struct.pack("!Q", len(encoded)) + encoded)
            if compile_scope:
                # Admission can outlast the Lean allowance. EOF still detects an
                # exited broker, and active Lean work has the server's watchdog.
                connection.settimeout(None)
            response_deadline = deadline + check_budget.CLEANUP_GRACE_SECONDS
            size = struct.unpack(
                "!Q", receive_bytes(connection, 8, None if compile_scope else response_deadline)
            )[0]
            if size > MAX_MESSAGE_BYTES:
                raise BrokerClientError(
                    "response_too_large", "response exceeds the message limit"
                )
            if compile_scope:
                deadline = time.monotonic() + timeout
            value = json.loads(receive_bytes(connection, size, deadline if compile_scope else response_deadline).decode("utf-8"))
    except (OSError, ValueError, struct.error) as error:
        raise BrokerClientError(
            "transport_timeout" if isinstance(error, TimeoutError) else "transport_failed",
            f"broker request failed: {error}", retryable=not sent,
        ) from error
    result = validate_response(value, request)
    result["wall_seconds"] = time.perf_counter() - started
    return result
