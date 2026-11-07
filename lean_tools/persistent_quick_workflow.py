from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import argparse
import hmac
import json
import math
import os
import queue
import re
import secrets
import socket
import statistics
import struct
import subprocess
import sys
import tempfile
import threading
import time
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any, BinaryIO, Self

SCRIPT_ROOT = Path(__file__).resolve().parent
FEEDBACK_SUPPORT_ENV = "LEAN_REFACTOR_FEEDBACK_SUPPORT"
DEFAULT_STARTUP_TIMEOUT_SECONDS = 600.0
if str(SCRIPT_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPT_ROOT))

from lean_tools import arena_workflow as arena
from lean_tools import broker_client
from lean_tools.measurement_policy import (
    LEGACY_POLICY, SCORING_POLICY_ENV, resolve_scoring_policy, scoring_policy_context,
)
from lean_tools import process_memory
from lean_tools.process_memory import (
    ProcessTreeMemoryMonitor,
    process_descendants,
    process_tree_working_set_bytes,
)


class PersistentQuickError(RuntimeError):
    def __init__(self, message: str, *, result: dict[str, Any] | None = None,
                 code: str = "infrastructure_failure") -> None:
        super().__init__(message)
        self.result = result
        self.code = code


INFRASTRUCTURE_MESSAGE_PATTERN = re.compile(
    r"(?is)(?:\binvalid -D parameter, unknown configuration option\b|"
    r"\blake(?:\.exe)?\s+setup-file\b.*?\b(?:failed|exited)\b|"
    r"\bunknown module prefix\b|\bobject file\b[^\r\n]*\.olean\b[^\r\n]*\bdoes not exist\b|"
    r"\bfailed to load (?:the )?module\b|\bmodule\s+[`'\"]?[^\r\n]+?\bhas not been built\b)"
)


def is_infrastructure_message(message: str) -> bool:
    """Recognize process/module setup failures, not ordinary proof elaboration errors."""
    return INFRASTRUCTURE_MESSAGE_PATTERN.search(message) is not None


def encode_json_rpc_message(payload: dict[str, Any]) -> bytes:
    body = json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode(
        "utf-8"
    )
    return f"Content-Length: {len(body)}\r\n\r\n".encode("ascii") + body


def read_json_rpc_message(stream: BinaryIO) -> dict[str, Any] | None:
    content_length: int | None = None
    while True:
        line = stream.readline()
        if not line:
            return None
        if line in (b"\r\n", b"\n"):
            break
        name, separator, value = line.decode("ascii", errors="replace").partition(":")
        if separator and name.lower() == "content-length":
            content_length = int(value.strip())
    if content_length is None:
        raise PersistentQuickError("JSON-RPC message omitted Content-Length")
    body = stream.read(content_length)
    if len(body) != content_length:
        raise PersistentQuickError("truncated JSON-RPC message")
    value = json.loads(body.decode("utf-8"))
    if not isinstance(value, dict):
        raise PersistentQuickError("JSON-RPC payload is not an object")
    return value


@dataclass(frozen=True)
class Diagnostic:
    severity: str
    line: int | None
    character: int | None
    message: str

    def signature(self) -> tuple[str, int | None, int | None, str]:
        return (
            self.severity,
            self.line,
            self.character,
            re.sub(r"\s+", " ", self.message).strip(),
        )

    def semantic_signature(self) -> tuple[str, int | None, str]:
        return (
            self.severity,
            self.line,
            re.sub(r"\s+", " ", self.message).strip(),
        )

    def as_json(self) -> dict[str, Any]:
        return {
            "severity": self.severity,
            "line": self.line,
            "character": self.character,
            "message": self.message,
        }


class DiagnosticAccumulator:
    def __init__(self, uri: str, version: int) -> None:
        self.uri = uri
        self.version = version
        self.values: list[dict[str, Any]] = []

    def observe(self, message: dict[str, Any]) -> None:
        if message.get("method") != "textDocument/publishDiagnostics":
            return
        params = message.get("params")
        if not isinstance(params, dict) or params.get("uri") != self.uri:
            return
        version = params.get("version")
        if isinstance(version, int) and version != self.version:
            return
        diagnostics = params.get("diagnostics")
        if not isinstance(diagnostics, list):
            return
        if params.get("isIncremental") is True:
            self.values.extend(item for item in diagnostics if isinstance(item, dict))
        else:
            self.values = [item for item in diagnostics if isinstance(item, dict)]


def lsp_diagnostics(values: list[dict[str, Any]]) -> list[Diagnostic]:
    diagnostics: list[Diagnostic] = []
    for value in values:
        severity_value = value.get("severity")
        severity = {
            1: "error",
            2: "warning",
            3: "information",
            4: "hint",
        }.get(severity_value, str(severity_value or "unknown"))
        range_value = value.get("range")
        start = range_value.get("start") if isinstance(range_value, dict) else None
        line = start.get("line") if isinstance(start, dict) else None
        character = start.get("character") if isinstance(start, dict) else None
        diagnostics.append(
            Diagnostic(
                severity,
                line if isinstance(line, int) else None,
                character if isinstance(character, int) else None,
                str(value.get("message", "")),
            )
        )
    return diagnostics


def cold_json_diagnostics(output: str) -> list[Diagnostic]:
    diagnostics: list[Diagnostic] = []
    unparsed: list[str] = []
    for line_text in output.splitlines():
        line_text = line_text.strip()
        if not line_text:
            continue
        try:
            value = json.loads(line_text)
        except json.JSONDecodeError:
            unparsed.append(line_text)
            continue
        if not isinstance(value, dict):
            continue
        severity_value = value.get("severity")
        severity = (
            str(severity_value).lower()
            if isinstance(severity_value, str)
            else {1: "error", 2: "warning", 3: "information", 4: "hint"}.get(
                severity_value, str(severity_value or "unknown")
            )
        )
        position = value.get("pos")
        line = position.get("line") if isinstance(position, dict) else None
        column = position.get("column") if isinstance(position, dict) else None
        diagnostics.append(
            Diagnostic(
                severity,
                line - 1 if isinstance(line, int) else None,
                column if isinstance(column, int) else None,
                str(value.get("data", value.get("message", ""))),
            )
        )
    if not diagnostics:
        for text in unparsed:
            if "error" in text.lower():
                diagnostics.append(Diagnostic("error", None, None, text))
    return diagnostics


def error_signatures(
    values: list[Diagnostic],
) -> list[tuple[str, int | None, int | None, str]]:
    return sorted(value.signature() for value in values if value.severity == "error")


def diagnostics_equivalent(
    cold: list[Diagnostic], persistent: list[Diagnostic]
) -> bool:
    cold_values = sorted(
        value.semantic_signature() for value in cold if value.severity == "error"
    )
    persistent_values = sorted(
        value.semantic_signature() for value in persistent if value.severity == "error"
    )
    return cold_values == persistent_values


def diagnostic_locations_equivalent(
    cold: list[Diagnostic], persistent: list[Diagnostic]
) -> bool:
    return error_signatures(cold) == error_signatures(persistent)


@dataclass(frozen=True)
class ColdRun:
    returncode: int
    seconds: float
    output: str
    peak_tree_working_set_bytes: int | None


class ColdLeanTimeout(PersistentQuickError):
    def __init__(self, result: ColdRun, log_path: Path) -> None:
        super().__init__(f"cold Lean benchmark timed out; diagnostics: {log_path}")
        self.result = result
        self.log_path = log_path


def run_cold_lean(
    document_path: Path,
    project_root: Path,
    scratch_root: Path,
    timeout_seconds: int,
) -> ColdRun:
    if os.environ.get("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE") == "compile":
        # Discovery fallback uses the same admission, launch cache and bounded
        # process cleanup as authoritative checks in E6.
        run = arena.run_lean(document_path, project_root, timeout_seconds,
                             lean_args=["--json", "-R", str(scratch_root.resolve())])
        result = ColdRun(run.returncode, run.seconds, run.output, run.peak_working_set_bytes)
        if run.timed_out:
            if run.log_path:
                log_path = Path(run.log_path)
            else:
                scratch_root.mkdir(parents=True, exist_ok=True)
                with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8",
                        prefix="cold-lean-timeout-", suffix=".log", dir=scratch_root, delete=False) as log:
                    log.write(run.output)
                    log_path = Path(log.name)
            raise ColdLeanTimeout(result, log_path)
        return result
    command = [
        "lake",
        "env",
        "lean",
        "--json",
        "-R",
        str(scratch_root.resolve()),
        str(document_path.resolve()),
    ]
    deadline = time.monotonic() + timeout_seconds
    try:
        with arena.resource_gate.permit_from_environment(
            "lean",
            priority=10,
            metadata={"purpose": "phase3-cold-quick-benchmark"},
            timeout_seconds=timeout_seconds,
        ):
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise PersistentQuickError(
                    "cold Lean deadline expired during admission"
                )
            started = time.perf_counter()
            command = arena.lean_launch.native_command(command)
            process = subprocess.Popen(
                command,
                env=arena.lean_launch.native_environment(),
                cwd=project_root,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                encoding="utf-8",
                errors="replace",
                creationflags=(
                    subprocess.CREATE_NEW_PROCESS_GROUP if os.name == "nt" else 0
                ),
                start_new_session=os.name != "nt",
            )
            process_memory.capture_process_identity(process)
            timed_out = False
            with ProcessTreeMemoryMonitor(process.pid) as memory:
                try:
                    output, _ = process.communicate(
                        timeout=max(0.0, deadline - time.monotonic())
                    )
                except subprocess.TimeoutExpired as error:
                    timed_out = True
                    arena.terminate_process_tree(process)
                    output, _ = process.communicate()
                    if not output:
                        partial = error.output or ""
                        output = (
                            partial.decode("utf-8", errors="replace")
                            if isinstance(partial, bytes)
                            else partial
                        )
            result = ColdRun(
                process.returncode if process.returncode is not None else -1,
                time.perf_counter() - started,
                output,
                memory.peak_bytes,
            )
            if timed_out:
                scratch_root.mkdir(parents=True, exist_ok=True)
                with tempfile.NamedTemporaryFile(
                    mode="w",
                    encoding="utf-8",
                    prefix="cold-lean-timeout-",
                    suffix=".log",
                    dir=scratch_root,
                    delete=False,
                ) as log:
                    log.write(output)
                    log_path = Path(log.name)
                raise ColdLeanTimeout(result, log_path)
            return result
    except arena.resource_gate.ResourceGateError as error:
        raise PersistentQuickError(f"Lean admission failed: {error}") from error


class LeanLspSession:
    def __init__(
        self,
        project_root: Path,
        document_path: Path,
        stderr_path: Path,
        timeout_seconds: float,
        *,
        lean_path_prefixes: list[Path] | None = None,
    ) -> None:
        self.project_root = project_root.resolve()
        self.document_path = document_path.resolve()
        self.uri = self.document_path.as_uri()
        self.stderr_path = stderr_path.resolve()
        self.timeout_seconds = timeout_seconds
        self.lean_path_prefixes = [path.resolve() for path in lean_path_prefixes or []]
        self.process: subprocess.Popen[bytes] | None = None
        self.stderr_file: BinaryIO | None = None
        self.messages: queue.Queue[dict[str, Any] | Exception | None] = queue.Queue()
        self.reader: threading.Thread | None = None
        self.request_id = 1
        self.version = 0
        self.send_lock = threading.Lock()
        self.startup_seconds: float | None = None
        self.process_launch_seconds: float | None = None
        self.initialization_seconds: float | None = None
        self.request_deadline: float | None = None

    def start(self) -> None:
        if self.process is not None:
            raise PersistentQuickError("Lean LSP session is already running")
        self.stderr_path.parent.mkdir(parents=True, exist_ok=True)
        self.stderr_file = self.stderr_path.open("wb")
        started = time.perf_counter()
        environment = arena.lean_launch.native_environment()
        if self.lean_path_prefixes:
            environment["LEAN_PATH"] = os.pathsep.join(
                [
                    *(str(path) for path in self.lean_path_prefixes),
                    *(
                        [environment["LEAN_PATH"]]
                        if environment.get("LEAN_PATH")
                        else []
                    ),
                ]
            )
        try:
            self.process = subprocess.Popen(
                arena.lean_launch.native_command(["lake", "serve", "--", "-DstderrAsMessages=false"]),
                cwd=self.project_root,
                env=environment,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=self.stderr_file,
                creationflags=(
                    subprocess.CREATE_NEW_PROCESS_GROUP if os.name == "nt" else 0
                ),
                start_new_session=os.name != "nt",
            )
            process_memory.capture_process_identity(self.process)
        finally:
            self.process_launch_seconds = time.perf_counter() - started
        assert self.process.stdout is not None
        self.reader = threading.Thread(target=self._reader_loop, daemon=True)
        self.reader.start()
        initialization_started = time.perf_counter()
        try:
            self._request(
                "initialize",
                {
                    "processId": os.getpid(),
                    "clientInfo": {"name": "lean-refactor-phase3", "version": "1"},
                    "rootUri": self.project_root.as_uri(),
                    "initializationOptions": {"hasWidgets": False},
                    "capabilities": {
                        "lean": {
                            "incrementalDiagnosticSupport": True,
                            "silentDiagnosticSupport": True,
                        }
                    },
                },
            )
            self._send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
        finally:
            self.initialization_seconds = time.perf_counter() - initialization_started
        self.startup_seconds = time.perf_counter() - started

    def _reader_loop(self) -> None:
        assert self.process is not None and self.process.stdout is not None
        try:
            while True:
                message = read_json_rpc_message(self.process.stdout)
                self.messages.put(message)
                if message is None:
                    return
        except (OSError, ValueError, PersistentQuickError) as error:
            self.messages.put(error)

    def _send(self, payload: dict[str, Any]) -> None:
        if self.process is None or self.process.stdin is None:
            raise PersistentQuickError("Lean LSP session is not running")
        data = encode_json_rpc_message(payload)
        # A worker that stops reading can block write/flush before the
        # response-queue watchdog runs. Killing this owned process tree
        # releases the pipe without putting a deadline on queue admission.
        deadline = time.monotonic() + self.timeout_seconds
        if self.request_deadline is not None:
            deadline = min(deadline, self.request_deadline)
        remaining = deadline - time.monotonic()
        if remaining <= 0 or not self.send_lock.acquire(timeout=max(0, remaining)):
            raise PersistentQuickError("Lean LSP input deadline expired", code="operation_timeout")
        finished, expired = threading.Event(), threading.Event()
        process = self.process
        def expire():
            if not finished.is_set():
                expired.set()
                arena.terminate_process_tree(process)
        timer = threading.Timer(max(0, deadline - time.monotonic()), expire)
        timer.daemon = True
        timer.start()
        try:
            process.stdin.write(data)
            process.stdin.flush()
        except (BrokenPipeError, OSError) as error:
            message = "Lean LSP input deadline expired" if expired.is_set() else "Lean LSP input pipe closed"
            raise PersistentQuickError(message, code="operation_timeout" if expired.is_set() else "transport_failed") from error
        finally:
            finished.set()
            timer.cancel()
            timer.join(timeout=arena.check_budget.CLEANUP_GRACE_SECONDS)
            self.send_lock.release()
        if expired.is_set():
            raise PersistentQuickError("Lean LSP input deadline expired", code="operation_timeout")

    def _request(
        self,
        method: str,
        params: dict[str, Any] | None,
        accumulator: DiagnosticAccumulator | None = None,
    ) -> Any:
        deadline = time.monotonic() + self.timeout_seconds
        if self.request_deadline is not None:
            deadline = min(deadline, self.request_deadline)
        if deadline <= time.monotonic():
            raise PersistentQuickError(f"timed out waiting for {method}", code="operation_timeout")
        request_id = self.request_id
        self.request_id += 1
        self._send(
            {
                "jsonrpc": "2.0",
                "id": request_id,
                "method": method,
                "params": params,
            }
        )
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise PersistentQuickError(f"timed out waiting for {method}", code="operation_timeout")
            try:
                message = self.messages.get(timeout=remaining)
            except queue.Empty as error:
                raise PersistentQuickError(f"timed out waiting for {method}", code="operation_timeout") from error
            if message is None:
                returncode = self.process.poll() if self.process is not None else None
                raise PersistentQuickError(
                    f"Lean LSP output closed while waiting for {method}; returncode={returncode}"
                )
            if isinstance(message, Exception):
                raise PersistentQuickError(
                    f"Lean LSP reader failed: {message}"
                ) from message
            if accumulator is not None:
                accumulator.observe(message)
            if "method" in message and "id" in message:
                self._send(
                    {
                        "jsonrpc": "2.0",
                        "id": message["id"],
                        "result": None,
                    }
                )
                continue
            if message.get("id") != request_id:
                continue
            if "error" in message:
                raise PersistentQuickError(f"{method} failed: {message['error']}")
            return message.get("result")

    def _wait_for_diagnostics(self, version: int) -> list[Diagnostic]:
        accumulator = DiagnosticAccumulator(self.uri, version)
        self._request(
            "textDocument/waitForDiagnostics",
            {"uri": self.uri, "version": version},
            accumulator,
        )
        return lsp_diagnostics(accumulator.values)

    def open_document(self, text: str) -> tuple[float, list[Diagnostic]]:
        if self.version != 0:
            raise PersistentQuickError("document is already open")
        self.version = 1
        started = time.perf_counter()
        self._send(
            {
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": self.uri,
                        "languageId": "lean",
                        "version": self.version,
                        "text": text,
                    },
                    "dependencyBuildMode": "never",
                },
            }
        )
        diagnostics = self._wait_for_diagnostics(self.version)
        return time.perf_counter() - started, diagnostics

    def change_document(self, text: str) -> tuple[float, list[Diagnostic]]:
        if self.version == 0:
            raise PersistentQuickError("document is not open")
        self.version += 1
        started = time.perf_counter()
        self._send(
            {
                "jsonrpc": "2.0",
                "method": "textDocument/didChange",
                "params": {
                    "textDocument": {"uri": self.uri, "version": self.version},
                    "contentChanges": [{"text": text}],
                },
            }
        )
        diagnostics = self._wait_for_diagnostics(self.version)
        return time.perf_counter() - started, diagnostics

    def interactive_goals(self, position: dict[str, int]) -> Any:
        """Read goals for this document version while its owner holds admission."""
        if self.version == 0:
            raise PersistentQuickError("document must be open before requesting goals")
        connection = self._request("$/lean/rpc/connect", {"uri": self.uri})
        if not isinstance(connection, dict) or "sessionId" not in connection:
            raise PersistentQuickError("Lean did not return an RPC session identifier")
        session_id = connection["sessionId"]
        goal_params = {"textDocument": {"uri": self.uri}, "position": position}
        result = self._request(
            "$/lean/rpc/call",
            {
                **goal_params,
                "sessionId": session_id,
                "method": "Lean.Widget.getInteractiveGoals",
                "params": goal_params,
            },
        )
        refs = rpc_refs(result)
        if refs:
            self._send(
                {
                    "jsonrpc": "2.0",
                    "method": "$/lean/rpc/release",
                    "params": {"uri": self.uri, "sessionId": session_id, "refs": refs},
                }
            )
        return result

    def crash_file_worker(self) -> dict[str, Any]:
        if self.process is None or self.process.poll() is not None:
            raise PersistentQuickError("Lean LSP session is not running")
        descendants = process_descendants(self.process.pid)
        candidates = [
            (depth, pid, name)
            for pid, (_parent, name, depth) in descendants.items()
            if name.lower().startswith("lean")
        ]
        if not candidates:
            raise PersistentQuickError("could not locate a Lean file-worker process")
        depth, pid, name = max(candidates)
        if sys.platform == "linux":
            identity = process_memory.linux_process_identity(pid)
            if identity is None or pid not in process_descendants(self.process.pid):
                raise PersistentQuickError("Lean file worker exited before cleanup")
            if not process_memory.terminate_process_tree_pid(pid):
                raise PersistentQuickError(f"could not terminate file worker {pid}")
        else:
            completed = subprocess.run(
                ["taskkill", "/PID", str(pid), "/T", "/F"],
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                check=False,
                timeout=10,
            )
            if completed.returncode != 0:
                raise PersistentQuickError(
                    f"could not terminate file worker {pid}: "
                    f"{(completed.stdout + completed.stderr).strip()}"
                )
        return {"pid": pid, "name": name, "depth": depth}

    def tree_working_set_bytes(self) -> int | None:
        return (
            process_tree_working_set_bytes(self.process.pid)
            if self.process is not None
            else None
        )

    def close(self) -> None:
        process = self.process
        if process is None:
            if self.stderr_file is not None:
                self.stderr_file.close()
                self.stderr_file = None
            return
        original_timeout = self.timeout_seconds
        try:
            self.timeout_seconds = min(original_timeout, 10)
            if process.poll() is None:
                if self.version:
                    self._send(
                        {
                            "jsonrpc": "2.0",
                            "method": "textDocument/didClose",
                            "params": {"textDocument": {"uri": self.uri}},
                        }
                    )
                self._request("shutdown", None)
                self._send({"jsonrpc": "2.0", "method": "exit", "params": None})
                process.wait(timeout=10)
        except (PersistentQuickError, subprocess.TimeoutExpired):
            arena.terminate_process_tree(process)
        finally:
            if process.poll() is None:
                arena.terminate_process_tree(process)
            if process.stdin is not None:
                process.stdin.close()
            if process.stdout is not None:
                process.stdout.close()
            if self.stderr_file is not None:
                self.stderr_file.close()
            self.process = None
            self.timeout_seconds = original_timeout

    def __enter__(self) -> Self:
        try:
            self.start()
        except BaseException:
            self.close()
            raise
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()


def _remaining_seconds(deadline: float) -> float:
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise TimeoutError("feedback request deadline expired")
    return remaining


def _receive_socket_bytes(
    connection: socket.socket, size: int, deadline: float | None = None
) -> bytes:
    chunks: list[bytes] = []
    remaining = size
    while remaining:
        if deadline is not None:
            connection.settimeout(_remaining_seconds(deadline))
        chunk = connection.recv(remaining)
        if not chunk:
            raise PersistentQuickError("broker client sent a truncated message")
        chunks.append(chunk)
        remaining -= len(chunk)
    return b"".join(chunks)


@contextmanager
def _deadline_lock(lock: Any, deadline: float) -> Iterator[None]:
    if not lock.acquire(timeout=max(0.0, deadline - time.monotonic())):
        raise PersistentQuickError(
            "feedback request expired waiting for managed document", code="queue_timeout"
        )
    try:
        yield
    finally:
        lock.release()


@contextmanager
def _queued_lock(lock: Any, stop_event: threading.Event) -> Iterator[None]:
    """Wait for the managed document without charging the next Lean operation."""
    while not stop_event.is_set():
        if lock.acquire(timeout=0.2):
            break
    else:
        raise PersistentQuickError("broker closed while waiting for managed document", code="cancelled")
    try:
        if stop_event.is_set():
            raise PersistentQuickError("broker closed while waiting for managed document", code="cancelled")
        yield
    finally:
        lock.release()


def rpc_refs(value: Any) -> list[dict[str, str]]:
    if isinstance(value, list):
        return [ref for item in value for ref in rpc_refs(item)]
    if isinstance(value, dict):
        if set(value) == {"p"} and isinstance(value["p"], str):
            return [{"p": value["p"]}]
        return [ref for item in value.values() for ref in rpc_refs(item)]
    return []


def feedback_request(
    source: str,
    timeout_seconds: float,
    *,
    operation: str = "validate",
    position: dict[str, int] | None = None,
    target_start_line: int | None = None,
    scoring_policy: str | None = None,
) -> dict[str, Any]:
    """Issue an existing operation through the shared source-bound broker client."""
    request = broker_client.SourceRequest(
        source, timeout_seconds, operation, position, target_start_line, scoring_policy
    )
    try:
        request.validate_timeout()
    except broker_client.BrokerClientError as error:
        raise PersistentQuickError("feedback timeout must be positive and finite") from error
    endpoint = os.environ.get(broker_client.ENDPOINT_ENV, "")
    token = os.environ.get(broker_client.TOKEN_ENV, "")
    if not endpoint or not token:
        raise PersistentQuickError(
            "resident feedback service is not configured on loopback"
        )
    try:
        result = broker_client.request_to(
            endpoint, token, request,
            timeout_scope=os.environ.get("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE", ""),
        )
    except broker_client.BrokerClientError as error:
        messages = {
            "invalid_timeout": "feedback timeout must be positive and finite",
            "invalid_endpoint": "resident feedback service is not configured on loopback",
            "invalid_port": "feedback broker port is invalid",
            "request_too_large": "feedback request exceeds the message limit",
            "response_too_large": "feedback response exceeds the message limit",
            "source_mismatch": "feedback response does not match the requested source",
            "scoring_policy_mismatch": "feedback response does not match the requested scoring policy",
            "document_version_missing": "feedback response omitted its document version",
            "validity_missing": "feedback response omitted validity or diagnostics",
            "diagnostics_malformed": "feedback response omitted validity or diagnostics",
        }
        if error.code in {"infrastructure_failure", "malformed_response"}:
            value = error.result if error.result is not None else str(error)
            message = f"feedback service failed: {value}"
        else:
            message = messages.get(error.code, "feedback request failed: " + str(error))
        raise PersistentQuickError(message, result=error.result, code=error.code) from error
    setup_errors = [
        str(item["message"])
        for item in result["diagnostics"]
        if is_infrastructure_message(str(item.get("message", "")))
    ]
    if setup_errors:
        raise PersistentQuickError(
            "Lean setup infrastructure failure: " + "\n".join(setup_errors)
        )
    result["wall_seconds"] = round(result["wall_seconds"], 6)
    return result


class PersistentQuickBroker:
    """A loopback-only, serialized bridge to one managed Lean document."""

    def __init__(
        self,
        project_root: Path,
        work_root: Path,
        initial_source: str,
        *,
        timeout_seconds: int,
        startup_timeout_seconds: float = DEFAULT_STARTUP_TIMEOUT_SECONDS,
        lean_path_prefixes: list[Path] | None = None,
        scoring_policy: str | None = None,
    ) -> None:
        self.scoring_policy = resolve_scoring_policy(scoring_policy)
        self.project_root = project_root.resolve()
        self.work_root = work_root.resolve()
        self.initial_source = initial_source
        self.timeout_seconds = timeout_seconds
        if (
            isinstance(startup_timeout_seconds, bool)
            or not isinstance(startup_timeout_seconds, (int, float))
            or not math.isfinite(startup_timeout_seconds)
            or startup_timeout_seconds <= 0
        ):
            raise PersistentQuickError("startup timeout must be positive and finite")
        self.startup_timeout_seconds = float(startup_timeout_seconds)
        self.lean_path_prefixes = [path.resolve() for path in lean_path_prefixes or []]
        self.token = secrets.token_urlsafe(32)
        self.listener: socket.socket | None = None
        self.thread: threading.Thread | None = None
        self.stop_event = threading.Event()
        self.session_lock = threading.Lock()
        self.session: LeanLspSession | None = None
        self.session_started_at: str | None = None
        self.session_started_perf: float | None = None
        self.session_request_count = 0
        self.session_queue_wait_seconds = 0.0
        self.session_peak_working_set_bytes: int | None = None
        self.session_error: str | None = None
        self.port: int | None = None
        self.current_source_sha256: str | None = None
        self.current_diagnostics: list[Diagnostic] = []

    @property
    def document_path(self) -> Path:
        return self.work_root / "ManagedQuick.lean"

    @property
    def stderr_path(self) -> Path:
        return self.work_root / "lean-lsp.stderr.log"

    @property
    def startup_path(self) -> Path:
        return self.work_root / "startup.json"

    def prewarm(self, *, timeout_seconds: float | None = None) -> dict[str, Any]:
        """Load the original scaffold with its own budget before warm requests.

        Ordinary proof errors are retained but do not prevent readiness. This is a
        source-changing operation: call it before launching candidate work.
        """
        timeout = (
            self.startup_timeout_seconds if timeout_seconds is None else timeout_seconds
        )
        if (
            isinstance(timeout, bool)
            or not isinstance(timeout, (int, float))
            or not math.isfinite(timeout)
            or timeout <= 0
        ):
            raise PersistentQuickError("startup timeout must be positive and finite")
        timeout = min(float(timeout), self.startup_timeout_seconds)
        started = time.perf_counter()
        result = {
            "schema_version": 2,
            "operation": "prewarm",
            "status": "starting",
            "ready": False,
            "source_sha256": arena.sha256_bytes(self.initial_source.encode("utf-8")),
            "startup_timeout_seconds": self.startup_timeout_seconds,
            "timeout_seconds": timeout,
            "started_at": arena.utc_now(),
            "project_root": str(self.project_root),
            "stderr_path": str(self.stderr_path),
            "managed_document_path": str(self.document_path),
        }
        arena.write_json_atomic(self.startup_path, result)
        try:
            # Writing the startup record shares the same absolute operation budget.
            response = self._validate(
                self.initial_source,
                operation="prewarm",
                timeout_seconds=timeout - (time.perf_counter() - started),
            )
        except (PersistentQuickError, OSError) as error:
            result.update(getattr(error, "result", None) or {})
            result.update(
                ok=False,
                ready=False,
                valid=None,
                status="failed",
                error=str(error),
                wall_seconds=round(time.perf_counter() - started, 6),
                finished_at=arena.utc_now(),
            )
            arena.write_json_atomic(self.startup_path, result)
            raise PersistentQuickError(str(error), result=result) from error
        result.update(response)
        result.update(
            status="ready",
            ready=True,
            wall_seconds=round(time.perf_counter() - started, 6),
            finished_at=arena.utc_now(),
        )
        arena.write_json_atomic(self.startup_path, result)
        return result

    def start(self) -> None:
        if self.listener is not None:
            raise PersistentQuickError("persistent quick broker is already running")
        self.work_root.mkdir(parents=True, exist_ok=True)
        # The managed candidate versions stay inside the LSP process. Only the public
        # original proof is materialized at the stable document URI.
        self.document_path.write_text(self.initial_source, encoding="utf-8")
        listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        listener.bind(("127.0.0.1", 0))
        listener.listen(128)
        listener.settimeout(0.2)
        self.listener = listener
        self.port = int(listener.getsockname()[1])
        self.thread = threading.Thread(
            target=self._serve,
            name="persistent-quick-broker",
            daemon=True,
        )
        self.thread.start()

    def environment(self) -> dict[str, str]:
        if self.port is None:
            raise PersistentQuickError("persistent quick broker has not started")
        return {
            SCORING_POLICY_ENV: self.scoring_policy,
            arena.PERSISTENT_QUICK_ENDPOINT_ENV: f"127.0.0.1:{self.port}",
            arena.PERSISTENT_QUICK_TOKEN_ENV: self.token,
            arena.PERSISTENT_QUICK_PROJECT_ROOT_ENV: str(self.project_root),
            FEEDBACK_SUPPORT_ENV: json.dumps(
                [str(path) for path in self.lean_path_prefixes]
            ),
        }

    def _serve(self) -> None:
        assert self.listener is not None
        while not self.stop_event.is_set():
            try:
                connection, _address = self.listener.accept()
            except TimeoutError:
                continue
            except OSError:
                if self.stop_event.is_set():
                    return
                continue
            with connection:
                connection.settimeout(self.timeout_seconds)
                self._handle_connection(connection)

    def _handle_connection(self, connection: socket.socket) -> None:
        received_at = time.monotonic()
        compile_scope = False
        wire_deadline = received_at + max(
            self.timeout_seconds, self.startup_timeout_seconds
        )
        try:
            size = struct.unpack(
                "!Q", _receive_socket_bytes(connection, 8, wire_deadline)
            )[0]
            if size > arena.PERSISTENT_QUICK_MAX_MESSAGE_BYTES:
                raise PersistentQuickError("broker request exceeds the message limit")
            request = json.loads(
                _receive_socket_bytes(connection, size, wire_deadline).decode("utf-8")
            )
            if not isinstance(request, dict):
                raise PersistentQuickError("broker request is not an object")
            token = request.get("token")
            source = request.get("source")
            if not isinstance(token, str) or not hmac.compare_digest(token, self.token):
                raise PersistentQuickError("broker authentication failed")
            if not isinstance(source, str):
                raise PersistentQuickError("broker request omitted Lean source")
            operation = request.get("operation", "validate")
            if not isinstance(operation, str) or operation not in broker_client.OPERATIONS:
                raise PersistentQuickError("unknown feedback operation")
            source_digest = arena.sha256_bytes(source.encode("utf-8"))
            if request.get("source_sha256", source_digest) != source_digest:
                raise PersistentQuickError("feedback request source hash mismatch")
            budget = (
                self.startup_timeout_seconds
                if operation == "prewarm"
                else self.timeout_seconds
            )
            timeout = request.get("timeout_seconds", budget)
            if (
                isinstance(timeout, bool)
                or not isinstance(timeout, (int, float))
                or not math.isfinite(timeout)
                or timeout <= 0
            ):
                raise PersistentQuickError(
                    "feedback timeout must be positive and finite"
                )
            timeout = min(float(timeout), budget)
            compile_scope = (
                os.environ.get("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE") == "compile"
                and request.get("timeout_scope") == "compile"
            )
            if not compile_scope:
                operation_wire_deadline = received_at + timeout
                deadline_unix = request.get("deadline_unix", time.time() + timeout)
                if (
                    isinstance(deadline_unix, bool)
                    or not isinstance(deadline_unix, (int, float))
                    or not math.isfinite(deadline_unix)
                ):
                    raise PersistentQuickError("feedback deadline is invalid")
                timeout = min(timeout, deadline_unix - time.time())
                if timeout <= 0:
                    raise PersistentQuickError("feedback request expired while queued", code="queue_timeout")
                wire_deadline = min(operation_wire_deadline, time.monotonic() + timeout)
            position = request.get("position")
            if operation == "goals" and (
                not isinstance(position, dict)
                or set(position) != {"line", "character"}
                or any(
                    type(value) is not int or value < 0 for value in position.values()
                )
            ):
                raise PersistentQuickError(
                    "goals require a nonnegative LSP line and character"
                )
            target_start_line = request.get("target_start_line")
            if target_start_line is not None and (
                type(target_start_line) is not int or target_start_line < 0
            ):
                raise PersistentQuickError(
                    "target_start_line must be a nonnegative LSP line"
                )
            if not compile_scope:
                timeout = _remaining_seconds(wire_deadline)
            policy = request.get("scoring_policy", LEGACY_POLICY)
            try:
                if not isinstance(policy, str):
                    raise PersistentQuickError("feedback scoring_policy must be a supported version string")
                policy = resolve_scoring_policy(policy)
            except arena.WorkflowError as error:
                raise PersistentQuickError(str(error)) from error
            # Broker threads do not inherit a caller's ContextVar. Bind each wire
            # operation explicitly so two capsule policies can share this worker.
            with scoring_policy_context(policy):
                if operation == "prewarm":
                    if source != self.initial_source:
                        raise PersistentQuickError("prewarm requires the original scaffold")
                    response = self.prewarm(timeout_seconds=timeout)
                else:
                    response = self._validate(
                        source,
                        operation=operation,
                        position=position,
                        target_start_line=target_start_line,
                        timeout_seconds=timeout,
                        request_scope=not compile_scope,
                    )
            if policy != LEGACY_POLICY:
                response["scoring_policy"] = policy
        except (
            OSError,
            TimeoutError,
            UnicodeDecodeError,
            json.JSONDecodeError,
            struct.error,
            PersistentQuickError,
        ) as error:
            response = {
                **(getattr(error, "result", None) or {}),
                "ok": False,
                "error": str(error),
                "failure_kind": getattr(error, "code", "operation_timeout" if isinstance(error, TimeoutError) else "infrastructure_failure"),
            }
        encoded = json.dumps(
            response, ensure_ascii=False, separators=(",", ":")
        ).encode("utf-8")
        if len(encoded) > arena.PERSISTENT_QUICK_MAX_MESSAGE_BYTES:
            encoded = json.dumps(
                {"ok": False, "error": "broker response exceeds the message limit"},
                separators=(",", ":"),
            ).encode("utf-8")
        try:
            # Deadline replies are sent only after owned Lean cleanup. Permit a
            # finite cleanup/reply grace even after the operation deadline.
            wire_deadline = time.monotonic() + arena.check_budget.CLEANUP_GRACE_SECONDS
            connection.settimeout(_remaining_seconds(wire_deadline))
            connection.sendall(struct.pack("!Q", len(encoded)) + encoded)
        except OSError:
            return

    def _validate(
        self,
        source: str,
        *,
        operation: str = "validate",
        position: dict[str, int] | None = None,
        target_start_line: int | None = None,
        timeout_seconds: float | None = None,
        request_scope: bool | None = None,
    ) -> dict[str, Any]:
        operation_started = time.perf_counter()
        timeout = self.timeout_seconds if timeout_seconds is None else timeout_seconds
        deadline = time.monotonic() + timeout
        telemetry: dict[str, Any] = {
            "phase": "document_lock",
            "phase_started": operation_started,
            "phase_timings": {
                name: 0.0
                for name in (
                    "document_lock",
                    "admission",
                    "process_launch",
                    "initialization",
                    "first_document",
                    "change_document",
                    "goals",
                )
            },
        }
        try:
            return self._validate_operation(
                source,
                operation=operation,
                position=position,
                target_start_line=target_start_line,
                timeout_seconds=timeout,
                deadline=deadline,
                operation_started=operation_started,
                telemetry=telemetry,
                compile_scope=(os.environ.get("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE") == "compile"
                               if request_scope is None else not request_scope),
            )
        except (
            arena.resource_gate.ResourceGateError,
            PersistentQuickError,
            OSError,
            TimeoutError,
        ) as error:
            phase = telemetry["phase"]
            if phase in {"document_lock", "admission"}:
                telemetry["phase_timings"][phase] = (
                    time.perf_counter() - telemetry["phase_started"]
                )
            result = {
                "schema_version": 2,
                "ok": False,
                "ready": False,
                "operation": operation,
                "source_sha256": arena.sha256_bytes(source.encode("utf-8")),
                "valid": None,
                "timeout_seconds": timeout,
                "failure_phase": phase,
                "phase_timings": {
                    name: round(value, 6)
                    for name, value in telemetry["phase_timings"].items()
                },
                "lsp_seconds": round(time.perf_counter() - operation_started, 6),
                "error": str(error),
                "failure_kind": ("cancelled" if isinstance(error, arena.resource_gate.ResourceGateCancelled)
                                 else "queue_timeout" if isinstance(error, arena.resource_gate.ResourceGateTimeout)
                                 else "operation_timeout" if isinstance(error, TimeoutError)
                                 else getattr(error, "code", "infrastructure_failure")),
                "cleanup_complete": self.session is None,
            }
            arena.record_event("persistent_feedback", result)
            raise PersistentQuickError(str(error), result=result, code=result["failure_kind"]) from error

    def _validate_operation(
        self,
        source: str,
        *,
        operation: str,
        position: dict[str, int] | None,
        target_start_line: int | None,
        timeout_seconds: float,
        deadline: float,
        operation_started: float,
        telemetry: dict[str, Any],
        compile_scope: bool | None = None,
    ) -> dict[str, Any]:
        phases = telemetry["phase_timings"]
        if compile_scope is None:
            compile_scope = os.environ.get("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE") == "compile"
        document_lock = (_queued_lock(self.session_lock, self.stop_event) if compile_scope
                         else _deadline_lock(self.session_lock, deadline))
        with document_lock:
            phases["document_lock"] = time.perf_counter() - operation_started
            digest = arena.sha256_bytes(source.encode("utf-8"))
            reused = self.session is not None and digest == self.current_source_sha256
            edit_seconds = 0.0
            raw_goals: Any = None
            startup_seconds = 0.0
            session_touched = False
            telemetry.update(phase="admission", phase_started=time.perf_counter())
            try:
                with arena.resource_gate.permit_from_environment(
                    "lean",
                    priority=0,
                    timeout_seconds=None if compile_scope else max(0.0, deadline - time.monotonic()),
                    **({"cancel_event": self.stop_event} if compile_scope else {}),
                    metadata={
                        "purpose": "persistent-feedback",
                        "operation": operation,
                        "project_root": str(self.project_root),
                    },
                ) as permit:
                    phases["admission"] = (
                        time.perf_counter() - telemetry["phase_started"]
                    )
                    self.session_queue_wait_seconds += permit.queue_wait_seconds
                    if compile_scope:
                        deadline = time.monotonic() + timeout_seconds
                    if time.monotonic() >= deadline:
                        raise PersistentQuickError(
                            "feedback request expired waiting for Lean admission", code="queue_timeout"
                        )
                    session_touched = True
                    if self.session is None:
                        session = LeanLspSession(
                            self.project_root,
                            self.document_path,
                            self.stderr_path,
                            timeout_seconds,
                            **(
                                {"lean_path_prefixes": self.lean_path_prefixes}
                                if self.lean_path_prefixes
                                else {}
                            ),
                        )
                        self.session = session
                        self.session_started_at = arena.utc_now()
                        self.session_started_perf = time.perf_counter()
                        session.request_deadline = deadline
                        telemetry.update(
                            phase="process_launch", phase_started=time.perf_counter()
                        )
                        try:
                            session.start()
                        finally:
                            startup_seconds = (
                                time.perf_counter() - telemetry["phase_started"]
                            )
                            phases["process_launch"] = (
                                getattr(session, "process_launch_seconds", None) or 0.0
                            )
                            initialization = getattr(
                                session, "initialization_seconds", None
                            )
                            phases["initialization"] = initialization or 0.0
                            if initialization is not None:
                                telemetry["phase"] = "initialization"
                    assert self.session is not None
                    # Every LSP subrequest shares this operation's absolute budget.
                    # Prewarm may exceed the warm cap, but never lends it to a later edit.
                    self.session.timeout_seconds = timeout_seconds
                    self.session.request_deadline = deadline
                    _remaining_seconds(deadline)
                    if reused:
                        diagnostics = self.current_diagnostics
                    else:
                        first_document = self.session.version == 0
                        phase = (
                            "first_document" if first_document else "change_document"
                        )
                        telemetry.update(phase=phase, phase_started=time.perf_counter())
                        try:
                            edit_seconds, diagnostics = (
                                self.session.open_document(source)
                                if first_document
                                else self.session.change_document(source)
                            )
                        finally:
                            phases[phase] = (
                                time.perf_counter() - telemetry["phase_started"]
                            )
                    setup_errors = [
                        item.message
                        for item in diagnostics
                        if is_infrastructure_message(item.message)
                    ]
                    if setup_errors:
                        raise PersistentQuickError(
                            "Lean setup infrastructure failure: "
                            + "\n".join(setup_errors)
                        )
                    self.current_source_sha256 = digest
                    self.current_diagnostics = diagnostics
                    if operation == "goals":
                        assert position is not None
                        _remaining_seconds(deadline)
                        telemetry.update(
                            phase="goals", phase_started=time.perf_counter()
                        )
                        try:
                            raw_goals = self.session.interactive_goals(position)
                        finally:
                            phases["goals"] = (
                                time.perf_counter() - telemetry["phase_started"]
                            )
                    self.session.request_deadline = None
                    self.session.timeout_seconds = self.timeout_seconds
                    self.session_request_count += 1
                    working_set = self.session.tree_working_set_bytes()
                    if working_set is not None:
                        self.session_peak_working_set_bytes = max(
                            self.session_peak_working_set_bytes or 0, working_set
                        )
            except (
                arena.resource_gate.ResourceGateError,
                PersistentQuickError,
                OSError,
                TimeoutError,
            ) as error:
                if session_touched:
                    self.session_error = str(error)
                    self._retire_session("failed")
                code = ("cancelled" if isinstance(error, arena.resource_gate.ResourceGateCancelled)
                        else "queue_timeout" if isinstance(error, arena.resource_gate.ResourceGateTimeout)
                        else "operation_timeout" if isinstance(error, TimeoutError)
                        else getattr(error, "code", "infrastructure_failure"))
                raise PersistentQuickError(str(error), code=code) from error
            errors = [value for value in diagnostics if value.severity == "error"]
            # Prefix success messages can drown out the useful final suggestion/count.
            # Preserve every error/warning, measurement, suggestion and target message.
            essential: list[Diagnostic] = []
            background: list[Diagnostic] = []
            for value in diagnostics:
                if (
                    value.severity not in {"error", "warning"}
                    and value.message.strip() == "Goals accomplished!"
                ):
                    continue
                if (
                    value.severity in {"error", "warning"}
                    or re.search(
                        r"Try (?:this|these):|LRH_HEARTBEATS|Used [0-9]+ heartbeats",
                        value.message,
                    )
                    or (
                        target_start_line is not None
                        and value.line is not None
                        and value.line >= target_start_line
                    )
                ):
                    essential.append(value)
                else:
                    background.append(value)
            ordered = (
                sorted(essential, key=lambda value: value.severity != "error")
                + background[:50]
            )
            assert self.session is not None
            response = {
                "schema_version": 2,
                "ok": True,
                "operation": operation,
                "source_sha256": digest,
                "document_version": self.session.version,
                "reused_source": reused,
                "valid": not errors,
                "lsp_seconds": round(time.perf_counter() - operation_started, 6),
                "startup_seconds": round(startup_seconds, 6),
                "phase_timings": {
                    name: round(value, 6) for name, value in phases.items()
                },
                "elaboration_seconds": round(edit_seconds, 6),
                "queue_wait_seconds": round(permit.queue_wait_seconds, 6),
                "diagnostics": [value.as_json() for value in ordered],
                "diagnostics_truncated": len(background) > 50,
                "diagnostics_omitted": len(diagnostics) - len(ordered),
                "working_set_bytes": working_set,
            }
            if operation == "goals":
                response["goals"] = raw_goals
            if operation == "prewarm":
                response["ready"] = True
            arena.record_event(
                "persistent_feedback",
                {
                    key: value
                    for key, value in response.items()
                    if key not in {"goals", "diagnostics"}
                },
            )
            return response

    def _retire_session(self, status: str) -> None:
        session = self.session
        if session is None:
            return
        process_id = session.process.pid if session.process is not None else None
        peak = session.tree_working_set_bytes()
        if peak is not None:
            self.session_peak_working_set_bytes = max(
                self.session_peak_working_set_bytes or 0, peak
            )
        if status == "failed" and session.process is not None:
            arena.terminate_process_tree(session.process)
        session.close()
        finished_at = arena.utc_now()
        wall_seconds = (
            time.perf_counter() - self.session_started_perf
            if self.session_started_perf is not None
            else 0.0
        )
        arena.record_event(
            "persistent_lean_server",
            {
                "process_id": process_id,
                "status": status,
                "started_at": self.session_started_at,
                "finished_at": finished_at,
                "wall_seconds": round(wall_seconds, 6),
                "queue_wait_seconds": round(self.session_queue_wait_seconds, 6),
                "request_count": self.session_request_count,
                "peak_working_set_bytes": self.session_peak_working_set_bytes,
                "project_root": str(self.project_root),
                "command": ["lake", "serve", "--", "-DstderrAsMessages=false"],
                "error": self.session_error,
            },
        )
        self.session = None
        self.session_started_at = None
        self.session_started_perf = None
        self.session_request_count = 0
        self.current_source_sha256 = None
        self.current_diagnostics = []
        self.session_queue_wait_seconds = 0.0
        self.session_peak_working_set_bytes = None
        self.session_error = None

    def close(self) -> None:
        self.stop_event.set()
        listener = self.listener
        self.listener = None
        if listener is not None:
            listener.close()
        if self.thread is not None:
            self.thread.join(timeout=5)
            self.thread = None
        with self.session_lock:
            self._retire_session("completed")

    def __enter__(self) -> Self:
        self.start()
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()


def quantile_indexes(size: int, count: int) -> list[int]:
    if size < count or count < 1:
        raise PersistentQuickError(
            f"need at least {count} distinct archived candidates, found {size}"
        )
    if count == 1:
        return [0]
    return sorted({round(index * (size - 1) / (count - 1)) for index in range(count)})


def benchmark_variants(task_path: Path, archive: Path) -> list[dict[str, Any]]:
    _, row = arena.load_task(task_path)
    pool_path = archive / "candidate-pool.json"
    pool = json.loads(pool_path.read_text(encoding="utf-8"))
    declarations: dict[str, tuple[str, int]] = {}
    for record in pool:
        if not isinstance(record, dict) or not record.get("valid"):
            continue
        path_value = record.get("candidate_path")
        if not isinstance(path_value, str):
            continue
        candidate_path = archive / Path(path_value)
        declaration, body = arena.extract_candidate_declaration(
            row, candidate_path.read_text(encoding="utf-8")
        )
        digest = arena.sha256_bytes(declaration.encode("utf-8"))
        declarations[digest] = (declaration, arena.candidate_proof_token_count(body))
    ordered = sorted(
        ((digest, *value) for digest, value in declarations.items()),
        key=lambda item: (item[2], item[0]),
    )
    selected = [ordered[index] for index in quantile_indexes(len(ordered), 5)]
    invalid_bodies = [
        "by\n  exact lrhMissingTerm1",
        "by\n  apply lrhMissingTheorem2",
        "by\n  simpa using lrhMissingTerm3",
        "by\n  have h : False := lrhMissingTerm4\n  contradiction",
        "by\n  rw [lrhMissingRewrite5]",
    ]
    variants: list[dict[str, Any]] = []
    for index, (digest, declaration, tokens) in enumerate(selected):
        variants.append(
            {
                "label": f"valid-q{index}",
                "expected_valid": True,
                "declaration": declaration,
                "declaration_sha256": digest,
                "proof_tokens": tokens,
            }
        )
        invalid = row["signature"] + " := " + invalid_bodies[index]
        variants.append(
            {
                "label": f"invalid-{index}",
                "expected_valid": False,
                "declaration": invalid,
                "declaration_sha256": arena.sha256_bytes(invalid.encode("utf-8")),
                "proof_tokens": arena.candidate_proof_token_count(invalid_bodies[index]),
            }
        )
    return variants


def observation_json(
    seconds: float,
    diagnostics: list[Diagnostic],
    *,
    working_set_bytes: int | None = None,
) -> dict[str, Any]:
    errors = [value for value in diagnostics if value.severity == "error"]
    preview = [*errors, *(value for value in diagnostics if value.severity != "error")]
    return {
        "seconds": round(seconds, 6),
        "valid": not errors,
        "error_count": len(errors),
        "diagnostics": [value.as_json() for value in preview[:10]],
        "working_set_bytes": working_set_bytes,
    }


def run_benchmark(
    task_path: Path,
    archive: Path,
    project_root: Path,
    output_path: Path,
    *,
    timeout_seconds: int,
    crash_before_index: int,
) -> dict[str, Any]:
    task_path = task_path.resolve()
    archive = archive.resolve()
    project_root = project_root.resolve()
    _, row = arena.load_task(task_path)
    variants = benchmark_variants(task_path, archive)
    if not 1 <= crash_before_index < len(variants):
        raise PersistentQuickError("crash index must follow the first document version")

    with tempfile.TemporaryDirectory(prefix="lrh-phase3-") as temporary:
        scratch = Path(temporary).resolve()
        document_path = scratch / "ArenaProjectQuick.lean"
        harnesses = [
            arena.project_compile_harness(
                row, value["declaration"], project_root, exact=False
            )
            for value in variants
        ]

        document_path.write_text(harnesses[0], encoding="utf-8")
        run_cold_lean(document_path, project_root, scratch, timeout_seconds)

        cold_results: list[dict[str, Any]] = []
        cold_diagnostics: list[list[Diagnostic]] = []
        for harness in harnesses:
            document_path.write_text(harness, encoding="utf-8")
            result = run_cold_lean(
                document_path, project_root, scratch, timeout_seconds
            )
            diagnostics = cold_json_diagnostics(result.output)
            cold_diagnostics.append(diagnostics)
            value = observation_json(
                result.seconds,
                diagnostics,
                working_set_bytes=result.peak_tree_working_set_bytes,
            )
            value["returncode"] = result.returncode
            value["valid"] = result.returncode == 0
            cold_results.append(value)

        persistent_results: list[dict[str, Any]] = []
        persistent_diagnostics: list[list[Diagnostic]] = []
        recovery: dict[str, Any] = {"attempted": False, "succeeded": False}
        session = LeanLspSession(
            project_root,
            document_path,
            output_path.with_suffix(".lsp-stderr.log"),
            timeout_seconds,
        )
        try:
            session.start()
            for index, harness in enumerate(harnesses):
                document_path.write_text(harness, encoding="utf-8")
                if index == crash_before_index:
                    recovery_started = time.perf_counter()
                    recovery = {
                        "attempted": True,
                        "succeeded": False,
                        "crashed_process": session.crash_file_worker(),
                    }
                    # The watchdog notices the pipe exit asynchronously. Waiting for
                    # that state transition ensures this didChange is the event that
                    # asks it to create a fresh file worker, rather than being sent to
                    # the already-terminated worker.
                    time.sleep(1.5)
                if index == 0:
                    seconds, diagnostics = session.open_document(harness)
                else:
                    seconds, diagnostics = session.change_document(harness)
                if index == crash_before_index:
                    recovery["succeeded"] = True
                    recovery["edit_seconds"] = round(seconds, 6)
                    recovery["total_seconds"] = round(
                        time.perf_counter() - recovery_started, 6
                    )
                persistent_diagnostics.append(diagnostics)
                persistent_results.append(
                    observation_json(
                        seconds,
                        diagnostics,
                        working_set_bytes=session.tree_working_set_bytes(),
                    )
                )
        finally:
            startup_seconds = session.startup_seconds
            session.close()

        cases: list[dict[str, Any]] = []
        for index, variant in enumerate(variants):
            cold = cold_results[index]
            persistent = persistent_results[index]
            equivalent = diagnostics_equivalent(
                cold_diagnostics[index], persistent_diagnostics[index]
            )
            location_equivalent = diagnostic_locations_equivalent(
                cold_diagnostics[index], persistent_diagnostics[index]
            )
            cases.append(
                {
                    **{
                        key: value
                        for key, value in variant.items()
                        if key != "declaration"
                    },
                    "cold": cold,
                    "persistent": persistent,
                    "acceptance_equivalent": cold["valid"] == persistent["valid"],
                    "diagnostics_equivalent": equivalent,
                    "diagnostic_locations_equivalent": location_equivalent,
                    "recovery_edit": index == crash_before_index,
                }
            )

    cold_seconds = [case["cold"]["seconds"] for case in cases]
    warm_seconds = [
        case["persistent"]["seconds"]
        for index, case in enumerate(cases)
        if index not in (0, crash_before_index)
    ]
    cold_median = statistics.median(cold_seconds)
    warm_median = statistics.median(warm_seconds)
    acceptance_equivalent = all(case["acceptance_equivalent"] for case in cases)
    diagnostic_equivalent = all(case["diagnostics_equivalent"] for case in cases)
    all_diagnostic_locations_equivalent = all(
        case["diagnostic_locations_equivalent"] for case in cases
    )
    expected_classification = all(
        case["cold"]["valid"] == case["expected_valid"] for case in cases
    )
    max_memory = max(
        (
            case["persistent"]["working_set_bytes"]
            for case in cases
            if isinstance(case["persistent"]["working_set_bytes"], int)
        ),
        default=None,
    )
    summary = {
        "cold_median_seconds": round(cold_median, 6),
        "persistent_startup_seconds": (
            round(startup_seconds, 6) if startup_seconds is not None else None
        ),
        "persistent_first_document_seconds": cases[0]["persistent"]["seconds"],
        "persistent_warm_median_seconds": round(warm_median, 6),
        "warm_speedup": round(cold_median / warm_median, 3),
        "warm_median_seconds_saved": round(cold_median - warm_median, 6),
        "persistent_max_observed_tree_working_set_bytes": max_memory,
        "acceptance_equivalent": acceptance_equivalent,
        "diagnostics_equivalent": diagnostic_equivalent,
        "diagnostic_locations_equivalent": all_diagnostic_locations_equivalent,
        "expected_classification": expected_classification,
        "recovery": recovery,
    }
    summary["adoption_gate_passed"] = bool(
        acceptance_equivalent
        and diagnostic_equivalent
        and expected_classification
        and recovery.get("succeeded")
        and summary["warm_speedup"] >= 2.0
        and summary["warm_median_seconds_saved"] >= 1.0
    )
    report = {
        "schema_version": 1,
        "recorded_at": arena.utc_now(),
        "task": str(task_path),
        "archive": str(archive),
        "project_root": str(project_root),
        "configuration": {
            "variant_count": len(variants),
            "valid_variants": sum(value["expected_valid"] for value in variants),
            "invalid_variants": sum(not value["expected_valid"] for value in variants),
            "timeout_seconds": timeout_seconds,
            "crash_before_index": crash_before_index,
            "cold_command": [
                "lake",
                "env",
                "lean",
                "--json",
                "-R",
                "<scratch>",
                "<file>",
            ],
            "persistent_command": ["lake", "serve", "--", "-DstderrAsMessages=false"],
        },
        "summary": summary,
        "cases": cases,
    }
    output_path = output_path.resolve()
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Benchmark persistent Lean LSP quick validation against cold Lean"
    )
    parser.add_argument("--task", type=Path, required=True)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--project-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--crash-before-index", type=int, default=5)
    return parser


def main() -> int:
    args = build_parser().parse_args()
    try:
        report = run_benchmark(
            args.task,
            args.archive,
            args.project_root,
            args.output,
            timeout_seconds=args.timeout,
            crash_before_index=args.crash_before_index,
        )
    except (arena.WorkflowError, PersistentQuickError, OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    print(json.dumps(report["summary"], ensure_ascii=False, indent=2))
    print(args.output.resolve())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
