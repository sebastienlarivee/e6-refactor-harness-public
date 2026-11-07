from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import argparse
import datetime as dt
import hashlib
import json
import math
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import urllib.request
import uuid
from collections.abc import Callable
from contextlib import ExitStack, contextmanager
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Any

import tomllib

SCRIPT_ROOT = Path(__file__).resolve().parent
if str(SCRIPT_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPT_ROOT))

from lean_tools import lean_launch
from lean_tools import broker_client
from lean_tools import check_budget
from lean_tools import resource_gate
from lean_tools.process_memory import ProcessTreeMemoryMonitor
from lean_tools.workflow_errors import WorkflowError
from lean_tools.task import load_task, normalize_arena_row
from lean_tools import lean_source
from lean_tools.measurement_policy import (
    ARENA_POLICY, LEGACY_POLICY, candidate_token_offset, resolve_scoring_policy,
    scoring_policy_context,
)
from lean_tools.lean_source import (
    DEFAULT_HEADER,
    TARGET_BEGIN,
    TARGET_END,
    FORBIDDEN_PATTERNS,
    LEAN_TOKEN_PATTERN,
    PROJECT_MEASUREMENT_HELPER,
    local_proof_tokens,
    candidate_proof_token_count,
    ensure_section_gap,
    render_supplied_environment,
    render_environment,
    lean_code_mask,
    normalized_lean_code,
    declaration_short_name,
    theorem_declaration_matches,
    theorem_declaration_match,
    supported_supplied_prefix,
    matching_prefixed_declaration_start,
    exact_signature_assignment_start,
    declaration_assignment_start,
    supplied_assignment_start,
    validate_supplied_declaration,
    canonical_candidate_declaration,
    render_candidate_scaffold,
    metric_label,
    extract_candidate_declaration,
    validate_declaration,
    normalized_signature_example,
    heartbeat_harness,
    exact_heartbeat_audit_harness,
    is_project_resident,
    quick_compile_harness,
    project_source_path,
    project_source_has_module_header,
    project_axiom_target_command,
    project_axiom_audit_harness,
    project_compile_harness,
)
from lean_tools.scoring import contest_score_components, local_selection_score

ARENA_REVISION = "e034972db374b906d0fa9339b9d183bf215b8fae"
ARENA_WARMUP_URL = (
    "https://huggingface.co/spaces/delta-lab-ai/lean-refactor-arena/resolve/"
    f"{ARENA_REVISION}/benchmark_data_warmup.jsonl"
)
ARENA_HEARTBEATS_URL = (
    "https://huggingface.co/spaces/delta-lab-ai/lean-refactor-arena/resolve/"
    f"{ARENA_REVISION}/benchmark_heartbeats.jsonl"
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EVENT_SCHEMA_VERSION = 1
EVALUATION_CACHE_SCHEMA_VERSION = 1
EVALUATOR_CACHE_REVISION = "one-declaration-exact-v2"
FINGERPRINT_REGISTRY_SCHEMA_VERSION = 2
FINGERPRINT_GUARD_SCHEMA_VERSION = 1
PERSISTENT_QUICK_ENDPOINT_ENV = broker_client.ENDPOINT_ENV
PERSISTENT_QUICK_TOKEN_ENV = broker_client.TOKEN_ENV
PERSISTENT_QUICK_PROJECT_ROOT_ENV = broker_client.PROJECT_ROOT_ENV
PERSISTENT_QUICK_MAX_MESSAGE_BYTES = broker_client.MAX_MESSAGE_BYTES
_FILE_LOCKS_GUARD = threading.Lock()
_FILE_LOCKS: dict[str, threading.Lock] = {}

# This is retained as a reusable first-pass filter, not as a frozen copy of the
# competition contract. The live evaluator's list must be checked when the harness is built.


@dataclass(frozen=True)
class LeanRun:
    command: list[str]
    returncode: int
    seconds: float
    output: str
    timed_out: bool = False
    peak_working_set_bytes: int | None = None
    log_path: str | None = None
    queue_wait_seconds: float = 0.0
    # Failure evidence is separate from the complete, unmodified compiler log.
    diagnostics_path: str | None = None
    generated_source_path: str | None = None


class LeanTimeoutError(WorkflowError):
    def __init__(self, message: str, result: LeanRun) -> None:
        super().__init__(message)
        self.result = result


class LeanCompileError(WorkflowError):
    def __init__(self, message: str, result: LeanRun) -> None:
        super().__init__(message)
        self.result = result


class PersistentQuickFailure(WorkflowError):
    """Preserve typed broker failure evidence instead of replaying unknown work."""
    def __init__(self, error: broker_client.BrokerClientError) -> None:
        super().__init__("persistent quick " + str(error))
        self.code, self.result, self.retryable = error.code, error.result, error.retryable


@dataclass(frozen=True)
class Evaluation:
    task_id: str
    candidate_path: str
    valid: bool
    compile_seconds: float
    axiom_audit_seconds: float | None
    axioms: list[str] | None
    original_local_tokens: int
    candidate_local_tokens: int
    local_token_reduction_pct: float
    official_original_tokens: int | None
    published_reference_heartbeat: int | None = None
    local_reference_heartbeat: int | None = None
    environment_fingerprint: str | None = None
    heartbeat: int | None = None
    heartbeat_reduction_pct: float | None = None
    # Per-request provenance is never stored as part of a cached measurement.
    cache_status: str = "unknown"
    cache_source_mode: str | None = None
    request_wall_seconds: float | None = None
    diagnostics_path: str | None = None
    axiom_audit_shares_compile: bool | None = None
    # Full admitted file identity, including comments/markers/newline bytes.
    # This belongs to the request rather than a declaration measurement cache.
    source_sha256: str | None = None
    # Versioned scoring metadata; appended to preserve existing positional APIs.
    scoring_policy: str = LEGACY_POLICY
    candidate_token_offset: int = 0
    original_body_tokens: int | None = None
    reference_heartbeat_source: str | None = None


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def write_json_atomic(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    try:
        for attempt in range(6):
            try:
                temporary.replace(path)
                return
            except PermissionError:
                if attempt == 5:
                    raise
                time.sleep(0.05 * (attempt + 1))
    finally:
        try:
            temporary.unlink(missing_ok=True)
        except OSError:
            pass


def event_spool_path() -> Path | None:
    value = os.environ.get("LEAN_REFACTOR_EVENT_SPOOL")
    return Path(value).resolve() if value else None


def artifact_root_path() -> Path | None:
    value = os.environ.get("LEAN_REFACTOR_ARTIFACT_ROOT")
    return Path(value).resolve() if value else None


def record_event(kind: str, payload: dict[str, Any]) -> str | None:
    spool = event_spool_path()
    if spool is None:
        return None
    event_id = uuid.uuid4().hex
    event = {
        "schema_version": EVENT_SCHEMA_VERSION,
        "event_id": event_id,
        "recorded_at": utc_now(),
        "kind": kind,
        **payload,
    }
    name = f"{time.time_ns():020d}-{os.getpid()}-{event_id}.json"
    write_json_atomic(spool / name, event)
    return event_id


def load_recorded_events(spool: Path) -> list[dict[str, Any]]:
    if not spool.is_dir():
        return []
    events: list[dict[str, Any]] = []
    for path in sorted(spool.glob("*.json")):
        payload = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(payload, dict):
            events.append(payload)
    return sorted(
        events,
        key=lambda item: (str(item.get("recorded_at", "")), str(item.get("event_id", ""))),
    )


def maximum_interval_concurrency(
    events: list[dict[str, Any]], kind: str | set[str]
) -> int:
    kinds = {kind} if isinstance(kind, str) else kind
    points: list[tuple[dt.datetime, int]] = []
    for event in events:
        if event.get("kind") not in kinds:
            continue
        started = event.get("started_at")
        finished = event.get("finished_at")
        if not isinstance(started, str) or not isinstance(finished, str):
            continue
        try:
            points.append((dt.datetime.fromisoformat(started), 1))
            points.append((dt.datetime.fromisoformat(finished), -1))
        except ValueError:
            continue
    current = 0
    maximum = 0
    for _, delta in sorted(points, key=lambda item: (item[0], item[1])):
        current += delta
        maximum = max(maximum, current)
    return maximum


def summarize_recorded_events(events: list[dict[str, Any]]) -> dict[str, Any]:
    counts: dict[str, int] = {}
    for event in events:
        kind = str(event.get("kind", "unknown"))
        counts[kind] = counts.get(kind, 0) + 1
    lean_events = [event for event in events if event.get("kind") == "lean_process"]
    persistent_lean_events = [
        event for event in events if event.get("kind") == "persistent_lean_server"
    ]
    model_events = [event for event in events if event.get("kind") == "model_session"]
    evaluation_events = [
        event for event in events if event.get("kind") == "evaluation"
    ]
    peak_values = [
        event.get("peak_working_set_bytes")
        for event in [*lean_events, *persistent_lean_events, *model_events]
        if isinstance(event.get("peak_working_set_bytes"), int)
    ]
    return {
        "schema_version": 1,
        "event_counts": counts,
        "lean_processes": len(lean_events),
        "persistent_lean_servers": len(persistent_lean_events),
        "model_sessions": len(model_events),
        "peak_lean_concurrency": maximum_interval_concurrency(
            events, {"lean_process", "persistent_lean_server"}
        ),
        "peak_model_concurrency": maximum_interval_concurrency(
            events, "model_session"
        ),
        "peak_process_working_set_bytes": max(peak_values) if peak_values else None,
        "lean_queue_wait_seconds": round(
            sum(
                float(event.get("queue_wait_seconds", 0.0))
                for event in [*lean_events, *persistent_lean_events]
            ),
            3,
        ),
        "model_queue_wait_seconds": round(
            sum(
                float(event.get("queue_wait_seconds", 0.0))
                for event in model_events
            ),
            3,
        ),
        "evaluation_cache_hits": sum(
            1 for event in evaluation_events if event.get("cache_status") == "hit"
        ),
        "evaluation_cache_misses": sum(
            1 for event in evaluation_events if event.get("cache_status") == "miss"
        ),
    }


def materialize_event_log(spool: Path, output: Path) -> dict[str, Any]:
    events = load_recorded_events(spool)
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(f".{output.name}.{uuid.uuid4().hex}.tmp")
    temporary.write_text(
        "".join(json.dumps(event, ensure_ascii=False) + "\n" for event in events),
        encoding="utf-8",
    )
    temporary.replace(output)
    return summarize_recorded_events(events)


def process_peak_working_set_bytes(process: subprocess.Popen[str]) -> int | None:
    if os.name != "nt":
        return None
    try:
        import ctypes
        from ctypes import wintypes

        class ProcessMemoryCounters(ctypes.Structure):
            _fields_ = [
                ("cb", wintypes.DWORD),
                ("PageFaultCount", wintypes.DWORD),
                ("PeakWorkingSetSize", ctypes.c_size_t),
                ("WorkingSetSize", ctypes.c_size_t),
                ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
                ("QuotaPagedPoolUsage", ctypes.c_size_t),
                ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
                ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                ("PagefileUsage", ctypes.c_size_t),
                ("PeakPagefileUsage", ctypes.c_size_t),
            ]

        counters = ProcessMemoryCounters()
        counters.cb = ctypes.sizeof(counters)
        handle = getattr(process, "_handle", None)
        if handle is None:
            return None
        succeeded = ctypes.windll.psapi.GetProcessMemoryInfo(
            wintypes.HANDLE(int(handle)),
            ctypes.byref(counters),
            counters.cb,
        )
        return int(counters.PeakWorkingSetSize) if succeeded else None
    except (AttributeError, OSError, TypeError, ValueError):
        return None


def task_document(
    raw_row: dict[str, Any], source_url: str, reference_heartbeat: int | None = None
) -> dict[str, Any]:
    row = normalize_arena_row(raw_row)
    return {
        "schema_version": 1,
        "retrieved_at": utc_now(),
        "source": {
            "arena_revision": ARENA_REVISION,
            "url": source_url,
            "row_sha256": sha256_bytes(
                json.dumps(raw_row, ensure_ascii=False, sort_keys=True).encode("utf-8")
            ),
        },
        "reference": {"heartbeat": reference_heartbeat},
        "row": row,
    }


def fetch_warmup_task(name: str, output: Path) -> dict[str, Any]:
    def fetch_lines(url: str) -> list[str]:
        request = urllib.request.Request(
            url, headers={"User-Agent": "lean-refactor-harness/0.1"}
        )
        with urllib.request.urlopen(request, timeout=30) as response:
            return response.read().decode("utf-8").splitlines()

    lines = fetch_lines(ARENA_WARMUP_URL)
    matches = [json.loads(line) for line in lines if line.strip()]
    matches = [row for row in matches if row.get("name") == name]
    if len(matches) != 1:
        raise WorkflowError(
            f"expected one warm-up row named {name!r}, found {len(matches)}"
        )
    heartbeat_rows = [
        json.loads(line) for line in fetch_lines(ARENA_HEARTBEATS_URL) if line.strip()
    ]
    heartbeats = [
        row.get("heartbeat") for row in heartbeat_rows if row.get("name") == name
    ]
    if len(heartbeats) != 1 or not isinstance(heartbeats[0], int):
        raise WorkflowError(f"expected one reference heartbeat for {name!r}")
    document = task_document(matches[0], ARENA_WARMUP_URL, heartbeats[0])
    document["source"]["heartbeat_url"] = ARENA_HEARTBEATS_URL
    if output.exists():
        previous = json.loads(output.read_text(encoding="utf-8"))
        if (
            isinstance(previous, dict)
            and previous.get("source", {}).get("row_sha256")
            == document["source"]["row_sha256"]
            and isinstance(previous.get("local_baselines"), list)
        ):
            document["local_baselines"] = previous["local_baselines"]
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        json.dumps(document, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    return document


def terminate_process_tree(process: subprocess.Popen[str]) -> None:
    # Descendants can hold inherited pipes after the leader exits. Always address
    # the owned tree, with finite taskkill and leader-kill fallback.
    lean_launch._terminate(process)


def lean_timeout_scope() -> str:
    if check_budget.current() is not None:
        return "request"
    scope = os.environ.get("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE", "request")
    if scope not in {"request", "compile"}:
        raise WorkflowError("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE must be request or compile")
    return scope


def lean_command_path(path: Path, project_root: Path) -> str:
    try:
        return str(path.resolve().relative_to(project_root.resolve()))
    except ValueError:
        return str(path.resolve())


def run_lean(
    path: Path,
    project_root: Path,
    timeout_seconds: int,
    *,
    lean_args: list[str] | None = None,
    lean_path_prefixes: list[Path] | None = None,
) -> LeanRun:
    """Run Lean with a request deadline or an opt-in compilation-only watchdog."""
    if isinstance(timeout_seconds, bool) or not math.isfinite(timeout_seconds) or timeout_seconds <= 0:
        raise WorkflowError("Lean timeout must be finite and positive")
    check_budget.stage("cold_admission")
    timeout_seconds = check_budget.remaining(timeout_seconds)
    timeout_scope = lean_timeout_scope()
    command = [
        "lake",
        "env",
        "lean",
        *(lean_args or []),
        lean_command_path(path, project_root),
    ]
    environment = os.environ.copy()
    launch_cache_enabled = bool(environment.get(lean_launch.CACHE_ENV))
    launch_provenance: dict[str, Any] | None = None
    if lean_path_prefixes and not launch_cache_enabled:
        paths = [str(path.resolve()) for path in lean_path_prefixes]
        existing = environment.get("LEAN_PATH")
        if existing:
            paths.append(existing)
        environment["LEAN_PATH"] = os.pathsep.join(paths)
    creationflags = subprocess.CREATE_NEW_PROCESS_GROUP if os.name == "nt" else 0
    try:
        priority = int(os.environ.get("LEAN_REFACTOR_LEAN_PRIORITY", "10"))
    except ValueError as error:
        raise WorkflowError("LEAN_REFACTOR_LEAN_PRIORITY must be an integer") from error
    request_started = time.perf_counter()
    deadline = request_started + timeout_seconds if timeout_scope == "request" else None
    def admission_budget() -> float | None:
        return max(0.0, deadline - time.perf_counter()) if deadline is not None else None
    queued_at = utc_now()
    admitted_at: str | None = None
    try:
        with ExitStack() as permits:
            metadata = {
                "project_root": str(project_root.resolve()),
                "source": str(path.resolve()),
            }
            cold_permit = None
            if (
                environment.get("LEAN_REFACTOR_COLD_LEAN_GATE")
                or environment.get("LEAN_REFACTOR_COLD_LEAN_CAPACITY")
            ):
                cold_permit = permits.enter_context(resource_gate.permit_from_environment(
                    "cold_lean", priority=priority,
                    timeout_seconds=admission_budget(),
                    metadata=metadata,
                ))
                queued_at = cold_permit.queued_at
            permit = permits.enter_context(resource_gate.permit_from_environment(
                "lean", priority=priority,
                timeout_seconds=admission_budget(),
                metadata=metadata,
            ))
            if cold_permit is None:
                queued_at = permit.queued_at
            admitted_at = permit.admitted_at
            queue_wait_seconds = permit.queue_wait_seconds + (
                cold_permit.queue_wait_seconds if cold_permit is not None else 0.0
            )
            if deadline is not None and time.perf_counter() >= deadline:
                raise resource_gate.ResourceGateError(
                    "Lean deadline expired during admission"
                )
            start = time.perf_counter()
            started_at = utc_now()
            check_budget.stage("cold_compile")
            try:
                if launch_cache_enabled:
                    launch = lean_launch.prepare_launch(
                        project_root, deadline=deadline, environment=environment,
                        **({"export_timeout_seconds": timeout_seconds} if deadline is None else {}),
                        record_event=record_event,
                    )
                    environment = launch.environment
                    lean_launch.add_lean_path_prefixes(environment, os.environ, lean_path_prefixes or [])
                    launch_provenance = launch.provenance
                    command = [launch.executable, *(lean_args or []), lean_command_path(path, project_root)]
                    if deadline is not None and time.perf_counter() >= deadline:
                        raise lean_launch.LaunchCacheError("Lean launch preparation deadline expired")
                command = lean_launch.native_command(command)
                environment = lean_launch.native_environment(environment)
                process = subprocess.Popen(
                    command,
                    cwd=project_root,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    encoding="utf-8",
                    errors="replace",
                    env=environment,
                    creationflags=creationflags,
                    start_new_session=os.name != "nt",
                )
                lean_launch.process_memory.capture_process_identity(process)
                if deadline is None:
                    deadline = time.perf_counter() + timeout_seconds
            except (OSError, lean_launch.LaunchCacheError) as error:
                finished_at = utc_now()
                record_event(
                    "lean_process",
                    {
                        "status": "launch_failed",
                        "queued_at": queued_at,
                        "admitted_at": admitted_at,
                        "started_at": started_at,
                        "finished_at": finished_at,
                        "queue_wait_seconds": round(queue_wait_seconds, 6),
                        "wall_seconds": round(time.perf_counter() - start, 6),
                        "total_wall_seconds": round(time.perf_counter() - request_started, 6),
                        "timeout_seconds": timeout_seconds,
                        "timeout_scope": timeout_scope,
                        "project_root": str(project_root.resolve()),
                        "command": command,
                        "launch_cache": launch_provenance,
                        "error": str(error),
                    },
                )
                if isinstance(error, lean_launch.LaunchCacheError):
                    raise WorkflowError(f"Lean launch preparation failed: {error}") from error
                raise
            timed_out = False
            with ProcessTreeMemoryMonitor(process.pid) as memory:
                try:
                    output, _ = process.communicate(
                        timeout=max(0.0, deadline - time.perf_counter())
                    )
                except subprocess.TimeoutExpired as error:
                    timed_out = True
                    terminate_process_tree(process)
                    output, _ = lean_launch.drain_process(process, error)
            seconds = time.perf_counter() - start
            finished_at = utc_now()
            total_seconds = time.perf_counter() - request_started
            launcher_peak_memory = process_peak_working_set_bytes(process)
            peak_memory = memory.peak_bytes
    except resource_gate.ResourceGateError as error:
        elapsed = time.perf_counter() - request_started
        record_event(
            "lean_process",
            {
                "status": "admission_failed",
                "queued_at": queued_at,
                "admitted_at": admitted_at,
                "started_at": None,
                "finished_at": utc_now(),
                "queue_wait_seconds": round(elapsed, 6),
                "wall_seconds": 0.0,
                "total_wall_seconds": round(elapsed, 6),
                "timeout_seconds": timeout_seconds,
                "timeout_scope": timeout_scope,
                "project_root": str(project_root.resolve()),
                "command": command,
                "error": str(error),
            },
        )
        if check_budget.current() is not None and isinstance(error, resource_gate.ResourceGateTimeout):
            raise check_budget.DeadlineExpired("cold_admission") from error
        raise WorkflowError(f"Lean admission failed: {error}") from error
    event_id = uuid.uuid4().hex
    log_path: Path | None = None
    artifact_root = artifact_root_path()
    if artifact_root is not None:
        log_path = artifact_root / "lean-logs" / f"{event_id}.log"
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text(output, encoding="utf-8")
    record_event(
        "lean_process",
        {
            "process_id": process.pid,
            "status": (
                "timed_out"
                if timed_out
                else "completed" if process.returncode == 0 else "failed"
            ),
            "queued_at": queued_at,
            "admitted_at": admitted_at,
            "started_at": started_at,
            "finished_at": finished_at,
            "queue_wait_seconds": round(queue_wait_seconds, 6),
            "wall_seconds": round(seconds, 6),
            "total_wall_seconds": round(total_seconds, 6),
            "timeout_seconds": timeout_seconds,
            "timeout_scope": timeout_scope,
            "peak_working_set_bytes": peak_memory,
            "launcher_peak_working_set_bytes": launcher_peak_memory,
            "memory_measurement": memory.metadata(),
            "project_root": str(project_root.resolve()),
            "command": command,
            "launch_cache": launch_provenance,
            "returncode": process.returncode,
            "timed_out": timed_out,
            "log_path": (
                str(log_path.relative_to(artifact_root).as_posix())
                if log_path is not None and artifact_root is not None
                else None
            ),
            "lean_event_id": event_id,
        },
    )
    return LeanRun(
        command,
        process.returncode if process.returncode is not None else -1,
        seconds,
        output,
        timed_out=timed_out,
        peak_working_set_bytes=peak_memory,
        log_path=str(log_path) if log_path is not None else None,
        queue_wait_seconds=queue_wait_seconds,
    )


def lean_error_context(output: str) -> str:
    """Prefer the first compiler error and its following context to warning noise."""
    match = re.search(
        r"(?mi)^(?:.*?:\d+:\d+:\s*)?error(?:\([^\n)]+\))?:", output
    )
    if match is None:
        match = re.search(r"(?mi)^[ \t]*type mismatch\b", output)
    return output[match.start():] if match is not None else output


def compact_lean_diagnostic(output: str, limit: int = 12_000) -> str:
    text = output.rstrip()
    if len(text) <= limit:
        return text
    relevant = lean_error_context(text)
    if len(relevant) <= limit:
        return relevant
    head = max(1, (limit * 2) // 3)
    tail = max(1, limit - head)
    return (
        relevant[:head].rstrip()
        + "\n\n... diagnostic truncated; full output is archived ...\n\n"
        + relevant[-tail:].lstrip()
    )


def persistent_quick_matches_project(project_root: Path) -> bool:
    values = {
        "endpoint": os.environ.get(PERSISTENT_QUICK_ENDPOINT_ENV),
        "token": os.environ.get(PERSISTENT_QUICK_TOKEN_ENV),
        "project_root": os.environ.get(PERSISTENT_QUICK_PROJECT_ROOT_ENV),
    }
    if not any(values.values()):
        return False
    if not all(values.values()):
        raise WorkflowError("persistent quick broker environment is incomplete")
    assert values["project_root"] is not None
    expected = os.path.normcase(str(Path(values["project_root"]).resolve()))
    actual = os.path.normcase(str(project_root.resolve()))
    return expected == actual


def persistent_quick_request(
    source_text: str, timeout_seconds: float
) -> dict[str, Any]:
    endpoint = os.environ.get(PERSISTENT_QUICK_ENDPOINT_ENV)
    token = os.environ.get(PERSISTENT_QUICK_TOKEN_ENV)
    if endpoint is None or token is None:
        raise WorkflowError("persistent quick broker is not configured")
    return persistent_quick_request_to(
        endpoint, token, source_text, timeout_seconds
    )


def persistent_quick_request_to(
    endpoint: str,
    token: str,
    source_text: str,
    timeout_seconds: float,
) -> dict[str, Any]:
    """Compatibility facade over the shared source-bound broker client."""
    try:
        return broker_client.request_to(
            endpoint,
            token,
            broker_client.SourceRequest(source_text, timeout_seconds),
            timeout_scope=lean_timeout_scope(),
        )
    except broker_client.BrokerClientError as error:
        raise PersistentQuickFailure(error) from error


def persistent_quick_diagnostic_text(
    response: dict[str, Any],
    *,
    candidate_text: str | None = None,
    generated_source: str | None = None,
    declaration: str | None = None,
) -> str:
    from lean_tools import diagnostic_presentation as presentation
    source_map = None
    if candidate_text is not None and generated_source is not None and declaration is not None:
        source_map = presentation.SourceMap.for_declaration(
            candidate_text, generated_source, declaration
        )
    shown = presentation.present_diagnostics(
        response["diagnostics"], source_map, source=generated_source
    )
    text = presentation.diagnostic_text(shown["diagnostics"])
    if response.get("diagnostics_truncated"):
        text += "\nadditional service diagnostics omitted"
    return text


def compiler_text_diagnostics(
    output: str, source_path: Path, *, source_argument: str | None = None,
) -> list[dict[str, Any]]:
    """Read ordinary Lean CLI locations without changing the measured invocation.

    CLI positions use one-based lines and zero-based Unicode columns. Only
    positions attributed to this exact generated file may map to its candidate.
    Other files and unlocated messages retain their header in the message.
    """
    headers = list(re.finditer(
        r"(?m)^(?:(?P<file>[^\r\n]+?):(?P<line>\d+):(?P<column>\d+):\s*)?"
        r"(?P<severity>error|warning|information|info)(?:\([^\r\n)]+\))?:[ \t]*",
        output,
    ))
    diagnostics = []
    for index, match in enumerate(headers):
        end = headers[index + 1].start() if index + 1 < len(headers) else len(output)
        item: dict[str, Any] = {
            "severity": "information" if match["severity"] == "info" else match["severity"],
            "message": output[match.end():end].rstrip(),
        }
        filename = match["file"]
        if filename and (
            (Path(filename).is_absolute() and Path(filename).resolve() == source_path.resolve())
            or filename == source_argument
        ):
            item.update(line=int(match["line"]) - 1, character=int(match["column"]))
        elif filename:
            # A basename is not sufficient evidence of source identity.
            item["message"] = output[match.start():end].rstrip()
        diagnostics.append(item)
    if not diagnostics and output.strip():
        diagnostics.append({"severity": "error", "message": output.rstrip()})
    return diagnostics


def archive_failed_lean_run(
    result: LeanRun, source_path: Path, *, candidate_path: Path | None = None,
    candidate_bytes: bytes | None = None, declaration: str | None = None,
) -> tuple[LeanRun, str]:
    """Preserve just failed generated source and diagnostics before scratch cleanup."""
    from lean_tools import diagnostic_presentation as presentation

    source_bytes = source_path.read_bytes()
    source = source_bytes.decode("utf-8")
    source_map = None
    if candidate_bytes is not None and declaration is not None:
        try:
            source_map = presentation.SourceMap.for_declaration(
                lean_source.candidate_text_from_bytes(candidate_bytes), source, declaration
            )
        except presentation.PositionError:
            # Audit/helper files need durable generated locations, not guessed mappings.
            pass
    raw = compiler_text_diagnostics(
        result.output, source_path,
        source_argument=result.command[-1] if result.command else None,
    )
    shown = presentation.present_diagnostics(
        raw, source_map, source=source, position_encoding="unicode"
    )
    root = presentation.artifact_directory(candidate_path)
    root.mkdir(parents=True, exist_ok=True)
    source_digest = sha256_bytes(source_bytes)
    archived_source = root / f"{source_digest}.lean"
    if not archived_source.exists():
        descriptor, temporary = tempfile.mkstemp(prefix="source-", suffix=".lean", dir=root)
        try:
            with os.fdopen(descriptor, "wb") as stream:
                stream.write(source_bytes)
            os.replace(temporary, archived_source)
        finally:
            Path(temporary).unlink(missing_ok=True)
    if sha256_file(archived_source) != source_digest:
        raise ValueError("archived generated source hash mismatch")
    payload = {
        "schema_version": 1,
        "generated_source_path": str(archived_source.resolve()),
        "generated_source_sha256": source_digest,
        "original_generated_source_path": str(source_path.resolve()),
        "candidate": str(candidate_path.resolve()) if candidate_path else None,
        "candidate_source_sha256": sha256_bytes(candidate_bytes) if candidate_bytes is not None else None,
        "position_encoding": "unicode",
        "compiler_log_path": result.log_path,
        "raw_diagnostics": raw,
        **shown,
    }
    encoded = json.dumps(payload, ensure_ascii=False, sort_keys=True).encode("utf-8")
    diagnostics_path = root / f"{source_digest}-{sha256_bytes(encoded)}.json"
    if not diagnostics_path.exists():
        write_json_atomic(diagnostics_path, payload)
    return replace(
        result, diagnostics_path=str(diagnostics_path.resolve()),
        generated_source_path=str(archived_source.resolve()),
    ), presentation.diagnostic_text(shown["diagnostics"])


def require_lean_success(
    result: LeanRun, label: str, *, source_path: Path | None = None,
    candidate_path: Path | None = None, candidate_bytes: bytes | None = None,
    declaration: str | None = None,
) -> None:
    detail = None
    if (result.timed_out or result.returncode != 0) and source_path is not None:
        try:
            result, detail = archive_failed_lean_run(
                result, source_path, candidate_path=candidate_path,
                candidate_bytes=candidate_bytes, declaration=declaration,
            )
        except (OSError, ValueError, TypeError) as error:
            # Presentation failure must neither retry Lean nor change its verdict.
            try:
                record_event("diagnostic_archive_failed", {"source": str(source_path), "error": str(error)})
            except (OSError, ValueError, TypeError):
                pass
    source_note = f"\ngenerated Lean source: {result.generated_source_path}" if result.generated_source_path else ""
    if result.timed_out:
        raise LeanTimeoutError(
            f"{label} exceeded {result.seconds:.1f} seconds{source_note}", result
        )
    if result.returncode != 0:
        detail = compact_lean_diagnostic(detail if detail else result.output)
        log_note = f"\nfull Lean log: {result.log_path}" if result.log_path else ""
        raise LeanCompileError(
            f"{label} failed with exit {result.returncode}\n{detail}{source_note}{log_note}", result
        )


def parse_and_validate_axioms(task_id: str, output: str) -> list[str]:
    if "sorryAx" in output:
        raise WorkflowError(f"{task_id}: axiom audit contains sorryAx")
    match = re.search(
        rf"'{re.escape(task_id)}' depends on axioms:\s*\[(.*?)\]",
        output,
        re.DOTALL,
    )
    if match is not None:
        axioms = [item.strip() for item in match.group(1).split(",") if item.strip()]
    elif f"'{task_id}' does not depend on any axioms" in output:
        axioms = []
    else:
        raise WorkflowError(f"{task_id}: could not parse #print axioms output")
    unexpected = sorted(set(axioms) - ALLOWED_AXIOMS)
    if unexpected:
        raise WorkflowError(f"{task_id}: unexpected axiom dependencies: {unexpected}")
    return axioms


def read_submission(path: Path, expected_name: str) -> dict[str, str]:
    physical_lines = path.read_text(encoding="utf-8").splitlines()
    if len(physical_lines) != 1:
        raise WorkflowError(f"{path}: expected exactly one physical JSONL line")
    payload = json.loads(physical_lines[0])
    if not isinstance(payload, dict) or list(payload) != ["name", "proof"]:
        raise WorkflowError(f"{path}: keys must be exactly name,proof in that order")
    if payload["name"] != expected_name or not isinstance(payload["proof"], str):
        raise WorkflowError(f"{path}: name/proof schema mismatch")
    return payload


HEARTBEAT_OUTPUT_PATTERN = re.compile(
    r"Used ([0-9]+) heartbeats, which is (?:less|greater) than "
    r"the current maximum of [0-9]+\."
)
PROJECT_HEARTBEAT_OUTPUT_PATTERN = re.compile(r"LRH_HEARTBEATS ([0-9]+)")


def parse_project_axiom_target(name: str, output: str) -> str:
    targets = re.findall(r"(?m)^LRH_AUDIT_TARGET ([^\r\n]+)\r?$", output)
    permitted = {name, f"_private.ArenaProjectMeasured.0.{name}"}
    if len(targets) != 1 or targets[0] not in permitted:
        raise WorkflowError(f"{name}: expected one source-bound project axiom target, found {targets}")
    return targets[0]


def parse_exact_heartbeat_count(output: str) -> int:
    counts = [int(match) for match in HEARTBEAT_OUTPUT_PATTERN.findall(output)]
    if len(counts) != 1 or counts[0] <= 0:
        raise WorkflowError(
            f"expected exactly one positive #count_heartbeats result, found {counts}"
        )
    return counts[0]


def parse_project_heartbeat_count(output: str) -> int:
    counts = [int(match) for match in PROJECT_HEARTBEAT_OUTPUT_PATTERN.findall(output)]
    if len(counts) != 1 or counts[0] <= 0:
        raise WorkflowError(
            f"expected exactly one positive LRH_HEARTBEATS result, found {counts}"
        )
    return counts[0]


def evaluation_scratch_parent() -> Path:
    """Return a short, shared parent for ephemeral evaluator projects.

    Candidate archives can be deeply nested and include long theorem names. Creating
    temporary Lean projects beside them can exceed the legacy Windows path limit even
    when both the candidate and staged project are otherwise valid.
    """
    configured = os.environ.get("LEAN_REFACTOR_SCRATCH_ROOT")
    parent = Path(configured) if configured else Path(tempfile.gettempdir()) / "lrh"
    parent.mkdir(parents=True, exist_ok=True)
    return parent.resolve()


def temporary_evaluation_directory(prefix: str) -> tempfile.TemporaryDirectory[str]:
    return tempfile.TemporaryDirectory(prefix=prefix, dir=evaluation_scratch_parent())


def evaluation_cache_root() -> Path | None:
    value = os.environ.get("LEAN_REFACTOR_EVALUATION_CACHE")
    return Path(value).resolve() if value else None


def process_is_running(process_id: int) -> bool:
    if process_id <= 0:
        return False
    if process_id == os.getpid():
        return True
    if os.name == "nt":
        try:
            import ctypes
            from ctypes import wintypes

            process_query_limited_information = 0x1000
            still_active = 259
            kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
            kernel32.OpenProcess.argtypes = [
                wintypes.DWORD,
                wintypes.BOOL,
                wintypes.DWORD,
            ]
            kernel32.OpenProcess.restype = wintypes.HANDLE
            kernel32.GetExitCodeProcess.argtypes = [
                wintypes.HANDLE,
                ctypes.POINTER(wintypes.DWORD),
            ]
            kernel32.GetExitCodeProcess.restype = wintypes.BOOL
            kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
            kernel32.CloseHandle.restype = wintypes.BOOL
            handle = kernel32.OpenProcess(
                process_query_limited_information, False, process_id
            )
            if not handle:
                return ctypes.get_last_error() == 5  # access denied implies it exists
            try:
                exit_code = wintypes.DWORD()
                return bool(
                    kernel32.GetExitCodeProcess(handle, ctypes.byref(exit_code))
                ) and exit_code.value == still_active
            finally:
                kernel32.CloseHandle(handle)
        except (AttributeError, OSError, TypeError, ValueError):
            return False
    try:
        os.kill(process_id, 0)
        return True
    except PermissionError:
        return True
    except OSError:
        return False


class CacheLockTimeout(WorkflowError):
    """An evaluation was not attempted because its cache lock was unavailable."""

    def __init__(self, path: Path, phase: str, wait_seconds: float) -> None:
        self.phase = phase
        self.wait_seconds = wait_seconds
        qualifier = "local " if phase == "local" else ""
        super().__init__(f"timed out waiting for {qualifier}cache lock: {path}")


@contextmanager
def exclusive_file_lock(
    path: Path,
    timeout_seconds: float | None,
    *,
    request: dict[str, Any] | None = None,
    wait_metadata: dict[str, Any] | None = None,
) -> Any:
    timeout_seconds = check_budget.remaining(timeout_seconds)
    path.parent.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    deadline = started + max(0.0, timeout_seconds) if timeout_seconds is not None else None
    metadata = wait_metadata if wait_metadata is not None else {}
    request_id = uuid.uuid4().hex
    metadata.update(
        request_id=request_id, waiter_pid=os.getpid(), status="waiting_local"
    )

    def inspect_owner() -> None:
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            payload = None
        payload = payload if isinstance(payload, dict) else {}
        owner = payload.get("pid")
        metadata["owner_pid"] = owner if isinstance(owner, int) else None
        metadata["owner_request_id"] = payload.get("request_id")
        metadata["owner_request"] = payload.get("request")

    def timed_out(phase: str) -> None:
        waited = time.perf_counter() - started
        metadata.update(status="timeout", phase=phase, wait_seconds=waited)
        raise CacheLockTimeout(path, phase, waited)

    resolved_key = str(path.resolve())
    with _FILE_LOCKS_GUARD:
        local_lock = _FILE_LOCKS.setdefault(resolved_key, threading.Lock())
    acquired = (local_lock.acquire() if deadline is None else
                local_lock.acquire(timeout=max(0.0, deadline - time.perf_counter())))
    if not acquired:
        inspect_owner()
        timed_out("local")
    descriptor: int | None = None
    owned_identity: tuple[int, int] | None = None
    active_error: BaseException | None = None
    try:
        metadata["status"] = "waiting_file"
        while descriptor is None:
            if deadline is not None and timeout_seconds > 0 and time.perf_counter() >= deadline:
                inspect_owner()
                timed_out("file")
            try:
                descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
                identity = os.fstat(descriptor)
                owned_identity = (identity.st_dev, identity.st_ino)
                os.write(
                    descriptor,
                    json.dumps(
                        {
                            "pid": os.getpid(),
                            "created_at": utc_now(),
                            "request_id": request_id,
                            "request": request,
                        }
                    ).encode("utf-8"),
                )
            except FileExistsError:
                inspect_owner()
                owner = metadata["owner_pid"]
                remaining = deadline - time.perf_counter() if deadline is not None else None
                if remaining is not None and remaining <= 0:
                    timed_out("file")
                if owner == os.getpid() or (
                    owner is not None and not process_is_running(owner)
                ):
                    try:
                        path.unlink()
                    except FileNotFoundError:
                        pass
                    continue
                if owner is None:
                    try:
                        age = time.time() - path.stat().st_mtime
                    except OSError:
                        age = 0.0
                    if age >= 2.0:
                        try:
                            path.unlink()
                        except FileNotFoundError:
                            pass
                        continue
                remaining = deadline - time.perf_counter() if deadline is not None else None
                if remaining is not None and remaining <= 0:
                    timed_out("file")
                time.sleep(min(0.05, remaining) if remaining is not None else 0.05)
        waited = time.perf_counter() - started
        metadata.update(status="acquired", wait_seconds=waited)
        yield waited
    except BaseException as error:
        active_error = error
        if metadata["status"] in {"waiting_local", "waiting_file"}:
            metadata.update(
                status="failed", wait_seconds=time.perf_counter() - started
            )
        raise
    finally:
        try:
            if descriptor is not None:
                os.close(descriptor)
                # Only the creator may remove this file, and never a replacement.
                try:
                    current = path.stat()
                    if (current.st_dev, current.st_ino) == owned_identity:
                        path.unlink()
                except FileNotFoundError:
                    pass
        except OSError as cleanup_error:
            if active_error is None:
                raise
            active_error.add_note(f"cache lock cleanup also failed: {cleanup_error}")
        finally:
            local_lock.release()


def evaluation_cache_key(
    task_path: Path,
    row: dict[str, Any],
    declaration: str,
    environment_fingerprint: str,
    mode: str,
    scoring_policy: str | None = None,
) -> str:
    policy = resolve_scoring_policy(scoring_policy)
    material = {
        "scoring_policy": policy,
        "candidate_token_offset": candidate_token_offset(policy),
        "schema_version": EVALUATION_CACHE_SCHEMA_VERSION,
        "evaluator_revision": EVALUATOR_CACHE_REVISION,
        "mode": mode,
        "task_id": row["name"],
        "task_sha256": sha256_file(task_path),
        "declaration_sha256": sha256_bytes(declaration.encode("utf-8")),
        "environment_fingerprint": environment_fingerprint,
    }
    return sha256_bytes(
        json.dumps(material, sort_keys=True, separators=(",", ":")).encode("utf-8")
    )


def evaluation_cache_path(root: Path, mode: str, key: str) -> Path:
    return root / "evaluations" / mode / key[:2] / f"{key}.json"


def cached_evaluation(
    path: Path, candidate_path: Path, *, quick_view: bool = False,
    scoring_policy: str | None = None,
) -> Evaluation | None:
    policy = resolve_scoring_policy(scoring_policy)
    if not path.is_file():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        if (
            not isinstance(payload, dict)
            or payload.get("schema_version") != EVALUATION_CACHE_SCHEMA_VERSION
            or payload.get("key") != path.stem
            or payload.get("evaluator_revision") != EVALUATOR_CACHE_REVISION
            or not isinstance(payload.get("evaluation"), dict)
        ):
            return None
        fields = dict(payload["evaluation"])
        fields["candidate_path"] = str(candidate_path.resolve())
        fields.update(
            cache_status="hit",
            cache_source_mode=payload.get("mode"),
            request_wall_seconds=None,
            source_sha256=None,
        )
        evaluation = Evaluation(**fields)
        if (
            evaluation.scoring_policy != policy
            or evaluation.candidate_token_offset != candidate_token_offset(policy)
            or payload.get("scoring_policy", LEGACY_POLICY) != policy
            or payload.get("candidate_token_offset", 0) != candidate_token_offset(policy)
        ):
            return None
        if evaluation.valid is not True:
            return None
        # Older cached quick results may refer to an already removed snapshot.
        # Keep the valid measurement without advertising an absent artifact.
        if evaluation.diagnostics_path and not Path(evaluation.diagnostics_path).is_file():
            evaluation = replace(evaluation, diagnostics_path=None)
        if quick_view:
            evaluation = replace(
                evaluation,
                axiom_audit_seconds=None,
                axioms=None,
                heartbeat=None,
                heartbeat_reduction_pct=None,
                axiom_audit_shares_compile=None,
            )
        return evaluation
    except (OSError, TypeError, ValueError, json.JSONDecodeError):
        return None


def store_cached_evaluation(
    path: Path,
    key: str,
    mode: str,
    environment_fingerprint: str,
    declaration_sha256: str,
    evaluation: Evaluation,
) -> None:
    fields = asdict(evaluation)
    for name in ("cache_status", "cache_source_mode", "request_wall_seconds", "source_sha256"):
        fields.pop(name, None)
    fields["candidate_path"] = "<content-addressed candidate>"
    write_json_atomic(
        path,
        {
            "schema_version": EVALUATION_CACHE_SCHEMA_VERSION,
            "evaluator_revision": EVALUATOR_CACHE_REVISION,
            "scoring_policy": evaluation.scoring_policy,
            "candidate_token_offset": evaluation.candidate_token_offset,
            "key": key,
            "mode": mode,
            "environment_fingerprint": environment_fingerprint,
            "declaration_sha256": declaration_sha256,
            "created_at": utc_now(),
            "evaluation": fields,
        },
    )


def project_measurement_helper_lean_args(project_root: Path) -> list[str]:
    """Propagate the one project option needed to compile the module helper."""
    lakefile = project_root.resolve() / "lakefile.toml"
    if not lakefile.is_file():
        return []
    try:
        payload = tomllib.loads(lakefile.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError):
        return []
    lean_options = payload.get("leanOptions")
    if not isinstance(lean_options, dict):
        return []
    experimental = lean_options.get("experimental")
    if not isinstance(experimental, dict) or experimental.get("module") is not True:
        return []
    return ["-D", "experimental.module=true"]


def measurement_helper_cache_key(
    environment_fingerprint: str, lean_args: list[str] | None = None
) -> str:
    payload: dict[str, Any] = {
        "schema_version": 1,
        "environment_fingerprint": environment_fingerprint,
        "source_sha256": sha256_bytes(PROJECT_MEASUREMENT_HELPER.encode("utf-8")),
    }
    if lean_args:
        payload["lean_args"] = lean_args
    return sha256_bytes(
        json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    )


def measurement_helper_compile_args(lean_args: list[str] | None = None) -> list[str]:
    """The helper itself uses `module`; enable it only for the helper build.

    Keep project_measurement_helper_lean_args unchanged: it participates in the
    historical measurement fingerprint and in the target's frozen environment.
    """
    values = list(lean_args or [])
    if not any("experimental.module=" in value for value in values):
        values[:0] = ["-D", "experimental.module=true"]
    return values


def shared_measurement_helper_guard(project_root: Path) -> dict[str, Any] | None:
    """Cheap resolution/settings guard for a build provisioned to a frozen broker."""
    root = project_root.resolve()
    manifest, pin = root / "lake-manifest.json", root / "lean-toolchain"
    if not manifest.is_file() or not pin.is_file():
        return None
    # Only conventional pinned Lake layouts qualify. In particular, a path
    # dependency or custom library directory can hide a core import outside the
    # default roots checked below. Keep those environments on task-local caching.
    try:
        layout = json.loads(manifest.read_text(encoding="utf-8"))
        if not isinstance(layout, dict) or layout.get("packagesDir", ".lake/packages") != ".lake/packages" or layout.get("lakeDir", ".lake") != ".lake":
            return None
        packages = layout.get("packages", [])
        if not isinstance(packages, list):
            return None
        config_roots = [root]
        for package in packages:
            if not isinstance(package, dict) or package.get("type") != "git" or package.get("subDir"):
                return None
            name = package.get("name")
            if not isinstance(name, str) or not re.fullmatch(r"[A-Za-z0-9_-]+", name):
                return None
            if package.get("configFile", "lakefile.lean") not in {"lakefile.lean", "lakefile.toml"}:
                return None
            package_root = root / ".lake/packages" / name
            if not (package_root / package.get("configFile", "lakefile.lean")).is_file():
                return None
            config_roots.append(package_root)
        layout_settings = {}
        for config_root in config_roots:
            for name in ("lakefile.toml", "lakefile.lean"):
                config = config_root / name
                if not config.is_file():
                    continue
                contents = config.read_text(encoding="utf-8")
                if "LEAN_PATH" in contents or re.search(r"(?<![.\w])(?:buildDir|leanLibDir|packagesDir|lakeDir|leanPath)\s*(?::[^=\n]*)?=", contents):
                    return None
                layout_settings[config.relative_to(root).as_posix()] = sha256_bytes(contents.encode("utf-8"))
    except (OSError, ValueError):
        return None
    if any(os.environ.get(name) for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT")):
        return None
    toolchain = os.environ.get("ELAN_TOOLCHAIN") or pin.read_text(encoding="utf-8").strip()
    if not re.fullmatch(r"leanprover/lean4:v\d+\.\d+\.\d+(?:-rc\d+)?", toolchain):
        return None
    elan = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan"))).resolve()
    lake = shutil.which("lake")
    if not lake or Path(lake).resolve().parent != elan / "bin":
        return None
    installed = elan / "toolchains" / toolchain.replace("/", "--").replace(":", "---")
    library = installed / "lib" / "lean"
    if not (library / "Lean" / "Elab" / "Command.olean").is_file():
        return None
    # Include possible transitive core shadows, not just Lean.Elab.Command.
    search_roots = [root, root / ".lake/build/lib/lean", *(root / ".lake/packages").glob("*/.lake/build/lib/lean")]
    if any((base / name).exists() for base in search_roots for name in ("Init", "Init.olean", "Lean", "Lean.olean", "Std", "Std.olean")):
        return None
    critical = {}
    for path in [*(installed / "bin").glob("*"), *(library / "Lean/Elab").glob("Command.olean*")]:
        if path.is_file():
            info = path.stat()
            critical[path.relative_to(installed).as_posix()] = [info.st_size, info.st_mtime_ns]
    return {
        "schema": "pinned-helper-build-v1",
        "project_root": os.path.normcase(str(root)),
        "toolchain_root": os.path.normcase(str(installed.resolve())),
        "toolchain": toolchain,
        "critical_files": critical,
        "project_settings": {
            name: sha256_file(root / name) if (root / name).is_file() else None
            for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean")
        },
        "lake_layout_settings": layout_settings,
    }


def shared_measurement_helper_fingerprint(project_root: Path) -> str | None:
    """Inspect the pinned compiler/import closure at build selection, never install it."""
    guard = shared_measurement_helper_guard(project_root)
    if guard is None:
        return None
    installed = Path(guard["toolchain_root"])
    files = []
    for directory in (installed / "bin", installed / "lib/lean"):
        for path in sorted(directory.rglob("*")):
            if path.is_file() and (directory.name == "bin" or ".olean" in path.name or path.suffix in {".ir", ".so", ".dll", ".dylib"}):
                info = path.stat()
                files.append((path.relative_to(installed).as_posix(), info.st_size, info.st_mtime_ns))
    material = {key: value for key, value in guard.items() if key != "critical_files"}
    material["toolchain_files"] = files
    return sha256_bytes(json.dumps(material, sort_keys=True, separators=(",", ":")).encode())


def measurement_helper_cache_location(
    project_root: Path, environment_fingerprint: str, lean_args: list[str] | None = None,
) -> tuple[Path, str, str] | None:
    root = evaluation_cache_root()
    if root is None:
        return None
    shared = shared_measurement_helper_fingerprint(project_root)
    identity = shared or environment_fingerprint
    key = measurement_helper_cache_key(identity, measurement_helper_compile_args(lean_args))
    base = project_root.resolve() / ".lake/lrh-measurement-helpers" if shared else root / "helpers"
    return base / key[:2] / key, key, identity


def measurement_helper_is_ready(
    source: Path,
    olean: Path,
    marker: Path,
    key: str,
    environment_fingerprint: str,
    build_guard: dict[str, Any] | None = None,
) -> bool:
    if not (source.is_file() and olean.is_file() and marker.is_file()):
        return False
    try:
        payload = json.loads(marker.read_text(encoding="utf-8"))
        return (
            isinstance(payload, dict)
            and payload.get("schema_version") == 1
            and payload.get("key") == key
            and payload.get("environment_fingerprint")
            == environment_fingerprint
            and payload.get("source_sha256") == sha256_file(source)
            and payload.get("olean_sha256") == sha256_file(olean)
            and (build_guard is None or payload.get("build_guard") == build_guard)
            and all(
                Path(name).name == name and sha256_file(source.parent / name) == digest
                for name, digest in payload.get("artifacts_sha256", {}).items()
            )
        )
    except (OSError, ValueError, TypeError, AttributeError):
        return False


def cached_project_measurement_helper(
    project_root: Path,
    timeout_seconds: float,
    environment_fingerprint: str,
    lean_args: list[str] | None = None,
) -> Path | None:
    if not math.isfinite(timeout_seconds) or timeout_seconds <= 0:
        raise WorkflowError("measurement helper timeout must be finite and positive")
    compile_scope = lean_timeout_scope() == "compile"
    deadline = time.perf_counter() + timeout_seconds

    def remaining() -> float:
        if compile_scope:
            return timeout_seconds
        budget = deadline - time.perf_counter()
        if budget <= 0:
            raise WorkflowError("measurement helper setup deadline expired")
        return budget

    root = evaluation_cache_root()
    if root is None:
        return None
    requested_lean_args = list(lean_args or [])
    lean_args = measurement_helper_compile_args(requested_lean_args)
    location = measurement_helper_cache_location(project_root, environment_fingerprint, lean_args)
    assert location is not None
    support, key, cache_fingerprint = location
    build_guard = shared_measurement_helper_guard(project_root) if cache_fingerprint != environment_fingerprint else None
    if cache_fingerprint != environment_fingerprint and build_guard is None:
        raise WorkflowError("measurement helper build environment changed during setup")
    source = support / "LrhMeasurement.lean"
    olean = support / "LrhMeasurement.olean"
    marker = support / "ready.json"
    if measurement_helper_is_ready(
        source, olean, marker, key, cache_fingerprint, build_guard
    ):
        remaining()
        return support
    lock = support.with_suffix(".lock")
    with exclusive_file_lock(lock, None if compile_scope else remaining()):
        remaining()
        if cache_fingerprint != environment_fingerprint:
            if shared_measurement_helper_fingerprint(project_root) != cache_fingerprint:
                raise WorkflowError("measurement helper build environment changed during cache admission")
            build_guard = shared_measurement_helper_guard(project_root)
            if build_guard is None:
                raise WorkflowError("measurement helper build environment changed during cache admission")
        remaining()
        if measurement_helper_is_ready(
            source, olean, marker, key, cache_fingerprint, build_guard
        ):
            remaining()
            return support
        legacy_key = measurement_helper_cache_key(environment_fingerprint, requested_lean_args)
        legacy = root / "helpers" / legacy_key[:2] / legacy_key
        if support != legacy and measurement_helper_is_ready(
            legacy / source.name, legacy / olean.name, legacy / marker.name,
            legacy_key, environment_fingerprint,
        ):
            # Old markers lack build provenance: preserve task-local reuse, never
            # certify that artifact for another task or a new toolchain inventory.
            remaining()
            return legacy
        support.mkdir(parents=True, exist_ok=True)
        source.write_text(PROJECT_MEASUREMENT_HELPER, encoding="utf-8")
        helper_run = run_lean(
            source, project_root, remaining(),
            lean_args=[*lean_args, "-R", str(support), "-o", str(olean)],
        )
        require_lean_success(helper_run, "measurement helper")
        if cache_fingerprint != environment_fingerprint and shared_measurement_helper_fingerprint(project_root) != cache_fingerprint:
            raise WorkflowError("measurement helper build environment changed during setup")
        remaining()
        marker_payload: dict[str, Any] = {
            "schema_version": 1,
            "key": key,
            "environment_fingerprint": cache_fingerprint,
            "origin_task_fingerprint": environment_fingerprint,
            "cache_scope": "shared-build" if cache_fingerprint != environment_fingerprint else "task",
            "build_guard": build_guard,
            "source_sha256": sha256_file(source),
            "olean_sha256": sha256_file(olean),
            "artifacts_sha256": {
                path.name: sha256_file(path) for path in support.glob("LrhMeasurement.*") if path.is_file()
            },
            "created_at": utc_now(),
        }
        if lean_args:
            marker_payload["lean_args"] = lean_args
        remaining()
        write_json_atomic(marker, marker_payload)
        remaining()
    return support


def evaluate_project_declaration(
    row: dict[str, Any],
    declaration: str,
    project_root: Path,
    timeout_seconds: int,
    environment_fingerprint: str,
    *,
    diagnostic_candidate_path: Path | None = None,
    diagnostic_candidate_bytes: bytes | None = None,
) -> tuple[LeanRun, LeanRun, int, list[str]]:
    helper_lean_args = project_measurement_helper_lean_args(project_root)
    diagnostic_context = {
        "candidate_path": diagnostic_candidate_path,
        "candidate_bytes": diagnostic_candidate_bytes,
        "declaration": declaration,
    }
    with temporary_evaluation_directory("lrh-pm-") as temporary:
        scratch = Path(temporary)
        measured = scratch / "measured"
        audit = scratch / "audit"
        measured.mkdir()
        audit.mkdir()
        support = cached_project_measurement_helper(
            project_root,
            timeout_seconds,
            environment_fingerprint,
            helper_lean_args,
        )
        if support is None:
            support = scratch / "support"
            support.mkdir()
            helper_source = support / "LrhMeasurement.lean"
            helper_olean = support / "LrhMeasurement.olean"
            helper_source.write_text(PROJECT_MEASUREMENT_HELPER, encoding="utf-8")
            helper_run = run_lean(
                helper_source,
                project_root,
                timeout_seconds,
                lean_args=[
                    *measurement_helper_compile_args(helper_lean_args),
                    "-R",
                    str(support),
                    "-o",
                    str(helper_olean),
                ],
            )
            require_lean_success(helper_run, f"{row['name']}: measurement helper",
                                 source_path=helper_source, **diagnostic_context)

        measured_source = measured / "ArenaProjectMeasured.lean"
        measured_olean = measured / "ArenaProjectMeasured.olean"
        measured_harness = project_compile_harness(row, declaration, project_root, exact=True)
        measured_source.write_text(measured_harness, encoding="utf-8")
        measured_run = run_lean(
            measured_source,
            project_root,
            timeout_seconds,
            lean_args=["-R", str(measured), "-o", str(measured_olean)],
            lean_path_prefixes=[support],
        )
        require_lean_success(
            measured_run, f"{row['name']}: measured project compile",
            source_path=measured_source, **diagnostic_context,
        )
        heartbeat = parse_project_heartbeat_count(measured_run.output)

        audit_source = audit / "Audit.lean"
        audit_target = row["name"]
        audit_source.write_text(
            f"import ArenaProjectMeasured\n\n#print axioms {row['name']}\n",
            encoding="utf-8",
        )
        audit_run = run_lean(
            audit_source,
            project_root,
            timeout_seconds,
            lean_path_prefixes=[measured, support],
        )
        missing_target = re.search(
            rf"unknown constant\s+['\u2018`]{re.escape(row['name'])}['\u2019`]", audit_run.output,
            re.IGNORECASE,
        )
        if (
            audit_run.returncode != 0 and not audit_run.timed_out and missing_target
            and project_source_has_module_header(row, project_root)
        ):
            # Preserve the successful public-target path. Only a module visibility
            # failure needs local resolution; never bypass the axiom whitelist.
            # Resolve only the name in a separate copy of the same module. The
            # trailing command can perturb elaborator heartbeats, so its compile
            # is never a measurement and must not replace the measured .olean.
            probe = scratch / "resolve"
            probe.mkdir()
            probe_source = probe / measured_source.name
            probe_olean = probe / measured_olean.name
            probe_source.write_text(
                measured_harness + project_axiom_target_command(row["name"]),
                encoding="utf-8",
            )
            resolved_run = run_lean(
                probe_source,
                project_root,
                timeout_seconds,
                lean_args=["-R", str(probe), "-o", str(probe_olean)],
                lean_path_prefixes=[support],
            )
            require_lean_success(resolved_run, f"{row['name']}: resolved project compile",
                                 source_path=probe_source, **diagnostic_context)
            audit_target = parse_project_axiom_target(row["name"], resolved_run.output)
            audit_source.write_text(
                project_axiom_audit_harness(row["name"], audit_target), encoding="utf-8"
            )
            resolved_audit = run_lean(
                audit_source, project_root, timeout_seconds,
                lean_path_prefixes=[measured, support],
            )
            require_lean_success(resolved_audit, f"{row['name']}: resolved project axiom audit",
                                 source_path=audit_source, **diagnostic_context)
            # Audit the exact artifact that supplied the original heartbeat
            # count. The probe provides only a strictly source-bound name; a
            # missing name or forbidden axiom in the original still fails.
            # Include probe overhead in timing, retaining the measured output.
            def combined_run(first: LeanRun, final: LeanRun, *, result: LeanRun) -> LeanRun:
                peaks = [value for value in (first.peak_working_set_bytes, final.peak_working_set_bytes) if value is not None]
                return replace(
                    result, seconds=first.seconds + final.seconds,
                    queue_wait_seconds=first.queue_wait_seconds + final.queue_wait_seconds,
                    peak_working_set_bytes=max(peaks) if peaks else None,
                )

            measured_run = combined_run(measured_run, resolved_run, result=measured_run)
            audit_run = combined_run(audit_run, resolved_audit, result=resolved_audit)
        require_lean_success(audit_run, f"{row['name']}: project axiom audit",
                             source_path=audit_source, **diagnostic_context)
        axioms = parse_and_validate_axioms(audit_target, audit_run.output)
        return measured_run, audit_run, heartbeat, axioms


def heartbeat_result_kind(result: LeanRun) -> str:
    if result.timed_out:
        return "wall_timeout"
    if result.returncode == 0:
        return "pass"
    if "maximum number of heartbeats" in result.output:
        return "heartbeat_fail"
    return "compile_error"


def bracket_heartbeat_caps(
    observe: Callable[[int], str],
    fail_cap: int,
    pass_cap: int,
    tolerance: int,
) -> tuple[int, int]:
    """Binary-search a deterministic `(failing, passing]` heartbeat bracket."""
    if fail_cap <= 0 or pass_cap <= fail_cap or tolerance <= 0:
        raise WorkflowError("require 0 < fail-cap < pass-cap and tolerance > 0")
    if observe(fail_cap) != "heartbeat_fail":
        raise WorkflowError(f"fail-cap {fail_cap} unexpectedly compiled")
    if observe(pass_cap) != "pass":
        raise WorkflowError(f"pass-cap {pass_cap} did not compile")

    lower, upper = fail_cap, pass_cap
    while upper - lower > tolerance:
        midpoint = (lower + upper) // 2
        result = observe(midpoint)
        if result == "pass":
            upper = midpoint
        elif result == "heartbeat_fail":
            lower = midpoint
        else:
            raise WorkflowError(f"heartbeat observation at cap {midpoint}: {result}")
    return lower, upper


@check_budget.quick_evaluation
def evaluate_candidate_fresh(
    task_path: Path,
    candidate_path: Path,
    project_root: Path,
    timeout_seconds: int = 600,
    quick: bool = False,
    environment_fingerprint: str | None = None,
    *,
    diagnostic_candidate_path: Path | None = None,
    scoring_policy: str | None = None,
) -> Evaluation:
    policy = resolve_scoring_policy(scoring_policy)
    document, row = load_task(task_path)
    candidate_bytes = candidate_path.read_bytes()
    candidate_text = lean_source.candidate_text_from_bytes(candidate_bytes)
    candidate = lean_source.snapshot_candidate(row, candidate_text, candidate_path)
    declaration, candidate_body = candidate.declaration, candidate.proof_body
    original_body = validate_supplied_declaration(row, candidate.task.original_declaration)
    original_body_tokens = (
        None if document.get("statement_first") is True
        else len(local_proof_tokens(original_body, policy))
    )
    official_tokens = row.get("proof_length")
    if type(official_tokens) is not int:
        official_tokens = None
    if policy == ARENA_POLICY:
        original_tokens = official_tokens
        if original_tokens is None:
            original_tokens = document.get("original_metrics", {}).get("tokens")
        if type(original_tokens) is not int or original_tokens <= 0:
            raise WorkflowError("Arena scoring requires a positive proof_length or original token denominator")
    else:
        original_tokens = original_body_tokens
        # A statement-first capsule intentionally contains no original proof.
        if document.get("statement_first") is True:
            original_tokens = document.get("original_metrics", {}).get("tokens")
            if type(original_tokens) is not int or original_tokens <= 0:
                raise WorkflowError("Statement-first task requires a positive original token denominator")
    candidate_tokens = candidate_proof_token_count(candidate_body, policy)
    reduction = (
        100.0 * (original_tokens - candidate_tokens) / original_tokens
        if original_tokens else 0.0
    )

    audit_seconds: float | None = None
    axioms: list[str] | None = None
    heartbeat: int | None = None
    if quick:
        check_budget.stage("quick_source")
        harness = quick_compile_harness(row, declaration, project_root)
        compile_run: LeanRun | None = None
        broker_started_at = utc_now()
        broker_started = time.perf_counter()
        try:
            use_broker = persistent_quick_matches_project(project_root)
            if use_broker:
                check_budget.stage("warm_check")
                response = persistent_quick_request(harness, check_budget.remaining(timeout_seconds))
                wall_seconds = float(response["wall_seconds"])
                lsp_seconds = float(response.get("lsp_seconds", wall_seconds))
                peak_memory = response.get("working_set_bytes")
                # Establish the observed verdict before best-effort presentation.
                # A display/disk failure must never dispatch another Lean compile.
                compile_run = LeanRun(
                    command=["persistent-lean-lsp"],
                    returncode=0 if response["valid"] else 1,
                    seconds=wall_seconds,
                    output="\n".join(
                        str(item.get("message", "")) for item in response["diagnostics"]
                    ),
                    peak_working_set_bytes=(
                        peak_memory if isinstance(peak_memory, int) else None
                    ),
                    queue_wait_seconds=max(0.0, wall_seconds - lsp_seconds),
                )
                presentation_error: str | None = None
                try:
                    from lean_tools import diagnostic_presentation as presentation
                    source_map = presentation.SourceMap.for_declaration(
                        candidate_text, harness, declaration
                    )
                    shown = presentation.present_diagnostics(response["diagnostics"], source_map)
                    output = presentation.diagnostic_text(shown["diagnostics"])
                    if response.get("diagnostics_truncated"):
                        output += "\nadditional service diagnostics omitted"
                    diagnostics_path = presentation.archive_diagnostics(
                        response["diagnostics"],
                        shown,
                        source=harness,
                        candidate_path=diagnostic_candidate_path or candidate_path,
                        candidate_bytes=candidate_bytes,
                        source_map=source_map,
                        service_omitted=response.get("diagnostics_omitted", 0),
                    )
                    compile_run = replace(
                        compile_run, output=output, log_path=str(diagnostics_path)
                    )
                except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
                    presentation_error = str(error)
                record_event(
                    "persistent_quick",
                    {
                        "status": (
                            "completed" if response["valid"] else "failed"
                        ),
                        "started_at": broker_started_at,
                        "finished_at": utc_now(),
                        "wall_seconds": round(wall_seconds, 6),
                        "lsp_seconds": round(lsp_seconds, 6),
                        "broker_wait_seconds": round(
                            max(0.0, wall_seconds - lsp_seconds), 6
                        ),
                        "working_set_bytes": compile_run.peak_working_set_bytes,
                        "task_id": row["name"],
                        "diagnostic_count": len(response["diagnostics"]),
                        "diagnostic_presentation_error": presentation_error,
                        "valid": response["valid"],
                        "fallback": False,
                    },
                )
        except (WorkflowError, OSError, ValueError) as error:
            # A timeout is inconclusive. Retrying it cold repeats expensive work.
            # A mid-dispatch disconnect may leave the server cleaning up, so only
            # a proven connection failure before dispatch can use the cold lane.
            failure_kind = getattr(error, "code", "infrastructure_failure")
            retryable = isinstance(error, PersistentQuickFailure) and error.retryable
            record_event(
                "persistent_quick",
                {
                    "status": "fallback" if retryable else "failed",
                    "started_at": broker_started_at,
                    "finished_at": utc_now(),
                    "wall_seconds": round(time.perf_counter() - broker_started, 6),
                    "task_id": row["name"],
                    "fallback": retryable,
                    "failure_kind": failure_kind,
                    "failure_details": getattr(error, "result", None),
                    "error": str(error),
                },
            )
            if failure_kind in {"operation_timeout", "queue_timeout", "transport_timeout"}:
                run = LeanRun(["persistent-lean-lsp"], -1, time.perf_counter() - broker_started,
                              str(error), timed_out=True)
                timeout = LeanTimeoutError(str(error), run)
                timeout.code = failure_kind
                timeout.failure_details = getattr(error, "result", None)
                raise timeout from error
            if not retryable:
                raise
        if compile_run is None and not is_project_resident(row):
            # Fresh callers also get immutable admission when using cold Lean.
            # Reading the draft again here can compile different source from
            # the declaration and token count captured above.
            with temporary_evaluation_directory("lrh-q-") as temporary:
                compile_path = Path(temporary) / "Candidate.lean"
                compile_path.write_bytes(candidate_bytes)
                compile_run = run_lean(compile_path, project_root, timeout_seconds)
        if compile_run is None:
            with temporary_evaluation_directory("lrh-pq-") as temporary:
                quick_root = Path(temporary)
                compile_path = quick_root / "ArenaProjectQuick.lean"
                compile_path.write_text(harness, encoding="utf-8")
                compile_run = run_lean(
                    compile_path,
                    project_root,
                    timeout_seconds,
                    lean_args=["-R", str(quick_root)],
                )
        require_lean_success(compile_run, f"{row['name']}: candidate compile")
    else:
        if is_project_resident(row):
            fingerprint = environment_fingerprint or measurement_environment_fingerprint(
                row, project_root
            )
            compile_run, audit_run, heartbeat, axioms = evaluate_project_declaration(
                row, declaration, project_root, timeout_seconds, fingerprint,
                diagnostic_candidate_path=diagnostic_candidate_path or candidate_path,
                diagnostic_candidate_bytes=candidate_bytes,
            )
            audit_seconds = audit_run.seconds
        else:
            with temporary_evaluation_directory("lrh-m-") as temporary:
                audit_path = Path(temporary) / "Measured.lean"
                audit_path.write_text(
                    exact_heartbeat_audit_harness(row, declaration), encoding="utf-8"
                )
                audit_run = run_lean(audit_path, project_root, timeout_seconds)
                require_lean_success(
                    audit_run, f"{row['name']}: measured compile and axiom audit",
                    source_path=audit_path,
                    candidate_path=diagnostic_candidate_path or candidate_path,
                    candidate_bytes=candidate_bytes, declaration=declaration,
                )
                compile_run = audit_run
                audit_seconds = audit_run.seconds
                axioms = parse_and_validate_axioms(row["name"], audit_run.output)
                heartbeat = parse_exact_heartbeat_count(audit_run.output)

    reference = document.get("reference", {})
    published_reference_heartbeat = (
        reference.get("heartbeat") if isinstance(reference, dict) else None
    )
    if type(published_reference_heartbeat) is not int:
        published_reference_heartbeat = None
    reference_heartbeat_source = reference.get("source") if isinstance(reference, dict) else None
    effective_reference_heartbeat = published_reference_heartbeat
    if reference_heartbeat_source == "measured_original_heartbeat":
        published_reference_heartbeat = None
    fingerprint = environment_fingerprint or measurement_environment_fingerprint(
        row, project_root
    )
    local_reference_heartbeat: int | None = None
    baselines = document.get("local_baselines", [])
    if isinstance(baselines, list):
        matches = [
            item
            for item in baselines
            if isinstance(item, dict)
            and item.get("environment_fingerprint") == fingerprint
            and isinstance(item.get("heartbeat"), int)
        ]
        if len(matches) == 1:
            local_reference_heartbeat = matches[0]["heartbeat"]
    if (
        normalized_lean_code(declaration)
        == normalized_lean_code(canonical_candidate_declaration(row))
        and heartbeat is not None
    ):
        local_reference_heartbeat = heartbeat
    if policy == ARENA_POLICY:
        local_reference_heartbeat = effective_reference_heartbeat
    heartbeat_reduction = (
        round(
            100.0 * (local_reference_heartbeat - heartbeat) / local_reference_heartbeat,
            2,
        )
        if local_reference_heartbeat and heartbeat is not None
        else None
    )
    return Evaluation(
        task_id=row["name"],
        candidate_path=str(candidate_path.resolve()),
        valid=True,
        compile_seconds=compile_run.seconds,
        axiom_audit_seconds=audit_seconds,
        axioms=axioms,
        original_local_tokens=original_tokens,
        candidate_local_tokens=candidate_tokens,
        local_token_reduction_pct=round(reduction, 2),
        official_original_tokens=official_tokens,
        scoring_policy=policy,
        candidate_token_offset=candidate_token_offset(policy),
        original_body_tokens=original_body_tokens,
        published_reference_heartbeat=published_reference_heartbeat,
        reference_heartbeat_source=reference_heartbeat_source,
        local_reference_heartbeat=local_reference_heartbeat,
        environment_fingerprint=fingerprint,
        heartbeat=heartbeat,
        heartbeat_reduction_pct=heartbeat_reduction,
        axiom_audit_shares_compile=(None if quick else not is_project_resident(row)),
        diagnostics_path=(
            compile_run.log_path
            if quick and compile_run.command == ["persistent-lean-lsp"] else None
        ),
        source_sha256=sha256_bytes(candidate_bytes),
    )


# Kept for older callers; new fresh callers use lean_tools.evaluation.
_evaluate_candidate_uncached = evaluate_candidate_fresh


@check_budget.quick_evaluation
def evaluate_candidate(
    task_path: Path,
    candidate_path: Path,
    project_root: Path,
    timeout_seconds: int = 600,
    quick: bool = False,
    fingerprint_registry: Path | None = None,
    *,
    source_bytes: bytes | None = None,
    scoring_policy: str | None = None,
) -> Evaluation:
    check_budget.stage("evaluation_setup")
    policy = resolve_scoring_policy(scoring_policy)
    started_at = utc_now()
    started = time.perf_counter()
    task_path = task_path.resolve()
    candidate_path = candidate_path.resolve()
    project_root = project_root.resolve()
    _, row = load_task(task_path)
    candidate_bytes = candidate_path.read_bytes() if source_bytes is None else source_bytes
    candidate_text = lean_source.candidate_text_from_bytes(candidate_bytes)
    source_sha256 = sha256_bytes(candidate_bytes)
    declaration, _ = extract_candidate_declaration(row, candidate_text)
    declaration_sha256 = sha256_bytes(declaration.encode("utf-8"))
    fingerprint = (
        measurement_environment_fingerprint(row, project_root)
        if fingerprint_registry is None
        else measurement_environment_fingerprint(
            row, project_root, registry_path=fingerprint_registry
        )
    )
    mode = "quick" if quick else "exact"
    key = evaluation_cache_key(task_path, row, declaration, fingerprint, mode, policy)
    root = evaluation_cache_root()
    cache_lock: dict[str, Any] = {}

    def evaluate_admitted_source() -> Evaluation:
        # Cache identity, measurement and checkpoint provenance all originate
        # from this one admission. Concurrent edits to candidate_path cannot
        # affect the evaluator's later read or the cold Lean input.
        with temporary_evaluation_directory("lrh-c-") as temporary:
            snapshot = Path(temporary) / "Candidate.lean"
            snapshot.write_bytes(candidate_bytes)
            evaluation = _evaluate_candidate_uncached(
                task_path,
                snapshot,
                project_root,
                timeout_seconds=timeout_seconds,
                quick=quick,
                environment_fingerprint=fingerprint,
                # Archive against the caller's durable source location, not
                # the immutable compiler input deleted when this scope exits.
                diagnostic_candidate_path=candidate_path,
                scoring_policy=policy,
            )
            if snapshot.read_bytes() != candidate_bytes:
                raise WorkflowError("admitted candidate snapshot changed during evaluation")
            if not isinstance(evaluation, Evaluation) or evaluation.valid is not True:
                raise WorkflowError("evaluator did not confirm complete candidate validity")
            if (
                evaluation.scoring_policy != policy
                or evaluation.candidate_token_offset != candidate_token_offset(policy)
            ):
                raise WorkflowError("evaluator scoring policy does not match admitted request")
            if evaluation.source_sha256 is not None and evaluation.source_sha256 != source_sha256:
                raise WorkflowError("evaluator source provenance does not match admitted candidate")
            return replace(
                evaluation, candidate_path=str(candidate_path), source_sha256=source_sha256
            )

    def with_request_timing(
        evaluation: Evaluation, status: str, source_mode: str | None = None,
    ) -> Evaluation:
        return replace(
            evaluation,
            cache_status=status,
            cache_source_mode=source_mode,
            request_wall_seconds=time.perf_counter() - started,
            candidate_path=str(candidate_path),
            source_sha256=source_sha256,
        )

    def finish_event(
        status: str,
        cache_status: str,
        *,
        cache_source_mode: str | None = None,
        error: str | None = None,
        cache_wait_seconds: float = 0.0,
        error_kind: str | None = None,
    ) -> None:
        record_event(
            "evaluation",
            {
                "status": status,
                "cache_status": cache_status,
                "cache_source_mode": cache_source_mode,
                "cache_key": key,
                "scoring_policy": policy,
                "candidate_token_offset": candidate_token_offset(policy),
                "cache_wait_seconds": round(cache_wait_seconds, 6),
                "cache_lock": dict(cache_lock),
                "process_id": os.getpid(),
                "mode": mode,
                "task_id": row["name"],
                "declaration_sha256": declaration_sha256,
                "source_sha256": source_sha256,
                "environment_fingerprint": fingerprint,
                "started_at": started_at,
                "finished_at": utc_now(),
                "wall_seconds": round(time.perf_counter() - started, 6),
                "error": error,
                "error_kind": error_kind,
            },
        )

    if root is None:
        try:
            evaluation = evaluate_admitted_source()
        except Exception as error:
            finish_event("failed", "disabled", error=str(error))
            raise
        finish_event("completed", "disabled")
        return with_request_timing(evaluation, "disabled")

    cache_path = evaluation_cache_path(root, mode, key)
    cached = cached_evaluation(cache_path, candidate_path, scoring_policy=policy)
    if cached is not None:
        finish_event("completed", "hit", cache_source_mode=mode)
        return with_request_timing(cached, "hit", mode)
    if quick:
        exact_key = evaluation_cache_key(
            task_path, row, declaration, fingerprint, "exact", policy
        )
        exact_path = evaluation_cache_path(root, "exact", exact_key)
        cached_exact = cached_evaluation(
            exact_path, candidate_path, quick_view=True, scoring_policy=policy
        )
        if cached_exact is not None:
            finish_event("completed", "hit", cache_source_mode="exact")
            return with_request_timing(cached_exact, "hit", "exact")

    lock_path = cache_path.with_suffix(".lock")
    check_budget.stage("cache_lock")
    cache_wait = 0.0
    try:
        with exclusive_file_lock(
            lock_path,
            None if lean_timeout_scope() == "compile" else timeout_seconds,
            request={"task_id": row["name"], "mode": mode, "cache_key": key},
            wait_metadata=cache_lock,
        ) as waited:
            cache_wait = float(waited)
            cached = cached_evaluation(cache_path, candidate_path, scoring_policy=policy)
            if cached is not None:
                finish_event(
                    "completed",
                    "hit",
                    cache_source_mode=mode,
                    cache_wait_seconds=cache_wait,
                )
                return with_request_timing(cached, "hit", mode)
            evaluation = evaluate_admitted_source()
            store_cached_evaluation(
                cache_path,
                key,
                mode,
                fingerprint,
                declaration_sha256,
                evaluation,
            )
    except Exception as error:
        cache_wait = float(cache_lock.get("wait_seconds", cache_wait))
        finish_event(
            "failed",
            "miss",
            error=str(error),
            cache_wait_seconds=cache_wait,
            error_kind=(
                "cache_lock_timeout"
                if isinstance(error, CacheLockTimeout)
                else "infrastructure"
                if isinstance(error, OSError)
                else "evaluation_error"
            ),
        )
        raise
    finish_event("completed", "miss", cache_wait_seconds=cache_wait)
    return with_request_timing(evaluation, "miss")


def evaluation_payload(evaluation: Evaluation) -> dict[str, Any]:
    exact = evaluation.axiom_audit_seconds is not None
    return {
        "task_id": evaluation.task_id,
        "candidate_path": evaluation.candidate_path,
        "source_sha256": evaluation.source_sha256,
        "scoring_policy": evaluation.scoring_policy,
        "valid": evaluation.valid,
        "diagnostics_path": evaluation.diagnostics_path,
        "cache": {
            "status": evaluation.cache_status,
            "hit": (
                evaluation.cache_status == "hit"
                if evaluation.cache_status != "unknown" else None
            ),
            "source_mode": evaluation.cache_source_mode,
        },
        "timing": {
            "measurement_source": (
                "cached" if evaluation.cache_status == "hit"
                else "current_request" if evaluation.cache_status in {"miss", "disabled"}
                else "unknown"
            ),
            "axiom_audit_shares_compile": evaluation.axiom_audit_shares_compile,
            "phase_note": (
                "Compile and axiom audit timings describe the same process; do not add them."
                if evaluation.axiom_audit_shares_compile else None
            ),
            "request_wall_seconds": (
                round(evaluation.request_wall_seconds, 6)
                if evaluation.request_wall_seconds is not None else None
            ),
            "measurement_compile_seconds": round(evaluation.compile_seconds, 6),
            "measurement_axiom_audit_seconds": (
                round(evaluation.axiom_audit_seconds, 6)
                if evaluation.axiom_audit_seconds is not None else None
            ),
        },
        # Retain these legacy measurement aliases for archived-result consumers.
        "compile_seconds": round(evaluation.compile_seconds, 3),
        "axiom_audit_seconds": (
            round(evaluation.axiom_audit_seconds, 3)
            if evaluation.axiom_audit_seconds is not None
            else None
        ),
        "measurement_mode": "exact" if exact else "quick",
        "axioms": evaluation.axioms,
        "axiom_status": "measured" if exact else "not_run",
        "length": {
            "proxy": (
                "Arena Unicode lexer v1 + 1 presumed assignment token"
                if evaluation.scoring_policy == ARENA_POLICY
                else "comment-stripped local Lean lexer v1 (not the private Arena tokenizer)"
            ),
            "scoring_policy": evaluation.scoring_policy,
            "candidate_token_offset": evaluation.candidate_token_offset,
            "original_body_tokens": evaluation.original_body_tokens,
            "original_reference": (
                (("published proof_length" if evaluation.official_original_tokens is not None
                   else "measured original candidate token convention")
                 if evaluation.scoring_policy == ARENA_POLICY else "local proof body")
            ),
            "original_tokens": evaluation.original_local_tokens,
            "candidate_tokens": evaluation.candidate_local_tokens,
            "reduction_pct": evaluation.local_token_reduction_pct,
            "official_original_tokens": evaluation.official_original_tokens,
        },
        "heartbeat": {
            "status": "measured" if exact else "not_run",
            "published_reference": evaluation.published_reference_heartbeat,
            **({"reference_source": evaluation.reference_heartbeat_source}
               if evaluation.reference_heartbeat_source is not None else {}),
            "local_reference": evaluation.local_reference_heartbeat,
            "candidate": evaluation.heartbeat,
            "reduction_pct": evaluation.heartbeat_reduction_pct,
            "environment_fingerprint": evaluation.environment_fingerprint,
            "note": (
                ("Reduction uses the measured original heartbeat denominator."
                 if evaluation.reference_heartbeat_source == "measured_original_heartbeat"
                 else "Reduction uses the published Arena heartbeat reference.")
                if evaluation.scoring_policy == ARENA_POLICY else
                "Reduction uses the matching local baseline; the published Arena value "
                "is shown for calibration only."
            ),
        },
        "local_two_axis_mean": (
            local_selection_score(evaluation)
            if evaluation.heartbeat_reduction_pct is not None
            else None
        ),
    }


def checkpoint_candidate(
    candidate_path: Path, evaluation: Evaluation, checkpoint_dir: Path,
    *, source_bytes: bytes | None = None,
) -> Path:
    """Publish one source admission and a receipt bound to its full identity.

    Older callers may pass an already-frozen path without request provenance.
    An explicit byte override requires the evaluation's admitted source hash.
    """
    if not isinstance(evaluation, Evaluation) or evaluation.valid is not True:
        raise WorkflowError("only a valid candidate evaluation can be checkpointed")
    if type(evaluation.candidate_local_tokens) is not int or evaluation.candidate_local_tokens < 0:
        raise WorkflowError("candidate checkpoint lacks a valid token measurement")
    if evaluation.candidate_token_offset != candidate_token_offset(evaluation.scoring_policy):
        raise WorkflowError("candidate checkpoint scoring policy has an invalid token offset")
    if source_bytes is not None and evaluation.source_sha256 is None:
        raise WorkflowError("candidate byte override lacks evaluated source provenance")
    candidate_bytes = candidate_path.read_bytes() if source_bytes is None else source_bytes
    lean_source.candidate_text_from_bytes(candidate_bytes)
    if not candidate_bytes.strip():
        raise WorkflowError("empty candidate source cannot be checkpointed")
    digest = sha256_bytes(candidate_bytes)
    if evaluation.source_sha256 is not None and evaluation.source_sha256 != digest:
        raise WorkflowError("candidate source changed since evaluation; no checkpoint was saved")
    checkpoint_dir.mkdir(parents=True, exist_ok=True)
    checkpoint = checkpoint_dir / (
        f"{evaluation.candidate_local_tokens:06d}-{digest[:12]}.lean"
    )
    if checkpoint.is_symlink():
        raise WorkflowError("candidate checkpoint must not be a symlink")
    if checkpoint.exists():
        if checkpoint.read_bytes() != candidate_bytes:
            raise WorkflowError("candidate checkpoint content-address collision")
    else:
        temporary = checkpoint.with_name(f".{checkpoint.name}.{uuid.uuid4().hex}.tmp")
        try:
            temporary.write_bytes(candidate_bytes)
            temporary.replace(checkpoint)
        finally:
            temporary.unlink(missing_ok=True)
    receipt = checkpoint.with_suffix(".json")
    if receipt.is_symlink():
        raise WorkflowError("candidate checkpoint receipt must not be a symlink")
    if evaluation.axiom_audit_seconds is None and receipt.is_file():
        # A quick recheck of the same source/context must not erase its already
        # recorded exact measurement. Other contexts still get their own
        # truthful quick receipt rather than inheriting unrelated heartbeats.
        try:
            prior = json.loads(receipt.read_text(encoding="utf-8"))
            measured = prior.get("evaluation", {})
            heartbeat = measured.get("heartbeat", {})
            axioms = measured.get("axioms")
            if (
                prior.get("schema_version") == 1
                and prior.get("source_sha256") == digest
                and prior.get("task_id") == evaluation.task_id
                and measured.get("scoring_policy", LEGACY_POLICY) == evaluation.scoring_policy
                and measured.get("length", {}).get("candidate_token_offset", 0) == evaluation.candidate_token_offset
                and prior.get("validation") == "exact"
                and prior.get("valid") is True
                and prior.get("candidate_local_tokens") == evaluation.candidate_local_tokens
                and measured.get("source_sha256") == digest
                and measured.get("task_id") == evaluation.task_id
                and measured.get("valid") is True
                and measured.get("measurement_mode") == "exact"
                and measured.get("axiom_status") == "measured"
                and isinstance(axioms, list)
                and all(axiom in ALLOWED_AXIOMS for axiom in axioms)
                and type(heartbeat.get("candidate")) is int
                and heartbeat["candidate"] >= 0
                and prior.get("heartbeat") == heartbeat["candidate"]
                and isinstance(evaluation.environment_fingerprint, str)
                and heartbeat.get("environment_fingerprint") == evaluation.environment_fingerprint
            ):
                return checkpoint
        except (OSError, ValueError, AttributeError, TypeError):
            pass
    write_json_atomic(
        receipt,
        {
            "schema_version": 1,
            "source_sha256": digest,
            "task_id": evaluation.task_id,
            "validation": "exact" if evaluation.axiom_audit_seconds is not None else "quick",
            "valid": True,
            "candidate_local_tokens": evaluation.candidate_local_tokens,
            "heartbeat": evaluation.heartbeat,
            "evaluation": evaluation_payload(replace(evaluation, source_sha256=digest)),
        },
    )
    return checkpoint


def evaluation_checkpoint_dir(explicit: Path | None) -> Path | None:
    if explicit is not None:
        return explicit
    configured = os.environ.get("LEAN_REFACTOR_CHECKPOINT_DIR")
    return Path(configured) if configured else None


def candidate_token_count(
    task_path: Path, candidate_path: Path, scoring_policy: str | None = None,
) -> int:
    _, row = load_task(task_path)
    _, body = extract_candidate_declaration(
        row, candidate_path.read_text(encoding="utf-8")
    )
    return candidate_proof_token_count(body, scoring_policy)


def write_submission(
    task_path: Path, candidate_path: Path, output_path: Path
) -> dict[str, str]:
    _, row = load_task(task_path)
    declaration, _ = extract_candidate_declaration(
        row, candidate_path.read_text(encoding="utf-8")
    )
    payload = {"name": row["name"], "proof": declaration}
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(
        json.dumps(payload, ensure_ascii=False, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    return payload


def write_candidate_seed(task_path: Path, output_path: Path) -> None:
    _, row = load_task(task_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(render_candidate_scaffold(row), encoding="utf-8")


def find_codex(explicit: Path | None = None) -> Path:
    """Select a native CLI, honoring an explicitly pinned executable first."""
    configured = os.environ.get("LEAN_E6_CODEX")
    selected = explicit if explicit is not None else Path(configured).expanduser() if configured else None
    if selected is not None:
        selected = selected.expanduser().resolve()
        if not selected.is_file() or not os.access(selected, os.X_OK):
            raise WorkflowError(f"Codex executable is missing or not executable: {selected}")
        return selected
    found = shutil.which("codex")
    candidates = [Path(found)] if found else []
    candidates.append(Path.home() / ".local" / "bin" / "codex")
    for candidate in candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return candidate.resolve()
    raise WorkflowError("Native Codex CLI not found; pass its pinned path or set LEAN_E6_CODEX")


def command_output(command: list[str], cwd: Path) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    if completed.returncode != 0:
        detail = (completed.stdout + completed.stderr).strip()
        raise WorkflowError(
            f"command failed ({completed.returncode}): {' '.join(command)}\n{detail}"
        )
    return (completed.stdout + completed.stderr).strip()


def recorded_lean_version(project_root: Path, timeout_seconds: float = 120) -> str:
    timeout_seconds = check_budget.remaining(timeout_seconds)
    if not math.isfinite(timeout_seconds) or timeout_seconds <= 0:
        raise WorkflowError("Lean version timeout must be finite and positive")
    timeout_scope = lean_timeout_scope()
    deadline = time.perf_counter() + timeout_seconds if timeout_scope == "request" else None
    command = ["lake", "env", "lean", "--version"]
    try:
        priority = int(os.environ.get("LEAN_REFACTOR_LEAN_PRIORITY", "10"))
    except ValueError as error:
        raise WorkflowError("LEAN_REFACTOR_LEAN_PRIORITY must be an integer") from error
    try:
        with resource_gate.permit_from_environment(
            "lean",
            priority=priority,
            timeout_seconds=max(0.0, deadline - time.perf_counter()) if deadline is not None else None,
            metadata={
                "project_root": str(project_root.resolve()),
                "purpose": "environment-fingerprint",
            },
        ) as permit:
            if deadline is not None and time.perf_counter() >= deadline:
                raise resource_gate.ResourceGateError("Lean version deadline expired during admission")
            started_at = utc_now()
            started = time.perf_counter()
            command = lean_launch.native_command(command)
            process = subprocess.Popen(
                command,
                env=lean_launch.native_environment(),
                cwd=project_root,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                encoding="utf-8",
                errors="replace",
                creationflags=(
                    subprocess.CREATE_NEW_PROCESS_GROUP if os.name == "nt" else 0
                ),
                start_new_session=os.name != "nt",
            )
            lean_launch.process_memory.capture_process_identity(process)
            if deadline is None:
                deadline = time.perf_counter() + timeout_seconds
            timed_out = False
            try:
                stdout, stderr = process.communicate(timeout=max(0.0, deadline - time.perf_counter()))
            except subprocess.TimeoutExpired as error:
                timed_out = True
                terminate_process_tree(process)
                stdout, stderr = lean_launch.drain_process(process, error)
            # Keep the fingerprint material byte-for-byte compatible with
            # command_output(), including for Lake warnings written to stderr.
            output = (stdout or "") + (stderr or "")
            seconds = time.perf_counter() - started
            finished_at = utc_now()
            peak_memory = process_peak_working_set_bytes(process)
    except resource_gate.ResourceGateError as error:
        raise WorkflowError(f"Lean admission failed: {error}") from error
    event_id = uuid.uuid4().hex
    log_path: Path | None = None
    artifact_root = artifact_root_path()
    if artifact_root is not None:
        log_path = artifact_root / "lean-logs" / f"{event_id}.log"
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text(output, encoding="utf-8")
    record_event(
        "lean_process",
        {
            "process_id": process.pid,
            "status": (
                "timed_out"
                if timed_out
                else "completed" if process.returncode == 0 else "failed"
            ),
            "purpose": "environment-fingerprint",
            "timeout_scope": timeout_scope,
            "queued_at": permit.queued_at,
            "admitted_at": permit.admitted_at,
            "started_at": started_at,
            "finished_at": finished_at,
            "queue_wait_seconds": round(permit.queue_wait_seconds, 6),
            "wall_seconds": round(seconds, 6),
            "peak_working_set_bytes": peak_memory,
            "project_root": str(project_root.resolve()),
            "command": command,
            "returncode": process.returncode,
            "timed_out": timed_out,
            "log_path": (
                str(log_path.relative_to(artifact_root).as_posix())
                if log_path is not None and artifact_root is not None
                else None
            ),
            "lean_event_id": event_id,
        },
    )
    if timed_out:
        raise WorkflowError("Lean version query timed out")
    if process.returncode != 0:
        raise WorkflowError(
            f"Lean version query failed with {process.returncode}: "
            f"{compact_lean_diagnostic(output)}"
        )
    return output.strip()


def environment_fingerprint_registry_key(
    row: dict[str, Any], project_root: Path
) -> str:
    resolved = str(project_root.resolve())
    canonical_root = os.path.normcase(resolved) if os.name == "nt" else resolved
    return f"{row['name']}\n{canonical_root}"


def environment_fingerprint_guard_material(
    row: dict[str, Any], project_root: Path
) -> dict[str, Any]:
    """Return cheap inputs that detect a stale explicit fingerprint entry."""
    root = project_root.resolve()
    manifest = root / "lake-manifest.json"
    if not manifest.is_file():
        raise WorkflowError(f"missing Lake manifest: {manifest}")
    toolchain = root / "lean-toolchain"
    material: dict[str, Any] = {
        "schema_version": FINGERPRINT_GUARD_SCHEMA_VERSION,
        "registry_key": environment_fingerprint_registry_key(row, root),
        "instrumentation": (
            "project-command-heartbeat-v1"
            if is_project_resident(row)
            else "exact-heartbeat-audit-v1"
        ),
        "lake_manifest_sha256": sha256_file(manifest),
        "lean_toolchain_sha256": sha256_file(toolchain) if toolchain.is_file() else None,
        "environment_sha256": sha256_bytes(render_environment(row).encode("utf-8")),
        "original_declaration_sha256": sha256_bytes(
            canonical_candidate_declaration(row).encode("utf-8")
        ),
        "max_heartbeats": 1_000_000_000,
        "elab_async": False,
    }
    if is_project_resident(row):
        source_path = project_source_path(row, root)
        material.update(
            {
                "project_source_path": str(row["file_path"]),
                "project_source_sha256": sha256_file(source_path),
                "measurement_helper_sha256": sha256_bytes(
                    PROJECT_MEASUREMENT_HELPER.encode("utf-8")
                ),
                "measurement_helper_lean_args": project_measurement_helper_lean_args(
                    root
                ),
            }
        )
    return material


def environment_fingerprint_guard_sha256(
    row: dict[str, Any], project_root: Path
) -> str:
    return sha256_bytes(
        json.dumps(
            environment_fingerprint_guard_material(row, project_root),
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    )


def remaining_startup_seconds(deadline: float) -> float:
    """Remaining shared startup budget, including resource admission waits."""
    remaining = deadline - time.monotonic()
    if not math.isfinite(remaining) or remaining <= 0:
        raise WorkflowError("Lean startup budget expired")
    return remaining


def _measurement_environment_fingerprint_material(
    row: dict[str, Any], project_root: Path, *, deadline: float | None = None,
) -> dict[str, Any]:
    guard = environment_fingerprint_guard_material(row, project_root)
    material = {
        "schema": guard["instrumentation"],
        "lean_version": (
            recorded_lean_version(project_root)
            if deadline is None
            else recorded_lean_version(project_root, remaining_startup_seconds(deadline))
        ),
        "lake_manifest_sha256": guard["lake_manifest_sha256"],
        "environment_sha256": guard["environment_sha256"],
        "original_declaration_sha256": guard["original_declaration_sha256"],
        "max_heartbeats": guard["max_heartbeats"],
        "elab_async": guard["elab_async"],
    }
    if is_project_resident(row):
        material.update(
            {
                "project_source_path": guard["project_source_path"],
                "project_source_sha256": guard["project_source_sha256"],
                "measurement_helper_sha256": guard[
                    "measurement_helper_sha256"
                ],
            }
        )
        helper_lean_args = guard["measurement_helper_lean_args"]
        if helper_lean_args:
            material["measurement_helper_lean_args"] = helper_lean_args
    return material


def _measurement_environment_fingerprint_uncached(
    row: dict[str, Any], project_root: Path, *, deadline: float | None = None,
) -> str:
    material = _measurement_environment_fingerprint_material(row, project_root, deadline=deadline)
    return sha256_bytes(
        json.dumps(material, sort_keys=True, separators=(",", ":")).encode("utf-8")
    )


def compute_measurement_environment_fingerprint(
    row: dict[str, Any], project_root: Path, *, deadline: float | None = None,
) -> str:
    """Compute a fingerprint from current inputs without consulting a registry."""

    return _measurement_environment_fingerprint_uncached(row, project_root, deadline=deadline)


def environment_fingerprint_registry_entry(
    row: dict[str, Any],
    project_root: Path,
    registry_path: Path,
    *,
    validate_guard: bool,
) -> dict[str, Any]:
    try:
        registry = json.loads(registry_path.resolve().read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise WorkflowError(
            f"cannot read explicit fingerprint registry {registry_path}: {error}"
        ) from error
    if (
        not isinstance(registry, dict)
        or registry.get("schema_version") != FINGERPRINT_REGISTRY_SCHEMA_VERSION
        or not isinstance(registry.get("entries"), dict)
    ):
        raise WorkflowError(
            f"explicit fingerprint registry has an unsupported schema: {registry_path}"
        )
    key = environment_fingerprint_registry_key(row, project_root)
    entry = registry["entries"].get(key)
    if not isinstance(entry, dict):
        raise WorkflowError(
            f"explicit fingerprint registry has no entry for {row['name']} at "
            f"{project_root.resolve()}"
        )
    fingerprint = entry.get("fingerprint")
    if not isinstance(fingerprint, str) or not re.fullmatch(r"[0-9a-f]{64}", fingerprint):
        raise WorkflowError("explicit fingerprint registry entry has an invalid digest")
    lean_version = entry.get("lean_version")
    if not isinstance(lean_version, str) or not lean_version:
        raise WorkflowError("explicit fingerprint registry entry omits the Lean version")
    if validate_guard:
        expected = entry.get("guard_sha256")
        actual = environment_fingerprint_guard_sha256(row, project_root)
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise WorkflowError("explicit fingerprint registry entry has an invalid guard")
        if expected != actual:
            raise WorkflowError(
                "explicit fingerprint registry entry is stale for "
                f"{row['name']} at {project_root.resolve()}"
            )
    return entry


def measurement_environment_fingerprint(
    row: dict[str, Any],
    project_root: Path,
    *,
    registry_path: Path | None = None,
) -> str:
    if registry_path is not None:
        return str(
            environment_fingerprint_registry_entry(
                row, project_root, registry_path, validate_guard=True
            )["fingerprint"]
        )
    registry_value = os.environ.get("LEAN_REFACTOR_FINGERPRINT_REGISTRY")
    if registry_value:
        registry_path = Path(registry_value)
        try:
            registry = json.loads(registry_path.read_text(encoding="utf-8"))
            key = environment_fingerprint_registry_key(row, project_root)
            if (
                isinstance(registry, dict)
                and registry.get("schema_version")
                == FINGERPRINT_REGISTRY_SCHEMA_VERSION
                and isinstance(registry.get("entries"), dict)
            ):
                entry = registry["entries"].get(key)
                value = entry.get("fingerprint") if isinstance(entry, dict) else None
            else:
                # Keep archived/resumed experiments with the original flat registry
                # readable. New explicit contracts require the guarded schema above.
                value = registry.get(key) if isinstance(registry, dict) else None
            if isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value):
                return value
        except (OSError, json.JSONDecodeError):
            pass
    return compute_measurement_environment_fingerprint(row, project_root)


def write_environment_fingerprint_registry(
    row: dict[str, Any], roots: list[Path], output: Path, *, deadline: float | None = None,
) -> dict[str, str]:
    fingerprints: dict[str, str] = {}
    entries: dict[str, dict[str, Any]] = {}
    for root in roots:
        key = environment_fingerprint_registry_key(row, root)
        material = _measurement_environment_fingerprint_material(row, root, deadline=deadline)
        if deadline is not None:
            remaining_startup_seconds(deadline)
        fingerprint = sha256_bytes(
            json.dumps(material, sort_keys=True, separators=(",", ":")).encode(
                "utf-8"
            )
        )
        fingerprints[key] = fingerprint
        entries[key] = {
            "task_id": row["name"],
            "project_root": str(root.resolve()),
            "fingerprint": fingerprint,
            "lean_version": material["lean_version"],
            "guard_sha256": environment_fingerprint_guard_sha256(row, root),
        }
    write_json_atomic(
        output,
        {
            "schema_version": FINGERPRINT_REGISTRY_SCHEMA_VERSION,
            "entries": entries,
        },
    )
    return fingerprints


def record_local_baseline(
    task_path: Path, project_root: Path, heartbeat: int
) -> dict[str, Any]:
    if heartbeat <= 0:
        raise WorkflowError("local baseline heartbeat must be positive")
    document, row = load_task(task_path)
    fingerprint = measurement_environment_fingerprint(row, project_root)
    entry = {
        "environment_fingerprint": fingerprint,
        "heartbeat": heartbeat,
        "recorded_at": utc_now(),
        "lean_version": command_output(
            ["lake", "env", "lean", "--version"], project_root
        ),
        "lake_manifest_sha256": sha256_file(project_root / "lake-manifest.json"),
        "instrumentation": (
            "project-command-heartbeat-v1"
            if is_project_resident(row)
            else "exact-heartbeat-audit-v1"
        ),
    }
    baselines = document.setdefault("local_baselines", [])
    if not isinstance(baselines, list):
        raise WorkflowError(f"{task_path}: local_baselines is not a list")
    baselines[:] = [
        item
        for item in baselines
        if not isinstance(item, dict)
        or item.get("environment_fingerprint") != fingerprint
    ]
    baselines.append(entry)
    task_path.write_text(
        json.dumps(document, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    return entry


def repo_root_from_script() -> Path:
    return Path(__file__).resolve().parent.parent


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Minimal one-proof Lean Refactor Arena workflow"
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    fetch = subparsers.add_parser("fetch-task", help="fetch one pinned warm-up row")
    fetch.add_argument("--name", required=True)
    fetch.add_argument("--output", type=Path, required=True)

    evaluate = subparsers.add_parser("evaluate", help="validate exactly one candidate")
    evaluate.add_argument("--task", type=Path, required=True)
    evaluate.add_argument("--candidate", type=Path, required=True)
    evaluate.add_argument("--project-root", type=Path, default=repo_root_from_script())
    evaluate.add_argument("--timeout", type=int, default=None, help="Quick whole-request allowance (default 60); exact per-process allowance (default 600). Trusted preparation may supply a larger explicit allowance.")
    evaluate.add_argument("--quick", action="store_true")
    evaluate.add_argument("--json-output", type=Path)
    evaluate.add_argument("--checkpoint-dir", type=Path)
    evaluate.add_argument(
        "--fingerprint-registry",
        type=Path,
        help=(
            "explicit guarded environment-fingerprint registry; unlike the ambient "
            "registry, a missing, stale, or malformed entry is an error"
        ),
    )

    lean_file = subparsers.add_parser(
        "lean-file",
        help="run one Lean file through the configured shared admission gate",
    )
    lean_file.add_argument("--path", type=Path, required=True)
    lean_file.add_argument(
        "--project-root", type=Path, default=repo_root_from_script()
    )
    lean_file.add_argument("--timeout", type=int, default=600)

    seed = subparsers.add_parser("seed-candidate", help="write one editable candidate")
    seed.add_argument("--task", type=Path, required=True)
    seed.add_argument("--output", type=Path, required=True)

    submission = subparsers.add_parser(
        "write-submission", help="emit the exact one-row Arena JSONL payload"
    )
    submission.add_argument("--task", type=Path, required=True)
    submission.add_argument("--candidate", type=Path, required=True)
    submission.add_argument("--output", type=Path, required=True)

    baseline = subparsers.add_parser(
        "record-baseline",
        help="record a measured original heartbeat for this environment",
    )
    baseline.add_argument("--task", type=Path, required=True)
    baseline.add_argument("--project-root", type=Path, default=repo_root_from_script())
    baseline.add_argument("--heartbeat", type=int, required=True)

    return parser


def main(argv: list[str] | None = None) -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    if hasattr(sys.stderr, "reconfigure"):
        sys.stderr.reconfigure(encoding="utf-8")
    args = build_parser().parse_args(argv)
    try:
        if args.command == "fetch-task":
            document = fetch_warmup_task(args.name, args.output)
            print(json.dumps(document["source"], ensure_ascii=False, indent=2))
        elif args.command == "evaluate":
            source_bytes = args.candidate.read_bytes()
            evaluation = evaluate_candidate(
                args.task,
                args.candidate,
                args.project_root,
                timeout_seconds=args.timeout if args.timeout is not None else (60 if args.quick else 600),
                quick=args.quick,
                fingerprint_registry=args.fingerprint_registry,
                source_bytes=source_bytes,
            )
            payload = evaluation_payload(evaluation)
            rendered = json.dumps(payload, ensure_ascii=False, indent=2)
            print(rendered)
            if args.json_output:
                args.json_output.write_text(rendered + "\n", encoding="utf-8")
            checkpoint_dir = evaluation_checkpoint_dir(args.checkpoint_dir)
            if checkpoint_dir:
                checkpoint = checkpoint_candidate(
                    args.candidate, evaluation, checkpoint_dir, source_bytes=source_bytes
                )
                print(f"checkpoint: {checkpoint}")
        elif args.command == "seed-candidate":
            write_candidate_seed(args.task, args.output)
            print(args.output.resolve())
        elif args.command == "lean-file":
            result = run_lean(args.path, args.project_root, args.timeout)
            require_lean_success(result, str(args.path))
            if result.output.strip():
                print(compact_lean_diagnostic(result.output))
        elif args.command == "write-submission":
            write_submission(args.task, args.candidate, args.output)
            print(args.output.resolve())
        elif args.command == "record-baseline":
            entry = record_local_baseline(args.task, args.project_root, args.heartbeat)
            print(json.dumps(entry, indent=2))
        return 0
    except (
        WorkflowError,
        OSError,
        json.JSONDecodeError,
    ) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
