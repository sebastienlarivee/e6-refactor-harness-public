"""Host-only requests to finish the admitted pass before stopping a proof cell.

Admission and request publication share a short lock. Native inference and host
validation never hold that lock, and no request sends a process signal.
"""
from __future__ import annotations

from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import stat
import uuid

from lean_tools import arena_workflow as arena
from lean_tools import process_memory

REQUEST_NAME = "host-pass-boundary-stop.json"
RESULT_NAME = "host-pass-boundary-stop-result.json"
TERMINAL_STATUSES = {
    "failed", "interrupted", "unknown_usage", "budget_reached", "completed",
    "diminishing_returns", "host_requested_stop",
}


@contextmanager
def admission_lock(root: Path):
    """Serialize host requests with the next pass's admission, not its work."""
    import fcntl
    root = Path(root).resolve()
    descriptor = os.open(root / ".pass-boundary.lock", os.O_CREAT | os.O_RDWR, 0o600)
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        yield
    finally:
        os.close(descriptor)


def _read(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8-sig"))
    if not isinstance(value, dict):
        raise ValueError("Pass-boundary control must be a JSON object")
    return value


def runner_control(pid: int) -> dict:
    identity = process_memory.linux_process_identity(pid)
    if identity is None:
        raise RuntimeError("Cannot establish the proof runner's Linux identity")
    return {"schema_version": 1, "strategy": "cooperative",
            "runner_pid": identity.pid, "runner_start_time": identity.start_time}


def _same_live_identity(pid: int, start_time: int) -> bool:
    identity = process_memory.linux_process_identity(pid)
    return identity is not None and identity.start_time == start_time


def _active_state(root: Path, pid: int, start_time: int) -> dict:
    state = _read(root / "state.json")
    if (state.get("root") != str(root) or state.get("pid") != pid
            or type(pid) is not int or pid <= 1
            or type(start_time) is not int or start_time < 0
            or not _same_live_identity(pid, start_time)):
        raise ValueError("Pass-boundary request does not match the live proof runner")
    # Explicit resumes may retain a previous epoch's results.json as evidence.
    if state.get("status") in TERMINAL_STATUSES:
        raise ValueError("Proof runner already has terminal evidence")
    return state


def _request(root: Path, strategy: str, after_pass: int, pid: int, start_time: int,
             reason: str) -> dict:
    if type(after_pass) is not int or after_pass < 0:
        raise ValueError("Requested boundary must be a nonnegative pass number")
    if not isinstance(reason, str) or not reason.strip():
        raise ValueError("A host stop requires an explicit operator reason")
    return {"schema_version": 1, "request_id": uuid.uuid4().hex,
            "strategy": strategy, "root": str(root), "reason": reason,
            "after_pass": after_pass, "next_pass": after_pass + 1,
            "runner_pid": pid, "runner_start_time": start_time,
            "requested_at": arena.utc_now()}


def _existing_request(root: Path, request: dict) -> dict | None:
    path = root / REQUEST_NAME
    if not path.exists():
        return None
    existing = _read(path)
    keys = ("schema_version", "strategy", "root", "reason", "after_pass",
            "next_pass", "runner_pid", "runner_start_time")
    if any(existing.get(key) != request[key] for key in keys):
        raise ValueError("A different host pass-boundary request already exists")
    return existing


def archive_prior_request(root: Path, control: dict) -> None:
    """Retain consumed older receipts while admitting a new runner epoch."""
    path = Path(root) / REQUEST_NAME
    if not path.exists():
        return
    request = _read(path)
    if (request.get("runner_pid"), request.get("runner_start_time")) == (
            control["runner_pid"], control["runner_start_time"]):
        return
    if _same_live_identity(request["runner_pid"], request["runner_start_time"]):
        raise ValueError("An earlier boundary-control runner is still alive")
    result_path = Path(root) / RESULT_NAME
    result = _read(result_path) if result_path.exists() else None
    if result is not None and result.get("request_id") != request["request_id"]:
        raise ValueError("Earlier host stop receipt does not match its request")
    archive = Path(root) / "host-controls" / "archive" / request["request_id"]
    archive.mkdir(parents=True, exist_ok=True)
    destination = archive / REQUEST_NAME
    if destination.exists():
        raise ValueError("Earlier pass-boundary request archive already exists")
    path.rename(destination)
    if result is not None:
        result_path.rename(archive / RESULT_NAME)


def request_stop_after_pass(root: Path, *, reason="operator_requested") -> dict:
    """Request the currently admitted pass; no credentials or provider calls."""
    root = Path(root).resolve()
    with admission_lock(root):
        state = _read(root / "state.json")
        control = state.get("pass_boundary_control", {})
        if not isinstance(control, dict) or control.get("strategy") != "cooperative":
            raise ValueError("This runner has no native cooperative boundary control")
        pid, start_time = control.get("runner_pid"), control.get("runner_start_time")
        state = _active_state(root, pid, start_time)
        after_pass = state.get("pass_number", len(state.get("passes", [])))
        request = _request(root, "cooperative", after_pass, pid, start_time, reason)
        existing = _existing_request(root, request)
        if existing is not None:
            return existing
        arena.write_json_atomic(root / REQUEST_NAME, request)
        return request


def cooperative_request(root: Path, state: dict, completed_pass: int) -> dict | None:
    """Called only at admission or after complete host finalization."""
    path = Path(root) / REQUEST_NAME
    if not path.exists():
        return None
    request = _read(path)
    control = state.get("pass_boundary_control", {})
    # An old epoch's receipt remains audit evidence, not an ambient stop switch.
    if (request.get("strategy") != "cooperative"
            or request.get("runner_pid") != control.get("runner_pid")
            or request.get("runner_start_time") != control.get("runner_start_time")):
        return None
    if (request.get("schema_version") != 1 or request.get("root") != str(Path(root).resolve())
            or type(request.get("after_pass")) is not int or request["after_pass"] < 0
            or request.get("next_pass") != request["after_pass"] + 1
            or not isinstance(request.get("reason"), str) or not request["reason"].strip()):
        raise ValueError("Malformed host pass-boundary request")
    return request if completed_pass >= request["after_pass"] else None


def stopped_record(request: dict, *, completed_pass: int, candidate_sha256: str,
                   budget: dict) -> dict:
    """Keep the operator decision separate from native/convergence evidence."""
    if budget.get("active_requests", 0) != 0:
        raise ValueError("Host stop cannot claim unsettled active inference requests")
    return {**request, "status": "host_requested_stop", "completed_pass": completed_pass,
            "candidate_sha256": candidate_sha256, "budget": dict(budget),
            "boundary": "after_validation_and_accounting", "recorded_at": arena.utc_now()}


def reserve_legacy_stop(root: Path, *, after_pass: int, runner_pid: int,
                        runner_start_time: int, expected_source: Path,
                        expected_source_sha256: str, reason="operator_requested") -> dict:
    """Reserve the exact next capsule in a runner with strict fresh admission.

    This intentionally uses the old runner's existing FileExistsError guard.
    Its original failed result is retained; only a separate host receipt calls
    the boundary an operator stop. The caller supplies pinned runner/source
    identities so this helper cannot discover a different experiment to stop.
    """
    root, expected_source = Path(root).resolve(), Path(expected_source).resolve()
    if type(after_pass) is not int or after_pass < 1:
        raise ValueError("Legacy reservation requires an active positive pass")
    source_bytes = expected_source.read_bytes()
    if hashlib.sha256(source_bytes).hexdigest() != expected_source_sha256:
        raise ValueError("Legacy capsule admission source changed")
    source = source_bytes.decode("utf-8")
    if ('if capsule.exists():' not in source
            or 'raise FileExistsError("Every pass requires a fresh capsule")' not in source):
        raise ValueError("Legacy source lacks the verified strict capsule guard")
    with admission_lock(root):
        state = _active_state(root, runner_pid, runner_start_time)
        if state.get("pass_number") != after_pass:
            raise ValueError("Legacy current pass changed before reservation")
        request = _request(root, "legacy_capsule_reservation", after_pass,
                           runner_pid, runner_start_time, reason)
        existing = _existing_request(root, request)
        if existing is not None:
            _verified_reservation(root, existing)
            return existing
        reservation = root / f"pass-{after_pass + 1:03d}"
        descriptor = os.open(reservation, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
        try:
            identity = os.fstat(descriptor)
            request.update(reservation={"path": str(reservation), "device": identity.st_dev,
                                        "inode": identity.st_ino, "size": 0},
                           admission_source={"path": str(expected_source),
                                             "sha256": expected_source_sha256},
                           native_terminal_status="failed",
                           expected_native_error="FileExistsError: Every pass requires a fresh capsule")
            # The reservation is durable before the receipt is published.
            os.fsync(descriptor)
            arena.write_json_atomic(root / REQUEST_NAME, request)
        except BaseException:
            # Retire only the inode we just created, never another capsule.
            if reservation.lstat().st_ino == identity.st_ino:
                reservation.unlink()
            raise
        finally:
            os.close(descriptor)
        return request


def _verified_reservation(root: Path, request: dict) -> Path:
    expected = root / f"pass-{request['next_pass']:03d}"
    reservation = request.get("reservation", {})
    if reservation.get("path") != str(expected):
        raise ValueError("Legacy reservation path does not match the exact next pass")
    identity = expected.lstat()
    if (not stat.S_ISREG(identity.st_mode) or identity.st_size != 0
            or identity.st_dev != reservation.get("device")
            or identity.st_ino != reservation.get("inode")):
        raise ValueError("Legacy reservation ownership or emptiness changed")
    return expected


def classify_legacy_stop(root: Path) -> dict | None:
    """Read-only evidence verdict; never relabel the old runner's results."""
    root = Path(root).resolve()
    path = root / REQUEST_NAME
    if not path.exists():
        return None
    request = _read(path)
    if request.get("strategy") != "legacy_capsule_reservation":
        return None
    if (request.get("root") != str(root) or request.get("schema_version") != 1
            or type(request.get("after_pass")) is not int or request["after_pass"] < 1
            or request.get("next_pass") != request["after_pass"] + 1
            or type(request.get("runner_pid")) is not int or request["runner_pid"] <= 1
            or type(request.get("runner_start_time")) is not int or request["runner_start_time"] < 0
            or request.get("expected_native_error") != "FileExistsError: Every pass requires a fresh capsule"):
        raise ValueError("Legacy host request has invalid identity or admission evidence")
    if _same_live_identity(request["runner_pid"], request["runner_start_time"]):
        return None
    result_path = root / "results.json"
    if not result_path.exists():
        return None
    result = _read(result_path)
    passes = result.get("passes", [])
    after_pass = request["after_pass"]
    if (result.get("status") != "failed"
            or result.get("root") != str(root)
            or result.get("pid") != request["runner_pid"]
            or result.get("error") != request.get("expected_native_error")
            or not isinstance(passes, list) or len(passes) != after_pass
            or passes[-1].get("pass_number") != after_pass
            or result.get("pass_number") != after_pass
            or result.get("broker_cleanup_error")):
        return None
    if not (root / f"pass-{after_pass:03d}" / "selection.json").is_file():
        return None
    selection = _read(root / f"pass-{after_pass:03d}" / "selection.json")
    if selection.get("sha256") != passes[-1].get("candidate_sha256"):
        return None
    budget = result.get("budget", {})
    if budget.get("active_requests", 0) != 0:
        return None
    record = stopped_record(request, completed_pass=after_pass,
                            candidate_sha256=passes[-1]["candidate_sha256"], budget=budget)
    record.update(observed_native_status=result["status"],
                  observed_native_error=result["error"],
                  results_sha256=hashlib.sha256(result_path.read_bytes()).hexdigest())
    return record


def archive_legacy_reservation(root: Path) -> dict:
    """Archive only a verified owned guard after the old proof runner exits."""
    root = Path(root).resolve()
    with admission_lock(root):
        record = classify_legacy_stop(root)
        if record is None:
            raise ValueError("Legacy operator stop is not fully finalized")
        result_path = root / RESULT_NAME
        if result_path.exists():
            saved = _read(result_path)
            if (saved.get("request_id") == record["request_id"]
                    and saved.get("results_sha256") == record["results_sha256"]
                    and not (root / f"pass-{record['next_pass']:03d}").exists()):
                return saved
            raise ValueError("Existing host stop result differs from final evidence")
        reservation = _verified_reservation(root, record)
        archive = root / "host-controls" / "archive" / record["request_id"]
        archive.mkdir(parents=True, exist_ok=False)
        destination = archive / f"pass-{record['next_pass']:03d}.reservation"
        reservation.rename(destination)
        record.update(reservation_archived_path=str(destination), archived_at=arena.utc_now())
        arena.write_json_atomic(result_path, record)
        return record
