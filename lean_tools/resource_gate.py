from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import datetime as dt
import json
import math
import os
import re
import threading
import time
import uuid
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from lean_tools import check_budget

if os.name == "posix":
    import fcntl


class ResourceGateError(RuntimeError):
    pass


class ResourceGateTimeout(ResourceGateError):
    """A request expired before acquiring a resource; no Lean work started."""


class ResourceGateCancelled(ResourceGateError):
    """The owner closed while the request was still queued."""


@dataclass(frozen=True)
class PermitLease:
    resource: str
    queued_at: str
    admitted_at: str
    queue_wait_seconds: float
    slot: int | None
    token: str | None


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


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
                return ctypes.get_last_error() == 5
            try:
                exit_code = wintypes.DWORD()
                return (
                    bool(kernel32.GetExitCodeProcess(handle, ctypes.byref(exit_code)))
                    and exit_code.value == still_active
                )
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


def write_exclusive_json(path: Path, value: dict[str, Any]) -> int:
    descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    try:
        os.write(
            descriptor,
            (json.dumps(value, ensure_ascii=False) + "\n").encode("utf-8"),
        )
    except Exception:
        os.close(descriptor)
        try:
            path.unlink()
        except OSError:
            pass
        raise
    return descriptor


def read_json(path: Path) -> dict[str, Any] | None:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
        return value if isinstance(value, dict) else None
    except (OSError, json.JSONDecodeError):
        return None


def stale_unreadable(path: Path, grace_seconds: float = 2.0) -> bool:
    try:
        return time.time() - path.stat().st_mtime >= grace_seconds
    except OSError:
        return False


def unlink_with_retry(path: Path, timeout_seconds: float = 5.0) -> bool:
    started = time.perf_counter()
    while True:
        try:
            path.unlink()
            return True
        except FileNotFoundError:
            return True
        except PermissionError:
            if time.perf_counter() - started >= timeout_seconds:
                return False
            time.sleep(0.01)


class FilePermitPool:
    def __init__(
        self,
        root: Path,
        resource: str,
        capacity: int,
        *,
        aging_seconds: float = 120.0,
        poll_seconds: float = 0.05,
    ) -> None:
        if capacity < 1:
            raise ResourceGateError("permit capacity must be positive")
        if not resource or any(character in resource for character in "\\/:"):
            raise ResourceGateError(f"invalid permit resource: {resource!r}")
        self.root = root.resolve() / resource
        self.resource = resource
        self.capacity = capacity
        self.aging_seconds = max(1.0, aging_seconds)
        self.poll_seconds = max(0.01, poll_seconds)
        self.requests = self.root / "requests"
        self.holders = self.root / "holders"
        self.requests.mkdir(parents=True, exist_ok=True)
        self.holders.mkdir(parents=True, exist_ok=True)

    @contextmanager
    def _mutation_lock(self) -> Iterator[None]:
        if os.name != "posix":
            yield
            return
        descriptor = os.open(self.root / ".mutation.lock", os.O_CREAT | os.O_RDWR, 0o600)
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX)
            yield
        finally:
            os.close(descriptor)

    def _write_lease(self, path: Path, payload: dict[str, Any]) -> int | None:
        # Cleanup shares this short lock so a published file cannot be reaped
        # between exclusive creation and acquiring its lifetime ownership lock.
        with self._mutation_lock():
            descriptor = write_exclusive_json(path, payload)
            if os.name != "posix":
                os.close(descriptor)
                return None
            try:
                fcntl.flock(descriptor, fcntl.LOCK_EX)
            except BaseException:
                os.close(descriptor)
                unlink_with_retry(path)
                raise
            return descriptor

    def _clean_stale(self, paths: list[Path]) -> None:
        with self._mutation_lock():
            for path in paths:
                payload = read_json(path)
                if os.name == "posix" and payload is not None and payload.get("ownership") == "flock":
                    try:
                        descriptor = os.open(path, os.O_RDONLY)
                    except FileNotFoundError:
                        continue
                    try:
                        try:
                            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        except BlockingIOError:
                            continue
                        # No live owner retains this lock, even if its recorded
                        # PID belongs to an unrelated process in our namespace.
                        # The mutation lock prevents replacement while unlinking.
                        unlink_with_retry(path)
                    finally:
                        os.close(descriptor)
                    continue
                # Legacy and Windows leases retain their PID-based recovery.
                owner = payload.get("pid") if payload is not None else None
                stale = (isinstance(owner, int) and not process_is_running(owner)) or (
                    owner is None and stale_unreadable(path)
                )
                if stale:
                    unlink_with_retry(path)

    def _ordered_requests(self) -> list[Path]:
        paths = sorted(self.requests.glob("*.request"))
        self._clean_stale(paths)
        now = time.time()
        ordered: list[tuple[int, float, str, Path]] = []
        for path in sorted(self.requests.glob("*.request")):
            payload = read_json(path)
            if payload is None:
                continue
            priority = payload.get("priority", 10)
            created = payload.get("created_epoch", now)
            if not isinstance(priority, int) or not isinstance(created, (int, float)):
                continue
            waited = max(0.0, now - float(created))
            effective_priority = max(0, priority - int(waited // self.aging_seconds))
            ordered.append((effective_priority, float(created), path.name, path))
        return [item[3] for item in sorted(ordered)]

    def _available_slots(self) -> list[int]:
        holders = sorted(self.holders.glob("slot-*.json"))
        self._clean_stale(holders)
        occupied = {
            int(match.group(1))
            for path in self.holders.glob("slot-*.json")
            if (match := re.fullmatch(r"slot-(\d+)\.json", path.name))
        }
        return [slot for slot in range(self.capacity) if slot not in occupied]

    @contextmanager
    def acquire(
        self,
        *,
        priority: int = 10,
        timeout_seconds: float | None = None,
        metadata: dict[str, Any] | None = None,
        cancel_event: threading.Event | None = None,
    ) -> Iterator[PermitLease]:
        if priority < 0:
            raise ResourceGateError("permit priority must be nonnegative")
        if timeout_seconds is not None and (
            not math.isfinite(timeout_seconds) or timeout_seconds < 0
        ):
            raise ResourceGateError("permit timeout must be finite and nonnegative")
        token = uuid.uuid4().hex
        queued_at = utc_now()
        queued_epoch = time.time()
        queued_perf = time.perf_counter()
        request_path = self.requests / (
            f"{time.time_ns():020d}-{os.getpid()}-{token}.request"
        )
        request_payload = {
            "schema_version": 1,
            "resource": self.resource,
            "token": token,
            "pid": os.getpid(),
            "priority": priority,
            "created_at": queued_at,
            "created_epoch": queued_epoch,
            "metadata": metadata or {},
        }
        if os.name == "posix":
            # flock ownership is shared across mount/user/PID namespaces and
            # released by the kernel on exit. PIDs remain diagnostic metadata.
            request_payload.update(schema_version=2, ownership="flock")
        request_descriptor = self._write_lease(request_path, request_payload)
        holder_descriptor: int | None = None
        holder_path: Path | None = None
        slot: int | None = None
        try:
            while holder_path is None:
                if cancel_event is not None and cancel_event.is_set():
                    raise ResourceGateCancelled(f"cancelled waiting for {self.resource} permit")
                if (
                    timeout_seconds is not None
                    and time.perf_counter() - queued_perf >= timeout_seconds
                ):
                    raise ResourceGateTimeout(
                        f"timed out waiting for {self.resource} permit"
                    )
                ordered = self._ordered_requests()
                try:
                    position = ordered.index(request_path)
                except ValueError:
                    if not request_path.exists():
                        raise ResourceGateError(
                            f"{self.resource} permit request disappeared"
                        )
                    time.sleep(self.poll_seconds)
                    continue
                available = self._available_slots()
                if position < len(available):
                    for candidate_slot in available:
                        candidate = self.holders / f"slot-{candidate_slot}.json"
                        try:
                            holder_descriptor = self._write_lease(
                                candidate,
                                {
                                    **request_payload,
                                    "admitted_at": utc_now(),
                                    "slot": candidate_slot,
                                },
                            )
                        except FileExistsError:
                            continue
                        holder_path = candidate
                        slot = candidate_slot
                        break
                if holder_path is None:
                    time.sleep(self.poll_seconds)

            if not unlink_with_retry(request_path):
                raise ResourceGateError(
                    f"could not retire admitted {self.resource} request"
                )
            admitted_at = utc_now()
            yield PermitLease(
                resource=self.resource,
                queued_at=queued_at,
                admitted_at=admitted_at,
                queue_wait_seconds=time.perf_counter() - queued_perf,
                slot=slot,
                token=token,
            )
        finally:
            try:
                unlink_with_retry(request_path)
                if holder_path is not None:
                    payload = read_json(holder_path)
                    if (
                        payload is not None
                        and payload.get("token") == token
                        and not unlink_with_retry(holder_path)
                    ):
                        raise ResourceGateError(
                            f"could not release {self.resource} permit slot {slot}"
                        )
            finally:
                if request_descriptor is not None:
                    os.close(request_descriptor)
                if holder_descriptor is not None:
                    os.close(holder_descriptor)


@contextmanager
def permit_from_environment(
    resource: str,
    *,
    priority: int = 10,
    metadata: dict[str, Any] | None = None,
    timeout_seconds: float | None = None,
    cancel_event: threading.Event | None = None,
) -> Iterator[PermitLease]:
    """Acquire with the tighter of the caller's remaining budget and queue policy."""
    timeout_seconds = check_budget.remaining(timeout_seconds)
    if cancel_event is not None and cancel_event.is_set():
        raise ResourceGateCancelled(f"cancelled waiting for {resource} permit")
    if timeout_seconds is not None:
        if not math.isfinite(timeout_seconds) or timeout_seconds < 0:
            raise ResourceGateError("permit timeout must be finite and nonnegative")
        if timeout_seconds == 0:
            raise ResourceGateTimeout(f"timed out waiting for {resource} permit")
    prefix = f"LEAN_REFACTOR_{resource.upper()}"
    root_value = os.environ.get(f"{prefix}_GATE")
    capacity_value = os.environ.get(f"{prefix}_CAPACITY")
    queued_at = utc_now()
    if not root_value and not capacity_value:
        yield PermitLease(resource, queued_at, utc_now(), 0.0, None, None)
        return
    if not root_value or not capacity_value:
        raise ResourceGateError(
            f"{prefix}_GATE and {prefix}_CAPACITY must be configured together"
        )
    try:
        capacity = int(capacity_value)
        timeout_value = os.environ.get(f"{prefix}_QUEUE_TIMEOUT")
        timeout = float(timeout_value) if timeout_value else None
    except ValueError as error:
        raise ResourceGateError(f"invalid {resource} gate configuration") from error
    if timeout_seconds is not None:
        timeout = (
            min(timeout, timeout_seconds) if timeout is not None else timeout_seconds
        )
    pool = FilePermitPool(Path(root_value), resource, capacity)
    with pool.acquire(
        priority=priority,
        timeout_seconds=timeout,
        metadata=metadata,
        cancel_event=cancel_event,
    ) as lease:
        yield lease
