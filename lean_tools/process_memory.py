"""Process-tree identities and cleanup, with Windows working-set telemetry.

The peak is the largest sampled sum, not an OS-maintained simultaneous tree peak.
Short-lived children and peaks between samples can be missed.
"""
from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import ctypes
import os
import signal
import sys
from dataclasses import dataclass
from pathlib import Path
import threading
import time
from functools import lru_cache
from typing import Any, Self


@dataclass(frozen=True)
class LinuxProcessIdentity:
    pid: int
    parent_pid: int
    process_group: int
    session: int
    start_time: int
    name: str


def linux_process_identity(pid: int) -> LinuxProcessIdentity | None:
    """Read the kernel start tick as well as the PID; names may contain spaces or ')'."""
    try:
        text = (Path("/proc") / str(pid) / "stat").read_text()
        closing = text.rindex(")")
        fields = text[closing + 2:].split()
        return LinuxProcessIdentity(
            int(text[:text.index("(")].strip()), int(fields[1]),
            int(fields[2]), int(fields[3]), int(fields[19]),
            text[text.index("(") + 1:closing],
        )
    except (OSError, ValueError, IndexError):
        return None


def capture_process_identity(process: Any) -> int | None:
    """Record a newly spawned direct child's kernel identity for later cleanup."""
    if sys.platform != "linux":
        return None
    pid = getattr(process, "pid", None)
    if type(pid) is not int or pid <= 1:
        return None
    row = linux_process_identity(pid)
    if row is None or row.parent_pid != os.getpid():
        return None
    try:
        process._lean_start_time = row.start_time
    except (AttributeError, TypeError):
        return None
    return row.start_time


def _linux_process_rows() -> dict[int, LinuxProcessIdentity]:
    rows = {}
    try:
        paths = list(Path("/proc").iterdir())
    except OSError:
        return rows
    for path in paths:
        if path.name.isdecimal() and (row := linux_process_identity(int(path.name))) is not None:
            rows[row.pid] = row
    return rows


def terminate_process_tree_pid(
    root_pid: int, *, expected_start_time: int | None = None, allow_self: bool = False,
) -> bool:
    """Kill an owned Linux tree, including descendants in separate sessions.

    Freeze the leader and discover/freeze descendants before killing any parent.
    Kernel start ticks and, where available, pidfds prevent signaling reused PIDs.
    Without a recorded start tick, the root must still be a live descendant of
    the caller. A saved PID caller must supply its previously recorded start tick.
    Caller ancestors are always refused; self requires explicit allow_self.
    """
    if sys.platform != "linux" or type(root_pid) is not int or root_pid <= 1:
        return False
    caller = os.getpid()
    rows = _linux_process_rows()
    root = rows.get(root_pid)
    if root is None or caller not in rows or (expected_start_time is not None and root.start_time != expected_start_time):
        return False
    if expected_start_time is None and not (allow_self and root_pid == caller):
        simple_rows = {pid: (row.parent_pid, row.name) for pid, row in rows.items()}
        if root_pid not in descendants_from_rows(caller, simple_rows):
            return False
    ancestors = set()
    ancestor = caller
    while ancestor in rows and ancestor not in ancestors:
        ancestors.add(ancestor)
        ancestor = rows[ancestor].parent_pid
    if root_pid in ancestors and not (allow_self and root_pid == caller):
        return False
    protected = ancestors - ({caller} if allow_self and root_pid == caller else set())
    pinned: dict[int, tuple[LinuxProcessIdentity, int | None]] = {}
    stopped: set[int] = set()

    def pin(row: LinuxProcessIdentity) -> bool:
        if row.pid in protected:
            return False
        if row.pid in pinned:
            return pinned[row.pid][0].start_time == row.start_time
        descriptor = None
        if hasattr(os, "pidfd_open") and hasattr(signal, "pidfd_send_signal"):
            try:
                descriptor = os.pidfd_open(row.pid)
            except OSError:
                pass
        current = linux_process_identity(row.pid)
        if current is None or current.start_time != row.start_time:
            if descriptor is not None:
                os.close(descriptor)
            return False
        pinned[row.pid] = (row, descriptor)
        return True

    def send(pid: int, signum: int) -> bool:
        row, descriptor = pinned[pid]
        try:
            if descriptor is not None:
                signal.pidfd_send_signal(descriptor, signum)
            else:
                current = linux_process_identity(pid)
                if current is None or current.start_time != row.start_time:
                    return False
                os.kill(pid, signum)
            return True
        except OSError:
            return False

    if not pin(root):
        return False
    try:
        if root_pid != caller and send(root_pid, signal.SIGSTOP):
            stopped.add(root_pid)
        depths = {root_pid: 0}
        # Stopping parents before their children bounds new forks. Re-snapshot
        # to include any child created during the first ancestry walk.
        for _ in range(4):
            current_rows = _linux_process_rows()
            current_root = current_rows.get(root_pid)
            if current_root is None or current_root.start_time != root.start_time:
                break
            simple_rows = {pid: (row.parent_pid, row.name) for pid, row in current_rows.items()}
            discovered = descendants_from_rows(root_pid, simple_rows)
            # A session led by this still-pinned root also owns group members
            # whose parents exited before this snapshot. Never signal a group.
            if root.process_group == root.pid and root.session == root.pid:
                for pid, row in current_rows.items():
                    if row.process_group == root.pid and pid != root_pid:
                        discovered.setdefault(pid, (row.parent_pid, row.name, 1))
            added = False
            for pid, (_parent, _name, depth) in sorted(discovered.items(), key=lambda item: item[1][2]):
                row = current_rows[pid]
                if pid not in pinned and pin(row):
                    added = True
                    depths[pid] = depth
                    if send(pid, signal.SIGSTOP):
                        stopped.add(pid)
            if not added:
                break
        # Individual identity-pinned signals cover detached setsid children
        # without risking the caller's or an unrelated process group.
        signaled = False
        for pid in sorted(pinned, key=lambda item: depths.get(item, 0), reverse=True):
            if pid != root_pid:
                signaled = send(pid, signal.SIGKILL) or signaled
        return send(root_pid, signal.SIGKILL) or signaled
    finally:
        # If permission or a transient error blocked a kill, do not leave a
        # process suspended merely because cleanup was best effort.
        for pid in stopped:
            send(pid, signal.SIGCONT)
        for _row, descriptor in pinned.values():
            if descriptor is not None:
                os.close(descriptor)


class _WindowsBackend:
    def __init__(self) -> None:
        from ctypes import wintypes

        class ProcessEntry(ctypes.Structure):
            _fields_ = [
                ("dwSize", wintypes.DWORD), ("cntUsage", wintypes.DWORD),
                ("th32ProcessID", wintypes.DWORD), ("th32DefaultHeapID", ctypes.c_size_t),
                ("th32ModuleID", wintypes.DWORD), ("cntThreads", wintypes.DWORD),
                ("th32ParentProcessID", wintypes.DWORD), ("pcPriClassBase", wintypes.LONG),
                ("dwFlags", wintypes.DWORD), ("szExeFile", wintypes.WCHAR * 260),
            ]

        class MemoryCounters(ctypes.Structure):
            _fields_ = [
                ("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD),
                ("PeakWorkingSetSize", ctypes.c_size_t), ("WorkingSetSize", ctypes.c_size_t),
                ("QuotaPeakPagedPoolUsage", ctypes.c_size_t), ("QuotaPagedPoolUsage", ctypes.c_size_t),
                ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t), ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                ("PagefileUsage", ctypes.c_size_t), ("PeakPagefileUsage", ctypes.c_size_t),
            ]

        self.entry_type = ProcessEntry
        self.counters_type = MemoryCounters
        self.kernel = ctypes.WinDLL("kernel32", use_last_error=True)
        self.psapi = ctypes.WinDLL("psapi", use_last_error=True)
        declarations = [
            (self.kernel.CreateToolhelp32Snapshot, [wintypes.DWORD, wintypes.DWORD], wintypes.HANDLE),
            (self.kernel.Process32FirstW, [wintypes.HANDLE, ctypes.POINTER(ProcessEntry)], wintypes.BOOL),
            (self.kernel.Process32NextW, [wintypes.HANDLE, ctypes.POINTER(ProcessEntry)], wintypes.BOOL),
            (self.kernel.OpenProcess, [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD], wintypes.HANDLE),
            (self.kernel.CloseHandle, [wintypes.HANDLE], wintypes.BOOL),
            (self.psapi.GetProcessMemoryInfo, [wintypes.HANDLE, ctypes.POINTER(MemoryCounters), wintypes.DWORD], wintypes.BOOL),
        ]
        for function, arguments, result in declarations:
            function.argtypes = arguments
            function.restype = result

    def rows(self) -> dict[int, tuple[int, str]]:
        snapshot = self.kernel.CreateToolhelp32Snapshot(0x00000002, 0)
        if snapshot == ctypes.c_void_p(-1).value:
            return {}
        rows: dict[int, tuple[int, str]] = {}
        try:
            entry = self.entry_type()
            entry.dwSize = ctypes.sizeof(entry)
            succeeded = self.kernel.Process32FirstW(snapshot, ctypes.byref(entry))
            while succeeded:
                rows[int(entry.th32ProcessID)] = (int(entry.th32ParentProcessID), str(entry.szExeFile))
                succeeded = self.kernel.Process32NextW(snapshot, ctypes.byref(entry))
        finally:
            self.close(snapshot)
        return rows

    def open(self, pid: int) -> Any:
        return self.kernel.OpenProcess(0x1000 | 0x0010, False, pid)

    def working_set(self, handle: Any) -> int | None:
        counters = self.counters_type()
        counters.cb = ctypes.sizeof(counters)
        if not self.psapi.GetProcessMemoryInfo(handle, ctypes.byref(counters), counters.cb):
            return None
        return int(counters.WorkingSetSize)

    def close(self, handle: Any) -> None:
        self.kernel.CloseHandle(handle)


@lru_cache(maxsize=1)
def _backend() -> _WindowsBackend | None:
    return _WindowsBackend() if os.name == "nt" else None


def descendants_from_rows(root_pid: int, rows: dict[int, tuple[int, str]]) -> dict[int, tuple[int, str, int]]:
    children: dict[int, list[tuple[int, str]]] = {}
    for pid, (parent, name) in rows.items():
        children.setdefault(parent, []).append((pid, name))
    descendants: dict[int, tuple[int, str, int]] = {}
    seen = {root_pid}
    frontier = [(root_pid, 0)]
    while frontier:
        parent, depth = frontier.pop()
        for pid, name in children.get(parent, []):
            if pid not in seen:
                seen.add(pid)
                descendants[pid] = (parent, name, depth + 1)
                frontier.append((pid, depth + 1))
    return descendants


def process_descendants(root_pid: int) -> dict[int, tuple[int, str, int]]:
    backend = _backend()
    if backend:
        return descendants_from_rows(root_pid, backend.rows())
    if sys.platform == "linux":
        rows = {pid: (row.parent_pid, row.name) for pid, row in _linux_process_rows().items()}
        return descendants_from_rows(root_pid, rows)
    return {}


class ProcessTreeMemorySampler:
    def __init__(self, root_pid: int, *, backend: Any = None, discovery_interval: float = 0.5) -> None:
        self.root_pid = root_pid
        self.backend = _backend() if backend is None else backend
        self.discovery_interval = discovery_interval
        self.handles: dict[int, Any] = {}
        self.next_discovery = float("-inf")
        self.peak_bytes: int | None = None
        self.sample_count = 0
        self.observed_process_count = 0

    def sample(self, now: float | None = None) -> int | None:
        if self.backend is None:
            return None
        now = time.monotonic() if now is None else now
        if now >= self.next_discovery:
            pids = [self.root_pid, *descendants_from_rows(self.root_pid, self.backend.rows())]
            for pid in pids:
                if pid not in self.handles:
                    handle = self.backend.open(pid)
                    if handle:
                        # Retained handles pin process identities, including after exit.
                        self.handles[pid] = handle
                        self.observed_process_count += 1
            self.next_discovery = now + self.discovery_interval
        values = [value for handle in self.handles.values() if (value := self.backend.working_set(handle)) is not None]
        self.sample_count += 1
        current = sum(values) if values else None
        if current is not None:
            self.peak_bytes = max(self.peak_bytes or 0, current)
        return current

    def close(self) -> None:
        if self.backend is not None:
            for handle in self.handles.values():
                self.backend.close(handle)
        self.handles.clear()


class ProcessTreeMemoryMonitor:
    def __init__(self, root_pid: int, *, sample_interval: float = 0.25) -> None:
        self.sampler = ProcessTreeMemorySampler(root_pid)
        self.sample_interval = sample_interval
        self.stopped = threading.Event()
        self.thread: threading.Thread | None = None
        self.error: str | None = None

    @property
    def peak_bytes(self) -> int | None:
        return self.sampler.peak_bytes

    def metadata(self) -> dict[str, Any]:
        return {
            "method": "sampled_process_tree_working_set",
            "sample_interval_seconds": self.sample_interval,
            "discovery_interval_seconds": self.sampler.discovery_interval,
            "sample_count": self.sampler.sample_count,
            "observed_process_count": self.sampler.observed_process_count,
            "error": self.error,
        }

    def _sample(self) -> None:
        try:
            self.sampler.sample()
        except (OSError, ValueError) as error:
            self.error = str(error)

    def __enter__(self) -> Self:
        if self.sampler.backend is not None:
            self._sample()

            def watch() -> None:
                while not self.stopped.wait(self.sample_interval):
                    self._sample()

            self.thread = threading.Thread(target=watch, daemon=True, name="process-memory")
            self.thread.start()
        return self

    def __exit__(self, *exc: object) -> None:
        self.stopped.set()
        if self.thread is not None:
            self.thread.join(timeout=2)
            if self.thread.is_alive():
                # Telemetry must not hold a finished compiler's permit forever.
                # Avoid closing handles concurrently with a blocked sampler.
                self.error = "memory sampler did not stop within cleanup watchdog"
                return
            self._sample()
        self.sampler.close()


def process_tree_working_set_bytes(root_pid: int) -> int | None:
    sampler = ProcessTreeMemorySampler(root_pid)
    try:
        return sampler.sample()
    finally:
        sampler.close()
