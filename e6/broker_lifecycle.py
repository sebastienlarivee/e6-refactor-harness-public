"""Host-owned warm Lean broker and private pass-boundary control pipe.

No candidate histories or capabilities are written into a new model capsule.
The subprocess keeps telemetry environment stable while its parent switches
scratch, artifacts, event spools, and evaluation caches between fresh passes.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import queue
import secrets
import signal
import subprocess
import sys
import threading
import time
from types import SimpleNamespace

from lean_tools import arena_workflow as arena
from lean_tools import persistent_quick_workflow as persistent
from lean_tools import resource_gate, process_memory
from lean_tools import capsule as swarm
from .config import REPO_ROOT
from .experiment import DEFAULT_SPEC, experiment_spec
from .runtime import RuntimeContext, create_environment_directories

HERE = Path(__file__).resolve().parent
SELF_IDENTITY = None

BROKER_ENV = (arena.PERSISTENT_QUICK_ENDPOINT_ENV, arena.PERSISTENT_QUICK_TOKEN_ENV,
              arena.PERSISTENT_QUICK_PROJECT_ROOT_ENV, persistent.FEEDBACK_SUPPORT_ENV)
PRIVATE_HOST_ENV = ("E6_BASELINE_CACHE", "E6_BASELINE_SEEDS", "E6_CODEX_HOME",
                    "LRH_SERIAL_MODEL_TOKEN", "OPENAI_API_KEY", "OPENROUTER_API_KEY")


def host_environment(config, root):
    values = dict(os.environ)
    for name in (*BROKER_ENV, *PRIVATE_HOST_ENV):
        values.pop(name, None)
    for name in ("LEAN_REFACTOR_LEAN_QUEUE_TIMEOUT", "LEAN_REFACTOR_COLD_LEAN_QUEUE_TIMEOUT",
                 "LEAN_REFACTOR_COLD_LEAN_GATE", "LEAN_REFACTOR_COLD_LEAN_CAPACITY"):
        values.pop(name, None)
    values.update(RuntimeContext.resolve(root, config).environment(
        broker=True, registry=Path(config["fingerprint_registry"])))
    create_environment_directories(values, checkpoint=True)
    return values


class BrokerHost:
    """One owned subprocess, reused across every model pass in a proof cell."""
    def __init__(self, config, root, *, startup_timeout_seconds=None, request_timeout_seconds=None):
        self.config = config
        self.root = Path(root).resolve()
        self.work = self.root / "warm-broker"
        spec = experiment_spec(config)
        self.startup_timeout_seconds = (spec.broker_startup_timeout_seconds
            if startup_timeout_seconds is None else startup_timeout_seconds)
        self.request_timeout_seconds = (spec.lean_request_timeout_seconds
            if request_timeout_seconds is None else request_timeout_seconds)
        self.process = None
        self._replies = queue.Queue()
        self._reader = None
        self._stderr = None
        self._sequence = 0
        self._closed = False
        self._ready = False
        self._status_snapshot = {"status": "starting"}

    def start(self):
        if self.process is not None or self._closed:
            raise RuntimeError("Warm broker host is one-use")
        self.work.mkdir(parents=True, exist_ok=True)
        parent_identity = process_memory.linux_process_identity(os.getpid())
        if parent_identity is None:
            raise RuntimeError("Cannot record warm broker owner's Linux process identity")
        argv = [sys.executable, "-m", "e6.broker_lifecycle", "--serve", "--root", str(self.root),
                "--parent-pid", str(parent_identity.pid), "--parent-start-time", str(parent_identity.start_time),
                "--startup-seconds", str(self.startup_timeout_seconds),
                "--request-seconds", str(self.request_timeout_seconds)]
        self._stderr = (self.work / "host.stderr.log").open("w", encoding="utf-8")
        options = {"start_new_session": True}
        try:
            self.process = subprocess.Popen(argv, cwd=REPO_ROOT, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=self._stderr, text=True, encoding="utf-8", errors="strict",
                env=host_environment(self.config, self.root), **options)
            process_memory.capture_process_identity(self.process)
            assert self.process.stdout is not None
            def reader():
                try:
                    for line in self.process.stdout:
                        self._replies.put(line)
                finally:
                    self._replies.put(None)
            self._reader = threading.Thread(target=reader, name="e6-warm-host-control", daemon=True)
            self._reader.start()
            # Startup's real Lean work is bounded inside the host. Resource
            # queueing is allowed to wait, and EOF still detects host death.
            self._receive(0, None)
            self._ready = True
        except BaseException:
            self.close()
            raise
        return self

    def _receive(self, identity, timeout):
        try:
            line = self._replies.get(timeout=timeout)
        except queue.Empty as error:
            raise RuntimeError("Warm broker private control deadline expired; inspect warm-broker/host-state.json") from error
        if line is None:
            raise RuntimeError("Warm broker host exited before replying; inspect warm-broker/host-state.json")
        reply = json.loads(line)
        if not isinstance(reply, dict) or reply.get("id") != identity:
            raise RuntimeError("Warm broker private control protocol mismatch")
        if isinstance(reply.get("status_snapshot"), dict):
            self._status_snapshot = reply["status_snapshot"]
        if reply.get("ok") is not True:
            raise RuntimeError("Warm broker control failed: " + str(reply.get("error", "unknown failure")))
        return reply

    def _request(self, operation, *, control_timeout=None, **payload):
        if self.process is None or self.process.poll() is not None or self._closed:
            raise RuntimeError("Warm broker host is unavailable")
        self._sequence += 1
        assert self.process.stdin is not None
        self.process.stdin.write(json.dumps({"id": self._sequence, "operation": operation, **payload}) + "\n")
        self.process.stdin.flush()
        # Both begin/end can wait for an old authenticated operation to leave
        # admission. The host bounds actual work; explicit shutdown stays finite.
        return self._receive(self._sequence, control_timeout)

    def begin_pass(self, pass_number):
        return self._request("begin_pass", pass_number=pass_number)["environment"]

    def end_pass(self):
        self._request("end_pass")

    def status(self):
        try:
            saved = json.loads((self.work / "host-state.json").read_text(encoding="utf-8"))
            if isinstance(saved, dict) and saved.get("updated_at", "") >= self._status_snapshot.get("updated_at", ""):
                self._status_snapshot = saved
        except (OSError, ValueError):
            pass
        return dict(self._status_snapshot)

    def close(self):
        if self._closed:
            return
        process = self.process
        try:
            if process is not None and process.poll() is None:
                try:
                    if not self._ready:
                        raise RuntimeError("Broker startup has not completed")
                    self._request("shutdown", control_timeout=10)
                    process.wait(timeout=10)
                except (OSError, RuntimeError, ValueError, subprocess.TimeoutExpired):
                    arena.terminate_process_tree(process)
                    process.wait(timeout=10)
        finally:
            self._closed = True
            if process is not None:
                for stream in (process.stdin, process.stdout):
                    if stream is not None:
                        stream.close()
            if self._reader is not None:
                self._reader.join(timeout=2)
            if self._stderr is not None:
                self._stderr.close()


class PassBroker(persistent.PersistentQuickBroker):
    """Serialize capability changes with complete authenticated operations."""
    def __init__(self, *args, recorder=None, **kwargs):
        super().__init__(*args, **kwargs)
        self.capability_lock = threading.RLock()
        self.recorder = recorder
        self.pass_number = 0
        self.pass_active = False

    def _handle_connection(self, connection):
        with self.capability_lock:
            super()._handle_connection(connection)

    def start(self):
        if self.recorder:
            self.recorder(phase="broker_start")
        return super().start()

    def prewarm(self, **kwargs):
        if self.recorder:
            self.recorder(phase="canonical_prewarm")
        return super().prewarm(**kwargs)

    def begin_pass(self, pass_number, timeout_seconds=DEFAULT_SPEC.lean_request_timeout_seconds):
        with self.capability_lock:
            if type(pass_number) is not int or pass_number <= self.pass_number or self.pass_active:
                raise RuntimeError("Fresh broker pass numbers must increase without overlapping passes")
            # All old connections have either finished or will authenticate after
            # this transition and fail. A fresh capability is never logged.
            self.token = secrets.token_urlsafe(32)
            readiness = self.prewarm(timeout_seconds=timeout_seconds)
            if not readiness.get("ready"):
                raise RuntimeError("Canonical broker reset did not report readiness")
            self.pass_number, self.pass_active = pass_number, True
            return self.environment()

    def end_pass(self):
        with self.capability_lock:
            if not self.pass_active:
                raise RuntimeError("No active broker pass to retire")
            self.token = secrets.token_urlsafe(32)
            self.pass_active = False


def terminate_orphan_host():
    """Kill this owned process tree even if it is blocked in initial prewarm."""
    try:
        process_memory.terminate_process_tree_pid(
            os.getpid(), expected_start_time=SELF_IDENTITY.start_time if SELF_IDENTITY else None,
            allow_self=True)
    finally:
        os._exit(1)


def check_parent_liveness(parent_pid, record, *, parent_start_time=None):
    alive = resource_gate.process_is_running(parent_pid)
    if alive and parent_start_time is not None:
        current = process_memory.linux_process_identity(parent_pid)
        alive = current is not None and current.start_time == parent_start_time
    if not alive:
        try:
            record(status="orphaned", phase="parent_exit", finished_at=arena.utc_now())
        finally:
            # Diagnostic I/O must never leave an orphaned Lean tree resident.
            terminate_orphan_host()


def serve(root, parent_pid, startup_seconds, request_seconds, *, parent_start_time=None):
    global SELF_IDENTITY
    SELF_IDENTITY = process_memory.linux_process_identity(os.getpid())
    root = Path(root).resolve()
    config = json.loads((root / "config.json").read_text(encoding="utf-8"))
    values = host_environment(config, root)
    os.environ.clear()
    os.environ.update(values)
    work = root / "warm-broker"
    status = {"status": "starting", "phase": "measurement_support", "pid": os.getpid(),
              "parent_pid": parent_pid, "parent_start_time": parent_start_time,
              "start_time": SELF_IDENTITY.start_time if SELF_IDENTITY else None,
              "root": str(root), "started_at": arena.utc_now(),
              "startup_timeout_seconds": startup_seconds, "request_timeout_seconds": request_seconds,
              "pass_number": 0, "pass_active": False, "canonical_resets": 0}
    status_lock = threading.Lock()
    stopped = threading.Event()
    broker_holder = SimpleNamespace(broker=None)

    def record(**updates):
        with status_lock:
            status.update(updates, updated_at=arena.utc_now())
            try:
                arena.write_json_atomic(work / "host-state.json", dict(status))
            except OSError as error:
                # Status is telemetry. A locked file cannot abort a completed
                # paid pass after its capability has already been retired.
                status["telemetry_write_failures"] = status.get("telemetry_write_failures", 0) + 1
                status["last_telemetry_error"] = f"{type(error).__name__}: {error}"

    def watch_parent():
        sampled = 0.0
        while not stopped.wait(1):
            check_parent_liveness(parent_pid, record, parent_start_time=parent_start_time)
            broker = broker_holder.broker
            if broker is not None and time.monotonic() - sampled >= 5:
                sampled = time.monotonic()
                try:
                    session = broker.session
                    record(lean_pid=session.process.pid if session and session.process else None,
                           working_set_bytes=session.tree_working_set_bytes() if session else None,
                           session_request_count=broker.session_request_count)
                except Exception:
                    # A disappearing process or status sharing error must not
                    # stop the independent parent-liveness checks.
                    continue

    def reply(identity, **payload):
        # stdout is a private inherited pipe, never a console or archive log.
        with status_lock:
            snapshot = dict(status)
        sys.stdout.write(json.dumps({"id": identity, "status_snapshot": snapshot, **payload}) + "\n")
        sys.stdout.flush()

    record()
    watcher = threading.Thread(target=watch_parent, name="e6-broker-parent-watch", daemon=True)
    watcher.start()
    original_class = swarm.persistent_quick.PersistentQuickBroker
    def factory(*args, **kwargs):
        broker = PassBroker(*args, recorder=record, **kwargs)
        broker_holder.broker = broker
        return broker
    swarm.persistent_quick.PersistentQuickBroker = factory
    identity = 0
    try:
        _, row = arena.load_task(Path(config["task"]))
        broker = swarm.start_quick_broker(row, Path(config["primary"]), work, request_seconds,
                                          startup_timeout_seconds=startup_seconds)
        record(status="ready", phase="idle", canonical_source_sha256=arena.sha256_bytes(broker.initial_source.encode("utf-8")))
        reply(0, ok=True)
        for line in sys.stdin:
            request = json.loads(line)
            identity = request["id"]
            operation = request["operation"]
            if operation == "begin_pass":
                record(status="resetting", phase="canonical_reset", pass_number=request["pass_number"])
                values = broker.begin_pass(request["pass_number"], request_seconds)
                record(status="ready", phase="model_pass", pass_active=True,
                       canonical_resets=status["canonical_resets"] + 1)
                reply(identity, ok=True, environment=values)
            elif operation == "end_pass":
                broker.end_pass()
                record(status="ready", phase="cold_validation", pass_active=False)
                reply(identity, ok=True)
            elif operation == "shutdown":
                record(status="closing", phase="shutdown", pass_active=False)
                broker.close()
                broker_holder.broker = None
                record(status="closed", phase="closed", finished_at=arena.utc_now())
                reply(identity, ok=True)
                break
            else:
                raise RuntimeError("Unsupported warm broker control operation")
    except BaseException as error:
        record(status="failed", error=f"{type(error).__name__}: {error}", finished_at=arena.utc_now())
        reply(identity, ok=False, error=f"{type(error).__name__}: {error}")
        return 1
    finally:
        swarm.persistent_quick.PersistentQuickBroker = original_class
        if broker_holder.broker is not None:
            broker_holder.broker.close()
        stopped.set()
        record(status="closed" if status["status"] != "failed" else "failed", finished_at=arena.utc_now())
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--serve", action="store_true", required=True)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--parent-pid", type=int, required=True)
    parser.add_argument("--parent-start-time", type=int, required=True)
    parser.add_argument("--startup-seconds", type=float, default=DEFAULT_SPEC.broker_startup_timeout_seconds)
    parser.add_argument("--request-seconds", type=float, default=DEFAULT_SPEC.lean_request_timeout_seconds)
    args = parser.parse_args(argv)
    return serve(args.root, args.parent_pid, args.startup_seconds, args.request_seconds,
                 parent_start_time=args.parent_start_time)


if __name__ == "__main__":
    raise SystemExit(main())
