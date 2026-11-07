"""Durable feedback execution receipts and independent, read-only inspection.

Execution, stdio response writes and native transcript items are separate facts.
Nothing in this module claims a result was received by the model, cancels work,
restarts a broker, or edits the raw native transcript.
"""
from __future__ import annotations

import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import argparse
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass
import errno
import hashlib
import json
import math
import os
from pathlib import Path
import re
import sys
import time
from typing import Any, Callable
from uuid import uuid4

from lean_tools import arena_workflow as arena, process_memory

REQUEST_ID = re.compile(r"[0-9a-f]{32}\Z")
TOOL_NAME = re.compile(r"[a-zA-Z0-9_]{1,80}\Z")
MAX_RECEIPT_BYTES = 65536
MAX_NATIVE_EVENT_BYTES = 8 * 1024 * 1024


def _linux_process_stat(path: Path) -> tuple[int, int, str]:
    """Read PID, start tick and state together, without hiding lookup failures."""
    text = path.read_text(encoding="ascii")
    closing = text.rindex(")")
    fields = text[closing + 2:].split()
    pid, start_time, state = int(text[:text.index("(")].strip()), int(fields[19]), fields[0]
    if pid <= 0 or start_time < 0 or state not in {"R", "S", "D", "Z", "T", "W", "t", "X", "x", "K", "P", "I"}:
        raise ValueError("invalid process stat identity")
    return pid, start_time, state


def _linux_lookup_view() -> dict[str, Any] | None:
    """Identify the PID/start-tick view, including native-tool namespaces.

    A shared outer capsule PID namespace says nothing about a nested shell's
    /proc. In particular, an inherited /proc may number self differently from
    getpid(). Such a view cannot authoritatively resolve an owner's saved PID.
    """
    if sys.platform != "linux":
        return None
    try:
        if _linux_process_stat(Path("/proc/self/stat"))[0] != os.getpid():
            return None
        status = Path("/proc/self/status").read_text(encoding="ascii")
        namespace_pids = re.search(r"^NSpid:\s*([^\n]+)$", status, re.MULTILINE)
        if namespace_pids is None or namespace_pids.group(1).split() != [str(os.getpid())]:
            # Multiple entries mean /proc belongs to an ancestor namespace,
            # even if PID values happen to coincide after numeric reuse.
            return None
        root = Path("/proc").stat()
        boot_id = Path("/proc/sys/kernel/random/boot_id").read_text(encoding="ascii").strip()
        if not re.fullmatch(r"[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}", boot_id):
            return None
        namespaces = {}
        for name in ("pid", "user", "time"):
            identity = os.readlink(f"/proc/self/ns/{name}")
            if not re.fullmatch(rf"{name}:\[[0-9]+\]", identity):
                return None
            namespaces[f"{name}_namespace"] = identity
        return {"schema_version": 1, "boot_id": boot_id, **namespaces,
                "proc_device": root.st_dev, "proc_inode": root.st_ino}
    except (OSError, ValueError, IndexError, UnicodeError):
        return None


def arguments_sha256(arguments: Any) -> str:
    wire = json.dumps(arguments, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(wire.encode("utf-8")).hexdigest()


def _read_receipt(path: Path) -> dict[str, Any]:
    if path.is_symlink() or not path.is_file() or path.stat().st_size > MAX_RECEIPT_BYTES:
        raise ValueError("request receipt must be a bounded regular file")
    value = json.loads(path.read_text(encoding="utf-8"))
    if (not isinstance(value, dict) or value.get("request_id") != path.stem
            or not isinstance(value.get("phase"), str)
            or value["phase"] not in {"queued", "in_progress", "completed", "failed", "interrupted"}
            or not (type(value.get("started_ns")) is int or
                    (value.get("started_ns") is None and type(value.get("admitted_ns")) is int))
            or ("admitted_ns" in value and type(value["admitted_ns"]) is not int)
            or not isinstance(value.get("transport"), dict)):
        raise ValueError("invalid request receipt")
    return value


def _source(candidate: Path | None, arguments: Any) -> dict[str, Any]:
    result: dict[str, Any] = {}
    if candidate is not None:
        result["candidate"] = candidate.name
        try:
            result["current_sha256"] = arena.sha256_file(candidate)
        except OSError:
            result["current_sha256"] = None
    if isinstance(arguments, dict):
        for key in ("expected_sha256", "checkpoint_id"):
            value = arguments.get(key)
            if isinstance(value, str) and len(value) <= 128:
                result[key] = value
    return result


@dataclass
class AdmittedRequest:
    """An in-memory admission ticket; never a second execution receipt."""
    journal: "RequestJournal"
    receipt: dict[str, Any]
    monotonic: float
    claimed: bool = False

    @property
    def request_id(self) -> str:
        return self.receipt["request_id"]


class RequestJournal:
    def __init__(self, root: Path):
        self.root = Path(root).resolve()
        self.directory = self.root / ".feedback/requests"
        self._rpc: ContextVar[Any] = ContextVar(f"feedback_rpc_{id(self)}", default=None)
        self._last: ContextVar[str | None] = ContextVar(f"feedback_last_{id(self)}", default=None)
        self._admission: ContextVar[AdmittedRequest | None] = ContextVar(f"feedback_admission_{id(self)}", default=None)
        self._executing: ContextVar[dict[str, Any] | None] = ContextVar(f"feedback_executing_{id(self)}", default=None)

    def _confined_directory(self):
        if (self.directory.parent.is_symlink() or self.directory.is_symlink()
                or not self.directory.resolve().is_relative_to(self.root)):
            raise ValueError("request directory must stay inside the capsule without symlinks")

    @property
    def last_request_id(self) -> str | None:
        """Also available after operation() raises, for transport error receipts."""
        return self._last.get()

    @property
    def admitted_monotonic(self) -> float | None:
        admission = self._admission.get()
        return admission.monotonic if admission is not None else None

    def update_stage(self, stage: str, budget, details: dict[str, Any]) -> None:
        """Publish transitions for independent status reads without polling Lean."""
        request_id = self.last_request_id
        if request_id is None:
            return
        self._confined_directory()
        path = self.directory / f"{request_id}.json"
        receipt = self._executing.get()
        if receipt is None or receipt.get("request_id") != request_id:
            receipt = _read_receipt(path)
        receipt.update(stage=stage, stage_started_at=arena.utc_now(),
                       timeout_scope="quick_request", timeout_seconds=budget.seconds,
                       remaining_seconds_at_stage_start=round(max(0.0, budget.deadline - time.monotonic()), 6),
                       deadline_unix=time.time() + budget.deadline - time.monotonic(),
                       cleanup_grace_seconds=arena.check_budget.CLEANUP_GRACE_SECONDS)
        receipt.update(details)
        arena.write_json_atomic(path, receipt)

    @contextmanager
    def rpc_request(self, identity: Any, *, admission: AdmittedRequest | None = None):
        if (not (type(identity) is int or isinstance(identity, str))
                or len(str(identity).encode("utf-8")) > 1024):
            raise ValueError("JSON-RPC request id must be a string or integer")
        token = self._rpc.set(identity)
        previous = self._last.set(admission.request_id if admission is not None else None)
        admitted = self._admission.set(admission)
        try:
            yield
        finally:
            self._admission.reset(admitted)
            self._rpc.reset(token)
            self._last.reset(previous)

    def admit(self, name: str, arguments: Any, *, identity: Any,
              pending_ahead: int = 0, requested_candidate: Any = None,
              budget_seconds: float | None = None) -> AdmittedRequest:
        """Durably accept a bounded transport request without reading/editing source."""
        return self._new_admission(name, arguments, identity=identity, pending_ahead=pending_ahead,
                                   requested_candidate=requested_candidate, persist=True, budget_seconds=budget_seconds)

    def _new_admission(self, name: str, arguments: Any, *, identity: Any,
                       pending_ahead: int = 0, requested_candidate: Any = None,
                       persist: bool, budget_seconds: float | None = None) -> AdmittedRequest:
        if not isinstance(name, str) or not TOOL_NAME.fullmatch(name):
            raise ValueError("tool name must be a bounded identifier")
        self._confined_directory()
        if identity is not None:
            with self.rpc_request(identity):
                pass
        request_id = uuid4().hex
        admitted_monotonic = time.monotonic()
        receipt_path = self.directory / f"{request_id}.json"
        owner = process_memory.linux_process_identity(os.getpid()) if sys.platform == "linux" else None
        receipt: dict[str, Any] = {
            "schema_version": 1, "request_id": request_id, "tool": name,
            "arguments_sha256": arguments_sha256(arguments),
            "phase": "queued", "admitted_at": arena.utc_now(), "admitted_ns": time.time_ns(),
            "started_at": None, "started_ns": None, "pending_ahead_at_admission": pending_ahead,
            "owner": {"pid": os.getpid(), "start_time": owner.start_time if owner else None,
                      "lookup_view": _linux_lookup_view()},
            "transport": {"kind": "mcp_stdio" if identity is not None else "direct",
                          "json_rpc_id": identity, "state": "unobserved"},
            "source": _source(None, arguments),
            "request_path": str(receipt_path), "result_path": None,
        }
        if budget_seconds is not None:
            receipt.update(stage="feedback_queue", stage_started_at=arena.utc_now(),
                           timeout_scope="quick_request", timeout_seconds=budget_seconds,
                           deadline_unix=time.time() + budget_seconds)
        if (isinstance(requested_candidate, str) and requested_candidate.endswith(".lean")
                and len(requested_candidate.encode("utf-8")) <= 1024
                and not any(char in requested_candidate for char in "/\\\0")):
            receipt["requested_candidate"] = requested_candidate
        # If durable admission fails, no source mutation or Lean work has begun.
        if persist:
            arena.write_json_atomic(receipt_path, receipt)
        return AdmittedRequest(self, receipt, admitted_monotonic)

    def interrupt_queued(self, admission: AdmittedRequest, error: BaseException, *,
                         failed: bool = False) -> None:
        """Close accepted but unstarted work on transport shutdown; never cancel Lean."""
        if admission.journal is not self or admission.claimed:
            raise ValueError("request is not an unstarted admission from this journal")
        admission.claimed = True
        receipt = admission.receipt
        receipt.update(phase="failed" if failed else "interrupted",
                       finished_at=arena.utc_now(), finished_ns=time.time_ns(),
                       queue_wait_seconds=round(time.monotonic() - admission.monotonic, 6),
                       error={"type": type(error).__name__, "message": str(error)[:1024]})
        self._confined_directory()
        arena.write_json_atomic(Path(receipt["request_path"]), receipt)

    def call(self, name: str, arguments: Any, operation: Callable[[], dict[str, Any]], *,
             candidate: Path | None = None) -> dict[str, Any]:
        if candidate is not None and not candidate.resolve().is_relative_to(self.root):
            raise ValueError("candidate must stay inside the capsule")
        admission = self._admission.get()
        if admission is None:
            admission = self._new_admission(name, arguments, identity=self._rpc.get(), persist=False,
                                            requested_candidate=candidate.name if candidate is not None else None)
        receipt = admission.receipt
        if (admission.journal is not self or admission.claimed or receipt["tool"] != name
                or receipt["arguments_sha256"] != arguments_sha256(arguments)
                or receipt["transport"]["json_rpc_id"] != self._rpc.get()):
            raise ValueError("execution does not match its queued admission")
        request_id = admission.request_id
        receipt_path = Path(receipt["request_path"])
        result_path = self.directory / f"{request_id}.result.json"
        started_monotonic = time.monotonic()
        receipt.update(phase="in_progress", started_at=arena.utc_now(), started_ns=time.time_ns(),
                       queue_wait_seconds=round(started_monotonic - admission.monotonic, 6),
                       source=_source(candidate, arguments))
        self._confined_directory()
        arena.write_json_atomic(receipt_path, receipt)
        admission.claimed = True
        self._last.set(request_id)
        metadata = {"request_id": request_id, "request_path": str(receipt_path),
                    "result_path": str(result_path), "arguments_sha256": receipt["arguments_sha256"]}
        executing = self._executing.set(receipt)
        try:
            value = operation()
            if not isinstance(value, dict):
                raise TypeError("feedback operation must return an object")
            value = {**value, "feedback_request": metadata}
            self._confined_directory()
            arena.write_json_atomic(result_path, value)
            receipt.update(phase="completed", result_path=str(result_path),
                           result_status=value.get("status"), valid=value.get("valid"))
            for key in ("source_sha256", "checkpoint", "details_path"):
                field = value.get(key)
                if isinstance(field, (str, type(None))) and (field is None or len(field) <= 4096):
                    receipt[key] = field
        except BaseException as error:
            receipt.update(phase="interrupted" if isinstance(error, (KeyboardInterrupt, SystemExit)) else "failed",
                           error={"type": type(error).__name__, "message": str(error)[:1024]})
            raise
        finally:
            receipt.update(finished_at=arena.utc_now(), finished_ns=time.time_ns(),
                           wall_seconds=round(time.monotonic() - started_monotonic, 6),
                           source_after=_source(candidate, {}))
            try:
                self._confined_directory()
                arena.write_json_atomic(receipt_path, receipt)
            finally:
                self._executing.reset(executing)
        return value

    def transport_outcome(self, request_id: str | None, state: str, *, error: BaseException | None = None):
        """Record only actual write/flush outcomes, including error responses.

        Call with last_request_id when execution raised before returning a value.
        The caller must record this while still inside rpc_request().
        """
        if request_id is None:
            return
        self._confined_directory()
        if not REQUEST_ID.fullmatch(request_id) or state not in {"written", "write_failed"}:
            raise ValueError("invalid request id or transport state")
        path = self.directory / f"{request_id}.json"
        receipt = _read_receipt(path)
        receipt["transport"].update(state=state, observed_at=arena.utc_now())
        if error is not None:
            receipt["transport"]["error_type"] = type(error).__name__
        arena.write_json_atomic(path, receipt)


def _owner_observation(receipt: dict[str, Any]) -> dict[str, Any]:
    """Assert owner death only with comparable, affirmative process evidence."""
    def observed(state: str, reason: str, view=None):
        return {"state": state, "reason": reason, "lookup_view": view}

    owner = receipt.get("owner", {})
    if (not isinstance(owner, dict) or sys.platform != "linux"
            or type(owner.get("pid")) is not int or owner["pid"] <= 0
            or type(owner.get("start_time")) is not int or owner["start_time"] < 0):
        return observed("unknown", "owner_identity_unavailable")
    view = _linux_lookup_view()
    if view is None:
        return observed("unknown", "lookup_view_unavailable")
    if not isinstance(owner.get("lookup_view"), dict):
        # Version-1 receipts before lookup-view capture are still readable, but
        # their PID and start tick cannot establish visibility from this reader.
        return observed("unknown", "owner_lookup_view_unrecorded", view)
    if owner["lookup_view"] != view:
        return observed("unknown", "incomparable_lookup_view", view)
    try:
        pid, start_time, state = _linux_process_stat(Path("/proc") / str(owner["pid"]) / "stat")
        if pid != owner["pid"]:
            return observed("unknown", "malformed_process_identity", view)
        result = (observed("not_running", "pid_reused", view) if start_time != owner["start_time"] else
                  observed("not_running", "process_exited", view) if state in {"Z", "X", "x"} else
                  observed("running", "matching_process_identity", view))
    except FileNotFoundError:
        # /proc hidepid and similar restrictions can also look like ENOENT.
        # kill(0) uses the already-compared active PID namespace; only ESRCH
        # independently establishes absence. No signal is delivered.
        try:
            os.kill(owner["pid"], 0)
        except OSError as error:
            result = (observed("not_running", "process_absent", view) if error.errno == errno.ESRCH else
                      observed("unknown", "process_lookup_unavailable", view))
        else:
            result = observed("unknown", "process_stat_unavailable", view)
    except (OSError, ValueError, IndexError, UnicodeError):
        return observed("unknown", "process_stat_unavailable", view)
    if _linux_lookup_view() != view:
        return observed("unknown", "lookup_view_changed", view)
    return result


def _owner_state(receipt: dict[str, Any]) -> str:
    return _owner_observation(receipt)["state"]


def inspect_requests(root: Path, *, request_id: str | None = None, limit: int = 10) -> dict[str, Any]:
    """Read accepted/queued and executing requests independently of MCP execution."""
    if type(limit) is not int or not 1 <= limit <= 20:
        raise ValueError("limit must be between 1 and 20")
    if request_id is not None and not REQUEST_ID.fullmatch(request_id):
        raise ValueError("request_id must be a 32-character hexadecimal ID")
    journal = RequestJournal(root)
    journal._confined_directory()
    directory = journal.directory
    paths = [directory / f"{request_id}.json"] if request_id else list(directory.glob("*.json"))
    records, invalid = [], 0
    for path in paths:
        if not REQUEST_ID.fullmatch(path.stem):
            continue
        try:
            row = _read_receipt(path)
            observation = _owner_observation(row)
            row["owner_state"] = observation.pop("state")
            row["owner_observation"] = observation
            row["completion_observed"] = row.get("phase") == "completed"
            deadline = row.get("deadline_unix")
            if type(deadline) in {int, float} and math.isfinite(deadline):
                row["deadline_remaining_seconds"] = (round(max(0.0, deadline - time.time()), 6)
                    if row.get("phase") in {"queued", "in_progress"} else None)
            if row.get("phase") in {"queued", "in_progress"} and row["owner_state"] == "not_running":
                row["reconciliation"] = "owner_exited_without_completion_receipt"
            records.append(row)
        except (OSError, ValueError, TypeError, KeyError):
            invalid += 1
    records.sort(key=lambda row: row.get("admitted_ns", row.get("started_ns", 0)), reverse=True)
    return {"schema_version": 1, "status": "observed" if records else "missing",
            "requests": records[:limit], "omitted_count": max(0, len(records) - limit), "invalid_receipts": invalid,
            "guidance": "Inspect source hashes and the durable result before retrying. Queued work has not started and validates expected_sha256 when it executes. Avoid concurrent edits to a candidate with queued or in-progress work. This query does not cancel work; a written stdio response does not prove model receipt."}


def reconcile_native_events(root: Path, events_path: Path) -> dict[str, Any]:
    """Supplement raw events with unambiguous request-hash matches only."""
    starts, terminals = {}, set()
    malformed_records, incomplete_tail_records, oversized_records, invalid_utf8_records = 0, 0, 0, 0
    with Path(events_path).open("rb") as stream:
        while line := stream.readline(MAX_NATIVE_EVENT_BYTES + 1):
            if len(line) > MAX_NATIVE_EVENT_BYTES:
                oversized_records += 1
                while line and not line.endswith(b"\n"):
                    line = stream.readline(MAX_NATIVE_EVENT_BYTES + 1)
                continue
            try:
                event = json.loads(line.decode("utf-8"))
            except UnicodeDecodeError:
                invalid_utf8_records += 1
                if line.endswith(b"\n"):
                    malformed_records += 1
                else:
                    incomplete_tail_records += 1
                continue
            except ValueError:
                if line.endswith(b"\n"):
                    malformed_records += 1
                else:
                    incomplete_tail_records += 1
                continue
            if not isinstance(event, dict):
                malformed_records += 1
                continue
            item = event.get("item", {})
            if not isinstance(item, dict):
                malformed_records += 1
                continue
            if item.get("type") != "mcp_tool_call" or item.get("server") != "lean_feedback":
                continue
            if (not isinstance(item.get("id"), str) or not isinstance(item.get("tool"), str)
                    or not isinstance(item.get("arguments", {}), dict)):
                malformed_records += 1
                continue
            if event.get("type") == "item.started":
                starts[item["id"]] = item
            elif event.get("type") in {"item.completed", "item.failed"}:
                terminals.add(item["id"])
    journal = RequestJournal(root)
    journal._confined_directory()
    receipts: dict[tuple[str, str], list[dict[str, Any]]] = {}
    direct_receipts_excluded, invalid_receipts = 0, 0
    for path in journal.directory.glob("*.json"):
        if not REQUEST_ID.fullmatch(path.stem):
            continue
        try:
            receipt = _read_receipt(path)
            if receipt.get("transport", {}).get("kind") != "mcp_stdio":
                direct_receipts_excluded += 1
                continue
            key = receipt["tool"], receipt["arguments_sha256"]
            receipts.setdefault(key, []).append(receipt)
        except (OSError, ValueError, TypeError, KeyError):
            invalid_receipts += 1
            continue
    rows = []
    for item_id, item in starts.items():
        if item_id in terminals:
            continue
        key = item["tool"], arguments_sha256(item.get("arguments", {}))
        matches = receipts.get(key, [])
        duplicate_starts = sum((other["tool"], arguments_sha256(other.get("arguments", {}))) == key
                               for other in starts.values())
        row: dict[str, Any] = {"native_item_id": item_id, "tool": item["tool"],
                              "native_terminal_observed": False,
                              "matching_request_ids": [receipt["request_id"] for receipt in matches]}
        if len(matches) == 1 and duplicate_starts == 1:
            row.update(match="unique_arguments", execution_phase=matches[0]["phase"],
                       result_path=matches[0].get("result_path"), transport=matches[0].get("transport"))
        else:
            row["match"] = "ambiguous" if matches else "no_receipt"
        rows.append(row)
    return {"schema_version": 1, "native_events": str(Path(events_path).resolve()),
            "starts_without_terminal": rows, "model_received_result": "unknown",
            "malformed_records": malformed_records, "incomplete_tail_records": incomplete_tail_records,
            "oversized_records": oversized_records,
            "invalid_utf8_records": invalid_utf8_records, "invalid_receipts": invalid_receipts,
            "direct_receipts_excluded": direct_receipts_excluded,
            "note": "Supplemental execution evidence; raw native events are unchanged. Equal arguments with repeated calls do not establish call identity."}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True, help="capsule directory")
    parser.add_argument("--request-id")
    parser.add_argument("--limit", type=int, default=10)
    parser.add_argument("--native-events", type=Path, help="supplemental reconciliation; leaves raw events unchanged")
    args = parser.parse_args(argv)
    result = (reconcile_native_events(args.root, args.native_events) if args.native_events else
              inspect_requests(args.root, request_id=args.request_id, limit=args.limit))
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
