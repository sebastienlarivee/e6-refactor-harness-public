"""Execution receipts never pretend that the native client/model saw a result."""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import time

import pytest

from lean_tools import arena_workflow as arena
from lean_tools.feedback_requests import (RequestJournal, arguments_sha256,
    inspect_requests, reconcile_native_events)


def test_completed_result_is_durable_and_transport_is_a_separate_fact(tmp_path):
    candidate = tmp_path / "Candidate.lean"
    candidate.write_text("before")
    journal = RequestJournal(tmp_path)
    arguments = {"expected_sha256": arena.sha256_file(candidate), "body": "private-source" * 3000}
    def operation():
        candidate.write_text("after")
        return {"status": "valid", "valid": True, "diagnostics": "full-result" * 10000}
    with journal.rpc_request(17):
        value = journal.call("edit_check", arguments, operation, candidate=candidate)
        identifier = value["feedback_request"]["request_id"]
        row, = inspect_requests(tmp_path)["requests"]
        assert row["phase"] == "completed" and row["completion_observed"] is True
        assert row["arguments_sha256"] == arguments_sha256(arguments)
        assert row["transport"] == {"kind": "mcp_stdio", "json_rpc_id": 17, "state": "unobserved"}
        assert row["source"]["current_sha256"] != row["source_after"]["current_sha256"]
        assert "private-source" not in json.dumps(row) and len(json.dumps(row)) < 3000
        assert json.loads(Path(row["result_path"]).read_text()) == value
        journal.transport_outcome(identifier, "written")
        assert inspect_requests(tmp_path)["requests"][0]["transport"]["state"] == "written"
    assert journal.last_request_id is None


@pytest.mark.parametrize("error,phase", [(ValueError("bad request"), "failed"), (KeyboardInterrupt(), "interrupted")])
def test_failure_before_value_retains_id_for_transport_error_receipt(tmp_path, error, phase):
    journal = RequestJournal(tmp_path)
    def operation():
        raise error
    with journal.rpc_request("abc"):
        with pytest.raises(type(error)):
            journal.call("edit_check", {}, operation)
        assert journal.last_request_id
        journal.transport_outcome(journal.last_request_id, "write_failed", error=BrokenPipeError())
        row, = inspect_requests(tmp_path)["requests"]
        assert row["phase"] == phase and row["completion_observed"] is False
        assert row["transport"]["error_type"] == "BrokenPipeError"
        assert row["result_path"] is None


def test_admission_persistence_failure_prevents_tool_execution(tmp_path, monkeypatch):
    def cannot_write(*args):
        raise OSError("synthetic full disk")
    monkeypatch.setattr(arena, "write_json_atomic", cannot_write)
    with pytest.raises(OSError, match="full disk"):
        RequestJournal(tmp_path).call("edit_check", {}, lambda: pytest.fail("tool must not execute"))


def test_cli_reads_inflight_request_in_an_independent_process_without_mutation(tmp_path):
    repo = Path(__file__).resolve().parents[2]
    script = tmp_path / "fake_worker.py"
    script.write_text('''
import pathlib, sys, time
from lean_tools.feedback_requests import RequestJournal
root = pathlib.Path(sys.argv[1])
def blocked():
    while not (root / "release").exists():
        time.sleep(.01)
    return {"status": "valid", "valid": True}
RequestJournal(root).call("score_candidate", {}, blocked)
''')
    environment = {**os.environ, "PYTHONPATH": str(repo)}
    worker = subprocess.Popen([sys.executable, str(script), str(tmp_path)], cwd=repo, env=environment)
    try:
        deadline = time.monotonic() + 5
        paths = []
        while time.monotonic() < deadline:
            paths = list((tmp_path / ".feedback/requests").glob("*.json"))
            if paths:
                break
            time.sleep(.01)
        assert len(paths) == 1
        before = paths[0].read_bytes(), paths[0].stat().st_mtime_ns
        result = subprocess.run([sys.executable, str(repo / "lean_tools/feedback_requests.py"), "--root", str(tmp_path)],
                                cwd=tmp_path.parent, check=True, capture_output=True, text=True, timeout=5)
        row, = json.loads(result.stdout)["requests"]
        assert row["phase"] == "in_progress"
        assert row["owner_state"] == ("running" if row["owner"].get("lookup_view") is not None else "unknown")
        assert row["completion_observed"] is False
        assert (paths[0].read_bytes(), paths[0].stat().st_mtime_ns) == before
        (tmp_path / "release").touch()
        assert worker.wait(timeout=5) == 0
        assert inspect_requests(tmp_path)["requests"][0]["phase"] == "completed"
    finally:
        if worker.poll() is None:
            worker.kill()
        worker.wait(timeout=5)


def test_dead_owner_is_reported_without_fabricating_completion(tmp_path):
    value = RequestJournal(tmp_path).call("score_candidate", {}, lambda: {"status": "valid"})
    path = Path(value["feedback_request"]["request_path"])
    row = json.loads(path.read_text())
    row["owner"]["start_time"] = (row["owner"]["start_time"] or 0) + 1
    row.update(phase="in_progress", result_path=None)
    arena.write_json_atomic(path, row)
    before = path.read_bytes()
    observed, = inspect_requests(tmp_path)["requests"]
    if row["owner"].get("lookup_view") is not None:
        assert observed["owner_state"] == "not_running"
        assert observed["reconciliation"] == "owner_exited_without_completion_receipt"
    else:
        assert observed["owner_state"] == "unknown"
    assert observed["phase"] == "in_progress" and observed["completion_observed"] is False
    assert path.read_bytes() == before


def test_reconciliation_preserves_missing_terminal_and_detects_ambiguous_repeats(tmp_path):
    journal = RequestJournal(tmp_path)
    with journal.rpc_request(1):
        first = journal.call("score_candidate", {"body": "first"}, lambda: {"status": "valid"})
    with journal.rpc_request(2):
        journal.call("edit_check", {}, lambda: {"status": "invalid"})
    with journal.rpc_request(3):
        journal.call("edit_check", {}, lambda: {"status": "invalid"})
    journal.call("profile_proof", {}, lambda: {"status": "profiled"})
    events = tmp_path / "codex-events.jsonl"
    events.write_text("".join(json.dumps({"type": "item.started", "item": {
        "id": identifier, "type": "mcp_tool_call", "server": "lean_feedback", "tool": tool,
        "arguments": arguments}}) + "\n" for identifier, tool, arguments in (
            ("one", "score_candidate", {"body": "first"}), ("two", "edit_check", {}),
            ("three", "profile_proof", {}))))
    before = events.read_bytes()
    report = reconcile_native_events(tmp_path, events)
    unique, ambiguous, missing = report["starts_without_terminal"]
    assert unique["match"] == "unique_arguments" and unique["execution_phase"] == "completed"
    assert unique["matching_request_ids"] == [first["feedback_request"]["request_id"]]
    assert unique["native_terminal_observed"] is False
    assert ambiguous["match"] == "ambiguous" and len(ambiguous["matching_request_ids"]) == 2
    assert missing["match"] == "no_receipt"
    assert report["direct_receipts_excluded"] == 1
    assert report["model_received_result"] == "unknown" and events.read_bytes() == before


def test_cli_refuses_path_traversal_and_limits(tmp_path):
    with pytest.raises(ValueError, match="hexadecimal"):
        inspect_requests(tmp_path, request_id="../../elsewhere")
    with pytest.raises(ValueError, match="between"):
        inspect_requests(tmp_path, limit=100)


@pytest.mark.parametrize("symlink_parent", [False, True])
def test_request_directory_cannot_redirect_execution_receipts_outside_capsule(tmp_path, symlink_parent):
    capsule, elsewhere = tmp_path / "capsule", tmp_path / "elsewhere"
    capsule.mkdir()
    elsewhere.mkdir()
    if symlink_parent:
        (capsule / ".feedback").symlink_to(elsewhere, target_is_directory=True)
    else:
        (capsule / ".feedback").mkdir()
        (capsule / ".feedback/requests").symlink_to(elsewhere, target_is_directory=True)
    with pytest.raises(ValueError, match="inside the capsule"):
        RequestJournal(capsule).call("edit_check", {}, lambda: pytest.fail("escaped receipt admitted work"))
    with pytest.raises(ValueError, match="inside the capsule"):
        inspect_requests(capsule)
    assert not list(elsewhere.iterdir())


def test_api_rejects_oversized_metadata_before_starting_work(tmp_path):
    journal = RequestJournal(tmp_path)
    with pytest.raises(ValueError, match="bounded identifier"):
        journal.call("x" * 5000, {}, lambda: pytest.fail("oversized metadata admitted work"))
    with pytest.raises(ValueError, match="request id"):
        with journal.rpc_request("x" * 5000):
            pytest.fail("oversized request id accepted")


def test_live_native_reconciliation_preserves_valid_records_before_partial_tail(tmp_path):
    events = tmp_path / "codex-events.jsonl"
    start = {"type": "item.started", "item": {"id": "one", "tool": "edit_check",
             "type": "mcp_tool_call", "server": "lean_feedback", "arguments": {}}}
    malformed_start = {"type": "item.started", "item": {"type": "mcp_tool_call", "server": "lean_feedback"}}
    events.write_text(json.dumps(start) + "\n" + "not-json\n[]\n" + json.dumps(malformed_start) + '\n{"type":')
    before = events.read_bytes()
    report = reconcile_native_events(tmp_path, events)
    row, = report["starts_without_terminal"]
    assert row["native_item_id"] == "one" and row["match"] == "no_receipt"
    assert report["malformed_records"] == 3 and report["incomplete_tail_records"] == 1
    assert report["oversized_records"] == 0 and events.read_bytes() == before


def test_corrupted_receipt_and_utf8_tail_do_not_break_native_inspection(tmp_path):
    journal = RequestJournal(tmp_path)
    with journal.rpc_request(3):
        value = journal.call("edit_check", {}, lambda: {"status": "valid"})
    path = Path(value["feedback_request"]["request_path"])
    receipt = json.loads(path.read_text())
    receipt["transport"] = []
    arena.write_json_atomic(path, receipt)
    events = tmp_path / "codex-events.jsonl"
    events.write_bytes(b'{"type":"item.started","item":{"id":"one","tool":"edit_check","type":"mcp_tool_call","server":"lean_feedback"}}\n{"text":"\xc3')
    report = reconcile_native_events(tmp_path, events)
    assert report["starts_without_terminal"][0]["match"] == "no_receipt"
    assert report["invalid_receipts"] == report["invalid_utf8_records"] == report["incomplete_tail_records"] == 1
    assert inspect_requests(tmp_path)["invalid_receipts"] == 1
