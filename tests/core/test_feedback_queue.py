"""Piped MCP admission stays visible while serial proof execution is blocked."""
from __future__ import annotations

import io
import json
import os
from pathlib import Path
import queue
import subprocess
import sys
import threading
import time

import pytest

from lean_tools import feedback_requests as requests
from lean_tools import feedback_workflow as workflow

REPO = Path(__file__).resolve().parents[2]


@pytest.fixture
def service(tmp_path):
    row = {"name": "demo", "header": "import Lean\n\n", "contexts": [],
           "signature": "theorem demo : True", "src": "theorem demo : True := by trivial",
           "proof_length": 2}
    task = tmp_path / "Task.json"
    task.write_text(json.dumps({"schema_version": 1, "row": row}))
    candidate = tmp_path / "Candidate.lean"
    candidate.write_text(workflow.arena.render_candidate_scaffold(row))
    return workflow.Feedback({"task": str(task), "candidate": str(candidate), "project_root": str(tmp_path)})


def _request(identity, arguments=None, token=None):
    params = {"name": "edit_check", "arguments": arguments or {}}
    if token is not None:
        params["_meta"] = {"progressToken": token}
    return {"id": identity, "method": "tools/call", "params": params}


def _until(predicate, message="condition did not become true"):
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline:
        result = predicate()
        if result:
            return result
        time.sleep(.01)
    pytest.fail(message)


# A real pipe/stdio process, real journal, real source validation and checkpoints;
# only the Lean evaluator is synthetic. No model, provider or Lean process runs.
PIPE_SERVER = r'''
import json, pathlib, sys, threading, time
from lean_tools import feedback_workflow as workflow
root = pathlib.Path(sys.argv[1])
workflow.MAX_PENDING_REQUESTS = int(sys.argv[2])
feedback = workflow.Feedback(json.loads((root / "settings.json").read_text()))
def log(event):
    with (root / "execution.jsonl").open("a") as stream:
        stream.write(json.dumps({"event": event, "ns": time.time_ns()}) + "\n")
original_check = feedback.check
count = 0
def check(arguments):
    global count
    count += 1
    log(f"start:{count}")
    try:
        return original_check(arguments)
    finally:
        log(f"finish:{count}")
feedback.check = check
def evaluate(task, snapshot, project, **kwargs):
    print("incidental evaluator stdout")
    helper = threading.Thread(target=lambda: print("helper evaluator stdout"))
    helper.start()
    helper.join()
    log("evaluate")
    (root / "entered").touch()
    while not (root / "release").exists():
        time.sleep(.01)
    return workflow.arena.Evaluation(task_id="demo", candidate_path=str(snapshot), valid=True,
        compile_seconds=.01, axiom_audit_seconds=None, axioms=None,
        original_local_tokens=2, candidate_local_tokens=3, local_token_reduction_pct=-50,
        official_original_tokens=2, environment_fingerprint="synthetic")
workflow.arena.evaluate_candidate = evaluate
workflow.serve(feedback, sys.stdin, sys.stdout)
'''


class PipedServer:
    def __init__(self, service, capacity=workflow.MAX_PENDING_REQUESTS):
        self.root = service.root
        (self.root / "settings.json").write_text(json.dumps(service.settings))
        self.process = subprocess.Popen([sys.executable, "-c", PIPE_SERVER, str(self.root), str(capacity)],
            cwd=REPO, env={**os.environ, "PYTHONPATH": str(REPO)}, stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.messages = queue.Queue()
        def collect():
            for line in self.process.stdout:
                try:
                    self.messages.put(json.loads(line))
                except ValueError:
                    self.messages.put({"bad_wire": line})
        self.reader = threading.Thread(target=collect, daemon=True)
        self.reader.start()

    def send(self, value):
        self.process.stdin.write(json.dumps(value) + "\n")
        self.process.stdin.flush()

    def receive(self):
        return self.messages.get(timeout=5)

    def finish(self):
        self.process.stdin.close()
        (self.root / "release").touch()
        assert self.process.wait(timeout=5) == 0
        self.reader.join(timeout=5)
        stderr = self.process.stderr.read()
        assert "incidental evaluator stdout" in stderr
        assert "helper evaluator stdout" in stderr
        return list(self.messages.queue)

    def close(self):
        if self.process.poll() is None:
            self.process.kill()
        self.process.wait(timeout=5)
        for stream in (self.process.stdin, self.process.stdout, self.process.stderr):
            stream.close()
        self.reader.join(timeout=5)


def _rows(root):
    return {row["transport"]["json_rpc_id"]: row for row in requests.inspect_requests(root)["requests"]}


def test_piped_busy_server_admits_visible_queue_controls_and_executes_stale_hash_at_start(service):
    initial_hash = workflow.arena.sha256_file(service.candidate)
    server = PipedServer(service)
    try:
        server.send(_request("first", {"body": "by exact True.intro"}))
        _until(lambda: (service.root / "entered").exists())
        second_arguments = {"body": "by constructor", "expected_sha256": initial_hash}
        server.send(_request("second", second_arguments, token="queue-token"))
        notification = server.receive()
        assert notification["method"] == "notifications/progress"
        assert notification["params"]["progress"] == 0
        rows = _until(lambda: (rows if len(rows := _rows(service.root)) == 2 else None))
        assert rows["first"]["phase"] == "in_progress"
        queued = rows["second"]
        assert queued["phase"] == "queued" and queued["started_ns"] is None
        assert queued["pending_ahead_at_admission"] == 1
        assert queued["requested_candidate"] == "Candidate.lean"
        assert queued["arguments_sha256"] == requests.arguments_sha256(second_arguments)
        assert queued["source"] == {"expected_sha256": initial_hash}
        assert queued["request_id"] in notification["params"]["message"]
        path = Path(queued["request_path"])
        before = path.read_bytes(), path.stat().st_mtime_ns
        observation = subprocess.run([sys.executable, str(REPO / "lean_tools/feedback_requests.py"),
            "--root", str(service.root)], check=True, capture_output=True, text=True, timeout=5)
        independently_seen = {row["transport"]["json_rpc_id"]: row for row in json.loads(observation.stdout)["requests"]}
        assert independently_seen["second"]["phase"] == "queued"
        assert independently_seen["first"]["phase"] == "in_progress"
        assert (path.read_bytes(), path.stat().st_mtime_ns) == before
        for identity, method in (("ping", "ping"), ("catalog", "tools/list"), ("init", "initialize")):
            server.send({"id": identity, "method": method})
            reply = server.receive()
            assert reply["id"] == identity and "result" in reply
        server.send({"method": "notifications/cancelled", "params": {"requestId": "first"}})
        server.send({"id": "bad", "method": "unknown"})
        assert server.receive()["error"]["code"] == -32601
        assert server.process.poll() is None
        assert [json.loads(line)["event"] for line in (service.root / "execution.jsonl").read_text().splitlines()] == ["start:1", "evaluate"]
        # Closing stdin must drain both accepted calls, including the queued one.
        messages = server.finish()
        replies = {row["id"]: row for row in messages if "id" in row}
        assert set(replies) == {"first", "second"}
        assert json.loads(replies["first"]["result"]["content"][0]["text"])["valid"] is True
        second = json.loads(replies["second"]["result"]["content"][0]["text"])
        assert second["status"] == "source_conflict"
        rows = _rows(service.root)
        assert len(rows) == 2  # No second admission at execution.
        assert all(row["phase"] == "completed" and row["transport"]["state"] == "written" for row in rows.values())
        assert rows["second"]["started_ns"] >= rows["first"]["finished_ns"]
        assert rows["second"]["queue_wait_seconds"] > 0
        assert rows["second"]["wall_seconds"] < rows["second"]["queue_wait_seconds"]
        assert rows["second"]["request_id"] == queued["request_id"] == second["feedback_request"]["request_id"]
        assert "True.intro" in service.candidate.read_text() and "constructor" not in service.candidate.read_text()
        events = [json.loads(line)["event"] for line in (service.root / "execution.jsonl").read_text().splitlines()]
        assert events == ["start:1", "evaluate", "finish:1", "start:2", "finish:2"]
        progress = [notification] + [row for row in messages if "method" in row]
        assert [row["params"]["progress"] for row in progress] == [0, 1]
        assert all(row["params"]["progressToken"] == "queue-token" for row in progress)
    finally:
        server.close()


def test_queue_backpressure_and_duplicate_id_do_not_admit_extra_work(service):
    server = PipedServer(service, capacity=2)
    try:
        server.send(_request(1))
        _until(lambda: (service.root / "entered").exists())
        server.send(_request(2))
        _until(lambda: len(_rows(service.root)) == 2)
        server.send(_request(3))
        refused = server.receive()
        assert refused["id"] == 3 and refused["error"]["code"] == -32000
        assert "not accepted" in refused["error"]["message"]
        server.send(_request(2))
        assert "already pending" in server.receive()["error"]["message"]
        server.send({"id": 4, "method": "ping"})
        assert server.receive() == {"jsonrpc": "2.0", "id": 4, "result": {}}
        assert len(_rows(service.root)) == 2
        assert {row["id"] for row in server.finish()} == {1, 2}
        assert len(_rows(service.root)) == 2
    finally:
        server.close()


def test_broken_final_write_stops_unstarted_work_even_with_stdin_still_open(service, monkeypatch):
    entered, release = threading.Event(), threading.Event()
    executions = []
    def check(arguments):
        executions.append(arguments["body"])
        entered.set()
        assert release.wait(timeout=5)
        return {"status": "valid", "valid": True}
    monkeypatch.setattr(service, "check", check)
    class BrokenWriter(io.StringIO):
        def write(self, value):
            raise BrokenPipeError("synthetic dead client")
    read_fd, write_fd = os.pipe()
    input_stream = os.fdopen(read_fd, "r")
    producer = os.fdopen(write_fd, "w")
    errors = []
    original_stdout = sys.stdout
    def run():
        try:
            workflow.serve(service, input_stream, BrokenWriter())
        except BaseException as error:
            errors.append(error)
    worker = threading.Thread(target=run)
    worker.start()
    try:
        producer.write(json.dumps(_request(1, {"body": "first"})) + "\n")
        producer.flush()
        assert entered.wait(timeout=5)
        producer.write(json.dumps(_request(2, {"body": "second"})) + "\n")
        producer.flush()
        _until(lambda: len(_rows(service.root)) == 2)
        release.set()
        worker.join(timeout=5)
        assert not worker.is_alive(), "server waited on an idle stdin after its output failed"
        assert len(errors) == 1 and isinstance(errors[0], BrokenPipeError)
        assert sys.stdout is original_stdout
        assert executions == ["first"]
        rows = _rows(service.root)
        assert rows[1]["phase"] == "completed" and rows[1]["transport"]["state"] == "write_failed"
        assert rows[2]["phase"] == "interrupted" and rows[2]["started_ns"] is None
        assert rows[2]["result_path"] is None and rows[2]["transport"]["state"] == "unobserved"
    finally:
        release.set()
        producer.close()
        worker.join(timeout=5)
        input_stream.close()


def test_queue_progress_write_failure_never_starts_operation(service, monkeypatch):
    monkeypatch.setattr(service, "check", lambda _request: pytest.fail("failed admission progress started work"))
    class BrokenWriter(io.StringIO):
        def write(self, value):
            raise BrokenPipeError("progress delivery failed")
    with pytest.raises(BrokenPipeError):
        workflow.serve(service, io.StringIO(json.dumps(_request(1, token="opt-in")) + "\n"), BrokenWriter())
    row, = _rows(service.root).values()
    assert row["phase"] == "interrupted" and row["started_ns"] is None
    assert row["transport"]["state"] == "unobserved"


@pytest.mark.parametrize("token", [True, [], {}, "x" * 1025])
def test_invalid_progress_token_rejected_without_admission(service, token):
    output = io.StringIO()
    workflow.serve(service, io.StringIO(json.dumps(_request(1, token=token)) + "\n"), output)
    reply = json.loads(output.getvalue())
    assert reply["error"]["code"] == -32602
    assert not _rows(service.root)


def test_oversized_request_line_drains_only_its_frame_then_ping_works(service, monkeypatch):
    monkeypatch.setattr(workflow, "MAX_REQUEST_BYTES", 100)
    output = io.StringIO()
    workflow.serve(service, io.StringIO('"' + "😀" * 100 + '"\n' + '{"id":2,"method":"ping"}\n'), output)
    oversized, ping = map(json.loads, output.getvalue().splitlines())
    assert oversized["id"] is None and "exceeds" in oversized["error"]["message"]
    assert ping == {"jsonrpc": "2.0", "id": 2, "result": {}}
    assert not _rows(service.root)


def test_candidate_resolution_failure_is_failed_once_and_preserves_written_response(service):
    (service.root / "Loop.lean").symlink_to("Loop.lean")
    output = io.StringIO()
    workflow.serve(service, io.StringIO(json.dumps(_request(1, {"candidate": "Loop.lean"})) + "\n"), output)
    value = json.loads(json.loads(output.getvalue())["result"]["content"][0]["text"])
    row, = _rows(service.root).values()
    assert value["status"] == "infrastructure_error"
    assert row["phase"] == "failed" and row["error"]["type"] == "RuntimeError"
    assert row["transport"]["state"] == "written"
    assert row["request_id"] == value["feedback_request"]["request_id"]


def test_pre_journal_failure_closes_receipt_with_actual_error_before_response(service, monkeypatch):
    def early_failure(*args):
        raise RuntimeError("synthetic pre-execution failure")
    monkeypatch.setattr(service, "call", early_failure)
    output = io.StringIO()
    workflow.serve(service, io.StringIO(json.dumps(_request(1)) + "\n"), output)
    row, = _rows(service.root).values()
    assert row["phase"] == "failed" and row["started_ns"] is None
    assert row["error"]["message"] == "synthetic pre-execution failure"
    assert row["transport"]["state"] == "written"


def test_cached_control_write_failure_does_not_fabricate_final_write_attempt(service):
    journal = service.request_journal
    with journal.rpc_request(1):
        value = journal.call("edit_check", {}, lambda: {"status": "valid"})
        class BrokenWriter(io.StringIO):
            writes = 0
            def write(self, text):
                self.writes += 1
                raise BrokenPipeError("control response failed")
        stream = BrokenWriter()
        writer = workflow._MCPWriter(stream, journal)
        with pytest.raises(BrokenPipeError):
            writer.send({"id": "ping", "result": {}})
        with pytest.raises(BrokenPipeError):
            writer.send({"id": 1, "result": {}}, request_id=value["feedback_request"]["request_id"])
        assert stream.writes == 1
        row, = _rows(service.root).values()
        assert row["transport"]["state"] == "unobserved"


def test_reader_failure_is_propagated_after_empty_queue_wait(service):
    class BrokenReader(io.StringIO):
        def readline(self, *args):
            raise OSError("synthetic input failure")
    with pytest.raises(OSError, match="synthetic input failure"):
        workflow.serve(service, BrokenReader(), io.StringIO())


def test_stdout_is_restored_if_reader_cannot_start(service, monkeypatch):
    def cannot_start(self):
        raise RuntimeError("synthetic thread exhaustion")
    monkeypatch.setattr(threading.Thread, "start", cannot_start)
    original = sys.stdout
    with pytest.raises(RuntimeError, match="synthetic thread exhaustion"):
        workflow.serve(service, io.StringIO(), io.StringIO())
    assert sys.stdout is original


def test_null_progress_token_is_rejected_without_admission(service):
    request = _request(1)
    request["params"]["_meta"] = {"progressToken": None}
    output = io.StringIO()
    workflow.serve(service, io.StringIO(json.dumps(request) + "\n"), output)
    assert json.loads(output.getvalue())["error"]["code"] == -32602
    assert not _rows(service.root)


def test_admission_is_read_only_and_context_reuses_one_receipt(service, monkeypatch):
    journal = service.request_journal
    def forbid_source_read(*args):
        pytest.fail("admission tried to read source")
    with monkeypatch.context() as patch:
        patch.setattr(workflow.arena, "sha256_file", forbid_source_read)
        admission = journal.admit("edit_check", {"candidate": "Probe.lean"}, identity="queued",
                                  requested_candidate="Probe.lean")
    queued, = _rows(service.root).values()
    assert queued["phase"] == "queued" and queued["requested_candidate"] == "Probe.lean"
    assert "current_sha256" not in queued["source"]
    with journal.rpc_request("queued", admission=admission):
        result = journal.call("edit_check", {"candidate": "Probe.lean"}, lambda: {"status": "valid"})
    assert result["feedback_request"]["request_id"] == admission.request_id
    assert len(_rows(service.root)) == 1
    assert journal.last_request_id is None
    with journal.rpc_request("queued", admission=admission), pytest.raises(ValueError, match="match"):
        journal.call("edit_check", {"candidate": "Probe.lean"}, lambda: pytest.fail("admission reused"))


@pytest.mark.parametrize("bad_name", ["../Probe.lean", "sub/Probe.lean", "sub\\Probe.lean", "bad\0.lean"])
def test_admission_does_not_record_unsafe_requested_candidate(service, bad_name):
    service.request_journal.admit("edit_check", {}, identity=1, requested_candidate=bad_name)
    row, = _rows(service.root).values()
    assert "requested_candidate" not in row


@pytest.mark.parametrize("bad_time", [None, "corrupt", []])
def test_corrupt_admission_time_is_counted_without_breaking_inspector(service, bad_time):
    value = service.request_journal.call("edit_check", {}, lambda: {"status": "valid"})
    path = Path(value["feedback_request"]["request_path"])
    row = json.loads(path.read_text())
    row["admitted_ns"] = bad_time
    workflow.arena.write_json_atomic(path, row)
    observed = requests.inspect_requests(service.root)
    assert observed["invalid_receipts"] == 1 and observed["requests"] == []
