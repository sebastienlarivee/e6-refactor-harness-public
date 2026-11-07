from __future__ import annotations

import io
import json
from pathlib import Path

import pytest

from lean_tools import diagnostic_presentation as presentation
from lean_tools import feedback_response as response
from lean_tools import feedback_workflow as workflow


@pytest.fixture
def service(tmp_path):
    row = {"name": "demo", "header": "import Lean\n\n", "contexts": [],
           "signature": "theorem demo : True", "src": "theorem demo : True := by trivial",
           "proof_length": 2}
    task = tmp_path / "Task.json"
    task.write_text(json.dumps({"schema_version": 1, "row": row}), encoding="utf-8")
    candidate = tmp_path / "Candidate.lean"
    candidate.write_text(workflow.arena.render_candidate_scaffold(row), encoding="utf-8")
    return workflow.Feedback({"task": str(task), "candidate": str(candidate),
                              "project_root": str(tmp_path)})


def _request(identity="rpc-42", *, tool="edit_check", arguments=None):
    return {"jsonrpc": "2.0", "id": identity, "method": "tools/call",
            "params": {"name": tool, "arguments": {} if arguments is None else arguments}}


def _serve(service, request, writer=None):
    writer = writer if writer is not None else io.StringIO()
    workflow.serve(service, io.StringIO(response.json_text(request) + "\n"), writer)
    wire = writer.getvalue()
    assert len(wire.encode("utf-8")) <= response.RESPONSE_BYTE_LIMIT
    return json.loads(wire), wire


def _value(reply):
    return json.loads(reply["result"]["content"][0]["text"])


def _receipt(service):
    paths = [path for path in service.request_journal.directory.glob("*.json")
             if not path.name.endswith(".result.json")]
    assert len(paths) == 1
    return json.loads(paths[0].read_text(encoding="utf-8"))


@pytest.mark.parametrize("message", ["unsolved goals\n⊢ " + "😀λ" * 150_000,
                                     'trace\\"\n\t' * 150_000])
def test_native_exact_utf8_envelope_is_bounded_and_paths_recover_complete_result(service, monkeypatch, message):
    digest = workflow.arena.sha256_file(service.candidate)
    original = {"status": "invalid", "valid": False, "source_sha256": digest,
                "candidate": str(service.candidate), "checkpoint": None,
                "diagnostics": [{"severity": "error", "message": message,
                                 "location": {"scope": "candidate", "line": 4, "column": 3}}]}
    monkeypatch.setattr(service, "check", lambda _request: original)
    identity = 'rpc-😀-λ-"\\42'
    reply, wire = _serve(service, _request(identity))
    assert reply["id"] == identity
    value = _value(reply)
    assert value["source_sha256"] == digest
    metadata = value["feedback_request"]
    receipt = json.loads(Path(metadata["request_path"]).read_text(encoding="utf-8"))
    durable = json.loads(Path(metadata["result_path"]).read_text(encoding="utf-8"))
    archived = json.loads(Path(value["full_response_path"]).read_text(encoding="utf-8"))["result"]
    assert durable == archived
    assert durable["diagnostics"][0]["message"] == message
    assert metadata["arguments_sha256"] == receipt["arguments_sha256"]
    assert receipt["phase"] == "completed"
    assert receipt["transport"]["state"] == "written"
    assert receipt["transport"]["json_rpc_id"] == identity
    assert value["response_truncation"]["strings_truncated"] > 0
    assert message not in wire


def test_huge_unexpected_exception_is_bounded_with_durable_failed_request_and_full_error(service, monkeypatch):
    message = 'unexpected 😀 failure\\"\n' * 150_000

    def fail(_request):
        raise RuntimeError(message)

    monkeypatch.setattr(service, "check", fail)
    reply, _wire = _serve(service, _request("exception-😀"))
    assert reply["result"]["isError"] is True
    value = _value(reply)
    assert value["status"] == "infrastructure_error"
    receipt = json.loads(Path(value["feedback_request"]["request_path"]).read_text(encoding="utf-8"))
    assert receipt["phase"] == "failed"
    assert receipt["result_path"] is None
    assert receipt["transport"]["state"] == "written"
    full = json.loads(Path(value["full_response_path"]).read_text(encoding="utf-8"))["result"]
    assert full["error"] == message
    assert full["feedback_request"]["request_id"] == receipt["request_id"]


@pytest.mark.parametrize("identity", ["😀" * 257, "x" * 1025, True, {"bad": "id"}, [1]])
def test_invalid_or_oversized_rpc_id_is_rejected_with_null_id_then_server_continues(service, monkeypatch, identity):
    monkeypatch.setattr(service, "check", lambda _request: pytest.fail("invalid ID ran the tool"))
    invalid = _request(identity)
    ping = {"id": "next-😀", "method": "ping"}
    output = io.StringIO()
    workflow.serve(service, io.StringIO(response.json_text(invalid) + "\n" + response.json_text(ping) + "\n"), output)
    replies = [json.loads(line) for line in output.getvalue().splitlines()]
    assert len(replies) == 2
    assert replies[0]["id"] is None
    assert replies[0]["error"]["code"] == -32600
    assert "1024 UTF-8" in replies[0]["error"]["message"]
    assert replies[1] == {"jsonrpc": "2.0", "id": "next-😀", "result": {}}
    assert not service.request_journal.directory.exists()


@pytest.mark.parametrize("failure_point", ["write", "flush"])
@pytest.mark.parametrize("operation_raises", [False, True])
def test_write_and_flush_failure_record_delivery_outcome_without_losing_execution(service, monkeypatch, failure_point, operation_raises):
    def operation(_request):
        if operation_raises:
            raise RuntimeError("synthetic operation failure")
        return {"status": "valid", "valid": True, "source_sha256": workflow.arena.sha256_file(service.candidate)}

    class BrokenWriter(io.StringIO):
        def write(self, text):
            if failure_point == "write":
                raise BrokenPipeError("synthetic write failure")
            return super().write(text)

        def flush(self):
            if failure_point == "flush":
                raise BrokenPipeError("synthetic flush failure")
            return super().flush()

    monkeypatch.setattr(service, "check", operation)
    with pytest.raises(BrokenPipeError, match="synthetic"):
        _serve(service, _request(), BrokenWriter())
    receipt = _receipt(service)
    assert receipt["phase"] == ("failed" if operation_raises else "completed")
    assert receipt["transport"]["state"] == "write_failed"
    assert receipt["transport"]["error_type"] == "BrokenPipeError"
    if not operation_raises:
        durable = json.loads(Path(receipt["result_path"]).read_text(encoding="utf-8"))
        assert durable["valid"] is True
        assert durable["feedback_request"]["request_id"] == receipt["request_id"]


def test_missing_candidate_score_is_structured_and_journaled(service):
    settings = {**service.settings, "original_tokens": 10, "original_heartbeats": 20,
                "compatibility_roots": []}
    scoring = workflow.Feedback(settings)
    missing = scoring.root / "Missing.lean"
    reply, _wire = _serve(scoring, _request(tool="score_candidate", arguments={
        "candidate": missing.name, "expected_sha256": "a" * 64}))
    value = _value(reply)
    assert reply["result"]["isError"] is True
    assert value["status"] == "invalid_request"
    assert value["code"] == "candidate_missing"
    assert value["candidate"] == str(missing)
    assert value["valid"] is None and value["checkpoint"] is None
    assert _receipt(scoring)["phase"] == "completed"
    assert not missing.exists()


def _evaluation(path, diagnostic_path):
    return workflow.arena.Evaluation(
        task_id="demo", candidate_path=str(path), valid=True,
        compile_seconds=0.2, axiom_audit_seconds=None, axioms=None,
        original_local_tokens=2, candidate_local_tokens=3,
        local_token_reduction_pct=-50, official_original_tokens=2,
        environment_fingerprint="synthetic", diagnostics_path=str(diagnostic_path))


def test_cached_diagnostic_truncation_metadata_reaches_native_result_and_full_details(service, monkeypatch):
    source = service.candidate.read_text(encoding="utf-8")
    declaration, _ = workflow.arena.extract_candidate_declaration(service.row, source)
    generated = workflow.arena.quick_compile_harness(service.row, declaration, service.project)
    source_map = presentation.SourceMap.for_declaration(source, generated, declaration)
    line = generated.count("\n", 0, generated.index(declaration))
    message = "trace\n" + "😀" * 150_000
    raw = [{"severity": "information", "line": line, "character": 0, "message": message}]
    shown = presentation.present_diagnostics(raw, source_map)
    path = presentation.archive_diagnostics(raw, shown, source=generated,
                                           source_map=source_map, candidate_path=service.candidate)
    monkeypatch.setattr(workflow.arena, "evaluate_candidate", lambda _task, snapshot, _project, **_kwargs: _evaluation(snapshot, path))
    reply, _wire = _serve(service, _request())
    value = _value(reply)
    assert value["valid"] is True
    assert value["diagnostics_truncation"]["messages_truncated"] == 1
    assert value["diagnostics_compacted"] == 0
    assert value["diagnostics_path"] == str(path)
    assert value["diagnostics"][0]["message_truncation"]["original_utf8_bytes"] == len(message.encode("utf-8"))
    full = json.loads(Path(value["details_path"]).read_text(encoding="utf-8"))
    assert full["diagnostic_presentation"]["diagnostics_truncation"] == value["diagnostics_truncation"]
    assert full["diagnostic_presentation"]["mapped_diagnostics"][0]["message"] == message


def test_advisory_diagnostic_truncation_metadata_is_forwarded(service, monkeypatch):
    from lean_tools import advisory_feedback

    source = service.candidate.read_text(encoding="utf-8")
    declaration, _ = workflow.arena.extract_candidate_declaration(service.row, source)
    generated = "import Lean\n" + declaration + "\n"
    message = "Try this: " + "exact True.intro\n" * 30_000
    line = generated.count("\n", 0, generated.index(declaration))
    raw = [{"severity": "information", "line": line, "character": 0, "message": message}]
    monkeypatch.setattr(workflow.arena, "measurement_environment_fingerprint", lambda *_args, **_kwargs: "synthetic")
    monkeypatch.setattr(advisory_feedback, "source_for_measurement", lambda *_args: generated)
    monkeypatch.setattr(advisory_feedback, "observe", lambda *_args, **_kwargs: {
        "status": "completed", "authoritative": False, "valid": True,
        "source_sha256": workflow.arena.sha256_bytes(generated.encode("utf-8")),
        "diagnostics": raw})
    reply, _wire = _serve(service, _request(arguments={"mode": "advisory"}))
    value = _value(reply)
    assert value["diagnostics_truncation"]["messages_truncated"] == 1
    assert value["diagnostics_compacted"] == 0
    assert value["diagnostics"][0]["message_truncation"]["omitted_utf8_bytes"] > 0
    full = json.loads(Path(value["details_path"]).read_text(encoding="utf-8"))
    assert full["advisory_presentation"]["diagnostics_truncation"] == value["diagnostics_truncation"]
    assert full["advisory"]["diagnostics"][0]["message"] == message


def test_cli_success_uses_same_bounded_result_and_durable_paths(service, monkeypatch):
    original = {"status": "invalid", "valid": False, "error": "type mismatch\n" + "😀" * 200_000}
    monkeypatch.setattr(service, "check", lambda _request: original)
    monkeypatch.setattr(workflow, "Feedback", lambda _settings: service)
    config = service.root / "config.json"
    config.write_text("{}", encoding="utf-8")
    output = io.StringIO()
    monkeypatch.setattr(workflow.sys, "argv", ["feedback_workflow", "--config", str(config)])
    monkeypatch.setattr(workflow.sys, "stdin", io.StringIO("{}"))
    monkeypatch.setattr(workflow.sys, "stdout", output)
    assert workflow.main() == 0
    wire = output.getvalue()
    assert len(wire.encode("utf-8")) <= response.RESPONSE_BYTE_LIMIT
    value = json.loads(wire)
    assert Path(value["feedback_request"]["request_path"]).is_file()
    assert Path(value["feedback_request"]["result_path"]).is_file()
    assert json.loads(Path(value["full_response_path"]).read_text(encoding="utf-8"))["result"]["error"] == original["error"]
    assert _receipt(service)["transport"] == {"kind": "direct", "json_rpc_id": None, "state": "unobserved"}


def test_cli_unexpected_exception_remains_bounded_and_recoverable(service, monkeypatch):
    message = "unexpected 😀 failure\n" * 150_000

    def fail(_request):
        raise RuntimeError(message)

    monkeypatch.setattr(service, "check", fail)
    monkeypatch.setattr(workflow, "Feedback", lambda _settings: service)
    config = service.root / "config.json"
    config.write_text("{}", encoding="utf-8")
    output = io.StringIO()
    monkeypatch.setattr(workflow.sys, "argv", ["feedback_workflow", "--config", str(config)])
    monkeypatch.setattr(workflow.sys, "stdin", io.StringIO("{}"))
    monkeypatch.setattr(workflow.sys, "stdout", output)
    escaped_type = None
    try:
        workflow.main()
    except Exception as error:
        # Do not repeat the huge exception in the regression failure output.
        escaped_type = type(error).__name__
    assert escaped_type is None, "CLI let an unexpected exception escape its response bound"
    wire = output.getvalue()
    assert len(wire.encode("utf-8")) <= response.RESPONSE_BYTE_LIMIT
    value = json.loads(wire)
    assert value["status"] == "infrastructure_error"
    assert Path(value["feedback_request"]["request_path"]).is_file()
    assert json.loads(Path(value["full_response_path"]).read_text(encoding="utf-8"))["result"]["error"] == message
    assert _receipt(service)["phase"] == "failed"
