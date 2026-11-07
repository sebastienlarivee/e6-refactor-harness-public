from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

from lean_tools import diagnostic_presentation as diagnostics
from lean_tools import feedback_response as response
from lean_tools import context_tools as context


def _result(message: str) -> dict:
    return {
        "schema_version": 1, "status": "invalid", "valid": False,
        "candidate": "/capsule/Candidate.lean", "source_sha256": "a" * 64,
        "score": 73.125, "tokens": 123, "heartbeats": 456,
        "checkpoint": "/capsule/valid-candidates/accepted.lean", "checkpoint_id": "accepted.lean",
        "diagnostics_path": "/capsule/.feedback/diagnostics/full.json",
        "details_path": "/capsule/.feedback/results/full.json",
        "goal_handles": [{"goal_id": "goal-" + "b" * 64,
                          "goal": {"line": 12, "column": 5, "index": 0}, "case_name": "left"}],
        "default_goal_id": "goal-" + "b" * 64,
        "diagnostics": [{"severity": "error", "message": message,
                         "location": {"scope": "candidate", "line": 12, "column": 5}}],
    }


@pytest.mark.parametrize("message", ["error context\n" * 100_000, '"\\\t\n' * 100_000, "😀∀é\n" * 100_000])
def test_complete_mcp_response_is_bounded_and_full_receipt_is_exact(tmp_path, message):
    original = _result(message)
    before = copy.deepcopy(original)
    identity = "request-😀-42"
    envelope = lambda result: response.mcp_response(result, identity)
    bounded = response.bound_result(original, artifact_dir=tmp_path, envelope=envelope)
    wire = response.json_text(envelope(bounded)).encode("utf-8")
    assert len(wire) <= response.RESPONSE_BYTE_LIMIT
    assert original == before
    assert json.loads(Path(bounded["full_response_path"]).read_text(encoding="utf-8"))["result"] == original
    assert bounded["response_truncation"]["original_serialized_response_utf8_bytes"] == len(response.json_text(envelope(original)).encode("utf-8"))
    assert bounded["response_truncation"]["strings_truncated"] > 0
    decoded = json.loads(json.loads(wire)["result"]["content"][0]["text"])
    assert decoded == bounded
    for key in ("source_sha256", "candidate", "score", "tokens", "heartbeats", "checkpoint",
                "checkpoint_id", "details_path", "diagnostics_path", "goal_handles", "default_goal_id"):
        assert bounded[key] == original[key]


def test_small_result_is_unchanged_and_does_not_create_an_artifact(tmp_path):
    original = _result("type mismatch")
    assert response.bound_result(original, artifact_dir=tmp_path) is original
    assert list(tmp_path.iterdir()) == []


def test_nested_json_envelopes_are_measured_after_escaping(tmp_path):
    original = _result("error")
    original["native"] = {"content": [{"text": response.json_text({"trace": '\\"\n😀' * 60_000})}]}
    # A host may introduce yet another string-encoded envelope. Its escaping
    # must count too, rather than bounding the decoded diagnostic text alone.
    envelope = lambda result: {"content": [{"text": response.json_text(response.mcp_response(result, "native"))}]}
    bounded = response.bound_result(original, artifact_dir=tmp_path, envelope=envelope)
    assert response.serialized_bytes(envelope(bounded)) <= response.RESPONSE_BYTE_LIMIT
    assert bounded["full_response_path"]
    assert json.loads(Path(bounded["full_response_path"]).read_text(encoding="utf-8"))["result"] == original


def test_large_strings_in_non_diagnostic_fields_and_many_fields_are_bounded(tmp_path):
    original = _result("type mismatch")
    original.update({"malformed_" + str(index): {"value": "λ\n\\\"" * 20_000} for index in range(150)})
    original["oversized-list"] = [{"rendered": "z" * 20_000} for _ in range(500)]
    original["oversized-key" * 500] = "ignored key"
    bounded = response.bound_result(original, artifact_dir=tmp_path)
    assert response.serialized_bytes(response.mcp_response(bounded)) <= response.RESPONSE_BYTE_LIMIT
    assert bounded["source_sha256"] == original["source_sha256"]
    assert bounded["goal_handles"] == original["goal_handles"]
    metadata = bounded["response_truncation"]
    assert metadata["object_fields_omitted"] > 0
    assert metadata["strings_truncated"] > 0
    assert len(metadata["affected_fields"]) <= 8
    assert json.loads(Path(bounded["full_response_path"]).read_text(encoding="utf-8"))["result"] == original


def test_many_residual_cases_keep_handles_and_locations_while_bounding_text(tmp_path):
    original = _result("failure")
    original["unfinished_cases"] = {
        "status": "complete", "details_path": "/capsule/.feedback/cases/full.json",
        "cases": [{"goal_id": "goal-" + str(index), "goal": {"line": index + 1, "column": 2, "index": 0},
                   "target_preview": "∀ x, " + "😀" * 20_000} for index in range(12)],
        "total_cases": 12,
    }
    bounded = response.bound_result(original, artifact_dir=tmp_path)
    assert response.serialized_bytes(response.mcp_response(bounded)) <= response.RESPONSE_BYTE_LIMIT
    cases = bounded["unfinished_cases"]["cases"]
    assert len(cases) == 12
    assert [(case["goal_id"], case["goal"]) for case in cases] == [
        (case["goal_id"], case["goal"]) for case in original["unfinished_cases"]["cases"]]
    assert bounded["unfinished_cases"]["details_path"] == original["unfinished_cases"]["details_path"]


def test_second_boundary_retains_original_full_artifact(tmp_path):
    original = _result("x" * 500_000)
    first = response.bound_result(original, artifact_dir=tmp_path)
    second = response.bound_result(first, artifact_dir=tmp_path,
                                   envelope=lambda result: response.mcp_response(result, "request"),
                                   max_response_bytes=4096)
    assert response.serialized_bytes(response.mcp_response(second, "request")) <= 4096
    assert second["full_response_path"] == first["full_response_path"]
    assert json.loads(Path(second["full_response_path"]).read_text(encoding="utf-8"))["result"] == original


def test_fixed_envelope_overhead_cannot_be_silently_truncated(tmp_path):
    with pytest.raises(ValueError, match="envelope"):
        response.bound_result(_result("failure"), artifact_dir=tmp_path,
                              envelope=lambda result: response.mcp_response(result, "id" * 40_000))
    assert list(tmp_path.iterdir()) == []


def test_pathological_identity_fields_still_cannot_escape_response_budget(tmp_path):
    original = _result("failure")
    original.update({f"path_{index}_path": "/" + "z" * 4000 for index in range(200)})
    original.update(heartbeat=765, heartbeat_status="exact")
    bounded = response.bound_result(original, artifact_dir=tmp_path)
    assert response.serialized_bytes(response.mcp_response(bounded)) <= response.RESPONSE_BYTE_LIMIT
    assert bounded["source_sha256"] == original["source_sha256"]
    assert bounded["score"] == original["score"]
    assert bounded["checkpoint"] == original["checkpoint"]
    assert bounded["heartbeat"] == original["heartbeat"]
    assert bounded["heartbeat_status"] == original["heartbeat_status"]
    assert Path(bounded["full_response_path"]).is_file()
    assert bounded["response_truncation"]["object_fields_omitted"] > 0


def test_feedback_request_recovery_receipt_survives_bounds(tmp_path):
    original = _result("error context\n" * 100_000)
    original.update({f"extra_{index}": "x" * 1000 for index in range(100)})
    original.update({f"extra_{index}_path": "/" + "z" * 400 for index in range(80)})
    original["feedback_request"] = {
        "request_id": "feedback-" + "c" * 64,
        "request_path": "/capsule/.feedback/requests/request.json",
        "result_path": "/capsule/.feedback/requests/result.json",
        "arguments_sha256": "d" * 64,
    }
    bounded = response.bound_result(original, artifact_dir=tmp_path)
    assert bounded["feedback_request"] == original["feedback_request"]
    assert response.serialized_bytes(response.mcp_response(bounded)) <= response.RESPONSE_BYTE_LIMIT


def test_response_artifact_directory_cannot_follow_a_capsule_symlink(tmp_path):
    capsule, outside = tmp_path / "capsule", tmp_path / "outside"
    capsule.mkdir()
    outside.mkdir()
    (capsule / ".feedback").symlink_to(outside, target_is_directory=True)
    with pytest.raises(ValueError, match="symlinks"):
        response.bound_result(_result("error\n" * 100_000),
                              artifact_dir=capsule / ".feedback" / "responses")
    assert list(outside.iterdir()) == []


def test_response_artifact_existing_symlink_cannot_overwrite_another_file(tmp_path):
    original = _result("error\n" * 100_000)
    bounded = response.bound_result(original, artifact_dir=tmp_path / "responses")
    path = Path(bounded["full_response_path"])
    path.unlink()
    protected = tmp_path / "protected.json"
    protected.write_text("preserve this", encoding="utf-8")
    path.symlink_to(protected)
    with pytest.raises(ValueError, match="different content"):
        response.bound_result(original, artifact_dir=tmp_path / "responses")
    assert protected.read_text(encoding="utf-8") == "preserve this"


@pytest.mark.parametrize("severity,message", [
    ("information", "trace\n" * 100_000),
    ("error", "unsolved goals\n⊢ " + "😀" * 200_000),
    ("warning", "Try this: exact " + '"\\\n' * 200_000),
])
def test_all_diagnostic_severities_have_byte_bounded_excerpts_and_exact_artifacts(tmp_path, severity, message):
    raw = [{"severity": severity, "message": message, "line": 0, "character": 0}]
    shown = diagnostics.present_diagnostics(raw, source="example : True := by trivial")
    path = diagnostics.archive_diagnostics(raw, shown, source="example : True := by trivial",
                                            candidate_path=tmp_path / "Candidate.lean")
    item = shown["diagnostics"][0]
    assert len(item["message"].encode("utf-8")) <= diagnostics.MESSAGE_BYTE_LIMIT
    assert item["location"] == {"scope": "generated", "line": 1, "column": 1}
    assert item["message_truncation"]["omitted_utf8_bytes"] > 0
    assert shown["diagnostics_truncation"]["messages_truncated"] == 1
    artifact = json.loads(path.read_text(encoding="utf-8"))
    assert artifact["raw_diagnostics"] == raw
    assert artifact["mapped_diagnostics"][0]["message"] == message


def test_many_small_errors_obey_total_diagnostic_text_and_serialized_limits():
    raw = [{"severity": "error", "message": f"failure {index}: " + "é" * 50,
            "line": index, "character": 0} for index in range(2000)]
    shown = diagnostics.present_diagnostics(raw)
    inline = shown["diagnostics"]
    metadata = shown["diagnostics_truncation"]
    assert len(inline) < len(raw)
    assert sum(len(item["message"].encode("utf-8")) for item in inline) <= diagnostics.MESSAGE_TOTAL_BYTE_LIMIT
    assert response.serialized_bytes(inline) <= diagnostics.DIAGNOSTICS_BYTE_LIMIT
    assert metadata["inline_json_utf8_bytes"] == response.serialized_bytes(inline)
    assert metadata["diagnostics_omitted"] == len(raw) - len(inline) == shown["diagnostics_compacted"]
    assert len(shown["mapped_diagnostics"]) == len(raw)


def test_compact_diagnostics_direct_call_cannot_bypass_message_budget():
    raw = [{"severity": "error", "message": "x" * 1_000_000}]
    shown, omitted = diagnostics.compact_diagnostics(raw)
    assert omitted == 0
    assert len(shown[0]["message"].encode("utf-8")) <= diagnostics.MESSAGE_BYTE_LIMIT
    assert raw[0]["message"] == "x" * 1_000_000


def test_diagnostic_budget_metadata_counts_grouped_and_information_omissions():
    raw = [{"severity": "warning", "message": "unused variable `x`"}] * 20
    raw += [{"severity": "information", "message": "Goals accomplished!"}]
    raw += [{"severity": "information", "message": "trace"}] * 40
    shown = diagnostics.present_diagnostics(raw, information_limit=1)
    metadata = shown["diagnostics_truncation"]
    assert len(shown["diagnostics"]) == 2
    assert metadata["diagnostics_omitted"] == len(raw) - 2
    assert metadata["original_message_utf8_bytes"] == sum(len(item["message"].encode("utf-8")) for item in raw)
    assert metadata["omitted_message_utf8_bytes"] == metadata["original_message_utf8_bytes"] - metadata["inline_message_utf8_bytes"]


def test_context_reports_message_truncation_even_without_an_omitted_entry(tmp_path):
    source = "example : True := by trivial\n"
    message = "type mismatch\n" + "x" * 100_000
    observation = context.SourceObservation(0.1, ({"severity": "error", "message": message,
                                                   "line": 0, "character": 0},))
    compact, truncated = context.compact_diagnostics(observation, source=source)
    assert truncated is True
    assert len(compact) == 1
    report = context.diagnostic_report(observation, source, candidate_path=tmp_path / "Candidate.lean")
    assert report["diagnostics_compacted"] == 0
    assert report["diagnostics_truncated"] is True
    assert report["diagnostics_truncation"]["messages_truncated"] == 1
    assert json.loads(Path(report["diagnostics_path"]).read_text(encoding="utf-8"))["raw_diagnostics"][0]["message"] == message
