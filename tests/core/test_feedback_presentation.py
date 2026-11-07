"""Real producer/2026-10-27 receipt shapes with synthetic paths and proof text.

The fixtures preserve the fields seen in Sol native events without importing
archived solutions, invoking Lean, or launching a model.
"""
from __future__ import annotations

import copy
import hashlib
import io
import json
from pathlib import Path

import pytest

from lean_tools import feedback_presentation as presentation
from lean_tools import feedback_response as response
from lean_tools import feedback_workflow as workflow
from lean_tools.feedback_requests import inspect_requests

from tests.core.test_feedback_transport_integration import service


def _journal():
    return {"request_id": "request-123", "request_path": "/capsule/.feedback/requests/request-123.json",
            "result_path": "/capsule/.feedback/requests/request-123.result.json", "arguments_sha256": "f" * 64}


def _edit():
    return {"schema_version": 1, "candidate": "/capsule/Candidate.lean", "source_sha256": "a" * 64,
            "snapshot_path": "/capsule/.feedback/sources/source.lean", "mode": "quick",
            "cache": {"status": "miss", "hit": False, "source_mode": None},
            "timing": {"measurement_source": "current_request", "axiom_audit_shares_compile": None,
                       "phase_note": None, "request_wall_seconds": .3, "measurement_compile_seconds": .2,
                       "measurement_axiom_audit_seconds": None},
            "diagnostics": [], "diagnostics_compacted": 0,
            "diagnostics_truncation": {"message_utf8_byte_limit": 4096, "total_message_utf8_byte_limit": 16384,
                "inline_json_utf8_byte_limit": 24576, "inline_json_utf8_bytes": 2, "inline_message_utf8_bytes": 0,
                "original_message_utf8_bytes": 0, "omitted_message_utf8_bytes": 0,
                "messages_truncated": 0, "diagnostics_omitted": 0},
            "diagnostics_path": "/capsule/.feedback/diagnostics/source.json", "status": "valid", "valid": True,
            "tokens": 80, "heartbeat": None, "heartbeat_status": "not_run",
            "checkpoint": "/capsule/valid-candidates/accepted.lean", "checkpoint_id": "accepted.lean",
            "checkpoint_validation": "quick", "checkpoint_receipt_path": "/capsule/valid-candidates/accepted.json",
            "wall_seconds": .4, "details_path": "/capsule/.feedback/results/result.json", "feedback_request": _journal()}


def _score():
    return {"schema_version": 1, "authoritative": False, "candidate": "/capsule/Candidate.lean",
            "base_source_sha256": "b" * 64, "source_sha256": "a" * 64,
            "original_tokens": 200, "original_heartbeats": 4000, "incumbent_score": 85.,
            "wall_seconds": 5., "details_path": "/capsule/.feedback/batches/batch/results.json", "label": "candidate",
            "status": "valid_scored", "valid": True, "tokens": 80, "heartbeats": 200,
            "compatibility_pct": 100., "compatibility_status": "complete", "score": 85.,
            "score_breakdown": {"length_reduction_pct": 60., "heartbeat_reduction_pct": 95., "compatibility_pct": 100.,
                "score_points": {"length": 20., "heartbeats": 31.6667, "compatibility": 33.3333},
                "rounding_adjustment": 0., "score": 85.},
            "incumbent_delta": {"status": "scalar_only", "reason": "missing_binding", "score": 0.},
            "checkpoint": "/capsule/valid-candidates/accepted.lean", "checkpoint_id": "accepted.lean",
            "details_index": 0, "snapshot_path": "/capsule/.feedback/batches/batch/0-source.lean",
            "optimistic_score": 85., "checkpoint_validation": "exact",
            "checkpoint_receipt_path": "/capsule/valid-candidates/accepted.json", "tool": "score_candidate",
            "feedback_request": _journal()}


def _profile():
    environment = {"project_root": "/environment/project", "fingerprint": "c" * 64,
        "launch_guard_sha256": "d" * 64, "prefix_sha256": "e" * 64, "prefix_kind": "project-source-prefix",
        "lean_toolchain": "leanprover/lean4:test", "lean_executable": "/toolchain/bin/lean",
        "launch_cache_status": "hit", "note": "Pinned artifacts are assumed immutable; no dependency-content audit.",
        "lean_githash": "f" * 40}
    span = {"start_byte": 32, "end_byte": 40, "start_line": 2, "start_column": 2, "end_line": 2, "end_column": 10,
        "byte_convention": "half-open UTF-8", "line_convention": "1-based lines, 0-based Unicode code-point columns",
        "text": "by exact h", "text_truncated": False, "text_sha256": "b" * 64,
        "mapping_confidence": "exact_original_parsed_syntax"}
    return {"schema_version": 1, "status": "profiled", "outcome": "complete", "authoritative": False,
        "measurement_mode": "profile", "mode": "regions", "source_sha256": "a" * 64, "instrumented_sha256": "b" * 64,
        "source_kind": "current", "selected_source_path": "/capsule/Candidate.lean", "selected_source_sha256": "a" * 64,
        "snapshot_path": "/capsule/.feedback/profiles/run/Source.lean", "checkpoint": None, "valid": True,
        "note": "Inclusive instrumented observations include overhead; do not add parents to children or treat a region as removable official heartbeats. Ordinary scoring remains authoritative.",
        "truncated": False, "details_path": "/capsule/.feedback/profiles/run/details.json", "timeout_seconds": 30.,
        "budgets": {"timeout_scope": "per_lean_process", "setup_seconds": 30., "maximum_process_seconds": 30,
            "source_validation_process_seconds": 30., "profile_process_seconds": 30., "shared_queue_wait_seconds": 10,
            "total_stage_seconds": 100., "note": "Separate process caps; admission pools share one allowance."},
        "units": {"heartbeats": "raw allocation heartbeats (1000 raw = 1 user-facing heartbeat)",
                  "elapsed": "monotonic nanoseconds", "native_wall_time": "milliseconds"},
        "capability": {"schema_version": 1, "available": True, "supported_modes": ["regions", "wall_time"],
            "outcome": "available", "reason": None, "prefix_sha256": "e" * 64, "source_form": "module",
            "default_timeout_seconds": 30, "max_timeout_seconds": 30, "timeout_scope": "per_lean_process",
            "shared_queue_wait_seconds": 10, "max_default_stage_seconds": 100, "max_top_n": 8, "instrumentation_revision": 3},
        "instrumentation_revision": 3, "environment": environment,
        "uninstrumented_compile_source_sha256": "c" * 64,
        "source_validation": {"status": "compiled", "source_sha256": "a" * 64, "compile_source_sha256": "c" * 64,
            "receipt_path": "/capsule/.feedback/profiles/validation.json", "binding": {"schema_version": 1,
                "source_sha256": "a" * 64, "compile_source_sha256": "c" * 64, "task_sha256": "d" * 64,
                "scoring_policy": "arena-v1", "project_root": "/environment/project",
                "environment": {key: environment[key] for key in ("fingerprint", "launch_guard_sha256", "prefix_sha256", "lean_githash", "lean_toolchain")},
                "compiler_file": {"path": "/toolchain/bin/lean", "size": 100, "mtime_ns": 42, "inode": 12}}},
        "instrumented_path": "/capsule/.feedback/profiles/run/Instrumented.lean", "diagnostics": [],
        "selection_strategy": "unique_outermost_parsed_tactic_sequence", "regions": [{"id": "whole_proof",
            "parent_id": "declaration_command", "inclusive": True, "original_span": span,
            "instrumented_span": {"start_byte": 1000, "end_byte": 1008}, "raw_heartbeats": 1000,
            "user_heartbeat_equivalent": 1., "elapsed_nanoseconds": 100, "observations": 1, "outcome": "measured"}],
        "complete": True, "measurement_outcome": "complete", "missing_regions": [], "repeated_regions": [],
        "containment_mismatches": [], "declaration_command": {"id": "declaration_command", "inclusive": True,
            "scope": "synchronous instrumented command elaborator call", "raw_heartbeats": 1200, "elapsed_nanoseconds": 120},
        "unattributed": {"raw_heartbeats": 200, "elapsed_nanoseconds": 20, "includes": "unselected work and overhead"},
        "useful_region_observations": ["whole_proof"], "instrumentation_overhead": {"status": "not_separately_measured",
            "included_in": "parent counts and unattributed remainder"}, "wall_seconds": 1.,
        "timings": {"stage_wall_seconds": {"launch_preparation": .1, "source_validation": .2, "profile": .6},
            "other_wall_seconds": .1, "queue_wait_seconds": 0., "queue_wait_complete": True,
            "stage_queue_wait_seconds": {"original_compile": 0., "profile": 0.},
            "source_validation_process_seconds": .2, "profile_process_seconds": .6,
            "note": "Process seconds exclude admission; independent caps."}, "feedback_request": _journal()}


def _present(raw, tmp_path, tool):
    return presentation.present_result(raw, artifact_dir=tmp_path / "responses", policy="compact-v1", tool=tool)


@pytest.mark.parametrize("tool,factory", [("edit_check", _edit), ("score_candidate", _score), ("profile_proof", _profile)])
def test_legacy_is_exact_identity_and_does_not_write(tmp_path, tool, factory):
    raw = factory()
    assert presentation.present_result(raw, artifact_dir=tmp_path / "missing", tool=tool) is raw
    assert not (tmp_path / "missing").exists()


@pytest.mark.parametrize("tool,factory", [("edit_check", _edit), ("score_candidate", _score), ("profile_proof", _profile)])
def test_archive_is_exact_content_addressed_and_non_mutating(tmp_path, tool, factory):
    raw = factory()
    before = copy.deepcopy(raw)
    compact = _present(raw, tmp_path, tool)
    path = Path(compact["full_response_path"])
    encoded = path.read_bytes()
    assert path.name == hashlib.sha256(encoded).hexdigest() + ".json"
    assert json.loads(encoded) == {"schema_version": 1, "result": before}
    assert raw == before
    assert compact["response_presentation"]["policy"] == "compact-v1"
    assert compact["response_presentation"]["omitted_fields"] > 0
    assert _present(compact, tmp_path, tool) is compact
    assert _present(raw, tmp_path, tool) == compact
    assert len(list(path.parent.iterdir())) == 1


@pytest.mark.parametrize("tool,factory", [("edit_check", _edit), ("score_candidate", _score), ("profile_proof", _profile)])
def test_all_non_bookkeeping_semantics_and_future_fields_survive(tmp_path, tool, factory):
    raw = factory()
    raw["future_semantics"] = {"goal": "∀ p, p → p", "values": [None, 0, False]}
    compact = _present(raw, tmp_path, tool)
    omitted = {"snapshot_path", "details_path", "wall_seconds", "checkpoint_receipt_path", "feedback_request",
               "diagnostics_compacted", "diagnostics_truncation", "timing", "cache", "details_index",
               "instrumented_path", "capability", "timings", "budgets", "environment", "source_validation"}
    assert {key: value for key, value in compact.items() if key in raw and key not in omitted} == {
        key: value for key, value in raw.items() if key not in omitted}
    assert compact["feedback_request"] == {"request_id": raw["feedback_request"]["request_id"]}
    assert compact["future_semantics"] == raw["future_semantics"]


def test_profile_keeps_all_units_caveats_and_source_environment_binding(tmp_path):
    raw = _profile()
    compact = _present(raw, tmp_path, "profile_proof")
    for key in ("units", "note", "instrumentation_overhead", "regions", "declaration_command", "unattributed"):
        assert compact[key] == raw[key]
    for key in ("fingerprint", "launch_guard_sha256", "prefix_sha256", "lean_toolchain", "lean_githash", "note"):
        assert compact["environment"][key] == raw["environment"][key]
    assert compact["source_validation"]["binding"] == {
        "schema_version": 1, "task_sha256": "d" * 64, "scoring_policy": "arena-v1"}
    assert "source_sha256" in compact and compact["selected_source_sha256"] == raw["selected_source_sha256"]


@pytest.mark.parametrize("status", ["invalid", "timeout", "check_failed", "infrastructure_error"])
def test_edit_failures_keep_complete_actionable_diagnostics_and_goals(tmp_path, status):
    raw = _edit()
    raw.update(status=status, valid=False if status == "invalid" else None,
        error="failure\n" + "detail😀" * 2000,
        diagnostics=[{"severity": "error", "message": "unsolved goals\n" + "x : α\n" * 2000,
            "location": {"scope": "candidate", "line": 4, "column": 2},
            "generated_position": {"line": 100, "character": 1, "encoding": "utf-16"}}],
        goals="case left\nh : P\n⊢ P", goal_position={"line": 4, "column": 2},
        goal_handles=[{"goal_id": "goal-1", "goal": {"line": 4, "column": 2, "index": 0}}], default_goal_id="goal-1",
        goal_details_path="/capsule/.feedback/goals/full.json",
        unfinished_cases={"status": "complete", "cases": [{"goal_id": "goal-1", "target_preview": "P",
            "local_context": ["h : P"]}], "total_cases": 1, "details_path": "/capsule/.feedback/cases/full.json"})
    compact = _present(raw, tmp_path, "edit_check")
    for key in ("status", "valid", "error", "diagnostics", "goals", "goal_position", "goal_handles", "default_goal_id",
                "goal_details_path", "unfinished_cases", "diagnostics_path", "cache", "timing"):
        assert compact[key] == raw[key]


@pytest.mark.parametrize("status", ["unsupported", "timeout", "unavailable", "invalid"])
def test_failed_profiles_keep_menu_timeout_repair_context_and_observations(tmp_path, status):
    raw = _profile()
    raw.update(status=status, outcome="unsupported_region", complete=False, error="Choose an exact parsed byte span",
        retry_hint="Retry explicitly after the lock is released.", timeout_stage="profile_queue",
        region_menu={"source_sha256": raw["source_sha256"], "regions": [{"id": "region_1",
            "original_span": raw["regions"][0]["original_span"], "selector": {"id": "region_1", "start_byte": 32, "end_byte": 40}}],
            "truncated": False, "selection_hint": "Copy exact selectors with the same expected_sha256."})
    compact = _present(raw, tmp_path, "profile_proof")
    for key in ("error", "retry_hint", "timeout_stage", "region_menu", "regions", "complete", "capability", "timings", "budgets"):
        assert compact[key] == raw[key]


def test_wall_time_keeps_thread_aggregation_and_all_accounting_caveats(tmp_path):
    raw = _profile()
    raw.update(mode="wall_time", hotspots=[{"label": "Lean.Parser.Tactic.exact", "exclusive_slice_milliseconds": 1.2,
        "original_span": None, "mapping_confidence": "unavailable_native_label_only"}],
        wall_time_milliseconds=4.2, unattributed_milliseconds=3.,
        thread_aggregation="Sum of native thread slices; may include concurrent work and is not elapsed process wall time.",
        boundary="native runFrontend including imports and prefix", grouping="exclusive slices by nearest tactic label",
        native_slice_accounting={"raw_trace_unchanged": True, "policy": "No sorting or cancellation across labels/threads."},
        native_profile_path="/capsule/.feedback/profiles/run/native-wall-time.json")
    compact = _present(raw, tmp_path, "profile_proof")
    for key in ("hotspots", "wall_time_milliseconds", "unattributed_milliseconds", "thread_aggregation", "boundary",
                "grouping", "native_slice_accounting", "native_profile_path", "units", "note"):
        assert compact[key] == raw[key]


@pytest.mark.parametrize("field,unknown", [("schema_version", 2), ("schema_version", True), ("mode", {}),
    ("valid", "true"), ("tool", "future_tool")])
def test_unrecognized_receipt_shapes_pass_through(tmp_path, field, unknown):
    raw = _edit()
    raw[field] = unknown
    assert _present(raw, tmp_path, "edit_check") is raw
    assert not (tmp_path / "responses").exists()


def test_unknown_nested_metadata_is_never_omitted(tmp_path):
    raw = _profile()
    raw["capability"]["new_required_action"] = "Repair the launch environment"
    raw["timings"]["profile_process_seconds"] = {"error": "unavailable"}
    raw["budgets"]["setup_seconds"] = {"error": "unknown"}
    raw["source_validation"]["binding"]["compiler_file"]["new_requirement"] = "Keep compiler state"
    compact = _present(raw, tmp_path, "profile_proof")
    for key in ("capability", "timings", "budgets"):
        assert compact[key] == raw[key]
    assert compact["source_validation"]["binding"]["compiler_file"] == raw["source_validation"]["binding"]["compiler_file"]


def test_actual_diagnostic_omission_metadata_and_unique_evidence_paths_survive(tmp_path):
    raw = _edit()
    raw["diagnostics_truncation"].update(messages_truncated=1, omitted_message_utf8_bytes=100)
    raw["diagnostics_compacted"] = 4
    raw["checkpoint_receipt_path"] = "/capsule/special-validation.json"
    raw["feedback_request"]["new_recovery_path"] = "/capsule/new.json"
    compact = _present(raw, tmp_path, "edit_check")
    for key in ("diagnostics_truncation", "diagnostics_compacted", "checkpoint_receipt_path", "feedback_request"):
        assert compact[key] == raw[key]


def test_comparison_keeps_ranking_all_alternatives_failures_and_pruning_semantics(tmp_path):
    row = _score()
    row.pop("feedback_request")
    row.pop("tool")
    other = copy.deepcopy(row)
    other.update(label="loser", status="valid_pruned", score=None, compatibility_status="skipped_optimistic_bound",
                 pruning_floor=90., optimistic_score=85., incumbent_delta=None)
    raw = {"schema_version": 1, "status": "completed", "authoritative": False, "candidate": row["candidate"],
           "base_source_sha256": row["base_source_sha256"], "original_tokens": 200, "original_heartbeats": 4000,
           "alternatives": [row, other], "ranking": ["candidate"], "best_label": "candidate",
           "details_path": row["details_path"], "wall_seconds": 5., "feedback_request": _journal()}
    compact = _present(raw, tmp_path, "compare_candidates")
    assert compact["ranking"] == raw["ranking"] and compact["best_label"] == raw["best_label"]
    for original, inline in zip(raw["alternatives"], compact["alternatives"]):
        for key in ("label", "status", "valid", "source_sha256", "base_source_sha256", "score", "score_breakdown",
                    "compatibility_pct", "compatibility_status", "checkpoint", "checkpoint_id", "incumbent_delta", "optimistic_score"):
            assert inline[key] == original[key]
    assert compact["alternatives"][1]["pruning_floor"] == 90.


@pytest.mark.parametrize("envelope", [lambda value: response.mcp_response(value, "native-😀"),
    lambda value: {"stdout": response.json_text(value)},
    lambda value: {"content": [{"type": "text", "text": response.json_text(response.mcp_response(value, "nested"))}]}])
def test_native_cli_and_replay_bounding_keep_original_receipt(tmp_path, envelope):
    raw = _edit()
    raw.update(valid=False, status="invalid", diagnostics=[{"severity": "error", "message": '😀\\"\n' * 100_000}])
    compact = _present(raw, tmp_path, "edit_check")
    first = response.bound_result(compact, artifact_dir=tmp_path / "responses", envelope=envelope)
    second = response.bound_result(first, artifact_dir=tmp_path / "responses", envelope=envelope, max_response_bytes=4096)
    assert response.serialized_bytes(envelope(first)) <= response.RESPONSE_BYTE_LIMIT
    assert response.serialized_bytes(envelope(second)) <= 4096
    assert first["full_response_path"] == second["full_response_path"] == compact["full_response_path"]
    assert json.loads(Path(second["full_response_path"]).read_text())["result"] == raw
    assert first["response_presentation"]["policy"] == "compact-v1"
    assert len(list((tmp_path / "responses").iterdir())) == 1


def test_archive_failure_does_not_mutate_or_return_a_lossy_receipt(tmp_path, monkeypatch):
    raw = _edit()
    before = copy.deepcopy(raw)
    def fail(*_):
        raise OSError("disk unavailable")
    monkeypatch.setattr(response, "archive_result", fail)
    with pytest.raises(OSError, match="disk unavailable"):
        _present(raw, tmp_path, "edit_check")
    assert raw == before


def test_compact_archive_refuses_symlink_escape(tmp_path):
    outside = tmp_path / "outside"
    outside.mkdir()
    (tmp_path / "responses").symlink_to(outside, target_is_directory=True)
    with pytest.raises(ValueError, match="symlinks"):
        _present(_edit(), tmp_path, "edit_check")
    assert list(outside.iterdir()) == []


def test_small_receipts_never_inflate_or_create_unused_artifacts(tmp_path):
    raw = {"schema_version": 1, "status": "valid", "valid": True, "mode": "quick", "wall_seconds": .2}
    assert _present(raw, tmp_path, "edit_check") is raw
    assert not (tmp_path / "responses").exists()


@pytest.mark.parametrize("policy", [[], {}, None, 1, True, "typo"])
def test_invalid_policy_types_are_reported_as_value_errors(tmp_path, policy):
    with pytest.raises(ValueError, match="policy"):
        presentation.present_result(_edit(), artifact_dir=tmp_path, policy=policy)


@pytest.mark.parametrize("field", ["mode", "operation", "tool"])
def test_unhashable_unknown_discriminators_pass_through(tmp_path, field):
    raw = _edit()
    raw[field] = {"future": ["shape"]}
    assert _present(raw, tmp_path, "edit_check") is raw


def test_archive_publication_fsyncs_receipt_and_directory_before_returning(tmp_path, monkeypatch):
    import os
    real_fsync = response.os.fsync
    synced = []
    def record(descriptor):
        synced.append(os.fstat(descriptor).st_mode)
        real_fsync(descriptor)
    monkeypatch.setattr(response.os, "fsync", record)
    compact = _present(_edit(), tmp_path, "edit_check")
    assert Path(compact["full_response_path"]).is_file()
    assert len(synced) == (1 if os.name == "nt" else 2)


def test_rebounding_does_not_trust_a_non_content_addressed_original(tmp_path):
    raw = _edit()
    raw["diagnostics"] = [{"message": "x" * 200_000}]
    compact = _present(raw, tmp_path, "edit_check")
    fake = tmp_path / "responses" / "not-a-hash.json"
    fake.write_text(json.dumps({"schema_version": 1, "result": {"unrelated": True}}))
    compact["full_response_path"] = str(fake)
    bounded = response.bound_result(compact, artifact_dir=tmp_path / "responses")
    assert bounded["full_response_path"] != str(fake)
    assert json.loads(Path(bounded["full_response_path"]).read_text())["result"] == compact


def test_invalid_policy_and_non_object_inputs_are_rejected(tmp_path):
    with pytest.raises(ValueError, match="policy"):
        presentation.present_result(_edit(), artifact_dir=tmp_path, policy="typo")
    with pytest.raises(TypeError, match="object"):
        presentation.present_result([], artifact_dir=tmp_path, policy="compact-v1")


@pytest.mark.parametrize("policy", [None, True, 0, "compact", "COMPACT-V1", [], {}])
def test_capsule_and_feedback_validate_response_policy_before_persisting(tmp_path, policy):
    with pytest.raises(ValueError, match="response_policy"):
        workflow.configure_capsule(tmp_path, tmp_path, response_policy=policy)
    assert not (tmp_path / workflow.CONFIG_NAME).exists()
    with pytest.raises(ValueError, match="response_policy"):
        workflow.Feedback({"response_policy": policy})


@pytest.mark.parametrize("policy", ["legacy", "compact-v1"])
def test_capsule_freezes_only_nonlegacy_response_policy(tmp_path, policy):
    path = workflow.configure_capsule(tmp_path, tmp_path, response_policy=policy)
    settings = json.loads(path.read_text())
    if policy == "legacy":
        assert "response_policy" not in settings
    else:
        assert settings["response_policy"] == policy


@pytest.mark.parametrize("policy", [None, "legacy", "compact-v1"])
def test_native_presentation_preserves_raw_journal_bytes_and_archive(service, monkeypatch, policy):
    settings = dict(service.settings)
    if policy is not None:
        settings["response_policy"] = policy
    service = workflow.Feedback(settings)
    raw = _edit()
    raw.update(candidate=str(service.candidate),
               source_sha256=workflow.arena.sha256_file(service.candidate))
    before = copy.deepcopy(raw)
    monkeypatch.setattr(service, "check", lambda _request: raw)
    journal_bytes = []
    present = presentation.present_result

    def capture(value, **kwargs):
        path = Path(value["feedback_request"]["result_path"])
        journal_bytes.append((path, path.read_bytes()))
        return present(value, **kwargs)

    monkeypatch.setattr(presentation, "present_result", capture)
    identity = "receipt-native-42"
    request = {"jsonrpc": "2.0", "id": identity, "method": "tools/call",
               "params": {"name": "edit_check", "arguments": {}}}
    output = io.StringIO()
    workflow.serve(service, io.StringIO(response.json_text(request) + "\n"), output)
    wire = output.getvalue()
    assert len(wire.encode("utf-8")) <= response.RESPONSE_BYTE_LIMIT
    reply = json.loads(wire)
    shown = json.loads(reply["result"]["content"][0]["text"])
    assert reply["id"] == identity and reply["result"]["isError"] is False
    assert raw == before
    assert len(journal_bytes) == 1
    path, encoded = journal_bytes[0]
    assert path.read_bytes() == encoded
    durable = json.loads(encoded)
    assert "response_presentation" not in durable and "full_response_path" not in durable
    receipt, = inspect_requests(service.root)["requests"]
    assert receipt["phase"] == "completed"
    assert receipt["transport"]["kind"] == "mcp_stdio"
    assert receipt["transport"]["json_rpc_id"] == identity
    assert receipt["transport"]["state"] == "written"
    assert durable["feedback_request"]["request_id"] == receipt["request_id"]
    if policy == "compact-v1":
        assert shown["response_presentation"]["policy"] == policy
        assert json.loads(Path(shown["full_response_path"]).read_text())["result"] == durable
        assert shown["feedback_request"] == {"request_id": receipt["request_id"]}
        assert len(wire.encode("utf-8")) < response.serialized_bytes(response.mcp_response(durable, identity)) + 1
        for key in ("source_sha256", "candidate", "tokens", "heartbeat", "heartbeat_status",
                    "checkpoint", "checkpoint_id", "diagnostics", "diagnostics_path"):
            assert shown[key] == durable[key]
    else:
        assert shown == durable
        assert not (service.root / ".feedback" / "responses").exists()
