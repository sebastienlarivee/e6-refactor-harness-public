"""Frozen token-efficiency settings reach real capsules and durable MCP replies."""
from dataclasses import replace
import io
import json
from pathlib import Path

import pytest

from e6 import prompt_bundle, proof, run
from e6.experiment import (
    DEFAULT_PANEL_SPEC, DEFAULT_RUN_SPEC, DEFAULT_SPEC, EFFICIENT_CONTROL_PROMPT,
    ExperimentSpec, experiment_spec,
)
from lean_tools import arena_workflow as arena
from lean_tools import feedback_response, feedback_workflow as feedback
from lean_tools.feedback_requests import inspect_requests
from tests.core.test_efficient_candidate_roundtrips import evaluation


def rebuild_settings(root, *, variant=EFFICIENT_CONTROL_PROMPT):
    """Build a portable source-bound capsule fixture without Lean or inference."""
    root.mkdir()
    row = {"name": "Reference.task", "signature": "theorem Reference.task : True",
           "header": "", "contexts": [], "file_path": "Target.lean", "start_line": 3,
           "src": "theorem Reference.task : True := by\n  trivial -- ORIGINAL_PROOF_REFERENCE\n"}
    primary = root / "primary"
    primary.mkdir()
    (primary / "Target.lean").write_text("\n\n" + row["src"])
    (primary / "lean-toolchain").write_text("leanprover/lean4:v4.29.1")
    (primary / "lake-manifest.json").write_text('{"packages":[]}')
    task, registry = root / "Task.json", root / "environment-fingerprints.json"
    arena.write_json_atomic(task, {"schema_version": 1, "row": row})
    arena.write_json_atomic(registry, {"schema_version": arena.FINGERPRINT_REGISTRY_SCHEMA_VERSION,
        "entries": {arena.environment_fingerprint_registry_key(row, primary): {
            "fingerprint": "b" * 64, "lean_version": "Synthetic Lean",
            "guard_sha256": arena.environment_fingerprint_guard_sha256(row, primary)}}})
    spec = replace(DEFAULT_RUN_SPEC, prompt_variant=variant)
    settings = {**spec.proof_settings(), "root": str(root), "task": str(task),
        "fingerprint_registry": str(registry), "primary": str(primary), "compatibility": [],
        "original_tokens": 100, "original_heartbeats": 500, "label": "toy",
        "task_id": row["name"], "task_sha256": arena.sha256_file(task),
        "proof_metadata_sha256": "m" * 64}
    source = arena.render_candidate_scaffold(row)
    settings["initial_best"] = {**proof._incumbent_metadata(settings), "source": source,
        "sha256": proof._digest(source), "tokens": 100, "heartbeats": 500,
        "compatibility_pct": 100, "score": proof._policy(settings).score(
            tokens=100, heartbeats=500, compatibility_pct=100),
        "valid": True, "compatibility_complete": True,
        "evaluation": {"heartbeat": {"environment_fingerprint": "b" * 64}}}
    settings["prompt_bundle"] = prompt_bundle.snapshot(variant)
    (root / "proof-guide.md").write_text(prompt_bundle.render_guide(settings))
    arena.write_json_atomic(root / "config.json", settings)
    return settings, row


def efficient_spec(**changes):
    return replace(DEFAULT_RUN_SPEC, **changes)


def capsule_settings(root, *, mode="reference_rebuild"):
    settings, row = rebuild_settings(root, variant=EFFICIENT_CONTROL_PROMPT)
    spec = efficient_spec(first_pass_reprove=mode == "statement_first_reprove",
                          first_pass_reference_rebuild=mode == "reference_rebuild")
    settings.update(spec.proof_settings())
    settings["initial_best"].update(proof._incumbent_metadata(settings))
    settings["initial_best"]["score"] = proof._policy(settings).score(
        tokens=100, heartbeats=500, compatibility_pct=100)
    settings["prompt_bundle"] = prompt_bundle.snapshot(EFFICIENT_CONTROL_PROMPT)
    (root / "proof-guide.md").write_text(prompt_bundle.render_guide(settings))
    arena.write_json_atomic(root / "config.json", settings)
    return settings, row


def serve_value(service, tool, arguments, *, identity="efficient-native-42"):
    request = {"jsonrpc": "2.0", "id": identity, "method": "tools/call",
               "params": {"name": tool, "arguments": arguments}}
    output = io.StringIO()
    feedback.serve(service, io.StringIO(json.dumps(request) + "\n"), output)
    wire = output.getvalue()
    reply = json.loads(wire)
    assert reply["id"] == identity
    assert len(wire.encode("utf-8")) <= feedback_response.RESPONSE_BYTE_LIMIT
    assert reply["result"]["isError"] is False
    return json.loads(reply["result"]["content"][0]["text"]), wire


def durable_result(service, request_id):
    receipt, = inspect_requests(service.root, request_id=request_id)["requests"]
    assert receipt["phase"] == "completed"
    return receipt, json.loads(Path(receipt["result_path"]).read_text())


@pytest.mark.parametrize("spec", [DEFAULT_SPEC, DEFAULT_RUN_SPEC, DEFAULT_PANEL_SPEC])
def test_all_defaults_use_the_single_production_prompt_contract(spec):
    assert spec.prompt_variant == EFFICIENT_CONTROL_PROMPT
    assert spec.response_policy == "compact-v1" and spec.candidate_batches
    assert spec.unfinished_cases and spec.regional_profiler
    for saved in (spec.common_settings(), spec.proof_settings(), spec.panel_settings()):
        assert saved["prompt_variant"] == saved["experiment_spec"]["prompt_variant"] == EFFICIENT_CONTROL_PROMPT
        assert saved["response_policy"] == saved["experiment_spec"]["response_policy"] == "compact-v1"
    assert ExperimentSpec.from_dict(spec.to_dict()).to_dict() == spec.to_dict()



@pytest.mark.parametrize("policy", [None, True, 0, "compact", "COMPACT-V1", [], {}])
def test_response_policy_rejects_nonversioned_or_nonstring_values(tmp_path, policy):
    with pytest.raises(ValueError, match="response_policy"):
        replace(DEFAULT_SPEC, response_policy=policy)
    with pytest.raises(ValueError, match="response_policy"):
        feedback.configure_capsule(tmp_path, tmp_path / "primary", response_policy=policy)
    assert not (tmp_path / feedback.CONFIG_NAME).exists()
    with pytest.raises(ValueError, match="response_policy"):
        feedback.Feedback({"response_policy": policy})


def test_compact_response_policy_roundtrips_and_rejects_alias_drift():
    spec = efficient_spec()
    assert ExperimentSpec.from_dict(json.loads(json.dumps(spec.to_dict()))) == spec
    for saved in (spec.proof_settings(), spec.panel_settings()):
        assert saved["response_policy"] == saved["experiment_spec"]["response_policy"] == "compact-v1"
        assert experiment_spec(json.loads(json.dumps(saved))) == spec
        with pytest.raises(ValueError, match="response_policy"):
            experiment_spec({**saved, "response_policy": "legacy"})
    with pytest.raises(ValueError, match="response_policy"):
        experiment_spec({**DEFAULT_SPEC.proof_settings(), "response_policy": "legacy"})
    # Missing top-level aliases are legal in frozen snapshots; the nested spec
    # remains authoritative and does not silently fall back to legacy replies.
    saved = spec.proof_settings()
    del saved["response_policy"]
    assert experiment_spec(saved).response_policy == "compact-v1"


def test_efficient_cost_policy_preserves_full_budget_and_unbounded_passes():
    spec = efficient_spec(stopping_policy="cost")
    assert spec.budget_text == "3"
    assert spec.max_passes is None
    assert [spec.pass_mode(number) for number in (1, 2, 3, 4)] == [
        "reference_rebuild", "refactor", "refactor", "refactor"]
    saved = spec.proof_settings()
    assert saved["total_budget_usd"] == 3
    assert "max_passes" not in saved and "max_passes" not in saved["experiment_spec"]
    assert experiment_spec(json.loads(json.dumps(saved))) == spec


@pytest.mark.parametrize("changes", [
    {"candidate_batches": False}, {"unfinished_cases": False}, {"regional_profiler": False},
    {"local_attempts_guidance": True}, {"search_extensions": True},
    {"check_timeout_seconds": 2}, {"rerank_config": None},
])
def test_efficient_prompt_requires_the_feedback_and_batch_tool_contract(changes):
    with pytest.raises(ValueError):
        replace(efficient_spec(), **changes)


def test_efficient_bundle_is_separately_pinned_and_detects_source_drift(tmp_path, monkeypatch):
    selected = prompt_bundle.source_paths(EFFICIENT_CONTROL_PROMPT)
    assert len(selected) == 7
    assert all(path.parent.name == EFFICIENT_CONTROL_PROMPT for path in selected)
    snapshot = prompt_bundle.snapshot(EFFICIENT_CONTROL_PROMPT)
    assert snapshot["variant"] == EFFICIENT_CONTROL_PROMPT
    assert snapshot["base_prompt_variant"] == "control-feedback-v2"
    assert snapshot["source_hashes"] == {path.name: arena.sha256_file(path) for path in selected}
    before, after = run.source_hashes(), run.source_hashes(EFFICIENT_CONTROL_PROMPT)
    assert before == after
    assert set(map(str, selected)) <= set(after)
    assert all(after[str(path)] == snapshot["source_hashes"][path.name] for path in selected)
    copies = []
    for original in selected:
        copied = tmp_path / original.name
        copied.write_bytes(original.read_bytes())
        copies.append(copied)
    monkeypatch.setattr(prompt_bundle, "source_paths", lambda _variant: copies)
    settings = efficient_spec().proof_settings()
    settings["prompt_bundle"] = snapshot
    prompt_bundle.verify_snapshot(settings)
    copies[0].write_text(copies[0].read_text() + "\nchanged after preparation\n")
    with pytest.raises(ValueError, match="Frozen approved prompt bundle"):
        prompt_bundle.verify_snapshot(settings)


@pytest.mark.parametrize("mode,pass_number", [
    ("reference_rebuild", 1), ("statement_first_reprove", 1),
    ("refactor", 1), ("refactor", 2),
])
def test_efficient_capsules_render_pass_modes_and_forward_frozen_feedback_policy(
        tmp_path, monkeypatch, mode, pass_number):
    settings, row = capsule_settings(tmp_path / "run", mode=mode)
    root = Path(settings["root"])
    incumbent = settings["initial_best"]
    if pass_number > 1:
        arena.write_json_atomic(root / "pass-001/selection.json", incumbent)
    monkeypatch.setattr(proof, "_verify_config", prompt_bundle.verify_snapshot)
    capsule = proof.make_capsule(root, pass_number, incumbent["source"])
    actual_mode = json.loads((capsule / "pass-mode.json").read_text())
    assert actual_mode["mode"] == mode
    config = json.loads((capsule / "feedback-config.json").read_text())
    assert config["response_policy"] == "compact-v1"
    assert config["candidate_batches"] is True
    assert {"edit_check", "score_candidate", "compare_candidates", "unfinished_cases", "profile_proof"} <= set(config["enabled_tools"])
    service = feedback.Feedback(config)
    assert service.settings["response_policy"] == "compact-v1"
    for name in ("prompt.md", "AGENTS.md", "COMMANDS.md", "LEAN_PROOF_GUIDE.md"):
        text = (capsule / name).read_text()
        assert "{{" not in text and "}}" not in text
    guidance = "\n".join((capsule / name).read_text() for name in ("prompt.md", "COMMANDS.md", "AGENTS.md"))
    assert "score_candidate" in guidance and "compare_candidates" in guidance
    assert "full_response_path" in guidance
    assert (capsule / "LEAN_PROOF_GUIDE.md").read_bytes() == (root / "proof-guide.md").read_bytes()
    if mode == "reference_rebuild":
        assert (capsule / "Original.lean").read_text() == incumbent["source"]
        assert "ORIGINAL_PROOF_REFERENCE" not in (capsule / "Candidate.lean").read_text()
        assert actual_mode["starting_candidate_valid"] is False
    elif mode == "statement_first_reprove":
        assert "ORIGINAL_PROOF_REFERENCE" not in (capsule / "Candidate.lean").read_text()
        assert "ORIGINAL_PROOF_REFERENCE" not in (capsule / "Task.json").read_text()
    else:
        assert (capsule / "Candidate.lean").read_text() == incumbent["source"]


def test_compact_capsule_native_score_keeps_metrics_and_recovers_full_execution_receipt(tmp_path, monkeypatch):
    settings, _row = capsule_settings(tmp_path / "run")
    root = Path(settings["root"])
    monkeypatch.setattr(proof, "_verify_config", prompt_bundle.verify_snapshot)
    capsule = proof.make_capsule(root, 1, settings["initial_best"]["source"])
    service = feedback.Feedback(json.loads((capsule / "feedback-config.json").read_text()))
    before = service.candidate.read_bytes()
    calls = []

    def evaluate(_task, snapshot, project, *, quick, **_kwargs):
        calls.append((snapshot.read_text(), project, quick))
        return evaluation(snapshot, quick=quick)

    monkeypatch.setattr(arena, "evaluate_candidate", evaluate)
    shown, wire = serve_value(service, "score_candidate", {
        "expected_sha256": arena.sha256_bytes(before), "body": "by exact True.intro"})
    assert len(calls) == 2 and [call[2] for call in calls] == [True, False]
    assert service.candidate.read_bytes() == before
    assert shown["status"] == "valid_scored" and shown["valid"] is True
    assert shown["tokens"] == 10 and shown["heartbeats"] == 20
    assert shown["compatibility_status"] == "complete" and shown["compatibility_pct"] == 100
    assert shown["response_presentation"]["policy"] == "compact-v1"
    assert shown["response_presentation"]["omitted_fields"] > 0
    receipt, durable = durable_result(service, shown["feedback_request"]["request_id"])
    assert receipt["transport"]["kind"] == "mcp_stdio"
    assert receipt["transport"]["json_rpc_id"] == "efficient-native-42"
    assert receipt["transport"]["state"] == "written"
    assert durable["feedback_request"]["result_path"] == receipt["result_path"]
    assert "response_presentation" not in durable
    assert json.loads(Path(shown["full_response_path"]).read_text())["result"] == durable
    for key in ("score", "tokens", "heartbeats", "source_sha256", "checkpoint", "checkpoint_id",
                "score_breakdown", "incumbent_delta"):
        assert shown[key] == durable[key]
    assert arena.sha256_file(Path(shown["checkpoint"])) == shown["source_sha256"]
    assert durable["details_path"] and durable["snapshot_path"]
    assert "details_path" not in shown and "snapshot_path" not in shown
    assert len(wire.encode("utf-8")) < len(feedback_response.json_text(feedback_response.mcp_response(durable, "efficient-native-42")).encode("utf-8"))


@pytest.mark.parametrize("explicit_legacy", [False, True])
def test_legacy_native_results_preserve_the_complete_small_payload(tmp_path, monkeypatch, explicit_legacy):
    settings, _row = rebuild_settings(tmp_path / "run")
    capsule = Path(settings["root"])
    (capsule / "Candidate.lean").write_text(settings["initial_best"]["source"])
    config_path = feedback.configure_capsule(capsule, Path(settings["primary"]))
    config = json.loads(config_path.read_text())
    assert "response_policy" not in config
    if explicit_legacy:
        config["response_policy"] = "legacy"
    service = feedback.Feedback(config)
    original = {"schema_version": 1, "status": "valid", "valid": True,
                "source_sha256": arena.sha256_file(service.candidate),
                "cache": {"warm": True}, "wall_seconds": 0.123,
                "diagnostics": [{"severity": "information", "message": "Try this: trivial"}],
                "details_path": str(capsule / "complete-details.json")}
    monkeypatch.setattr(service, "check", lambda _request: original)
    shown, _wire = serve_value(service, "edit_check", {})
    _receipt, durable = durable_result(service, shown["feedback_request"]["request_id"])
    assert shown == durable == {**original, "feedback_request": shown["feedback_request"]}
    assert "response_presentation" not in shown and "full_response_path" not in shown
    assert not (capsule / ".feedback/responses").exists()


@pytest.mark.parametrize("variant", ["baseline", "control-approved-v1", "control-feedback-v2"])
def test_historical_prompts_require_the_original_frozen_release(variant):
    with pytest.raises(ValueError, match="original frozen release"):
        replace(DEFAULT_SPEC, prompt_variant=variant)
    with pytest.raises(ValueError, match="original frozen release"):
        ExperimentSpec.from_dict({**DEFAULT_SPEC.to_dict(), "prompt_variant": variant})
    with pytest.raises(ValueError, match="original frozen release"):
        prompt_bundle.source_paths(variant)


def test_unversioned_frozen_configs_cannot_silently_select_another_prompt():
    with pytest.raises(ValueError, match="original frozen release"):
        experiment_spec({"stopping_policy": "cost"})
    saved = DEFAULT_SPEC.to_dict()
    saved.pop("prompt_variant")
    with pytest.raises(ValueError, match="original frozen release"):
        ExperimentSpec.from_dict(saved)


@pytest.mark.parametrize("policy", ["cost", "convergence", "screening"])
def test_new_run_resolution_uses_the_same_production_prompt_for_each_stopping_policy(tmp_path, policy):
    from e6.experiment import resolve_spec
    spec = resolve_spec(tmp_path, stopping_policy=policy)
    assert spec.prompt_variant == EFFICIENT_CONTROL_PROMPT
    assert spec.response_policy == "compact-v1" and spec.candidate_batches
    assert spec.first_pass_reference_rebuild and not spec.first_pass_reprove
    assert spec.scoring_policy == "arena-v1"
