"""Product optimizer recovery tests. All compiler/engine calls are scripted."""
from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from e6 import proof
from e6.experiment import ExperimentSpec, experiment_spec
from harness import optimizer

_REAL_OPTIMIZE = optimizer.deterministic.optimize


@pytest.fixture
def cell(tmp_path, monkeypatch):
    root = tmp_path / "proof"
    root.mkdir()
    capsule = root / "pass-001"
    capsule.mkdir()
    task = root / "Task.json"
    task.write_text('{"name":"test"}')
    registry = root / "environment-fingerprints.json"
    registry.write_text('{"entries":{}}')
    config = {"root": str(root), "optimizer": "compact", "label": "test",
        "task_id": "test", "proof_metadata_sha256": "metadata",
        "task": str(task), "task_sha256": hashlib.sha256(task.read_bytes()).hexdigest(),
        "fingerprint_registry": str(registry),
        "fingerprint_registry_sha256": hashlib.sha256(registry.read_bytes()).hexdigest(),
        "primary": str(tmp_path / "primary"), "compatibility": [str(tmp_path / "compat")],
        "original_tokens": 100, "original_heartbeats": 100,
        "experiment_spec": ExperimentSpec().to_dict()}

    def candidate(source, tokens, heartbeats):
        return {**proof._incumbent_metadata(config), "source": source,
            "sha256": proof._digest(source), "tokens": tokens, "heartbeats": heartbeats,
            "score": proof._policy(config).score(tokens=tokens, heartbeats=heartbeats, compatibility_pct=100),
            "valid": True, "compatibility_complete": True, "compatibility_pct": 100,
            "selected_path": str(capsule / "Selected.lean")}

    original = candidate("by exact True.intro\n", 80, 70)
    improved = candidate("by trivial\n", 30, 20)
    (capsule / "Selected.lean").write_text(original["source"])
    selection = {**original, "candidate_records": [{"valid": False}], "validation_healthy": True,
                 "unique_candidate_count": 1}
    (capsule / "selection.json").write_text(json.dumps(selection))
    calls, checks, dictionary_calls = [], [], []
    report = {"status": "completed", "evaluated_candidates": 11, "accepted_candidates": 1,
        "health_status": "degraded", "health_counts": {"cache_errors": 2, "generator_invalid": 3},
        "warnings": ["cache_errors", "generator_invalid"], "errors": [{"phase": "cache", "type": "OSError"}],
        "negative_cache_hits": 4, "model_calls": 0, "cost_usd": 0}

    def optimize(config, capsule, incumbent):
        calls.append(deepcopy((config, capsule, incumbent)))
        return deepcopy(improved), deepcopy(report)

    def dictionary(config, capsule, incumbent):
        dictionary_calls.append(deepcopy((config, capsule, incumbent)))
        return deepcopy(incumbent), {"status": "completed", "health_status": "healthy",
            "health_counts": {}, "warnings": [], "errors": [], "model_calls": 0, "cost_usd": 0}

    def check(config, path, project, *, quick=False, **kwargs):
        checks.append((str(path), str(project), quick))
        source = Path(path).read_text()
        found = next((item for item in (original, improved) if item["source"] == source), None)
        if found is None:
            return {"valid": False}
        return {"valid": True, "source_sha256": found["sha256"], "measurement_mode": "exact",
            "axiom_status": "measured", "axioms": [], "length": {"candidate_tokens": found["tokens"]},
            "heartbeat": {"candidate": found["heartbeats"], "local_reference": 100}}

    monkeypatch.setattr(optimizer.proof.arena, "load_task", lambda _: ({}, {"signature": "theorem test : True"}))
    monkeypatch.setattr(optimizer.proof.arena, "extract_candidate_declaration", lambda _, source: (source, source))
    monkeypatch.setattr(optimizer.deterministic, "optimize", optimize)
    monkeypatch.setattr(optimizer.deterministic, "optimize_dictionary", dictionary)
    monkeypatch.setattr(optimizer.proof, "_check", check)
    monkeypatch.setattr(optimizer, "tool_identity", lambda _: "engine-v1")
    return SimpleNamespace(config=config, root=root, capsule=capsule, original=original,
        improved=improved, selection=selection, calls=calls, checks=checks, report=report,
        dictionary_calls=dictionary_calls, candidate=candidate,
        directory=root / "optimizer-boundaries" / capsule.name)


def run(cell, best=None, selection=None):
    return optimizer.optimize_pass_result(cell.config, cell.root, cell.capsule,
        cell.original if best is None else best, cell.selection if selection is None else selection)


def transaction(cell):
    return json.loads((cell.directory / "transaction.json").read_text())


def test_schedule_and_immutable_compact_engine_adapter(cell):
    frozen = deepcopy(cell.config)
    for pass_number, expected in ((1, 1200), (2, 1200), (3, 300), (99, 300)):
        assert optimizer.budget_seconds(pass_number) == expected
        effective = optimizer.engine_config(cell.config, pass_number)
        spec = experiment_spec(effective)
        assert spec.deterministic_budget_for_pass(pass_number) == expected
        assert spec.deterministic_policy == "compact"
        assert spec.deterministic_cache and spec.deterministic_regenerate
    assert cell.config == frozen
    assert optimizer.budget_seconds(1, "off") == 0
    for invalid in (0, -1, True, 1.5):
        with pytest.raises(ValueError):
            optimizer.budget_seconds(invalid)
    with pytest.raises(ValueError):
        optimizer.budget_seconds(1, "other")


def test_promote_verifies_output_and_keeps_engine_health(cell):
    best, selection, report = run(cell)
    assert best["source"] == cell.improved["source"]
    assert Path(best["selected_path"]).read_text() == best["source"]
    assert selection["candidate_records"] == cell.selection["candidate_records"]
    assert report["health_counts"] == cell.report["health_counts"]
    assert report["health_status"] == "degraded"
    assert report["negative_cache_hits"] == 4
    assert report["warnings"] == cell.report["warnings"]
    assert report["effective_budget_seconds"] == 1200
    assert report["search_seconds"] >= 0 and report["verification_seconds"] >= 0
    assert report["total_seconds"] >= report["search_seconds"] + report["verification_seconds"]
    assert transaction(cell)["stage"] == "committed"
    assert len(cell.checks) == 2
    assert cell.checks[0][2] is False and cell.checks[1][2] is True
    assert len(cell.calls) == 1


@pytest.mark.parametrize("caller", ["original", "output"])
def test_replay_admits_saved_input_or_promoted_output_without_second_search(cell, caller):
    best, selection, report = run(cell)
    checks_before = len(cell.checks)
    recovered = run(cell) if caller == "original" else run(cell, best, selection)
    assert recovered == (best, selection, report)
    assert len(cell.calls) == 1
    # Both saved input and output are independently rechecked, not admitted by hash.
    assert len(cell.checks) == checks_before + 4


@pytest.mark.parametrize("stage", ["after_prepare", "after_verify", "before_source", "after_source", "after_selection", "after_commit"])
def test_crash_boundaries_recover_from_previous_input(cell, monkeypatch, stage):
    class PowerLoss(BaseException):
        pass

    def interrupt(current, directory):
        if current == stage:
            raise PowerLoss

    monkeypatch.setattr(optimizer, "_promotion_checkpoint", interrupt)
    with pytest.raises(PowerLoss):
        run(cell)
    if stage in {"after_prepare", "after_verify", "before_source"}:
        assert (cell.capsule / "Selected.lean").read_text() == cell.original["source"]
    else:
        assert (cell.capsule / "Selected.lean").read_text() == cell.improved["source"]
    monkeypatch.setattr(optimizer, "_promotion_checkpoint", lambda *args: None)
    best, selection, _ = run(cell)
    assert best["sha256"] == cell.improved["sha256"]
    assert selection["sha256"] == best["sha256"]
    assert (cell.capsule / "Selected.lean").read_text() == best["source"]
    assert transaction(cell)["stage"] == "committed"
    assert len(cell.calls) == 1


def test_failed_engine_retains_input_and_does_not_repeat_failure(cell, monkeypatch):
    def fail(*args):
        cell.calls.append("failure")
        raise RuntimeError("negative cache write failed")
    monkeypatch.setattr(optimizer.deterministic, "optimize", fail)
    best, selection, report = run(cell)
    assert best["sha256"] == cell.original["sha256"]
    assert report["status"] == "failed_retained_incumbent"
    assert report["health_status"] == "degraded"
    assert report["health_counts"]["boundary_failures"] == 1
    assert "negative cache write failed" in report["errors"][-1]["message"]
    assert run(cell) == (best, selection, report)
    assert cell.calls == ["failure"]


def test_failed_verification_retains_input_without_concealing_cache_failures(cell, monkeypatch):
    def fail(*args, **kwargs):
        raise TimeoutError("compiler queue limit")
    monkeypatch.setattr(optimizer.proof, "_check", fail)
    best, _, report = run(cell)
    assert best["sha256"] == cell.original["sha256"]
    assert report["health_counts"]["cache_errors"] == 2
    assert report["health_counts"]["generator_invalid"] == 3
    assert report["health_counts"]["boundary_failures"] == 1
    assert report["negative_cache_hits"] == 4
    assert report["status"] == "failed_retained_incumbent"


def test_worker_failure_can_still_promote_independently_verified_checkpoint(cell):
    cell.report.update(status="infrastructure_failure", termination_reason="worker_failure")
    best, _, report = run(cell)
    assert best["sha256"] == cell.improved["sha256"]
    assert report["status"] == "infrastructure_failure"
    assert report["health_counts"]["cache_errors"] == 2


def test_disabled_has_no_optimizer_or_compiler_calls(cell):
    cell.config["optimizer"] = "off"
    best, _, report = run(cell)
    assert best["sha256"] == cell.original["sha256"]
    assert report["status"] == report["health_status"] == "disabled"
    assert report["model_calls"] == report["effective_budget_seconds"] == 0
    assert not cell.calls and not cell.checks
    assert report["search_seconds"] == report["verification_seconds"] == 0


@pytest.mark.parametrize("artifact", ["Input.lean", "Output.lean", "transaction.json", "agent-selection.json"])
def test_saved_artifact_tampering_is_rejected_without_overwrite(cell, artifact):
    best, selection, _ = run(cell)
    path = cell.directory / artifact
    path.write_text("tampered")
    with pytest.raises(optimizer.OptimizerBoundaryError):
        run(cell, best, selection)
    assert path.read_text() == "tampered"
    assert len(cell.calls) == 1


def test_resealed_forged_measurements_are_rejected_by_independent_compiler(cell):
    best, selection, _ = run(cell)
    saved = transaction(cell)
    saved["output"]["tokens"] = 1
    saved["output"]["score"] = proof._policy(cell.config).score(tokens=1, heartbeats=20, compatibility_pct=100)
    # An attacker or defective writer can recompute a digest; that is not validation.
    saved = optimizer._seal(saved)
    (cell.directory / "transaction.json").write_text(json.dumps(saved))
    with pytest.raises(optimizer.OptimizerBoundaryError, match="independent verification"):
        run(cell)
    assert len(cell.calls) == 1
    assert (cell.capsule / "Selected.lean").read_text() == best["source"]


def test_matching_hash_cannot_admit_changed_caller_measurements(cell):
    run(cell)
    changed = {**cell.original, "tokens": 1,
        "score": proof._policy(cell.config).score(tokens=1, heartbeats=70, compatibility_pct=100)}
    with pytest.raises(optimizer.OptimizerBoundaryError, match="neither"):
        run(cell, changed)
    assert len(cell.calls) == 1


@pytest.mark.parametrize("identity", ["config", "task", "registry", "engine"])
def test_frozen_task_environment_policy_and_engine_identity_are_guarded(cell, monkeypatch, identity):
    run(cell)
    if identity == "config":
        cell.config["model_profile_sha256"] = "different-model"
    elif identity == "task":
        Path(cell.config["task"]).write_text("changed task")
    elif identity == "registry":
        Path(cell.config["fingerprint_registry"]).write_text("changed environment")
    else:
        monkeypatch.setattr(optimizer, "tool_identity", lambda _: "engine-v2")
    with pytest.raises(optimizer.OptimizerBoundaryError):
        run(cell)
    assert len(cell.calls) == 1


def test_unhealthy_selection_and_unrelated_candidate_are_rejected(cell):
    with pytest.raises(optimizer.OptimizerBoundaryError, match="healthy"):
        run(cell, selection={**cell.selection, "validation_healthy": False})
    with pytest.raises(optimizer.OptimizerBoundaryError, match="differs"):
        run(cell, best=cell.improved)
    assert not cell.calls


@pytest.mark.parametrize("progress_binding", ["matching", "foreign"])
def test_engine_checkpoint_is_recovered_after_crash_without_repeating_worker(cell, monkeypatch, progress_binding):
    launched = []
    monkeypatch.setattr(optimizer.deterministic, "optimize", _REAL_OPTIMIZE)

    def launch(config, directory, deadline):
        launched.append(deadline)
        receipt = optimizer.deterministic._read(directory / "progress.json")
        destination = directory / "validated" / f"{cell.improved['sha256']}.lean"
        destination.parent.mkdir()
        optimizer.deterministic._immutable_source(destination, cell.improved["source"])
        candidate = {**cell.improved, "selected_path": str(destination), "compatibility": []}
        for index, environment in enumerate([config["primary"], *config["compatibility"]]):
            evaluation = proof._check(config, destination, Path(environment), quick=index > 0)
            candidate["compatibility"].append({"environment": environment,
                "passed": True, "evaluation": evaluation})
        proof._write(directory / "checkpoint.json", {"binding_sha256": receipt["binding_sha256"], "best": candidate})
        receipt.update(status="completed", accepted_candidates=1, evaluated_candidates=1,
                       termination_reason="frontier_exhausted", after=optimizer._summary(candidate))
        proof._write(directory / "progress.json", receipt)
        return {"returncode": 0, "timed_out": False}

    class PowerLoss(BaseException):
        pass

    def interrupt(stage, directory):
        if stage == "after_engine":
            raise PowerLoss

    monkeypatch.setattr(optimizer.deterministic, "_launch_worker", launch)
    monkeypatch.setattr(optimizer, "_promotion_checkpoint", interrupt)
    with pytest.raises(PowerLoss):
        run(cell)
    assert len(launched) == 1
    assert transaction(cell)["stage"] == "prepared"
    # Even a worker report lost after its checkpoint is recovered as interrupted.
    engine_directory = cell.root / "deterministic" / cell.capsule.name
    (engine_directory / "report.json").unlink()
    progress = optimizer.deterministic._read(engine_directory / "progress.json")
    progress.update(wall_seconds=101.5, evaluated_candidates=22, accepted_candidates=3, rounds_completed=3)
    if progress_binding == "foreign":
        progress["binding_sha256"] = "unrelated-search"
    proof._write(engine_directory / "progress.json", progress)
    monkeypatch.setattr(optimizer, "_promotion_checkpoint", lambda *args: None)
    best, selection, report = run(cell)
    assert best["sha256"] == selection["sha256"] == cell.improved["sha256"]
    assert len(launched) == 1
    assert report["status"] == "interrupted" and report["reused"]
    assert report["termination_reason"] == "host_interrupted"
    assert report["wall_seconds"] == (101.5 if progress_binding == "matching" else 0)
    assert report["evaluated_candidates"] == (22 if progress_binding == "matching" else 0)
    assert report["accepted_candidates"] == (3 if progress_binding == "matching" else 0)
    assert transaction(cell)["verification"]["verification"] == "independent_host_exact_and_compatibility"
    assert run(cell, best, selection)[0] == best
    assert len(launched) == 1


@pytest.mark.parametrize("failure", [
    TimeoutError("queue timeout"), OSError("negative cache inaccessible"),
    ValueError("compatibility parser failed")])
def test_boundary_failures_never_become_negative_cache_invalidity(cell, monkeypatch, failure):
    from e6.deterministic_support.search_cache import compile_rejection
    assert compile_rejection(failure, proof.arena.LeanCompileError) is None
    cell.report.update(status="infrastructure_failure", health_counts={
        "cache_errors": 1, "candidate_infrastructure_failures": 1, "candidate_invalid": 0},
        warnings=["cache_errors", "candidate_infrastructure_failures"])

    def failed_engine(*args):
        cell.calls.append("engine")
        return deepcopy(cell.original), deepcopy(cell.report)
    monkeypatch.setattr(optimizer.deterministic, "optimize", failed_engine)
    best, _, report = run(cell)
    assert best["sha256"] == cell.original["sha256"]
    assert report["health_counts"]["candidate_invalid"] == 0
    assert report["health_counts"]["candidate_infrastructure_failures"] == 1
    assert report["health_counts"]["cache_errors"] == 1
    assert run(cell)[0]["sha256"] == cell.original["sha256"]
    assert cell.calls == ["engine"]


def test_replay_rechecks_source_intake_before_accepting_saved_output(cell, monkeypatch):
    run(cell)
    monkeypatch.setattr(proof.arena, "extract_candidate_declaration",
        lambda _, source: ("x" * (experiment_spec(cell.config).candidate_intake_characters + 1), source))
    with pytest.raises(optimizer.OptimizerBoundaryError, match="independent verification"):
        run(cell)
    assert len(cell.calls) == 1


def test_replay_preserves_host_verified_input_with_partial_compatibility(cell, monkeypatch):
    cell.config["optimizer"] = "off"
    cell.original["compatibility_pct"] = 50
    cell.original["score"] = proof._policy(cell.config).score(tokens=80, heartbeats=70, compatibility_pct=50)
    cell.selection.update(cell.original)
    normal_check = proof._check

    def partial(config, path, project, *, quick=False, **kwargs):
        return {**normal_check(config, path, project, quick=quick, **kwargs), "valid": not quick}

    monkeypatch.setattr(proof, "_check", partial)
    best, selection, report = run(cell)
    assert run(cell, best, selection) == (best, selection, report)
    assert best["compatibility_pct"] == 50
    assert not cell.calls


def test_changed_optimizer_source_requires_every_compatibility_environment(cell, monkeypatch):
    cell.improved["compatibility_pct"] = 50
    cell.improved["score"] = proof._policy(cell.config).score(tokens=30, heartbeats=20, compatibility_pct=50)
    normal_check = proof._check

    def partial(config, path, project, *, quick=False, **kwargs):
        return {**normal_check(config, path, project, quick=quick, **kwargs), "valid": not quick}

    monkeypatch.setattr(proof, "_check", partial)
    best, _, report = run(cell)
    assert best["sha256"] == cell.original["sha256"]
    assert report["status"] == "failed_retained_incumbent"
    assert report["health_counts"]["boundary_failures"] == 1


def enable_dictionary_gain(cell, monkeypatch):
    cached = cell.candidate("by exact (show True from trivial)\n", 20, 10)
    normal_check = proof._check

    def check(config, path, project, *, quick=False, **kwargs):
        if Path(path).read_text() != cached["source"]:
            return normal_check(config, path, project, quick=quick, **kwargs)
        cell.checks.append((str(path), str(project), quick))
        return {"valid": True, "source_sha256": cached["sha256"], "measurement_mode": "exact",
            "axiom_status": "measured", "axioms": [], "length": {"candidate_tokens": cached["tokens"]},
            "heartbeat": {"candidate": cached["heartbeats"], "local_reference": 100}}

    def dictionary(config, capsule, incumbent):
        assert incumbent["sha256"] == cell.improved["sha256"]
        assert any(Path(path).name == "Compact.lean" for path, _, _ in cell.checks)
        cell.dictionary_calls.append(deepcopy((config, capsule, incumbent)))
        return deepcopy(cached), {"status": "completed", "health_status": "healthy", "health_counts": {},
            "evaluated_candidates": 4, "accepted_candidates": 1, "model_calls": 0, "cost_usd": 0}

    monkeypatch.setattr(proof, "_check", check)
    monkeypatch.setattr(optimizer.deterministic, "optimize_dictionary", dictionary)
    return cached


def test_dictionary_after_verified_compact_promotes_and_replay_skips_both_searches(cell, monkeypatch):
    cached = enable_dictionary_gain(cell, monkeypatch)
    best, selected, report = run(cell)
    assert best["sha256"] == cached["sha256"] == selected["sha256"]
    assert len(cell.calls) == len(cell.dictionary_calls) == 1
    assert len(cell.checks) == 4
    assert report["stage_order"] == ["compact", "dictionary_cache"]
    assert report["effective_budget_seconds"] == 1200
    assert report["dictionary_budget_seconds"] == 900
    assert report["dictionary_cache"]["before"]["sha256"] == cell.improved["sha256"]
    assert report["dictionary_cache"]["after"]["sha256"] == cached["sha256"]
    assert report["evaluated_candidates"] == 15 and report["accepted_candidates"] == 2
    assert transaction(cell)["compact"]["output"]["sha256"] == cell.improved["sha256"]
    assert run(cell, best, selected) == (best, selected, report)
    assert len(cell.calls) == len(cell.dictionary_calls) == 1


@pytest.mark.parametrize("stage", ["after_compact_verify", "after_dictionary", "after_verify", "after_source"])
def test_dictionary_boundary_crash_keeps_verified_compact_checkpoint(cell, monkeypatch, stage):
    cached = enable_dictionary_gain(cell, monkeypatch)

    class PowerLoss(BaseException):
        pass

    def crash(current, directory):
        if current == stage:
            raise PowerLoss

    monkeypatch.setattr(optimizer, "_promotion_checkpoint", crash)
    with pytest.raises(PowerLoss):
        run(cell)
    assert transaction(cell)["compact"]["output"]["sha256"] == cell.improved["sha256"]
    monkeypatch.setattr(optimizer, "_promotion_checkpoint", lambda *args: None)
    best, _, report = run(cell)
    assert best["sha256"] == cached["sha256"]
    assert len(cell.calls) == 1
    assert report["total_seconds"] >= report["search_seconds"] + report["verification_seconds"]
    # The real dictionary engine consumes its own durable boundary on replay;
    # this mock records entry invocations rather than native worker launches.
    assert len(cell.dictionary_calls) == (2 if stage == "after_dictionary" else 1)


def test_dictionary_exception_retains_compact_and_exposes_failure(cell, monkeypatch):
    def fail(*args):
        cell.dictionary_calls.append("failed")
        raise TimeoutError("dictionary worker deadline")

    monkeypatch.setattr(optimizer.deterministic, "optimize_dictionary", fail)
    best, selected, report = run(cell)
    assert best["sha256"] == cell.improved["sha256"]
    assert report["dictionary_cache"]["status"] == "failed_retained_incumbent"
    assert report["health_status"] == "degraded"
    assert report["health_counts"]["boundary_failures"] == 1
    assert report["health_counts"]["cache_errors"] == 2
    assert run(cell, best, selected) == (best, selected, report)
    assert cell.dictionary_calls == ["failed"]


@pytest.mark.parametrize("failure", ["compatibility", "measurements", "axioms"])
def test_dictionary_independent_verification_falls_back_to_compact(cell, monkeypatch, failure):
    cached = enable_dictionary_gain(cell, monkeypatch)
    normal_check = proof._check

    def fail(config, path, project, *, quick=False, **kwargs):
        evaluation = normal_check(config, path, project, quick=quick, **kwargs)
        if Path(path).read_text() == cached["source"]:
            if failure == "compatibility" and quick:
                evaluation["valid"] = False
            if failure == "measurements" and not quick:
                evaluation["heartbeat"]["candidate"] += 1
            if failure == "axioms" and not quick:
                evaluation["axioms"] = ["sorryAx"]
        return evaluation

    monkeypatch.setattr(proof, "_check", fail)
    best, selected, report = run(cell)
    assert best["sha256"] == cell.improved["sha256"]
    assert selected["sha256"] == best["sha256"]
    assert (cell.directory / "Output.lean").read_text() == cell.improved["source"]
    assert report["dictionary_cache"]["errors"][-1]["phase"] == "boundary_dictionary_verification_failure"
    assert transaction(cell)["verification"]["candidate_sha256"] == cell.improved["sha256"]


@pytest.mark.parametrize("candidate_kind", ["regression", "equal_score_changed_source", "changed_measurements"])
def test_dictionary_rejects_non_improving_or_inconsistent_result(cell, monkeypatch, candidate_kind):
    if candidate_kind == "regression":
        candidate = cell.original
    elif candidate_kind == "equal_score_changed_source":
        candidate = cell.candidate("by exact (True.intro)\n", 30, 20)
    else:
        candidate = cell.candidate(cell.improved["source"], 20, 10)
    monkeypatch.setattr(optimizer.deterministic, "optimize_dictionary", lambda *args: (deepcopy(candidate), {}))
    best, _, report = run(cell)
    assert best["sha256"] == cell.improved["sha256"]
    assert report["dictionary_cache"]["status"] == "failed_retained_incumbent"


def test_corrupt_compact_stage_cannot_be_used_as_dictionary_input(cell, monkeypatch):
    class PowerLoss(BaseException):
        pass

    def crash(stage, directory):
        if stage == "after_compact_verify":
            raise PowerLoss

    monkeypatch.setattr(optimizer, "_promotion_checkpoint", crash)
    with pytest.raises(PowerLoss):
        run(cell)
    (cell.directory / "Compact.lean").write_text("by sorry\n")
    monkeypatch.setattr(optimizer, "_promotion_checkpoint", lambda *args: None)
    with pytest.raises(optimizer.OptimizerBoundaryError, match="compact output"):
        run(cell)
    assert not cell.dictionary_calls


def test_dictionary_disabled_when_optimizer_off(cell):
    cell.config["optimizer"] = "off"
    _, _, report = run(cell)
    assert not cell.dictionary_calls
    assert report["dictionary_cache"]["status"] == "disabled"
    assert report["dictionary_budget_seconds"] == 0


def test_dictionary_not_called_after_compact_fails_host_verification(cell, monkeypatch):
    monkeypatch.setattr(proof, "_check", lambda *args, **kwargs: {"valid": False})
    best, _, report = run(cell)
    assert best["sha256"] == cell.original["sha256"]
    assert not cell.dictionary_calls
    assert report["dictionary_cache"]["reason"] == "compact_stage_failure"


def test_recovered_dictionary_worker_time_remains_in_accounting(cell, monkeypatch):
    def dictionary(config, capsule, incumbent):
        return dict(incumbent), {"status": "completed", "health_status": "healthy",
            "health_counts": {}, "reused": True, "wall_seconds": 47.5}

    monkeypatch.setattr(optimizer.deterministic, "optimize_dictionary", dictionary)
    _, _, report = run(cell)
    assert report["recovered_search_seconds"] == 47.5
    assert report["search_seconds"] >= 47.5
    assert report["total_seconds"] >= report["search_seconds"] + report["verification_seconds"]
    assert report["boundary_wall_seconds"] < report["total_seconds"]
