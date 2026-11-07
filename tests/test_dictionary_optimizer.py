"""Fixed dictionary stage boundaries; all generation and compiler calls are mocked."""
from copy import deepcopy
from dataclasses import replace
from pathlib import Path
import time
from types import SimpleNamespace

import pytest

from e6 import deterministic, proof
from e6.deterministic_support import dictionary_cache, dictionary_search
from e6.experiment import DEFAULT_SPEC
from .core.test_proof import config, manifest


@pytest.fixture
def cell(tmp_path, monkeypatch, manifest):
    settings = config(tmp_path)
    settings.update(replace(DEFAULT_SPEC, deterministic_refactoring=True,
        deterministic_budget_seconds=5, deterministic_max_candidates=2,
        deterministic_rounds=2).proof_settings())
    capsule = tmp_path / "pass-001"
    capsule.mkdir()
    (capsule / "Selected.lean").write_text(settings["initial_best"]["source"])
    proof._write(capsule / "selection.json", settings["initial_best"])
    state = {"values": [], "generated": [], "checked": [], "launches": [],
             "generator_status": "completed", "analysis": {"walk_cap_reached": False}}
    monkeypatch.setattr(proof.arena, "load_task", lambda _: ({}, {"signature": "theorem Task.st : True"}))
    monkeypatch.setattr(proof.arena, "extract_candidate_declaration", lambda _, source: (source, source))

    def generate(**kwargs):
        state["generated"].append(kwargs)
        workdir = kwargs["workdir"]
        workdir.mkdir(parents=True, exist_ok=True)
        proof._write(workdir / "dictionary-proposals.json", {
            "source_sha256": proof._digest(kwargs["source"]), "status": state["generator_status"],
            "candidate_count": len(state["values"]), "max_candidates": 4,
            "hard_limits": {"expr_nodes": 30000}, "analysis": state["analysis"],
            "compiler_seconds": kwargs["timeout_seconds"], "native_capture_calls": 1})
        return [{"id": str(i), "family": "census_dictionary_cache", "source": source}
                for i, source in enumerate(state["values"])]

    def check(_config, candidate, project, *, quick=False, timeout_seconds):
        source = candidate.read_text()
        state["checked"].append((source, str(project), quick, timeout_seconds))
        tokens, beats = {"better": (130, 600), "best": (80, 100),
                         "partial": (1, 0), "bad": (1, 0)}.get(source, (200, 800))
        return {"valid": source != "bad" and not (source == "partial" and quick),
            "measurement_mode": "exact", "axiom_status": "measured", "axioms": [],
            "source_sha256": proof._digest(source), "length": {"candidate_tokens": tokens},
            "heartbeat": {"candidate": beats, "local_reference": settings["original_heartbeats"]}}

    def launch(config, directory, deadline):
        state["launches"].append((directory, deadline - time.monotonic()))
        dictionary_search.search(config, deterministic._read(directory / "incumbent-before.json"),
                                 directory, deterministic._read(directory / "request.json"))
        return {"returncode": 0, "timed_out": False}

    monkeypatch.setattr(dictionary_cache, "generate_candidates", generate)
    monkeypatch.setattr(proof, "_check", check)
    monkeypatch.setattr(deterministic, "_launch_worker", launch)
    return settings, capsule, state, launch


def run(cell, incumbent=None):
    config, capsule, _, _ = cell
    return deterministic.optimize_dictionary(config, capsule, incumbent or config["initial_best"])


def details(cell):
    return deterministic._read(cell[1].parent / "deterministic-dictionary" / cell[1].name / "report.json")


def test_fixed_one_census_four_siblings_separate_allowance_and_selection_isolation(cell):
    settings, capsule, state, _ = cell
    frozen = deepcopy(settings)
    raw_selection = (capsule / "selection.json").read_bytes()
    compact = capsule.parent / "deterministic" / capsule.name
    compact.mkdir(parents=True)
    (compact / "sentinel").write_text("preserved")
    state["values"] = ["better", "best", "bad", "same"]
    best, report = run(cell)
    assert best["source"] == "best" and report["accepted_candidates"] == 2
    assert len(state["generated"]) == 1 and state["generated"][0]["source"] == "previous"
    assert state["generated"][0]["max_candidates"] == 4
    assert state["generated"][0]["timeout_seconds"] == 180
    assert 899 < state["launches"][0][1] <= 900
    assert settings == frozen and (compact / "sentinel").read_text() == "preserved"
    assert (capsule / "selection.json").read_bytes() == raw_selection
    assert (capsule / "Selected.lean").read_text() == "previous"
    assert report["effective_budget_seconds"] == 900 and report["fixed_stage"] == "dictionary_cache"
    assert report["model_calls"] == report["cost_usd"] == 0
    assert report["dictionary_telemetry"]["candidate_count"] == 4
    assert report["dictionary_telemetry"]["candidate_cap_reached"]
    assert {r["parent_sha256"] for r in details(cell)["candidate_records"]} == {settings["initial_best"]["sha256"]}
    request = deterministic._read(Path(report["report_path"]).parent / "request.json")
    assert request["fixed_stage"] == "dictionary_cache" and request["settings"] == deterministic.dictionary_settings()


def test_exact_duplicates_are_skipped_without_validation_or_regeneration(cell):
    _, _, state, _ = cell
    state["values"] = ["previous", "better", "better", "same"]
    best, report = run(cell)
    assert best["source"] == "better" and report["evaluated_candidates"] == 2
    assert len(state["generated"]) == 1
    assert sum(source == "better" and not quick for source, _, quick, _ in state["checked"]) == 1
    assert not any(source == "previous" for source, *_ in state["checked"])
    assert report["search_exhausted"] and report["termination_reason"] == "frontier_exhausted"


@pytest.mark.parametrize("source,status", [("bad", "primary_invalid"), ("same", "no_improvement"),
                                            ("partial", "compatibility_failed")])
def test_strict_gain_and_full_compatibility_are_required(cell, source, status):
    _, _, state, _ = cell
    state["values"] = [source]
    best, report = run(cell)
    assert best["source"] == "previous" and not report["improved"]
    assert details(cell)["candidate_records"][0]["status"] == status


@pytest.mark.parametrize("field,value", [("axiom_status", None), ("axioms", ["badAxiom"]),
                                         ("measurement_mode", "estimated")])
def test_exact_measured_allowed_axiom_audit_is_required(cell, monkeypatch, field, value):
    _, _, state, _ = cell
    state["values"] = ["better"]
    original = proof._check
    def missing(*args, **kwargs):
        return {**original(*args, **kwargs), field: value}
    monkeypatch.setattr(proof, "_check", missing)
    best, report = run(cell)
    assert best["source"] == "previous" and not report["search_exhausted"]
    assert report["health_counts"]["candidate_infrastructure_failures"] == 1


def test_checkpoint_guard_rejects_incomplete_validator_result_before_writing(cell, monkeypatch):
    settings, _, state, _ = cell
    state["values"] = ["better", "best"]
    validate = deterministic._validate
    def incomplete(*args, **kwargs):
        result = validate(*args, **kwargs)
        if args[2] == "best":
            result["compatibility"] = []
        return result
    monkeypatch.setattr(deterministic, "_validate", incomplete)
    best, report = run(cell)
    assert best["source"] == "better" and report["accepted_candidates"] == 1
    saved = deterministic._read(Path(report["checkpoint_path"]))
    assert saved["best"]["sha256"] == best["sha256"]
    deterministic._checkpoint(settings, Path(report["checkpoint_path"]).parent, report["binding_sha256"], settings["initial_best"])


@pytest.mark.parametrize("status,reason", [("unsupported_shape", "unsupported_shape"),
                                          ("completed", "frontier_exhausted")])
def test_unsupported_shape_and_completed_empty_have_distinct_receipts(cell, status, reason):
    _, _, state, _ = cell
    state["generator_status"] = status
    _, report = run(cell)
    telemetry = report["dictionary_telemetry"]
    assert telemetry["unsupported_shape"] == (status == "unsupported_shape")
    assert telemetry["completed_empty"] == (status == "completed")
    assert report["status"] == "completed" and report["search_exhausted"]
    assert report["termination_reason"] == reason and report["health_status"] == "healthy"


@pytest.mark.parametrize("resource", [False, True])
def test_generator_failure_does_not_become_an_empty_exhausted_inventory(cell, monkeypatch, resource):
    def fail(**kwargs):
        workdir = kwargs["workdir"]
        workdir.mkdir(parents=True)
        proof._write(workdir / "capture-run.json", {"run": {"timed_out": resource}})
        proof._write(workdir / "dictionary-proposals.json", {"source_sha256": proof._digest(kwargs["source"]),
            "status": "failed", "candidate_count": 0, "partial_candidates_discarded": True})
        raise RuntimeError("capture failed")
    monkeypatch.setattr(dictionary_cache, "generate_candidates", fail)
    best, report = run(cell)
    assert best["source"] == "previous" and report["status"] == ("completed" if resource else "infrastructure_failure")
    assert not report["search_exhausted"]
    assert report["termination_reason"] == ("generation_resource_limit" if resource else "generation_failure")
    assert report["health_status"] == ("limited" if resource else "degraded")
    assert report["dictionary_telemetry"]["failure_kind"] == ("resource_limit" if resource else "infrastructure")
    key = "generator_resource_limits" if resource else "generator_failures"
    assert report["health_counts"][key] == 1


def test_generation_walk_cap_is_exposed(cell):
    cell[2]["analysis"]["walk_cap_reached"] = True
    _, report = run(cell)
    assert report["dictionary_telemetry"]["analysis"]["walk_cap_reached"]


@pytest.mark.parametrize("where", ["capture", "analysis"])
def test_resource_diagnostics_classify_census_and_compiler_caps(cell, monkeypatch, where):
    def fail(**kwargs):
        workdir = kwargs["workdir"]
        workdir.mkdir(parents=True)
        if where == "capture":
            (workdir / "capture.log").write_text("maximum number of heartbeats exceeded")
        else:
            proof._write(workdir / "dictionary-census.json", {"analysis": {
                "status": "failed", "error": "maximum recursion depth has been reached"}})
        raise RuntimeError("capture failed")
    monkeypatch.setattr(dictionary_cache, "generate_candidates", fail)
    best, report = run(cell)
    assert best["source"] == "previous"
    assert report["health_counts"]["generator_resource_limits"] == 1
    assert report["dictionary_telemetry"]["failure_kind"] == "resource_limit"


def test_worker_deadline_stops_inventory_and_consumes_boundary(cell, monkeypatch):
    cell[2]["values"] = ["better"]
    generator = dictionary_cache.generate_candidates
    clock = {"now": 0.0}
    monkeypatch.setattr(dictionary_search, "time", SimpleNamespace(monotonic=lambda: clock["now"]))
    def expire(**kwargs):
        values = generator(**kwargs)
        clock["now"] = 901.0
        return values
    monkeypatch.setattr(dictionary_cache, "generate_candidates", expire)
    best, report = run(cell)
    assert best["source"] == "previous" and not cell[2]["checked"]
    assert report["status"] == "timed_out" and report["termination_reason"] == "wall_deadline"
    assert not report["search_exhausted"]
    monkeypatch.setattr(deterministic, "_launch_worker", lambda *_: pytest.fail("second allowance"))
    assert run(cell)[1]["reused"]


def test_generator_inventory_above_four_is_rejected(cell):
    cell[2]["values"] = ["better", "best", "bad", "same", "extra"]
    best, report = run(cell)
    assert best["source"] == "previous" and not cell[2]["checked"]
    assert report["health_counts"]["generator_failures"] == 1 and not report["search_exhausted"]


def test_verified_gain_survives_later_resource_failure(cell, monkeypatch):
    cell[2]["values"] = ["better", "best"]
    check = proof._check
    def fail(*args, **kwargs):
        if args[1].read_text() == "best":
            raise TimeoutError("queue deadline")
        return check(*args, **kwargs)
    monkeypatch.setattr(proof, "_check", fail)
    best, report = run(cell)
    assert best["source"] == "better" and report["accepted_candidates"] == 1
    assert report["health_counts"]["candidate_resource_limits"] == 1
    assert not report["search_exhausted"]


def test_deadline_and_host_interruption_recover_checkpoint_without_another_allowance(cell, monkeypatch):
    cell[2]["values"] = ["better"]
    direct = cell[3]
    def timeout(config, directory, deadline):
        direct(config, directory, deadline)
        return {"returncode": -9, "timed_out": True}
    monkeypatch.setattr(deterministic, "_launch_worker", timeout)
    best, report = run(cell)
    assert best["source"] == "better" and report["status"] == "timed_out"
    Path(report["report_path"]).unlink()
    monkeypatch.setattr(deterministic, "_launch_worker", lambda *_: pytest.fail("second allowance"))
    recovered, reused = run(cell)
    assert recovered == best and reused["reused"] and reused["status"] == "interrupted"
    assert len(cell[2]["generated"]) == 1


def test_replay_accepts_saved_input_or_verified_output_but_rejects_different_seed(cell, monkeypatch):
    settings, _, state, _ = cell
    state["values"] = ["better"]
    best, report = run(cell)
    monkeypatch.setattr(deterministic, "_launch_worker", lambda *_: pytest.fail("repeated stage"))
    assert run(cell)[0] == best
    assert run(cell, best)[0] == best
    different = {**settings["initial_best"], "source": "different", "sha256": proof._digest("different")}
    retained, rejected = run(cell, different)
    assert retained == different and rejected["status"] == "infrastructure_failure"
    assert len(state["generated"]) == 1


@pytest.mark.parametrize("change", ["stage", "settings", "seed", "directory"])
def test_worker_checks_stage_settings_seed_and_artifact_isolation(cell, change):
    _, report = run(cell)
    directory = Path(report["report_path"]).parent
    request = deterministic._read(directory / "request.json")
    if change == "stage":
        request["fixed_stage"] = "compact"
    elif change == "settings":
        request["settings"]["max_candidates"] = 8
    elif change == "seed":
        request["seed_sha256"] = "different"
    else:
        request["capsule"] = str(cell[1].parent / "pass-002")
    progress = deterministic._read(directory / "progress.json")
    progress["binding_sha256"] = deterministic._json_digest(request)
    proof._write(directory / "progress.json", progress)
    with pytest.raises(ValueError, match="input binding"):
        dictionary_search.search(cell[0], cell[0]["initial_best"], directory, request)


def test_dictionary_settings_are_copied_and_ordinary_defaults_unchanged(cell):
    settings = deterministic.dictionary_settings()
    settings["max_candidates"] = 999
    assert deterministic.dictionary_settings()["max_candidates"] == 4
    assert deterministic._settings(cell[0])["deterministic_max_candidates"] == 2
