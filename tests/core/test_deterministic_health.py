"""Compact receipts expose search health without changing proof admissibility."""
from dataclasses import replace
from types import SimpleNamespace

import pytest

from e6 import deterministic, proof
from e6.experiment import experiment_spec
from lean_tools import lean_source
from .test_deterministic import detailed, run_search, search
from .test_deterministic_cache import compiler_error
from .test_proof import manifest


@pytest.fixture(params=["compact", "deep"])
def health_search(search, monkeypatch, request):
    settings, _, _, _ = search
    settings.update(replace(experiment_spec(settings), deterministic_policy=request.param).proof_settings())
    monkeypatch.setattr(lean_source, "extract_candidate_declaration", lambda row, source: (source, source))
    return search


def test_missing_validator_is_degraded_even_when_every_candidate_fails(health_search, monkeypatch):
    settings, capsule, state, _ = health_search
    state["candidates"] = ["one", "two"]

    def missing(*args, **kwargs):
        raise FileNotFoundError("Lean executable missing")

    monkeypatch.setattr(proof, "_check", missing)
    best, report = run_search(health_search)
    assert best["sha256"] == settings["initial_best"]["sha256"]
    assert report["status"] == "completed"  # Historical search lifecycle field.
    assert report["health_status"] == "degraded"
    assert report["health_counts"]["candidate_infrastructure_failures"] == 2
    assert report["health_counts"]["candidate_invalid"] == 0
    assert "candidate_infrastructure_failures" in report["warnings"]
    assert report["termination_reason"] == "retryable_validation_failure"
    assert not report["search_exhausted"]
    assert detailed(capsule)["health_counts"] == report["health_counts"]


def test_validator_failure_retains_verified_improvement(health_search, monkeypatch):
    settings, _, state, _ = health_search
    state["candidates"] = ["better", "best"]
    check = proof._check

    def missing_best(*args, **kwargs):
        if args[1].read_text() == "best":
            raise ValueError("compatibility parser failed")
        return check(*args, **kwargs)

    monkeypatch.setattr(proof, "_check", missing_best)
    best, report = run_search(health_search)
    assert best["source"] == "better" and report["accepted_candidates"] == 1
    proof._verify_incumbent(settings, best)
    assert report["health_status"] == "degraded"
    assert report["health_counts"]["candidate_infrastructure_failures"] == 1


@pytest.mark.parametrize("case", ["bad", "partial", "compiler"])
def test_ordinary_candidate_rejection_is_healthy(health_search, monkeypatch, case):
    settings, _, state, _ = health_search
    state["candidates"] = [case]
    if case == "compiler":
        def reject(*args, **kwargs):
            raise compiler_error()
        monkeypatch.setattr(proof, "_check", reject)
    best, report = run_search(health_search)
    assert best["sha256"] == settings["initial_best"]["sha256"]
    assert report["health_status"] == "healthy" and not report["warnings"]
    assert report["health_counts"]["candidate_invalid"] == 1
    assert report["health_counts"]["candidate_infrastructure_failures"] == 0
    assert report["search_exhausted"] and report["termination_reason"] == "frontier_exhausted"


@pytest.mark.parametrize("failure", [
    compiler_error(output="Candidate.lean:1:0: error: maximum number of heartbeats exceeded"),
    compiler_error(output="Candidate.lean:1:0: error: maximum recursion depth reached"),
    TimeoutError("candidate check timed out"),
    {"valid": False, "diagnostic": {"timed_out": True}},
])
def test_candidate_resource_caps_are_limited_and_retryable(health_search, monkeypatch, failure):
    settings, capsule, state, _ = health_search
    state["candidates"] = ["best"]

    def capped(*args, **kwargs):
        if isinstance(failure, BaseException):
            raise failure
        return failure

    monkeypatch.setattr(proof, "_check", capped)
    best, report = run_search(health_search)
    assert best["sha256"] == settings["initial_best"]["sha256"]
    assert report["health_status"] == "limited" and not report["warnings"]
    assert report["health_counts"]["candidate_resource_limits"] == 1
    assert report["health_counts"]["candidate_infrastructure_failures"] == 0
    assert "candidate_resource_limits" in report["partial_reasons"]
    assert not report["search_exhausted"]
    record, = detailed(capsule)["candidate_records"]
    assert record["error_kind"] == "infrastructure"
    assert record["failure_kind"] == "resource_limit" and not record.get("negative_cache_stored")


def test_wall_budget_expiry_is_distinct_from_a_validator_failure(health_search, monkeypatch):
    settings, _, state, _ = health_search
    state["candidates"] = ["best"]
    now = [1000.0]
    monkeypatch.setattr(deterministic.time, "monotonic", lambda: now[0])

    def budget_stop(*args, **kwargs):
        now[0] += settings["deterministic_budget_seconds"] + 1
        raise TimeoutError("validation deadline expired")

    monkeypatch.setattr(proof, "_check", budget_stop)
    best, report = run_search(health_search)
    assert best["sha256"] == settings["initial_best"]["sha256"]
    assert report["status"] == "timed_out" and report["health_status"] == "limited"
    assert report["termination_reason"] == "wall_deadline" and not report["warnings"]
    assert report["health_counts"]["candidate_budget_stops"] == 1
    assert report["health_counts"]["candidate_resource_limits"] == 0
    assert report["health_counts"]["infrastructure_errors"] == 0


def test_declared_candidate_cap_is_limited_without_tooling_warning(health_search):
    settings, _, state, _ = health_search
    settings.update(replace(experiment_spec(settings), deterministic_max_candidates=1).proof_settings())
    state["candidates"] = ["one", "two"]
    _, report = run_search(health_search)
    assert report["health_status"] == "limited" and not report["warnings"]
    assert report["termination_reason"] == "candidate_limit"
    assert report["evaluated_candidates"] == 1 and not report["search_exhausted"]


def test_compact_round_cap_is_explicit_without_tooling_warning(search, monkeypatch):
    settings, _, state, _ = search
    settings.update(replace(experiment_spec(settings), deterministic_policy="compact",
                            deterministic_rounds=1).proof_settings())
    monkeypatch.setattr(lean_source, "extract_candidate_declaration", lambda row, source: (source, source))
    state["candidates"] = ["better"]
    best, report = run_search(search)
    assert best["source"] == "better" and report["health_status"] == "limited"
    assert not report["warnings"] and report["termination_reason"] == "round_limit"


@pytest.mark.parametrize("kind,health", [("infrastructure", "degraded"), ("resource_limit", "limited"),
                                        ("budget", "limited"), ("skipped", "limited")])
def test_generator_health_is_visible_without_losing_cleanup(health_search, monkeypatch, kind, health):
    _, _, state, _ = health_search

    def generate(config, source, signature, directory, deadline, maximum, records):
        if source != "previous":
            return []
        record = {"generator": "semantic", "count": 0}
        if kind == "skipped":
            record.update(status="skipped", incomplete=True, skip_reason="validation_reserve")
        else:
            record.update(status="failed", failure_kind=kind,
                          error={"type": "RuntimeError", "message": "helper failure"})
        records.append(record)
        return [{"id": "cleanup", "family": "test", "source": "better"}]

    monkeypatch.setattr(deterministic, "_generators", generate)
    best, report = run_search(health_search)
    assert best["source"] == "better" and report["accepted_candidates"] == 1
    assert report["health_status"] == health
    key = {"infrastructure": "generator_failures", "resource_limit": "generator_resource_limits",
           "budget": "generator_budget_stops", "skipped": "generation_skips"}[kind]
    assert report["health_counts"][key] == 1 and key in report["partial_reasons"]


@pytest.mark.parametrize("operation", ["initialize", "lookup", "save"])
def test_optional_cache_failures_are_degraded_in_final_receipt(health_search, monkeypatch, operation):
    settings, capsule, state, _ = health_search
    settings.update(replace(experiment_spec(settings), deterministic_cache=True).proof_settings())
    state["candidates"] = lambda source: ["better"] if source == "previous" else []

    def broken(*args, **kwargs):
        raise OSError("cache unavailable")

    cache = SimpleNamespace(binding="cache", search_binding="search", load_search=lambda: None,
        negative=broken if operation == "lookup" else lambda sha: None,
        save_search=broken if operation == "save" else lambda state: True)
    monkeypatch.setattr(deterministic, "_search_cache", broken if operation == "initialize" else lambda *args: cache)
    best, report = run_search(health_search)
    assert best["source"] == "better"
    assert report["health_status"] == "degraded" and "cache_errors" in report["warnings"]
    assert report["health_counts"]["cache_errors"] > 0
    assert detailed(capsule)["health_counts"] == report["health_counts"]


def test_final_report_write_failure_reaches_returned_health(search, monkeypatch):
    state = search[2]
    state["candidates"] = ["better"]
    write = proof._write

    def no_report(path, value):
        if path.name == "report.json":
            raise OSError("receipt storage unavailable")
        return write(path, value)

    monkeypatch.setattr(proof, "_write", no_report)
    best, report = run_search(search)
    assert best["source"] == "better" and report["health_status"] == "degraded"
    assert report["health_counts"]["infrastructure_errors"] == 1
    assert report["errors"][-1]["phase"] == "report"


def test_resource_options_in_source_or_command_do_not_hide_infrastructure():
    report = {"status": "completed", "candidate_records": [{"error_kind": "infrastructure", "error": {
        "type": "ValueError", "message": "unexpected parser result for set_option maxHeartbeats 0",
        "source": "set_option maxRecDepth 100 in by exact True.intro",
        "lean_run": {"command": ["lean", "out of memory.lean"], "output_tail": "unknown identifier maxHeartbeats"}}}]}
    health = deterministic._compact(report)
    assert health["health_status"] == "degraded"
    assert health["health_counts"]["candidate_infrastructure_failures"] == 1
    assert health["health_counts"]["candidate_resource_limits"] == 0


@pytest.mark.parametrize("phase", ["worker", "search"])
def test_legacy_wall_timeout_receipts_remain_limited_on_replay(phase):
    report = {"status": "timed_out", "errors": [
        {"phase": phase, "type": "TimeoutError", "message": "Deterministic wall deadline expired"}]}
    compact = deterministic._compact(report)
    assert compact["health_status"] == "limited" and not compact["warnings"]
    assert compact["termination_reason"] == "wall_deadline"
    assert compact["health_counts"]["infrastructure_errors"] == 0


def test_compact_health_is_bounded_even_with_large_error_logs():
    report = {"status": "infrastructure_failure", "errors": [
        {"phase": "search", "type": "RuntimeError", "message": "x" * 100000,
         "lean_run": {"output_tail": "y" * 100000}} for _ in range(20)]}
    compact = deterministic._compact(report)
    assert len(compact["errors"]) == 8
    assert all(len(error["message"]) == 512 and "lean_run" not in error for error in compact["errors"])
    assert compact["health_counts"]["infrastructure_errors"] == 20
    assert compact["health_status"] == "degraded"
