"""Opt-in compact discovery, safe score bounds, and source-bound regeneration."""
from copy import deepcopy
from dataclasses import replace
import json
from pathlib import Path
import time
from types import SimpleNamespace

import pytest

from e6 import deterministic, deterministic_candidates, deterministic_native, proof
from e6.deterministic_support import compiler_simp, semantic_compact, semantic_search
from e6.deterministic_support.edit_packs import OFFSET_UNIT
from e6.deterministic_support.search_policy import (
    COMPACT_PRIORITY_FAMILIES, PRIORITY_FAMILIES, exploration_quotas, order_candidates,
)
from e6.experiment import DEFAULT_SPEC, ExperimentSpec, experiment_spec
from lean_tools import lean_source
from lean_tools.measurement_policy import scoring_policy_context
from .test_deterministic import detailed, run_search, search
from .test_proof import config, manifest


GENERATORS = deterministic._generators


def settings(**kwargs):
    return replace(DEFAULT_SPEC, deterministic_refactoring=True,
                   deterministic_policy="compact", **kwargs).proof_settings()


def candidate(family, name, **kwargs):
    return {"family": family, "id": name, "source": name, **kwargs}


def test_compact_settings_are_explicit_and_roundtrip_without_changing_defaults():
    spec = replace(DEFAULT_SPEC, deterministic_refactoring=True, deterministic_policy="compact",
                   deterministic_cache=True, deterministic_regenerate=True)
    assert ExperimentSpec.from_dict(json.loads(json.dumps(spec.to_dict()))) == spec
    assert experiment_spec(spec.proof_settings()) == experiment_spec(spec.panel_settings()) == spec
    assert deterministic._settings(spec.proof_settings())["deterministic_policy"] == "compact"
    assert DEFAULT_SPEC.deterministic_policy == "legacy"
    assert "deterministic_policy" not in DEFAULT_SPEC.to_dict()
    with pytest.raises(ValueError, match="requires deterministic_refactoring"):
        replace(DEFAULT_SPEC, deterministic_policy="compact")
    with pytest.raises(ValueError, match="requires deterministic_policy=deep"):
        replace(spec, deterministic_beam_width=2)


def test_compact_solver_gets_first_turn_then_existing_cleanup_and_exploration_quotas():
    rows = [candidate("other", "other")]
    for family in reversed(COMPACT_PRIORITY_FAMILIES):
        rows.extend(candidate(family, f"{family}-{i}") for i in range(100))
    rows.extend(candidate("native-normal", f"native-{i}") for i in range(100))
    rows.extend(candidate("native-delete-window", f"window-{i}") for i in range(100))
    before = deepcopy(rows)
    result = order_candidates(rows, policy="compact", maximum=64)
    assert [row["family"] for row in result[:8]] == list(COMPACT_PRIORITY_FAMILIES[:8])
    assert result[8]["family"] == "other"
    assert len(result) == 64
    assert sum(row["family"] == "native-normal" for row in result) <= exploration_quotas(64)["native_terms"]
    assert sum(row["family"] == "native-delete-window" for row in result) <= exploration_quotas(64)["blind_windows"]
    assert rows == before
    assert order_candidates(rows, policy="compact", maximum=1)[0]["family"] == semantic_search.SOLVER_FAMILY


def test_compact_deduplicates_before_cap_and_keeps_semantic_metadata():
    cleanup = candidate("normalization_fusion", "same")
    compact = candidate(semantic_search.SOLVER_FAMILY, "same", compaction="exact_term_parentheses")
    final = candidate(semantic_search.SOLVER_FAMILY, "last")
    rows = [cleanup, cleanup, compact, compact, final]
    result = order_candidates(rows, policy="compact", maximum=2)
    assert result == [compact, final]
    assert result[0] is compact
    # The historical schedulers retain duplicates for their original caller.
    assert len(order_candidates(rows, policy="prioritized", maximum=4)) == 4
    assert order_candidates(rows, policy="legacy", maximum=1) == rows


@pytest.mark.parametrize("deep,expected_count", [(False, 8), (True, 22)])
def test_pure_option_inventory_keeps_existing_compact_and_deep_forms(deep, expected_count):
    signature = "theorem compact_option_inventory : True"
    source = signature + " := by trivial"
    rows = deterministic_candidates.generate(source, signature, deep=deep)
    options = [row for row in rows if row["family"] == "elaborator_option"]
    assert len(options) == expected_count
    assert all(":= set_option " in row["source"] for row in options)


def test_generation_uses_fixed_narrow_limits_and_retains_expansion_until_scheduling(tmp_path, monkeypatch):
    calls = {}
    cleanup = candidate("normalization_fusion", "cleanup")
    monkeypatch.setattr(deterministic_candidates, "generate",
                        lambda *args, **kwargs: calls.setdefault("pure", kwargs) and [cleanup])
    monkeypatch.setattr(deterministic_native, "generate",
                        lambda *args, **kwargs: calls.setdefault("native", kwargs) and [])

    def semantic(**kwargs):
        calls["semantic"] = kwargs
        # Duplicate wrappers ahead of the useful compact form must not fill a
        # small cap before the global source deduplication sees the expansion.
        original = candidate(semantic_search.SOLVER_FAMILY, "wrapper")
        return [original] * 16 + [candidate(semantic_search.SOLVER_FAMILY, "compact", compaction="term")]

    monkeypatch.setattr(semantic_compact, "generate_candidates", semantic)
    cfg = {**settings(), "optimizer_v5_generator": {"max_sites": 128},
           "semantic_search_max_sites": 128, "semantic_search_solvers": ["ignored"]}
    original = deepcopy(cfg)
    records = []
    rows = GENERATORS(cfg, "source", "signature", tmp_path, time.monotonic() + 1000, 4, records)
    assert calls["pure"] == {"max_candidates": 4}
    assert calls["native"]["policy"] == "prioritized"
    assert calls["native"]["policy_maximum"] == 4
    kwargs = calls["semantic"]
    assert kwargs["family"] == "semantic_solvers" and kwargs["max_candidates"] == 4
    assert kwargs["timeout_seconds"] == 240
    assert semantic_search.resolve_limits(kwargs["config"], kwargs["timeout_seconds"], kwargs["max_candidates"]) == {
        **deterministic.COMPACT_DISCOVERY_SETTINGS, "effective_timeout_seconds": 240,
        "effective_max_candidates": 4, "scan_milliseconds": 45000,
    }
    assert semantic_search.select_solvers(kwargs["family"], kwargs["config"]["semantic_search_solvers"]) == semantic_search.SEARCH_SOLVERS
    assert cfg == original
    assert {row["source"] for row in rows} == {"wrapper", "compact", "cleanup"}
    assert records[-1]["generator"] == "semantic_compact" and records[-1]["count"] == 17
    assert all(record["parent_sha256"] == proof._digest("source") for record in records)


@pytest.mark.parametrize("maximum,cap", [(1, 1), (64, 64), (256, 64), (4096, 64)])
def test_semantic_discovery_cap_is_independent_of_threefold_output(tmp_path, monkeypatch, maximum, cap):
    monkeypatch.setattr(deterministic_candidates, "generate", lambda *args, **kwargs: [])
    monkeypatch.setattr(deterministic_native, "generate", lambda *args, **kwargs: [])
    calls = []

    def semantic(**kwargs):
        calls.append(kwargs)
        return [candidate(semantic_search.SOLVER_FAMILY, f"semantic-{i}") for i in range(3 * cap)]

    monkeypatch.setattr(semantic_compact, "generate_candidates", semantic)
    records = []
    rows = GENERATORS(settings(), "source", "signature", tmp_path, time.monotonic() + 1000, maximum, records)
    assert calls[0]["max_candidates"] == cap
    assert len(rows) == min(maximum, 3 * cap)
    assert records[-1]["count"] == 3 * cap


def test_remaining_discovery_budget_reserves_validation_after_native_work(tmp_path, monkeypatch):
    now = [1000.0]
    monkeypatch.setattr(deterministic.time, "monotonic", lambda: now[0])
    monkeypatch.setattr(deterministic_candidates, "generate", lambda *args, **kwargs: [])
    calls = {}

    def native(*args, **kwargs):
        calls["native"] = kwargs
        now[0] += 20
        return []

    def semantic(**kwargs):
        calls["semantic"] = kwargs
        return []

    monkeypatch.setattr(deterministic_native, "generate", native)
    monkeypatch.setattr(semantic_compact, "generate_candidates", semantic)
    GENERATORS(settings(), "source", "signature", tmp_path, 1200, 256, [])
    assert calls["native"]["timeout_seconds"] == 80
    assert calls["semantic"]["timeout_seconds"] == 60


def test_semantic_failure_preserves_generated_cleanup(tmp_path, monkeypatch):
    cleanup = candidate("normalization_fusion", "cleanup")
    monkeypatch.setattr(deterministic_candidates, "generate", lambda *args, **kwargs: [cleanup])
    monkeypatch.setattr(deterministic_native, "generate", lambda *args, **kwargs: [])

    def broken(**kwargs):
        raise RuntimeError("semantic helper failed")

    monkeypatch.setattr(semantic_compact, "generate_candidates", broken)
    records = []
    assert GENERATORS(settings(), "source", "signature", tmp_path, time.monotonic() + 1000, 16, records) == [cleanup]
    assert records[-1]["generator"] == "semantic_compact" and records[-1]["status"] == "failed"
    assert "semantic helper failed" in records[-1]["error"]["message"]


def test_validation_reserve_skip_is_distinct_and_cannot_exhaust_search(search, monkeypatch):
    cfg, capsule, state, _ = search
    cfg.update(settings(deterministic_budget_seconds=5, deterministic_max_candidates=8, deterministic_rounds=2))
    monkeypatch.setattr(deterministic, "_generators", GENERATORS)
    monkeypatch.setattr(deterministic_candidates, "generate", lambda *args, **kwargs: [])
    monkeypatch.setattr(deterministic_native, "generate", lambda *args, **kwargs: pytest.fail("native spent validation reserve"))
    monkeypatch.setattr(semantic_compact, "generate_candidates", lambda **kwargs: pytest.fail("semantic spent validation reserve"))
    _, report = run_search(search)
    assert not state["checks"]
    receipt = detailed(capsule)
    assert [(r["generator"], r["status"]) for r in receipt["generator_records"]] == [
        ("pure", "generated"), ("native", "skipped"), ("semantic_compact", "skipped")]
    assert all(r["incomplete"] and r["skip_reason"] == "validation_reserve" for r in receipt["generator_records"][1:])
    assert not report["search_exhausted"] and report["incomplete_generations"] == 1


@pytest.mark.parametrize("policy", ["legacy", "prioritized", "regional", "deep"])
def test_historical_generator_names_and_settings_unchanged(tmp_path, monkeypatch, policy):
    calls = {}
    monkeypatch.setattr(deterministic_candidates, "generate", lambda *args, **kwargs: calls.setdefault("pure", kwargs) and [])
    monkeypatch.setattr(deterministic_native, "generate", lambda *args, **kwargs: calls.setdefault("native", kwargs) and [])
    monkeypatch.setattr(compiler_simp, "generate", lambda *args, **kwargs: calls.setdefault("compiler_simp", kwargs) and [])
    monkeypatch.setattr(semantic_compact, "generate_candidates", lambda **kwargs: pytest.fail("historical policy discovered semantic terms"))
    cfg = replace(DEFAULT_SPEC, deterministic_refactoring=True, deterministic_policy=policy).proof_settings()
    records = []
    GENERATORS(cfg, "source", "signature", tmp_path, time.monotonic() + 10, 256, records)
    assert [r["generator"] for r in records] == (["pure", "native", "compiler_simp"] if policy == "deep" else ["pure", "native"])
    assert calls["pure"] == {"max_candidates": 256, **({"deep": True} if policy == "deep" else {})}
    assert calls["native"].get("policy", "legacy") == policy
    assert all(r["status"] == "generated" and "validation_reserve_seconds" not in r for r in records)


def source_fixture():
    row = {"name": "sample", "signature": "theorem sample : True", "header": ""}
    body = "by\n  exact True.intro /- ignored ÃŽÂ» Ã°Å¸Ëœâ‚¬ -/"
    source = lean_source.render_environment(row) + row["signature"] + " := " + body
    return row, source, body


@pytest.mark.parametrize("scoring", ["legacy-v1", "arena-v1"])
def test_source_bound_uses_exact_policy_tokens_and_prunes_equal_upper_bound(tmp_path, monkeypatch, scoring):
    row, source, body = source_fixture()
    cfg = {**settings(scoring_policy=scoring), "original_tokens": 238, "original_heartbeats": 4251}
    tokens = lean_source.candidate_proof_token_count(body, policy=scoring)
    upper = proof._policy(cfg).optimistic_score(tokens=tokens)
    monkeypatch.setattr(proof, "_check", lambda *args, **kwargs: pytest.fail("pruned source reached Lean"))
    record, path = {}, tmp_path / "Candidate.lean"
    # Ambient policy may differ; the frozen config controls the source lexer.
    with scoring_policy_context("arena-v1" if scoring == "legacy-v1" else "legacy-v1"):
        assert deterministic._validate(cfg, row, source, path, {"score": upper}, time.monotonic() + 10, record) is None
    assert not path.exists()
    assert record["source_tokens"] == tokens and record["score_upper_bound"] == upper
    assert record["status"] == "score_bound_pruned" and record["valid"] is None and record["validity"] == "unknown"
    assert record["native_validation_started"] is False
    assert record["declaration_sha256"] == proof._digest(source.strip())
    assert record["score_bound"] == {
        "source_sha256": proof._digest(source), "declaration_sha256": proof._digest(source.strip()),
        "scoring_policy": scoring, "tokens": tokens, "assumed_heartbeats": 0,
        "assumed_compatibility_pct": 100, "optimistic_score": upper, "incumbent_score": upper,
        "selection_policy": "strict_score_gain",
    }


@pytest.mark.parametrize("change", [lambda text: text.replace("sample : True", "sample : False"),
                                     lambda text: text.replace("exact True.intro", "sorry"),
                                     lambda text: text + "\ntheorem extra : True := by trivial"])
def test_ordinary_preflight_guards_run_before_source_bound(tmp_path, monkeypatch, change):
    row, source, _ = source_fixture()
    cfg = {**settings(), "original_tokens": 238, "original_heartbeats": 4251}
    monkeypatch.setattr(lean_source, "candidate_proof_token_count", lambda *args, **kwargs: pytest.fail("bound preceded preflight"))
    monkeypatch.setattr(proof, "_check", lambda *args, **kwargs: pytest.fail("invalid source reached Lean"))
    with pytest.raises(deterministic._GeneratorInvalid):
        deterministic._validate(cfg, row, change(source), tmp_path / "Candidate.lean", {"score": 100}, time.monotonic() + 10, {})


def test_promising_source_still_requires_exact_axioms_and_every_compatibility_version(search, monkeypatch):
    cfg, capsule, state, _ = search
    cfg.update(settings(deterministic_budget_seconds=5, deterministic_max_candidates=8, deterministic_rounds=2))
    state["candidates"] = ["best"]
    monkeypatch.setattr(lean_source, "extract_candidate_declaration", lambda row, source: (source, source))
    best, report = run_search(search)
    assert best["source"] == "best" and report["accepted_candidates"] == 1
    assert [quick for _, _, quick, _ in state["checks"]] == [False, True, True]
    record, = detailed(capsule)["candidate_records"]
    assert record["token_measurement_mode"] == "exact_source_lexer"
    assert record["native_validation_started"] is True and record["compatibility_complete"]
    assert record["evaluation"]["axiom_status"] == "measured"


def test_bound_pruning_is_terminal_traversal_without_negative_invalidity_cache(search, monkeypatch):
    cfg, capsule, state, _ = search
    cfg.update(settings(deterministic_budget_seconds=5, deterministic_max_candidates=8,
                        deterministic_rounds=2, deterministic_cache=True))
    state["candidates"] = ["same"]
    saved = []
    cache = SimpleNamespace(binding="binding", search_binding="search-binding", load_search=lambda: None,
        negative=lambda sha: None, save_search=lambda value: saved.append(value) or True,
        remember_invalid=lambda *args: pytest.fail("unknown validity entered negative cache"))
    monkeypatch.setattr(deterministic, "_search_cache", lambda *args: cache)
    monkeypatch.setattr(lean_source, "extract_candidate_declaration", lambda row, source: (source, source))
    monkeypatch.setattr(lean_source, "candidate_proof_token_count", lambda *args, **kwargs: 10000)
    _, report = run_search(search)
    assert not state["checks"] and report["negative_cache_hits"] == 0
    record, = detailed(capsule)["candidate_records"]
    assert record["status"] == "score_bound_pruned" and record["valid"] is None
    assert proof._digest("same") in saved[-1]["completed_sources"]
    assert report["search_exhausted"]


@pytest.mark.parametrize("policy", ["legacy", "prioritized", "regional", "deep"])
def test_historical_validator_does_not_compute_source_bound(tmp_path, monkeypatch, policy):
    row, source, _ = source_fixture()
    cfg = {**replace(DEFAULT_SPEC, deterministic_refactoring=True, deterministic_policy=policy).proof_settings(),
           "original_tokens": 238, "original_heartbeats": 4251, "primary": str(tmp_path), "compatibility": []}
    monkeypatch.setattr(lean_source, "candidate_proof_token_count", lambda *args, **kwargs: pytest.fail("historical source bound"))
    checks = []
    monkeypatch.setattr(proof, "_check", lambda *args, **kwargs: checks.append(1) or {"valid": False})
    record = {}
    assert deterministic._validate(cfg, row, source, tmp_path / "Candidate.lean", {"score": 100}, time.monotonic() + 10, record) is None
    assert checks == [1] and record["status"] == "primary_invalid"
    assert "score_bound" not in record


def semantic_edit(source, old, term):
    start = source.index(old)
    end = start + len(old)
    replacement = "exact (" + term + ")"
    child = source[:start] + replacement + source[end:]
    return {"id": "semantic-" + proof._digest(child)[:16], "family": semantic_search.SOLVER_FAMILY,
            "source": child, "source_sha256": proof._digest(child), "parent_sha256": proof._digest(source),
            "requires_full_validation": True, "site": start,
            "edits": [{"start": start, "end": end, "old": old, "new": replacement,
                       "old_sha256": proof._digest(old), "new_sha256": proof._digest(replacement),
                       "offset_unit": OFFSET_UNIT}]}


def test_regeneration_composes_compact_wins_from_fresh_source_bound_edits(search, monkeypatch):
    cfg, capsule, state, _ = search
    cfg.update(settings(deterministic_budget_seconds=5, deterministic_max_candidates=8,
                        deterministic_rounds=3, deterministic_regenerate=True))
    signature = "theorem Task.st : True"
    seed = (lean_source.render_environment({"name": "Task.st", "signature": signature}) + signature
            + " := by\n  have a : True := (by originalFirst)\n  have b : True := (by originalSecond)\n  exact a\n")
    cfg["initial_best"] = {**cfg["initial_best"], "source": seed, "sha256": proof._digest(seed)}
    generated, stale = [], []

    def generate(config, source, current_signature, directory, deadline, maximum, records):
        generated.append(source)
        proposals = [semantic_edit(source, old, "True.intro") for old in ("originalFirst", "originalSecond") if old in source]
        rows = [r for r in semantic_compact.compact_candidates(source, current_signature, proposals)
                if r.get("compaction") == "whole_parenthesized_by_term"]
        rows.sort(key=lambda row: "originalFirst" in row["source"])
        for row in rows:
            edit, = row["edits"]
            assert row["parent_sha256"] == proof._digest(source)
            assert source[edit["start"]:edit["end"]] == edit["old"]
        if source == seed:
            stale.extend(row for row in rows if "originalFirst" in row["source"])
        records.append({"generator": "semantic_compact", "status": "generated", "parent_sha256": proof._digest(source), "count": len(rows)})
        return rows

    def check(config, path, project, *, quick, timeout_seconds):
        source = path.read_text()
        state["checks"].append((source, str(project), quick, timeout_seconds))
        tokens = 100 if "originalSecond" in source else 50
        return {"valid": True, "measurement_mode": "exact", "axiom_status": "measured", "axioms": [],
                "length": {"candidate_tokens": tokens},
                "heartbeat": {"candidate": 100, "local_reference": config["original_heartbeats"]}}

    monkeypatch.setattr(deterministic, "_generators", generate)
    monkeypatch.setattr(proof, "_check", check)
    best, report = run_search(search)
    assert best["source"].count("(True.intro)") == 2
    assert "originalFirst" not in best["source"] and "originalSecond" not in best["source"]
    assert report["accepted_candidates"] == 2
    assert generated == [seed, generated[1], best["source"]]
    assert "originalFirst" not in generated[1] and "originalSecond" in generated[1]
    records = detailed(capsule)["candidate_records"]
    accepted = [r for r in records if r["status"] == "accepted"]
    # Retained parent alternatives may still receive ordinary validation after
    # the current parent is exhausted. They never replace the combined winner.
    stale_shas = {row["source_sha256"] for row in stale}
    assert all(r["sha256"] not in stale_shas for r in accepted)
    assert records[-1]["incumbent_after"]["sha256"] == best["sha256"]
    assert len(accepted) == 2 and all(r["compaction"] == "whole_parenthesized_by_term" for r in accepted)
    first, second = accepted
    assert second["parent_sha256"] == first["sha256"]
    assert second["edits"][0]["start"] != stale[0]["edits"][0]["start"]
    assert second["validation_started_seconds"] >= first["checkpoint_committed_seconds"]
