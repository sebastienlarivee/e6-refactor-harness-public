"""Optional traversal caches cannot promote missing evidence or consume retries."""
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from e6 import deterministic, proof
from e6.deterministic_support import search_cache
from e6.experiment import DEFAULT_SPEC, experiment_spec
from .test_deterministic import search, detailed
from .test_proof import manifest


@pytest.fixture
def cached(search, monkeypatch):
    settings, capsule, state, launch = search
    settings.update(replace(DEFAULT_SPEC, deterministic_refactoring=True,
        deterministic_budget_seconds=5, deterministic_max_candidates=8,
        deterministic_rounds=2, deterministic_cache=True).proof_settings())
    monkeypatch.setattr(proof.arena, "measurement_environment_fingerprint",
        lambda _row, project, **_kwargs: proof._digest(str(project)))
    monkeypatch.setattr(search_cache, "tool_identity", lambda _root: "tools-v1")
    return settings, capsule, state, launch


def next_pass(settings, number):
    capsule = Path(settings["root"]) / f"pass-{number:03d}"
    capsule.mkdir()
    return capsule


def run(cached, capsule=None, incumbent=None):
    settings, original, _, _ = cached
    return deterministic.optimize(settings, capsule or original, incumbent or settings["initial_best"])


def compiler_error(*, output="Candidate.lean:1:0: error: unknown identifier 'broken'", code=1, timeout=False,
                   stage="measured project compile"):
    return proof.arena.LeanCompileError(f"Task.st: {stage} failed with exit {code}", SimpleNamespace(
        output=output, returncode=code, timed_out=timeout))


def test_completed_identical_seed_reuses_verified_search_without_generation_or_checks(cached):
    settings, _, state, _ = cached
    state["candidates"] = ["same"]
    first, _ = run(cached)
    counts = len(state["generated"]), len(state["checks"])
    repeated, report = run(cached, next_pass(settings, 2))
    assert repeated["sha256"] == first["sha256"]
    assert report["search_reused"] and report["search_exhausted"]
    assert report["evaluated_candidates"] == 0
    assert counts == (len(state["generated"]), len(state["checks"]))


def test_cached_improvement_is_copied_into_new_immutable_verified_checkpoint(cached):
    settings, _, state, _ = cached
    state["candidates"] = ["better"]
    first, _ = run(cached)
    repeated, report = run(cached, next_pass(settings, 2))
    assert repeated["sha256"] == first["sha256"] and report["search_reused"]
    assert repeated["selected_path"] != first["selected_path"]
    proof._verify_incumbent(settings, repeated)
    assert Path(repeated["selected_path"]).read_text() == "better"
    assert len(state["checks"]) == 3


def test_truncated_seed_resumes_unseen_inventory_in_next_pass(cached):
    settings, _, state, _ = cached
    settings.update(replace(DEFAULT_SPEC, deterministic_refactoring=True,
        deterministic_budget_seconds=5, deterministic_max_candidates=2,
        deterministic_rounds=1, deterministic_cache=True).proof_settings())
    state["candidates"] = ["one", "two", "best"]
    first, initial = run(cached)
    assert first["source"] == "previous" and not initial["search_exhausted"]
    repeated, report = run(cached, next_pass(settings, 2))
    assert repeated["source"] == "best" and report["search_resumed"]
    assert report["evaluated_candidates"] == 1
    assert state["generated"] == ["previous"]
    assert [source for source, _, quick, _ in state["checks"] if not quick] == ["one", "two", "best"]


@pytest.mark.parametrize("failure", [TimeoutError("queue stalled"),
    compiler_error(timeout=True), compiler_error(code=-9),
    compiler_error(output="error: maximum number of heartbeats exceeded"),
    compiler_error(output="error: object file missing"),
    compiler_error(output="error: operation cancelled"),
    compiler_error(stage="measurement helper"), compiler_error(stage="project axiom audit"),
    compiler_error(stage="resolved project compile"), compiler_error(stage="resolved project axiom audit")])
def test_timeout_cancel_resource_and_infrastructure_are_retried_after_boundary(cached, monkeypatch, failure):
    settings, _, state, _ = cached
    state["candidates"] = ["best"]
    original, attempts = proof._check, []

    def fail_once(*args, **kwargs):
        attempts.append(1)
        if len(attempts) == 1:
            raise failure
        return original(*args, **kwargs)

    monkeypatch.setattr(proof, "_check", fail_once)
    first, report = run(cached)
    assert first["source"] == "previous" and not report["search_exhausted"]
    repeated, report = run(cached, next_pass(settings, 2))
    assert repeated["source"] == "best" and report["search_resumed"]
    assert report["negative_cache_hits"] == 0 and len(attempts) == 4


def test_negative_cache_skips_repeated_compile_invalid_source_from_another_seed(cached, monkeypatch):
    settings, _, state, _ = cached
    state["candidates"] = ["broken"]
    attempts = []

    def reject(*args, **kwargs):
        attempts.append(args[1].read_text())
        raise compiler_error()

    monkeypatch.setattr(proof, "_check", reject)
    run(cached)
    other_seed = {**settings["initial_best"], "source": "other", "sha256": proof._digest("other")}
    _, report = run(cached, next_pass(settings, 2), other_seed)
    assert attempts == ["broken"] and report["negative_cache_hits"] == 1
    assert not report["search_reused"]


@pytest.mark.parametrize("marker", [{"status": "cancelled"}, {"error_kind": "interrupted"},
                                  {"error_type": "CancelledError"}])
def test_structured_cancellation_does_not_exhaust_or_consume_cached_search(cached, monkeypatch, marker):
    settings, _, state, _ = cached
    state["candidates"] = ["best"]
    original, attempts = proof._check, []

    def fail_once(*args, **kwargs):
        attempts.append(1)
        return {"valid": False, "error": marker} if len(attempts) == 1 else original(*args, **kwargs)

    monkeypatch.setattr(proof, "_check", fail_once)
    first, report = run(cached)
    assert first["source"] == "previous" and not report["search_exhausted"]
    repeated, report = run(cached, next_pass(settings, 2))
    assert repeated["source"] == "best" and report["search_resumed"] and len(attempts) == 4


def test_cache_can_be_disabled_for_cold_ablation(cached, monkeypatch):
    settings, _, state, _ = cached
    settings.update(replace(experiment_spec(settings), deterministic_cache=False).proof_settings())
    settings.pop("deterministic_cache")
    state["candidates"] = ["same"]
    monkeypatch.setattr(deterministic, "_search_cache", lambda *_args: pytest.fail("disabled cache used"))
    run(cached)
    run(cached, next_pass(settings, 2))
    assert len(state["generated"]) == len(state["checks"]) == 2


def test_changed_checkpoint_audit_cannot_be_promoted_from_cached_search(cached):
    settings, capsule, state, _ = cached
    state["candidates"] = ["better"]
    run(cached)
    directory = capsule.parent / "deterministic" / capsule.name
    checkpoint = deterministic._read(directory / "checkpoint.json")
    checkpoint["best"]["compatibility"][0]["evaluation"]["axiom_status"] = "not_run"
    proof._write(directory / "checkpoint.json", checkpoint)
    state["candidates"] = []
    result, report = run(cached, next_pass(settings, 2))
    assert result["source"] == "previous" and not report["search_reused"]
    assert detailed(Path(settings["root"]) / "pass-002")["cache_errors"]


def test_cache_binding_tracks_environment_task_scoring_and_tool_content(cached, monkeypatch):
    settings, _, _, _ = cached
    row, seed = {}, settings["initial_best"]

    def key(config=settings, incumbent=seed):
        value = deterministic._search_cache(config, row, deterministic._settings(config), incumbent)
        return value.binding, value.search_binding

    original = key()
    alternate_seed = {**seed, "source": "other", "sha256": proof._digest("other")}
    changed_seed = key(incumbent=alternate_seed)
    assert changed_seed[0] == original[0] and changed_seed[1] != original[1]
    assert key({**settings, "original_tokens": settings["original_tokens"] + 1})[0] != original[0]
    monkeypatch.setattr(search_cache, "tool_identity", lambda _root: "tools-v2")
    assert key()[0] != original[0]
    monkeypatch.setattr(search_cache, "tool_identity", lambda _root: "tools-v1")
    monkeypatch.setattr(proof.arena, "measurement_environment_fingerprint", lambda *_args, **_kwargs: "other-env")
    assert key()[0] != original[0]
    monkeypatch.setattr(proof.arena, "measurement_environment_fingerprint",
        lambda _row, project, **_kwargs: proof._digest(str(project)))
    Path(settings["task"]).write_text("changed task")
    assert key()[0] != original[0]


def test_cache_binding_ignores_run_root_and_selected_path(cached, tmp_path, monkeypatch):
    settings, _, _, _ = cached
    monkeypatch.setenv("E6_DETERMINISTIC_CACHE_ROOT", str(tmp_path / "shared-cache"))
    seed = {**settings["initial_best"], "selected_path": str(Path(settings["root"]) / "pass-001/Selected.lean")}
    first = deterministic._search_cache(settings, {}, deterministic._settings(settings), seed)
    new_root = tmp_path / "new-proof-root"
    new_root.mkdir()
    for name in ("task", "fingerprint_registry"):
        (new_root / Path(settings[name]).name).write_bytes(Path(settings[name]).read_bytes())
    relocated = {**settings, "root": str(new_root),
        "task": str(new_root / Path(settings["task"]).name),
        "fingerprint_registry": str(new_root / Path(settings["fingerprint_registry"]).name),
        "source_migration": {"path": str(new_root / "resumes/migration.json"), "sha256": "per-job-digest"}}
    relocated_seed = {**seed, "selected_path": str(new_root / "pass-002/Selected.lean")}
    second = deterministic._search_cache(relocated, {}, deterministic._settings(relocated), relocated_seed)
    assert first.directory == second.directory and first.search_binding == second.search_binding


def test_source_intake_is_generator_invalid_before_any_validation(search, monkeypatch):
    settings, capsule, state, _ = search
    state["candidates"] = ["broken scaffold"]
    monkeypatch.setattr(proof.arena, "extract_candidate_declaration",
        lambda *_args: (_ for _ in ()).throw(proof.arena.WorkflowError("missing target end marker")))
    result, _ = deterministic.optimize(settings, capsule, settings["initial_best"])
    assert result["source"] == "previous" and not state["checks"]
    record = detailed(capsule)["candidate_records"][0]
    assert record["status"] == record["error_kind"] == "generator_invalid"


def test_elapsed_proposal_validation_acceptance_and_commit_are_monotonic(search):
    settings, capsule, state, _ = search
    state["candidates"] = ["better"]
    deterministic.optimize(settings, capsule, settings["initial_best"])
    report = detailed(capsule)
    accepted = next(record for record in report["candidate_records"] if record.get("status") == "accepted")
    values = [accepted[key] for key in ("proposal_ready_seconds", "validation_started_seconds",
        "validation_finished_seconds", "accepted_seconds", "checkpoint_committed_seconds")]
    assert 0 <= values[0] <= values[1] <= values[2] <= values[3] <= values[4] <= report["wall_seconds"]
    assert report["timing_clock"] == "worker_monotonic_elapsed_seconds"


def test_rebase_composes_next_round_from_winner_before_old_parent_tail(search):
    settings, capsule, state, _ = search
    settings.update(replace(experiment_spec(settings), deterministic_regenerate=True).proof_settings())
    state["candidates"] = lambda source: ["better", "old-tail"] if source == "previous" else ["best"]
    best, _ = deterministic.optimize(settings, capsule, settings["initial_best"])
    assert best["source"] == "best" and state["generated"] == ["previous", "better"]
    assert "old-tail" not in state["sources"]


def test_rebase_retains_parent_breadth_when_winner_has_no_children(search):
    settings, capsule, state, _ = search
    settings.update(replace(experiment_spec(settings), deterministic_regenerate=True).proof_settings())
    state["candidates"] = lambda source: ["better", "best"] if source == "previous" else []
    best, report = deterministic.optimize(settings, capsule, settings["initial_best"])
    assert best["source"] == "best" and state["generated"] == ["previous", "better"]
    # The last accepted source still needs its own generation before exhaustion.
    assert not report["search_exhausted"]


def test_failed_checkpoint_write_does_not_consume_candidate_for_resume(cached, monkeypatch):
    settings, capsule, state, _ = cached
    state["candidates"] = ["best"]
    original = deterministic._immutable_source
    attempts = []

    def fail_once(path, source):
        if path.parent.name == "validated":
            attempts.append(1)
            if len(attempts) == 1:
                raise OSError("checkpoint disk interrupted")
        return original(path, source)

    monkeypatch.setattr(deterministic, "_immutable_source", fail_once)
    first, report = run(cached)
    assert first["source"] == "previous" and not report["search_exhausted"]
    repeated, report = run(cached, next_pass(settings, 2))
    assert repeated["source"] == "best" and report["search_resumed"]


def test_deadline_before_candidate_admission_keeps_offset_unseen(cached, monkeypatch):
    settings, capsule, state, _ = cached
    clock = {"now": 0.0}
    monkeypatch.setattr(deterministic.time, "monotonic", lambda: clock["now"])
    original = deterministic._generators

    def finish_generation_at_deadline(*args, **kwargs):
        values = original(*args, **kwargs)
        clock["now"] = 10.0
        return values

    state["candidates"] = ["best"]
    monkeypatch.setattr(deterministic, "_generators", finish_generation_at_deadline)
    first, report = run(cached)
    assert first["source"] == "previous" and report["evaluated_candidates"] == 0
    monkeypatch.setattr(deterministic, "_generators", original)
    # Worker starts with a fresh relative deadline even though monotonic's
    # arbitrary absolute origin is unchanged.
    repeated, report = run(cached, next_pass(settings, 2))
    assert repeated["source"] == "best" and report["search_resumed"]


def test_tool_identity_includes_compiler_helper_assets(tmp_path):
    root = tmp_path / "source"
    (root / "e6/support").mkdir(parents=True)
    (root / "lean_tools").mkdir()
    helper = root / "e6/support/helper.lean.inc"
    helper.write_text("first helper")
    before = search_cache.tool_identity(root)
    helper.write_text("changed helper")
    assert search_cache.tool_identity(root) != before


def test_cache_snapshot_size_and_negative_entry_count_are_bounded(tmp_path, monkeypatch):
    monkeypatch.setattr(search_cache, "MAX_NEGATIVES", 2)
    cache = search_cache.SearchCache(tmp_path, {"environment": "one"}, {"seed": "one"})
    receipt = search_cache.compile_rejection(compiler_error(), proof.arena.LeanCompileError)
    for number in range(3):
        cache.remember_invalid(str(number), receipt)
    assert cache.negative("0") is None and cache.negative("2") is not None
    monkeypatch.setattr(search_cache, "MAX_SNAPSHOT_BYTES", 64)
    assert not cache.save_search({"oversized": "x" * 100})
    assert cache.load_search() == {}
