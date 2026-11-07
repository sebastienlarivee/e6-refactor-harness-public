"""Offline admission/provenance fixtures; these never invoke Lean or a model."""
from __future__ import annotations

import json
import threading
from dataclasses import replace
from pathlib import Path

import pytest

from lean_tools import arena_workflow as arena
from lean_tools import lean_source


@pytest.fixture
def source_fixture(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    row = {
        "name": "demo",
        "header": "import Mathlib\nimport Aesop\n\n",
        "contexts": [],
        "signature": "theorem demo : True",
        "src": "theorem demo : True := by trivial",
    }
    task = tmp_path / "Task.json"
    task.write_text(json.dumps({"schema_version": 1, "row": row}), encoding="utf-8")
    candidate = tmp_path / "Candidate.lean"
    original = lean_source.render_candidate_scaffold(row).encode("utf-8")
    candidate.write_bytes(original)
    scratch = tmp_path / "scratch"
    scratch.mkdir()
    monkeypatch.setattr(arena, "evaluation_scratch_parent", lambda: scratch)
    monkeypatch.setattr(arena, "evaluation_cache_root", lambda: None)
    monkeypatch.setattr(arena, "measurement_environment_fingerprint", lambda *a, **k: "f" * 64)
    monkeypatch.setattr(arena, "record_event", lambda *a, **k: None)
    monkeypatch.setattr(arena, "persistent_quick_matches_project", lambda _root: False)
    return task, candidate, row, original


def measurement(path: Path, row: dict, *, quick: bool = False) -> arena.Evaluation:
    data = path.read_bytes()
    _, body = lean_source.extract_candidate_declaration(
        row, lean_source.candidate_text_from_bytes(data)
    )
    return arena.Evaluation(
        task_id=row["name"], candidate_path=str(path), valid=True,
        compile_seconds=0.1, axiom_audit_seconds=None if quick else 0.1,
        axioms=None if quick else [], original_local_tokens=10,
        candidate_local_tokens=len(lean_source.local_proof_tokens(body)),
        local_token_reduction_pct=80.0, official_original_tokens=None,
        heartbeat=None if quick else 7, environment_fingerprint="f" * 64,
        source_sha256=arena.sha256_bytes(data),
    )


@pytest.mark.parametrize("cached", [False, True])
def test_cli_concurrent_draft_edit_keeps_measurement_and_checkpoint_bound(
    source_fixture, tmp_path, monkeypatch, capsys, cached,
):
    task, candidate, row, original = source_fixture
    if cached:
        monkeypatch.setattr(arena, "evaluation_cache_root", lambda: tmp_path / "cache")
    admitted = threading.Event()
    edited = threading.Event()
    observed = []

    def evaluate(_task, snapshot, _project, **_kwargs):
        assert snapshot != candidate
        admitted.set()
        assert edited.wait(5), "draft mutation did not finish"
        observed.append(snapshot.read_bytes())
        return measurement(snapshot, row)

    def mutate():
        assert admitted.wait(5), "evaluation did not admit a snapshot"
        candidate.write_bytes(original.replace(b"by trivial", b"by exact True.intro"))
        edited.set()

    monkeypatch.setattr(arena, "_evaluate_candidate_uncached", evaluate)
    editor = threading.Thread(target=mutate)
    editor.start()
    try:
        result = arena.main([
            "evaluate", "--task", str(task), "--candidate", str(candidate),
            "--project-root", str(tmp_path), "--checkpoint-dir", str(tmp_path / "valid"),
        ])
    finally:
        editor.join(5)
    assert result == 0
    assert observed == [original]
    assert candidate.read_bytes() != original
    checkpoint, = (tmp_path / "valid").glob("*.lean")
    assert checkpoint.read_bytes() == original
    receipt = json.loads(checkpoint.with_suffix(".json").read_text())
    payload = json.loads(capsys.readouterr().out.split("\ncheckpoint:", 1)[0])
    digest = arena.sha256_bytes(original)
    assert checkpoint.name.endswith(f"-{digest[:12]}.lean")
    assert receipt["source_sha256"] == payload["source_sha256"] == digest
    assert receipt["task_id"] == "demo" and receipt["validation"] == "exact"
    assert receipt["candidate_local_tokens"] == payload["length"]["candidate_tokens"] == 2
    assert payload["candidate_path"] == str(candidate.resolve())


def test_cache_identity_stays_declaration_based_and_source_hash_is_per_request(
    source_fixture, tmp_path, monkeypatch,
):
    task, candidate, row, original = source_fixture
    cache = tmp_path / "cache"
    monkeypatch.setattr(arena, "evaluation_cache_root", lambda: cache)
    calls = []

    def evaluate(_task, snapshot, _project, **_kwargs):
        calls.append(snapshot.read_bytes())
        return measurement(snapshot, row)

    monkeypatch.setattr(arena, "_evaluate_candidate_uncached", evaluate)
    first = arena.evaluate_candidate(task, candidate, tmp_path)
    # Candidate markers and raw newline bytes are outside declaration identity.
    alternate = (lean_source.render_environment(row) + row["src"] + "\n\n").replace("\n", "\r\n").encode()
    candidate.write_bytes(alternate)
    second = arena.evaluate_candidate(task, candidate, tmp_path, quick=True)
    assert calls == [original]
    assert first.cache_status == "miss" and second.cache_status == "hit"
    assert second.cache_source_mode == "exact" and second.heartbeat is None
    assert first.source_sha256 == arena.sha256_bytes(original)
    assert second.source_sha256 == arena.sha256_bytes(alternate) != first.source_sha256
    entries = list(cache.rglob("*.json"))
    assert len(entries) == 1
    assert "source_sha256" not in json.loads(entries[0].read_text())["evaluation"]


def test_fresh_quick_compile_uses_the_captured_bytes(source_fixture, tmp_path, monkeypatch):
    task, candidate, row, original = source_fixture
    compiled = []

    def broker_unavailable(_project):
        candidate.write_bytes(original.replace(b"by trivial", b"by exact True.intro"))
        return False

    def compile_snapshot(path, _project, _timeout):
        assert path != candidate
        compiled.append(path.read_bytes())
        return arena.LeanRun(["lean"], 0, 0.1, "")

    monkeypatch.setattr(arena, "persistent_quick_matches_project", broker_unavailable)
    monkeypatch.setattr(arena, "run_lean", compile_snapshot)
    result = arena.evaluate_candidate_fresh(task, candidate, tmp_path, quick=True)
    assert compiled == [original]
    assert result.source_sha256 == arena.sha256_bytes(original)
    assert result.candidate_local_tokens == 2


@pytest.mark.parametrize("invalid_result", [None, False])
def test_empty_or_invalid_evaluator_return_is_not_cached(source_fixture, tmp_path, monkeypatch, invalid_result):
    task, candidate, row, _original = source_fixture
    cache = tmp_path / "cache"
    monkeypatch.setattr(arena, "evaluation_cache_root", lambda: cache)
    monkeypatch.setattr(arena, "_evaluate_candidate_uncached", lambda *a, **k: (
        None if invalid_result is None else replace(measurement(candidate, row), valid=False)
    ))
    with pytest.raises(arena.WorkflowError, match="complete candidate validity"):
        arena.evaluate_candidate(task, candidate, tmp_path)
    assert not list(cache.rglob("*.json"))
    assert not list(cache.rglob("*.lock"))


def test_tampered_evaluation_snapshot_is_not_cached(source_fixture, tmp_path, monkeypatch):
    task, candidate, row, _original = source_fixture
    cache = tmp_path / "cache"
    monkeypatch.setattr(arena, "evaluation_cache_root", lambda: cache)

    def evaluate(_task, snapshot, _project, **_kwargs):
        result = measurement(snapshot, row)
        snapshot.write_text("tampered", encoding="utf-8")
        return result

    monkeypatch.setattr(arena, "_evaluate_candidate_uncached", evaluate)
    with pytest.raises(arena.WorkflowError, match="snapshot changed"):
        arena.evaluate_candidate(task, candidate, tmp_path)
    assert not list(cache.rglob("*.json"))


def test_checkpoint_override_requires_evaluated_hash_and_uses_admitted_bytes(source_fixture, tmp_path):
    _task, candidate, row, original = source_fixture
    result = measurement(candidate, row)
    candidate.write_text("the draft changed", encoding="utf-8")
    valid = tmp_path / "valid"
    with pytest.raises(arena.WorkflowError, match="changed since evaluation"):
        arena.checkpoint_candidate(candidate, result, valid)
    assert not valid.exists()
    checkpoint = arena.checkpoint_candidate(candidate, result, valid, source_bytes=original)
    assert checkpoint.read_bytes() == original
    with pytest.raises(arena.WorkflowError, match="changed since evaluation"):
        arena.checkpoint_candidate(candidate, result, valid, source_bytes=b"other source")
    with pytest.raises(arena.WorkflowError, match="lacks evaluated source provenance"):
        arena.checkpoint_candidate(candidate, replace(result, source_sha256=None), valid, source_bytes=original)


@pytest.mark.parametrize("value", [None, False, "empty", "bad_tokens"])
def test_checkpoint_invalid_inputs_create_no_artifacts(source_fixture, tmp_path, value):
    _task, candidate, row, _original = source_fixture
    result = measurement(candidate, row)
    if value is None:
        result = None
    elif value is False:
        result = replace(result, valid=False)
    elif value == "empty":
        candidate.write_bytes(b" \n")
        result = replace(result, source_sha256=arena.sha256_bytes(b" \n"))
    else:
        result = replace(result, candidate_local_tokens=True)
    valid = tmp_path / "valid"
    with pytest.raises(arena.WorkflowError):
        arena.checkpoint_candidate(candidate, result, valid)
    assert not valid.exists()


def test_checkpoint_collision_does_not_overwrite_existing_file(source_fixture, tmp_path):
    _task, candidate, row, original = source_fixture
    result = measurement(candidate, row)
    valid = tmp_path / "valid"
    valid.mkdir()
    checkpoint = valid / f"000002-{arena.sha256_bytes(original)[:12]}.lean"
    checkpoint.write_text("unrelated bytes", encoding="utf-8")
    with pytest.raises(arena.WorkflowError, match="content-address collision"):
        arena.checkpoint_candidate(candidate, result, valid)
    assert checkpoint.read_text() == "unrelated bytes"
    assert not checkpoint.with_suffix(".json").exists()


def test_quick_checkpoint_preserves_only_matching_context_exact_receipt(source_fixture, tmp_path):
    _task, candidate, row, _original = source_fixture
    exact = measurement(candidate, row)
    quick = measurement(candidate, row, quick=True)
    checkpoint = arena.checkpoint_candidate(candidate, exact, tmp_path / "valid")
    receipt = checkpoint.with_suffix(".json")
    arena.checkpoint_candidate(candidate, quick, tmp_path / "valid")
    saved = json.loads(receipt.read_text())
    assert saved["validation"] == "exact" and saved["heartbeat"] == 7
    arena.checkpoint_candidate(
        candidate, replace(quick, environment_fingerprint="other"), tmp_path / "valid"
    )
    saved = json.loads(receipt.read_text())
    assert saved["validation"] == "quick" and saved["heartbeat"] is None


@pytest.mark.parametrize("body", [
    "by aesop (add unsafe constructors ParallelReduction)",
    "by aesop (add unsafe 50% apply True.intro)",
    "by aesop (add unsafe cases Or)",
    "by\n  -- unsafe def in a comment\n  /- unsafe /- nested -/ theorem -/\n  trivial",
    'by\n  let hint := "unsafe def"\n  trivial',
])
def test_unsafe_rule_phase_and_comment_text_pass_lexical_guard(source_fixture, body):
    _task, _candidate, row, _original = source_fixture
    assert lean_source.validate_declaration(row, row["signature"] + " := " + body) == body


@pytest.mark.parametrize("construct", [
    "unsafe def evil : Nat := 0", "unsafe fun x => x", "unsafe theorem evil : True := by trivial",
    "private unsafe lemma evil : True := by trivial", "unsafe noncomputable def evil := 0",
    "unsafe\n/- separated modifier -/\ndef evil := 0", "unsafe abbrev evil := 0",
])
def test_unsafe_declarations_remain_forbidden(source_fixture, construct):
    _task, _candidate, row, _original = source_fixture
    with pytest.raises(arena.WorkflowError, match="forbidden proof construct.*unsafe"):
        lean_source.validate_declaration(row, row["signature"] + " := by\n  " + construct)


@pytest.mark.parametrize("construct", [
    "sorry", "axiom evil : False", "native_decide", "set_option debug.skipKernelTC true in trivial",
])
def test_other_kernel_and_axiom_guards_remain_forbidden(source_fixture, construct):
    _task, _candidate, row, _original = source_fixture
    with pytest.raises(arena.WorkflowError, match="forbidden proof construct"):
        lean_source.validate_declaration(row, row["signature"] + " := by\n  " + construct)


def test_rule_phase_exception_preserves_frozen_header_and_context(source_fixture):
    _task, _candidate, row, _original = source_fixture
    candidate = lean_source.render_environment(row) + row["signature"] + " := by aesop (add unsafe constructors True)\n"
    lean_source.extract_candidate_declaration(row, candidate)
    with pytest.raises(arena.WorkflowError, match="frozen header"):
        lean_source.extract_candidate_declaration(row, "open Classical\n" + candidate)
    contextual = dict(row, contexts=[{"src": "def fixed : Prop := True"}])
    with pytest.raises(arena.WorkflowError, match="frozen header.*contexts"):
        lean_source.extract_candidate_declaration(contextual, candidate)
    with pytest.raises(arena.WorkflowError, match="unexpected axiom dependencies"):
        arena.parse_and_validate_axioms("demo", "'demo' depends on axioms: [evil]")
