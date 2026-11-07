"""Regression coverage for one-call scoring and independent comparison policy."""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from lean_tools import candidate_batches as batches
from lean_tools import feedback_workflow as feedback

arena = feedback.arena


@pytest.fixture
def service(tmp_path):
    row = {"name": "efficient_demo", "header": "import Mathlib\n\n", "contexts": [],
           "signature": "theorem efficient_demo : True",
           "src": "theorem efficient_demo : True := by\n  exact True.intro", "proof_length": 10}
    task = tmp_path / "Task.json"
    task.write_text(json.dumps({"schema_version": 1, "row": row}), encoding="utf-8")
    candidate = tmp_path / "Candidate.lean"
    candidate.write_text(arena.render_candidate_scaffold(row), encoding="utf-8")
    return feedback.Feedback({"task": str(task), "candidate": str(candidate),
        "project_root": str(tmp_path / "primary"), "candidate_batches": False,
        "original_tokens": 100, "original_heartbeats": 100, "incumbent_score": 99,
        "compatibility_roots": [str(tmp_path / "compatibility")]})


def evaluation(path, *, quick):
    return arena.Evaluation(task_id="efficient_demo", candidate_path=str(path), valid=True,
        compile_seconds=0.1, axiom_audit_seconds=None if quick else 0.1,
        axioms=None if quick else [], original_local_tokens=100, candidate_local_tokens=10,
        local_token_reduction_pct=90, official_original_tokens=100,
        heartbeat=None if quick else 20, environment_fingerprint="synthetic")


@pytest.mark.parametrize("mutation", ["body", "edits", "source_text"])
def test_direct_score_mutations_need_no_prior_edit_and_never_prune(service, monkeypatch, mutation):
    before = service.candidate.read_bytes()
    digest = arena.sha256_bytes(before)
    source = before.decode("utf-8").replace("exact True.intro", "trivial")
    payload = {"body": "by\n  trivial", "edits": [{"old": "exact True.intro", "new": "trivial"}],
               "source_text": source}[mutation]
    if mutation == "body":
        source = source.replace(":= by\n", ":=\nby\n")
    calls = []

    def evaluate(_task, snapshot, project, *, quick, **_kwargs):
        calls.append((project, quick))
        assert snapshot.read_text() == source
        return evaluation(snapshot, quick=quick)

    monkeypatch.setattr(arena, "evaluate_candidate", evaluate)
    result = batches.score_candidate(service, {"expected_sha256": digest, mutation: payload})

    assert calls == [(service.project, True), (service.project, False),
                     (Path(service.settings["compatibility_roots"][0]).resolve(), True)]
    assert result["status"] == "valid_scored" and result["score"] == 90
    assert result["score"] < service.settings["incumbent_score"]
    assert result["compatibility_status"] == "complete"
    assert result["source_sha256"] == arena.sha256_bytes(source.encode("utf-8"))
    assert Path(result["checkpoint"]).read_text() == source
    assert service.candidate.read_bytes() == before


def test_direct_checkpoint_mutation_uses_current_destination_hash_without_rewriting_draft(service, monkeypatch):
    monkeypatch.setattr(arena, "evaluate_candidate", lambda _task, path, _project, *, quick, **_kw:
                        evaluation(path, quick=quick))
    first = batches.score_candidate(service, {"expected_sha256": arena.sha256_file(service.candidate)})
    # Source is intentionally unfinished: the checkpoint supplies the next experiment's base.
    service.candidate.write_text(service.candidate.read_text().replace("exact True.intro", "skip"))
    changed = service.candidate.read_bytes()
    destination_hash = arena.sha256_bytes(changed)
    result = batches.score_candidate(service, {"expected_sha256": destination_hash,
        "checkpoint_id": first["checkpoint_id"],
        "edits": [{"old": "exact True.intro", "new": "trivial"}]})

    assert result["status"] == "valid_scored" and result["score"] == 90
    assert "trivial" in Path(result["checkpoint"]).read_text()
    assert result["base_source_sha256"] == destination_hash
    assert result["source_sha256"] != destination_hash
    assert service.candidate.read_bytes() == changed


@pytest.mark.parametrize("good_first", [False, True])
def test_mixed_batch_failures_retain_valid_neighbors_and_full_evidence(service, monkeypatch, good_first):
    service.settings.update(candidate_batches=True, incumbent_score=None)
    before = service.candidate.read_bytes()
    alternatives = [
        {"label": "edit_error", "edits": [{"old": "missing exact fragment", "new": "trivial"}]},
        {"label": "compile_error", "body": "by exact Nat.zero"},
        {"label": "timeout", "body": "by trivial"},
        {"label": "good", "body": "by exact True.intro"},
    ]
    if good_first:
        alternatives.reverse()

    def evaluate(_task, path, _project, *, quick, **_kwargs):
        source = path.read_text()
        if "Nat.zero" in source:
            arena.require_lean_success(arena.LeanRun(command=[], returncode=1, seconds=0.1,
                output="type mismatch\nfull compile diagnostic", diagnostics_path="/missing/diagnostic.json"),
                "candidate compile")
        if "by trivial" in source:
            raise arena.LeanTimeoutError("test compile deadline", arena.LeanRun(
                command=[], returncode=1, seconds=0.1, output="full timeout diagnostic", timed_out=True))
        return evaluation(path, quick=quick)

    monkeypatch.setattr(arena, "evaluate_candidate", evaluate)
    result = batches.compare_candidates(service, {"expected_sha256": arena.sha256_bytes(before),
        "alternatives": alternatives})
    rows = {row["label"]: row for row in result["alternatives"]}

    assert len(rows) == 4 and result["ranking"] == ["good"] and result["best_label"] == "good"
    assert rows["edit_error"]["status"] == rows["compile_error"]["status"] == "invalid"
    assert rows["timeout"]["status"] == "timeout" and rows["timeout"]["valid"] is None
    assert rows["good"]["status"] == "valid_scored" and rows["good"]["score"] == 90
    assert "exact True.intro" in Path(rows["good"]["checkpoint"]).read_text()
    assert all(rows[label]["score"] is None and rows[label]["checkpoint"] is None
               for label in ("edit_error", "compile_error", "timeout"))
    full = json.loads(Path(result["details_path"]).read_text())
    assert full["summary"] == result
    details = {item["request"]["label"]: item for item in full["alternatives"]}
    assert "full compile diagnostic" in details["compile_error"]["lean_run"]["output"]
    assert "full timeout diagnostic" in details["timeout"]["lean_run"]["output"]
    assert service.candidate.read_bytes() == before


@pytest.mark.parametrize("tool", ["score_candidate", "compare_candidates"])
def test_candidate_failure_previews_preserve_goal_and_durable_raw_output(service, monkeypatch, tool):
    service.settings["candidate_batches"] = True
    before = service.candidate.read_bytes()
    output = ("candidate:4:3: error: unsolved goals\n" + "local : α\n" * 30
              + "⊢ first_target =\n    wrapped_target\n")

    def evaluate(*_args, **_kwargs):
        raise arena.LeanCompileError("candidate compile failed", arena.LeanRun(
            [], 1, 0.1, output, log_path="/archive/unchanged.log"))

    monkeypatch.setattr(arena, "evaluate_candidate", evaluate)
    request = {"expected_sha256": arena.sha256_bytes(before)}
    if tool == "compare_candidates":
        request["alternatives"] = [{"label": label, "body": "by skip"} for label in ("one", "two")]
    result = getattr(batches, tool)(service, request)
    rows = result["alternatives"] if tool == "compare_candidates" else [result]
    full = json.loads(Path(result["details_path"]).read_text())

    for index, row in enumerate(rows):
        assert row["status"] == "invalid" and row["valid"] is False
        assert row["score"] is None and row["checkpoint"] is None
        assert "⊢ first_target =\n    wrapped_target" in row["diagnostic"]["message"]
        assert row["diagnostic"]["truncated"] is True
        assert row["diagnostics_path"] == "/archive/unchanged.log"
        assert full["alternatives"][index]["lean_run"]["output"] == output
    assert service.candidate.read_bytes() == before
