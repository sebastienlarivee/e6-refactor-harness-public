"""No-model finalist and fresh-capsule regressions."""
from dataclasses import replace
import json
from pathlib import Path

import pytest

from e6 import prompt_bundle, proof
from e6.experiment import DEFAULT_SPEC


@pytest.fixture(autouse=True)
def manifest(tmp_path, monkeypatch):
    monkeypatch.delenv("E6_BASELINE_CACHE", raising=False)
    monkeypatch.delenv("E6_BASELINE_SEEDS", raising=False)
    canonical = tmp_path / "canonical"
    canonical.mkdir()
    proofs = {}
    for label, tokens, heartbeats, environment_count in (
            ("st", 238, 4251, 3), ("ph", 1240, 42080, 1),
            ("ar", 1424, 15646, 4), ("pu", 1837, 141101, 3)):
        task = canonical / f"{label}.json"
        task.write_text(json.dumps({"schema_version": 1, "row": {
            "name": f"Task.{label}", "signature": f"theorem Task.{label} : True",
            "src": f"theorem Task.{label} : True := by trivial"}}))
        proofs[label] = {
            "task_id": f"Task.{label}", "task": str(task), "task_sha256": proof.arena.sha256_file(task),
            "primary": str(tmp_path / label / "primary"),
            "compatibility": [str(tmp_path / label / f"old-{index}") for index in range(1, environment_count)],
            "original_tokens": tokens, "original_heartbeats": heartbeats,
            "registry_source": str(tmp_path / label / "source-registry.json"),
            "published_reference_heartbeats": heartbeats + 1,
            "original_baseline": {"heartbeat": heartbeats, "instrumentation": "project-command-heartbeat-v1"},
        }
    path = tmp_path / "proofs.json"
    path.write_text(json.dumps({"schema_version": 1, "proofs": proofs}))
    monkeypatch.setattr(proof, "PROOFS", path)
    return proofs


def config(root, label="st"):
    root.mkdir(parents=True, exist_ok=True)
    metadata = proof._metadata(label)
    task, registry = root / "Task.json", root / "environment-fingerprints.json"
    task.write_bytes(Path(metadata["task"]).read_bytes())
    registry.write_text('{"entries":{}}')
    original = "previous"
    settings = {**replace(DEFAULT_SPEC, stopping_policy="cost", first_pass_reference_rebuild=False).proof_settings(),
            **metadata, "root": str(root), "canonical_task": metadata["task"],
            "task": str(task), "task_sha256": proof.arena.sha256_file(task),
            "fingerprint_registry": str(registry), "fingerprint_registry_sha256": proof.arena.sha256_file(registry),
            "label": label, "proof_metadata_sha256": proof._metadata_digest(label, metadata),
            "pass_timeout_seconds": None, "total_budget_usd": 3,
            "check_timeout_seconds": 600}
    settings["prompt_bundle"] = prompt_bundle.snapshot(DEFAULT_SPEC.prompt_variant)
    settings["initial_best"] = {**proof._incumbent_metadata(settings),
                "source": original, "sha256": proof._digest(original), "valid": True,
                "compatibility_complete": True, "compatibility_pct": 100,
                "tokens": 200, "heartbeats": 800,
                "score": proof._policy(settings).score(tokens=200, heartbeats=800, compatibility_pct=100)}
    return settings


@pytest.fixture
def selection(tmp_path, monkeypatch):
    settings = config(tmp_path)
    capsule = tmp_path / "pass-001"
    (capsule / "valid-candidates").mkdir(parents=True)
    monkeypatch.setattr(proof.arena, "load_task", lambda _path: ({}, {"name": "fake"}))
    monkeypatch.setattr(proof.arena, "extract_candidate_declaration", lambda _row, source: (source, source))
    calls = []

    def check(_config, candidate, project, *, quick=False, timeout_seconds=600):
        source = candidate.read_text()
        calls.append((source, str(project), quick))
        if source == "invalid":
            return {"valid": False}
        tokens, beats = {"current": (130, 800), "saved": (100, 200), "worse": (230, 2000)}[source]
        return {"valid": not (quick and source == "incompatible"),
                "length": {"candidate_tokens": tokens},
                "heartbeat": {"candidate": beats, "local_reference": _config["original_heartbeats"]}}

    monkeypatch.setattr(proof, "_check", check)
    return settings, capsule, calls


def test_finalist_selects_best_saved_proof_with_original_denominators_and_deduplicates(selection):
    settings, capsule, calls = selection
    (capsule / "Candidate.lean").write_text("current")
    checkpoints = capsule / "valid-candidates"
    (checkpoints / "one.lean").write_text("saved")
    (checkpoints / "duplicate.lean").write_text("saved")
    (checkpoints / "incumbent.lean").write_text("previous")
    result = proof.finalize(settings, capsule)
    assert result["source"] == "saved"
    assert result["score"] == proof._policy(settings).score(tokens=100, heartbeats=200, compatibility_pct=100)
    assert len(calls) == 6 and sum(not item[2] for item in calls) == 2
    assert (capsule / "Selected.lean").read_text() == "saved"
    assert json.loads((capsule / "selection.json").read_text())["original_tokens"] == 238


@pytest.mark.parametrize("source", ["invalid", "worse"])
def test_invalid_or_nonimproving_candidate_preserves_verified_fallback(selection, source):
    settings, capsule, calls = selection
    (capsule / "Candidate.lean").write_text(source)
    result = proof.finalize(settings, capsule)
    assert result["source"] == "previous" and result["score"] == settings["initial_best"]["score"]
    assert len(calls) == 1 and calls[0][2] is False


def test_finalization_refuses_modified_frozen_task_before_any_check(selection):
    settings, capsule, calls = selection
    Path(settings["task"]).write_text("changed")
    with pytest.raises(ValueError, match="Frozen original task"):
        proof.finalize(settings, capsule)
    assert not calls


def test_finalist_applies_public_character_limit_only_to_submitted_declaration(selection, monkeypatch):
    settings, capsule, calls = selection
    # Large UTF-8 capsule/scaffold bytes do not enlarge the submitted theorem.
    (capsule / "Candidate.lean").write_text("λ" * 300000, encoding="utf-8")
    monkeypatch.setattr(proof.arena, "extract_candidate_declaration", lambda _row, source: ("d", source))
    def check(*_args, **_kwargs):
        calls.append("checked")
        return {"valid": False}
    monkeypatch.setattr(proof, "_check", check)
    proof.finalize(settings, capsule)
    assert calls == ["checked"]


def test_oversized_submitted_declaration_is_not_a_valid_contest_candidate(selection):
    settings, capsule, calls = selection
    (capsule / "Candidate.lean").write_text("d" * (256 * 1024 + 1))
    result = proof.finalize(settings, capsule)
    assert result["source"] == "previous" and not calls
    selection_record = json.loads((capsule / "selection.json").read_text())
    assert "intake limit" in selection_record["candidate_records"][0]["error"]


def test_higher_contest_score_can_trade_compatibility_for_length_and_heartbeats(selection, monkeypatch):
    settings, capsule, _calls = selection
    (capsule / "Candidate.lean").write_text("tiny")
    def check(_config, _candidate, project, *, quick=False, **_kwargs):
        return {"valid": not (quick and str(project) == settings["compatibility"][0]),
                "length": {"candidate_tokens": 2},
                "heartbeat": {"candidate": 0, "local_reference": settings["original_heartbeats"]}}
    monkeypatch.setattr(proof, "_check", check)
    result = proof.finalize(settings, capsule)
    assert result["source"] == "tiny" and result["compatibility_pct"] == 100 * 2 / 3
    assert result["score"] > settings["initial_best"]["score"]


def test_finalization_gives_each_candidate_and_version_its_full_check_allowance(selection, monkeypatch):
    settings, capsule, calls = selection
    (capsule / "Candidate.lean").write_text("current")
    (capsule / "valid-candidates" / "saved.lean").write_text("saved")
    check = proof._check
    timeouts = []
    def record(*args, timeout_seconds, **kwargs):
        timeouts.append(timeout_seconds)
        return check(*args, timeout_seconds=timeout_seconds, **kwargs)
    monkeypatch.setattr(proof, "_check", record)
    result = proof.finalize(settings, capsule)
    assert result["source"] == "saved"
    assert timeouts == [proof.CHECK_TIMEOUT] * 6




def test_first_capsule_keeps_original_task_and_original_incumbent(tmp_path, monkeypatch):
    settings = config(tmp_path)
    (tmp_path / "config.json").write_text(json.dumps(settings))
    (tmp_path / "proof-guide.md").write_text("Guide")
    monkeypatch.setattr(proof.swarm, "worker_commands_document", lambda *_args, **_kwargs: "Commands")
    capsule = proof.make_capsule(tmp_path, 1, settings["initial_best"]["source"] + "\r\n", 2.75)
    assert (capsule / "Task.json").read_bytes() == Path(settings["task"]).read_bytes()
    assert (capsule / "Candidate.lean").read_text() == settings["initial_best"]["source"]
    assert (capsule / "AGENTS.md").is_file() and (capsule / "feedback-config.json").is_file()
    instructions = (capsule / "AGENTS.md").read_text()
    briefing = (capsule / "prompt.md").read_text()
    assert "Task.st" in instructions and "Do not use children or subagents" in instructions
    assert "T0 = 238" in briefing and "H0 = 4251" in briefing
    assert "Host-verified starting incumbent" in briefing
    assert settings["initial_best"]["sha256"] in briefing
    with pytest.raises(FileExistsError):
        proof.make_capsule(tmp_path, 1, "duplicate", 2)


@pytest.mark.parametrize("first_pass_improves", [False, True])
def test_statement_first_capsule_hides_original_then_refactors_verified_selection(tmp_path, monkeypatch, first_pass_improves):
    from e6 import statement_first
    settings = config(tmp_path)
    settings.update(replace(DEFAULT_SPEC, first_pass_reprove=True, first_pass_reference_rebuild=False).proof_settings())
    (tmp_path / "config.json").write_text(json.dumps(settings))
    (tmp_path / "proof-guide.md").write_text("Guide")
    redacted_task = tmp_path / "safe-task.json"
    redacted_task.write_text(json.dumps({"schema_version": 1, "row": {
        "name": "Task.st", "signature": "theorem Task.st : True", "header": "import Mathlib\n",
        "contexts": [], "src": "theorem Task.st : True := by\n  skip\n"}}))
    monkeypatch.setattr(statement_first, "prepare_view", lambda _config: {
        "task": str(redacted_task), "registry": settings["fingerprint_registry"]})
    monkeypatch.setattr(proof.swarm, "worker_commands_document", lambda *_args, **_kwargs: "Commands")
    first = proof.make_capsule(tmp_path, 1, settings["initial_best"]["source"], 3)
    candidate = (first / "Candidate.lean").read_text()
    assert "theorem Task.st : True := by\n  skip" in candidate
    assert settings["initial_best"]["source"] not in candidate
    instructions = (first / "prompt.md").read_text()
    assert "independent reproof from the theorem statement" in instructions
    assert "The original proof is hidden" in instructions
    assert "resident warm feedback is unavailable" in instructions
    assert "Host-verified incumbent briefing" not in instructions
    assert settings["initial_best"]["sha256"] not in instructions
    assert (first / "Task.json").read_bytes() == redacted_task.read_bytes()
    assert json.loads((first / "pass-mode.json").read_text())["mode"] == "statement_first_reprove"
    selected = dict(settings["initial_best"])
    if first_pass_improves:
        selected.update(source="VERIFIED_REPROOF", sha256=proof._digest("VERIFIED_REPROOF"))
    (first / "selection.json").write_text(json.dumps(selected))
    second = proof.make_capsule(tmp_path, 2, selected["source"], 2)
    assert (second / "Candidate.lean").read_text() == selected["source"]
    assert (second / "Task.json").read_bytes() == Path(settings["task"]).read_bytes()
    assert "This pass starts from a verified incumbent" in (second / "prompt.md").read_text()
    assert "Starting Candidate.lean SHA-256" in (second / "prompt.md").read_text()
    assert "Host-verified starting incumbent" in (second / "prompt.md").read_text()
    assert json.loads((second / "pass-mode.json").read_text())["mode"] == "refactor"


def test_fresh_capsule_refuses_unverified_source_before_creation(tmp_path):
    settings = config(tmp_path)
    settings.update(replace(DEFAULT_SPEC, first_pass_reference_rebuild=False).proof_settings())
    (tmp_path / "config.json").write_text(json.dumps(settings))
    with pytest.raises(ValueError, match="current verified incumbent"):
        proof.make_capsule(tmp_path, 1, "another proof", 2.75)
    assert not (tmp_path / "pass-001").exists()


def test_next_capsule_copies_only_the_previous_verified_selection(tmp_path, monkeypatch):
    settings = config(tmp_path)
    (tmp_path / "config.json").write_text(json.dumps(settings))
    (tmp_path / "proof-guide.md").write_text("Guide")
    previous = tmp_path / "pass-001"
    previous.mkdir()
    source = "verified current proof"
    selection = {**settings["initial_best"], "source": source, "sha256": proof._digest(source)}
    (previous / "selection.json").write_text(json.dumps(selection))
    (previous / "secret-refactor.lean").write_text("unselected archive")
    monkeypatch.setattr(proof.swarm, "worker_commands_document", lambda *_args, **_kwargs: "Commands")
    capsule = proof.make_capsule(tmp_path, 2, source, 2.25)
    assert (capsule / "Candidate.lean").read_text() == source
    assert (capsule / "Task.json").read_bytes() == Path(settings["task"]).read_bytes()
    assert not (capsule / "secret-refactor.lean").exists()
    assert not (capsule / "selection.json").exists()


def test_next_capsule_briefing_reports_the_improved_verified_incumbent(tmp_path, monkeypatch):
    settings = config(tmp_path)
    settings.update(replace(DEFAULT_SPEC, incumbent_briefing=True).proof_settings())
    (tmp_path / "config.json").write_text(json.dumps(settings))
    (tmp_path / "proof-guide.md").write_text("Guide")
    previous = tmp_path / "pass-001"
    previous.mkdir()
    source = "improved verified proof\nsecond line\n"
    selected = {**settings["initial_best"], "source": source, "sha256": proof._digest(source),
                "tokens": 100, "heartbeats": 200, "compatibility_pct": 100 * 2 / 3,
                "score": proof._policy(settings).score(
                    tokens=100, heartbeats=200, compatibility_pct=100 * 2 / 3)}
    (previous / "selection.json").write_text(json.dumps(selected))
    monkeypatch.setattr(proof.swarm, "worker_commands_document", lambda *_args, **_kwargs: "Commands")
    capsule = proof.make_capsule(tmp_path, 2, source, 2.25)
    briefing = (capsule / "prompt.md").read_text()
    assert (capsule / "Candidate.lean").read_text() == source
    assert "| Proof tokens | 100 |" in briefing
    assert "| Exact primary heartbeats | 200 |" in briefing
    assert "| Compatibility | 66.6667% |" in briefing
    assert f"{selected['score']:.4f}/100" in briefing
    assert selected["sha256"] in briefing
    assert proof.arena.sha256_file(capsule / "Candidate.lean") == selected["sha256"]
    assert "T0 = 238" in briefing and "H0 = 4251" in briefing
    assert settings["initial_best"]["sha256"] not in briefing


def test_capsule_rejects_changed_candidate_bytes_during_construction(tmp_path, monkeypatch):
    settings = config(tmp_path)
    (tmp_path / "config.json").write_text(json.dumps(settings))
    (tmp_path / "proof-guide.md").write_text("Guide")
    prepare_capsule = proof.swarm.prepare_capsule
    def changed_capsule(capsule, *args, **kwargs):
        result = prepare_capsule(capsule, *args, **kwargs)
        candidate = capsule / "Candidate.lean"
        candidate.write_bytes(candidate.read_bytes() + b"\n")
        return result
    monkeypatch.setattr(proof.swarm, "prepare_capsule", changed_capsule)
    with pytest.raises(ValueError, match="does not match the verified incumbent"):
        proof.make_capsule(tmp_path, 1, settings["initial_best"]["source"], 3)


def test_next_capsule_refuses_modified_selection(tmp_path):
    settings = config(tmp_path)
    settings.update(replace(DEFAULT_SPEC, first_pass_reference_rebuild=False).proof_settings())
    (tmp_path / "config.json").write_text(json.dumps(settings))
    previous = tmp_path / "pass-001"
    previous.mkdir()
    selection = {**settings["initial_best"], "source": "changed"}
    (previous / "selection.json").write_text(json.dumps(selection))
    with pytest.raises(ValueError, match="current verified incumbent"):
        proof.make_capsule(tmp_path, 2, "changed", 2.25)
    assert not (tmp_path / "pass-002").exists()


def test_finalization_rejects_cross_proof_incumbent_before_checks(selection, tmp_path):
    settings, capsule, calls = selection
    foreign = config(tmp_path / "foreign", "ph")["initial_best"]
    with pytest.raises(ValueError, match="for this proof"):
        proof.finalize(settings, capsule, foreign)
    assert calls == []
    assert not (capsule / "final-validation").exists()


@pytest.mark.parametrize("field,value", [("label", "ph"), ("original_heartbeats", 42080),
                                         ("primary", "other-project"), ("original_tokens", 1240)])
def test_finalization_rejects_confused_or_modified_config(selection, field, value):
    settings, capsule, calls = selection
    settings[field] = value
    with pytest.raises(ValueError, match="Frozen proof metadata"):
        proof.finalize(settings, capsule)
    assert calls == []


def test_finalization_rejects_incumbent_score_using_different_denominators(selection):
    settings, capsule, calls = selection
    settings["initial_best"]["score"] += 1
    with pytest.raises(ValueError, match="score does not match"):
        proof.finalize(settings, capsule)
    assert calls == []


@pytest.fixture
def preparation(monkeypatch):
    guards, checks = [], []
    monkeypatch.setattr(proof.arena, "load_task", lambda path: ({}, json.loads(path.read_text())["row"]))
    monkeypatch.setattr(proof.arena, "render_candidate_scaffold", lambda row: f"canonical {row['name']}")
    monkeypatch.setattr(proof, "find_codex", lambda: Path("fake-native-codex"))
    def entry(row, project, registry, *, validate_guard):
        guards.append((row["name"], str(project), str(registry), validate_guard))
        return {"guard_valid": validate_guard}
    monkeypatch.setattr(proof.arena, "environment_fingerprint_registry_entry", entry)
    monkeypatch.setattr(proof.arena, "environment_fingerprint_registry_key", lambda row, project: str(project))
    def check(settings, candidate, project, *, quick=False, **_kwargs):
        checks.append((settings["label"], candidate.read_text(), str(project), quick))
        return {"valid": True, "length": {"candidate_tokens": settings["original_tokens"]},
                "heartbeat": {"candidate": settings["original_heartbeats"],
                              "local_reference": settings["original_heartbeats"]}}
    monkeypatch.setattr(proof, "_check", check)
    return guards, checks


@pytest.mark.parametrize("label", ["ph", "ar"])
def test_prepare_loads_canonical_metadata_and_checks_every_guard_and_original(tmp_path, manifest, preparation, label):
    guards, checks = preparation
    settings = proof.prepare(tmp_path / "experiment", label, spec=DEFAULT_SPEC)
    metadata = manifest[label]
    for key, value in metadata.items():
        assert settings["canonical_task" if key == "task" else key] == value
    expected_projects = [metadata["primary"], *metadata["compatibility"]]
    assert guards == [(metadata["task_id"], path, metadata["registry_source"], True) for path in expected_projects]
    assert checks == [(label, f"canonical Task.{label}", path, index != 0)
                      for index, path in enumerate(expected_projects)]
    assert Path(settings["task"]).read_bytes() == Path(metadata["task"]).read_bytes()
    assert settings["initial_best"]["tokens"] == metadata["original_tokens"]
    assert settings["initial_best"]["heartbeats"] == metadata["original_heartbeats"]
    guide = (tmp_path / "experiment/proof-guide.md").read_text()
    assert "max(0" not in guide
    assert "Reductions are not clamped" in guide
    assert settings["initial_best"]["score"] == 33.3333
    proof._verify_config(settings)
    proof._verify_incumbent(settings, settings["initial_best"])


def test_reference_rebuild_preparation_still_verifies_and_retains_the_complete_original(
        tmp_path, manifest, preparation):
    guards, checks = preparation
    spec = replace(DEFAULT_SPEC, first_pass_reference_rebuild=True)
    root = tmp_path / "reference-rebuild"
    settings = proof.prepare(root, "ar", spec=spec)
    metadata = manifest["ar"]
    projects = [metadata["primary"], *metadata["compatibility"]]
    original = "canonical Task.ar"
    assert checks == [("ar", original, project, index != 0) for index, project in enumerate(projects)]
    assert len(guards) == len(projects) and all(item[-1] for item in guards)
    assert settings["initial_best"]["source"] == (root / "Original.lean").read_text() == original
    assert settings["initial_best"]["sha256"] == proof._digest(original)
    assert settings["initial_best"]["compatibility_complete"] is True
    assert not (root / "statement-first").exists()
    proof._verify_config(settings)
    proof._verify_incumbent(settings, settings["initial_best"])


def test_prepare_records_one_heartbeat_drift_without_changing_denominator(tmp_path, preparation, monkeypatch):
    def check(settings, _candidate, _project, **_kwargs):
        return {"valid": True, "length": {"candidate_tokens": settings["original_tokens"]},
                "heartbeat": {"candidate": settings["original_heartbeats"] + 1,
                              "local_reference": settings["original_heartbeats"]}}
    monkeypatch.setattr(proof, "_check", check)
    root = tmp_path / "experiment"
    with pytest.raises(ValueError, match="explicit calibration required"):
        proof.prepare(root, "ph", spec=DEFAULT_SPEC)
    result = json.loads((root / "baseline-preflight.json").read_text())
    assert result["status"] == "failed"
    assert result["expected_original_heartbeats"] == 42080
    assert result["primary"]["heartbeat"]["candidate"] == 42081
    assert not (root / "config.json").exists()


def test_preparation_uses_efficient_guide_and_pins_the_single_bundle(tmp_path, preparation):
    from e6 import prompt_bundle
    from e6.experiment import EFFICIENT_CONTROL_PROMPT
    root = tmp_path / "efficient"
    settings = proof.prepare(root, "ph", spec=DEFAULT_SPEC)
    guide = (root / "proof-guide.md").read_text()
    assert guide.startswith("# Proof and scoring reference\n")
    assert "`T0 = 1240` and `H0 = 42080`" in guide
    assert "compatibility       = 100 * P / 1" in guide
    assert "{{" not in guide
    assert settings["prompt_bundle"] == prompt_bundle.snapshot(EFFICIENT_CONTROL_PROMPT)
    assert json.loads((root / "config.json").read_text())["prompt_bundle"] == settings["prompt_bundle"]



def test_recorded_control_measurement_preserves_scoring_denominator(tmp_path, preparation, monkeypatch):
    document = json.loads(proof.PROOFS.read_text())
    metadata = document["proofs"]["ph"]
    evidence = tmp_path / "verified-original-exact.json"
    evidence.write_text('{"control": 41896}')
    metadata.update(original_measurement_heartbeats=41896, original_measurement_evidence={
        "path": str(evidence), "sha256": proof.arena.sha256_file(evidence),
        "historical_heartbeats": 42080, "measured_heartbeats": 41896,
        "scoring_denominator_changed": False})
    proof.PROOFS.write_text(json.dumps(document))
    def check(settings, _candidate, _project, **_kwargs):
        return {"valid": True, "length": {"candidate_tokens": settings["original_tokens"]},
                "heartbeat": {"candidate": 41896, "local_reference": 41896}}
    monkeypatch.setattr(proof, "_check", check)
    settings = proof.prepare(tmp_path / "experiment", "ph", spec=DEFAULT_SPEC)
    assert settings["original_heartbeats"] == 42080
    assert settings["initial_best"]["heartbeats"] == 41896
    assert settings["initial_best"]["score"] == proof._policy(settings).score(
        tokens=1240, heartbeats=41896, compatibility_pct=100)
    proof._verify_config(settings)
    proof._verify_incumbent(settings, settings["initial_best"])
    report = json.loads((tmp_path / "experiment/baseline-preflight.json").read_text())
    assert report["control_heartbeat_drift"] == -184
    evidence.write_text("changed evidence")
    with pytest.raises(ValueError, match="frozen exact-cache evidence"):
        proof._metadata("ph")






@pytest.mark.parametrize("batch,goals", [(True, False), (True, True)])
def test_feature_capsule_uses_current_verified_incumbent_metrics(tmp_path, monkeypatch, batch, goals):
    from lean_tools import goal_retrieval
    monkeypatch.setattr(proof.arena, "load_task", lambda path: ({}, json.loads(path.read_text())["row"]))
    settings = config(tmp_path)
    settings.update(replace(DEFAULT_SPEC, candidate_batches=batch, goal_retrieval=goals,
                            reasoning_effort="high").proof_settings())
    validations = []
    if goals:
        artifact = {"path": str(tmp_path / "host-index.sqlite3"), "sha256": "a" * 64}
        settings["retrieval_index"] = artifact
        monkeypatch.setattr(goal_retrieval, "validate_prepared_index",
                            lambda *args, **kwargs: validations.append((args, kwargs)))
    (tmp_path / "config.json").write_text(json.dumps(settings))
    (tmp_path / "proof-guide.md").write_text("Guide")
    prior = tmp_path / "pass-001"
    prior.mkdir()
    incumbent = {**settings["initial_best"], "source": "current verified best", "tokens": 100,
                 "heartbeats": 500, "compatibility_pct": 100}
    incumbent["sha256"] = proof._digest(incumbent["source"])
    incumbent["score"] = proof._policy(settings).score(tokens=100, heartbeats=500, compatibility_pct=100)
    (prior / "selection.json").write_text(json.dumps(incumbent))
    capsule = proof.make_capsule(tmp_path, 2, incumbent["source"], 2.5)
    feedback_settings = json.loads((capsule / "feedback-config.json").read_text())
    assert feedback_settings.get("candidate_batches", False) is batch
    assert feedback_settings.get("goal_retrieval", False) is goals
    if goals:
        assert validations == [((artifact, json.loads(Path(settings["task"]).read_text())["row"], Path(settings["primary"])),
                                {"fingerprint_registry": Path(settings["fingerprint_registry"])})]
        assert feedback_settings["retrieval_index"] == artifact["path"]
        assert feedback_settings["retrieval_index_sha256"] == artifact["sha256"]
    assert (capsule / "Candidate.lean").read_text() == incumbent["source"]
    assert feedback_settings["original_tokens"] == settings["original_tokens"]
    assert feedback_settings["original_heartbeats"] == settings["original_heartbeats"]
    assert feedback_settings["incumbent_score"] == incumbent["score"]
    assert feedback_settings["incumbent_score"] != settings["initial_best"]["score"]
    assert feedback_settings["compatibility_roots"] == settings["compatibility"]
    assert "score_candidate" in feedback_settings["enabled_tools"]
    assert ("compare_candidates" in feedback_settings["enabled_tools"]) is batch
    assert feedback_settings["response_policy"] == "compact-v1"
    assert "score_candidate" in (capsule / "AGENTS.md").read_text()


@pytest.mark.parametrize("fails", [False, True])
def test_host_prepares_prefix_index_before_ready_and_records_failures(tmp_path, preparation, monkeypatch, fails):
    from lean_tools import goal_retrieval
    root = tmp_path / "experiment"
    monkeypatch.setattr(proof, "runtime_root", lambda: tmp_path / "runtime")
    artifact = {"path": str(tmp_path / "index.sqlite3"), "sha256": "a" * 64, "build": {"cache_hit": True}}
    calls = []
    def prepare_index(*args, **kwargs):
        calls.append((args, kwargs))
        assert json.loads((root / "state.json").read_text())["phase"] == "retrieval-index"
        assert not (root / "config.json").exists()
        if fails:
            raise RuntimeError("synthetic index failure")
        return artifact
    monkeypatch.setattr(goal_retrieval, "prepare_index", prepare_index)
    if fails:
        with pytest.raises(RuntimeError, match="synthetic index failure"):
            proof.prepare(root, "ph", spec=replace(DEFAULT_SPEC, goal_retrieval=True))
        assert not (root / "config.json").exists()
        assert json.loads((root / "state.json").read_text())["status"] == "preparation_failed"
    else:
        settings = proof.prepare(root, "ph", spec=replace(DEFAULT_SPEC, goal_retrieval=True))
        assert settings["retrieval_index"] == artifact
        assert json.loads((root / "config.json").read_text())["retrieval_index"] == artifact
    metadata = proof._metadata("ph")
    assert calls == [((json.loads(Path(metadata["task"]).read_text())["row"], Path(metadata["primary"]),
                        tmp_path / "runtime/retrieval-index-cache"),
                      {"fingerprint_registry": root / "environment-fingerprints.json"})]
    record = json.loads((root / "preparation/retrieval-index.json").read_text())
    assert record["status"] == ("failed" if fails else "passed")
    assert record["finished_at"]
    if fails:
        assert record["error"]["message"] == "synthetic index failure"
    else:
        assert record["artifact"] == artifact


@pytest.mark.parametrize("artifact", [None, {"path": "changed-index", "sha256": "a" * 64}])
def test_capsule_rejects_missing_or_invalid_host_index_before_creation(tmp_path, monkeypatch, artifact):
    from lean_tools import goal_retrieval
    monkeypatch.setattr(proof.arena, "load_task", lambda path: ({}, json.loads(path.read_text())["row"]))
    settings = config(tmp_path)
    settings.update(replace(DEFAULT_SPEC, goal_retrieval=True).proof_settings())
    if artifact:
        settings["retrieval_index"] = artifact
    def invalid(*_args, **_kwargs):
        raise ValueError("changed host-prepared index")
    monkeypatch.setattr(goal_retrieval, "validate_prepared_index", invalid)
    (tmp_path / "config.json").write_text(json.dumps(settings))
    with pytest.raises(ValueError, match="host-prepared index"):
        proof.make_capsule(tmp_path, 1, settings["initial_best"]["source"], 3)
    assert not (tmp_path / "pass-001").exists()


def test_prepare_refuses_failed_original_compatibility(tmp_path, preparation, monkeypatch):
    original_check = proof._check
    def check(*args, quick=False, **kwargs):
        result = original_check(*args, quick=quick, **kwargs)
        result["valid"] = not quick
        return result
    monkeypatch.setattr(proof, "_check", check)
    root = tmp_path / "experiment"
    with pytest.raises(ValueError, match="Original failed a cached compatibility"):
        proof.prepare(root, "pu", spec=DEFAULT_SPEC)
    result = json.loads((root / "baseline-preflight.json").read_text())
    assert result["status"] == "failed" and len(result["compatibility"]) == 3
    assert not (root / "config.json").exists()


def test_prepare_timeout_retains_finished_phases_and_failing_lean_run(tmp_path, preparation, monkeypatch):
    root = tmp_path / "experiment"
    original_check = proof._check
    count = 0
    def check(*args, **kwargs):
        nonlocal count
        count += 1
        if count == 3:
            run = proof.arena.LeanRun(["lake", "env", "lean"], 1, 1800.0, "timeout diagnostics", True,
                                      log_path="saved-lean.log", queue_wait_seconds=0.2)
            raise proof.arena.LeanTimeoutError("compatibility timeout", run)
        return original_check(*args, **kwargs)
    monkeypatch.setattr(proof, "_check", check)
    monkeypatch.setenv("LEAN_REFACTOR_EVALUATION_CACHE", str(tmp_path / "ambient-private"))
    with pytest.raises(proof.arena.LeanTimeoutError, match="compatibility timeout"):
        proof.prepare(root, "ar", spec=DEFAULT_SPEC)
    result = json.loads((root / "baseline-preflight.json").read_text())
    assert result["status"] == "failed" and result["primary"]["valid"]
    failed = result["phases"][-1]
    assert failed["status"] == "failed"
    assert failed["error"]["lean_run"]["timed_out"] is True
    assert failed["error"]["lean_run"]["log_path"] == "saved-lean.log"
    assert json.loads((root / "state.json").read_text())["status"] == "preparation_failed"
    assert proof.arena.evaluation_cache_root() == tmp_path / "ambient-private"
    assert not (root / "config.json").exists()


def test_prepare_metadata_exception_also_has_diagnostic_state(tmp_path, preparation, monkeypatch):
    root = tmp_path / "experiment"
    monkeypatch.setattr(proof, "_metadata", lambda *_args: (_ for _ in ()).throw(ValueError("broken manifest")))
    with pytest.raises(ValueError, match="broken manifest"):
        proof.prepare(root, "ar")
    result = json.loads((root / "baseline-preflight.json").read_text())
    assert result["status"] == "failed" and "broken manifest" in json.dumps(result)
    assert not (root / "config.json").exists()


@pytest.mark.parametrize("reference_matches_control", [True, False])
def test_finalization_uses_native_control_but_historical_score_denominator(tmp_path, monkeypatch, reference_matches_control):
    document = json.loads(proof.PROOFS.read_text())
    metadata = document["proofs"]["ph"]
    measured, historical = 41896, metadata["original_heartbeats"]
    evidence = tmp_path / "linux-original-control.json"
    evidence.write_text(json.dumps({"heartbeat": measured}))
    metadata.update(original_measurement_heartbeats=measured, original_measurement_evidence={
        "path": str(evidence), "sha256": proof.arena.sha256_file(evidence),
        "historical_heartbeats": historical, "measured_heartbeats": measured,
        "scoring_denominator_changed": False})
    proof.PROOFS.write_text(json.dumps(document))
    settings = config(tmp_path / "run", label="ph")
    settings["initial_best"].update(tokens=1000, score=proof._policy(settings).score(
        tokens=1000, heartbeats=800, compatibility_pct=100))
    capsule = Path(settings["root"]) / "pass-001"
    (capsule / "valid-candidates").mkdir(parents=True)
    (capsule / "Candidate.lean").write_text("native-finalist")
    monkeypatch.setattr(proof.arena, "load_task", lambda _path: ({}, {"name": settings["task_id"]}))
    monkeypatch.setattr(proof.arena, "extract_candidate_declaration", lambda _row, source: (source, source))
    def check(_config, _candidate, _project, **_kwargs):
        return {"valid": True, "length": {"candidate_tokens": 100},
                "heartbeat": {"candidate": 8000, "local_reference": measured if reference_matches_control else historical}}
    monkeypatch.setattr(proof, "_check", check)
    result = proof.finalize(settings, capsule)
    if reference_matches_control:
        assert result["source"] == "native-finalist"
        historical_score = proof.OriginalDenominatorScorePolicy(settings["original_tokens"], historical).score(
            tokens=100, heartbeats=8000, compatibility_pct=100)
        native_denominator_score = proof.OriginalDenominatorScorePolicy(settings["original_tokens"], measured).score(
            tokens=100, heartbeats=8000, compatibility_pct=100)
        assert result["score"] == historical_score and result["score"] != native_denominator_score
    else:
        assert result["source"] == "previous"
        record = json.loads((capsule / "selection.json").read_text())["candidate_records"][0]
        assert record["status"] == "validation_failed" and "native-control evidence" in record["error"]


def test_forged_agent_exact_cache_cannot_promote_a_finalist(selection, monkeypatch):
    settings, capsule, _calls = selection
    candidate = capsule / "Candidate.lean"
    candidate.write_text("forged-cache-candidate")
    model_cache = capsule / "evaluation-cache"
    key = "f" * 64
    forged_path = proof.arena.evaluation_cache_path(model_cache, "exact", key)
    forged = proof.arena.Evaluation(
        task_id=settings["task_id"], candidate_path=str(candidate), valid=True,
        compile_seconds=0.01, axiom_audit_seconds=0.01, axioms=["propext"],
        original_local_tokens=settings["original_tokens"], candidate_local_tokens=1,
        local_token_reduction_pct=99.0, official_original_tokens=settings["original_tokens"],
        environment_fingerprint="e" * 64, local_reference_heartbeat=settings["original_heartbeats"],
        heartbeat=1, heartbeat_reduction_pct=99.0, axiom_audit_shares_compile=False)
    proof.arena.store_cached_evaluation(forged_path, key, "exact", "e" * 64, "d" * 64, forged)
    assert proof.arena.cached_evaluation(forged_path, candidate).valid
    monkeypatch.setenv("LEAN_REFACTOR_EVALUATION_CACHE", str(model_cache))
    fresh_attempts = []
    def check(_config, candidate, _project, **_kwargs):
        cache = proof.arena.evaluation_cache_root()
        cached = proof.arena.cached_evaluation(proof.arena.evaluation_cache_path(cache, "exact", key), candidate)
        if cached is not None:
            return proof.arena.evaluation_payload(cached)
        fresh_attempts.append(cache)
        return {"valid": False}
    monkeypatch.setattr(proof, "_check", check)
    result = proof.finalize(settings, capsule)
    assert result["source"] == "previous"
    assert fresh_attempts == [Path(settings["root"]) / "preparation/host-final-validation-cache"]
    assert proof.arena.cached_evaluation(forged_path, candidate).valid
    assert proof.arena.evaluation_cache_root() == model_cache


@pytest.mark.parametrize("failure", [None, "candidate_fingerprint", "control_fingerprint",
                                      "control_heartbeat", "changed_original", "missing_control", "missing_audit",
                                      "conflicting_reference"])
def test_missing_platform_baseline_requires_frozen_native_original_evidence(selection, monkeypatch, failure):
    settings, capsule, _calls = selection
    original = settings["initial_best"]
    control = settings["original_heartbeats"]
    original.update(tokens=settings["original_tokens"], heartbeats=control,
                    score=proof._policy(settings).score(
                        tokens=settings["original_tokens"], heartbeats=control, compatibility_pct=100))
    fingerprint, guard = "a" * 64, "b" * 64
    original["evaluation"] = {
        "task_id": settings["task_id"], "valid": True, "measurement_mode": "exact",
        "axiom_status": "measured", "axioms": ["propext"],
        "length": {"candidate_tokens": settings["original_tokens"]},
        "heartbeat": {"candidate": control, "local_reference": control,
                      "environment_fingerprint": fingerprint}}
    monkeypatch.setattr(proof.arena, "render_candidate_scaffold", lambda _row: "previous")
    monkeypatch.setattr(proof.arena, "environment_fingerprint_registry_entry",
                        lambda *_args, **_kwargs: {"fingerprint": fingerprint, "guard_sha256": guard})
    primary = {"task_id": settings["task_id"], "valid": True, "measurement_mode": "exact",
               "axiom_status": "measured", "axioms": ["propext"],
               "length": {"candidate_tokens": 100},
               "heartbeat": {"candidate": 200, "local_reference": None,
                             "environment_fingerprint": fingerprint}}
    if failure == "candidate_fingerprint":
        primary["heartbeat"]["environment_fingerprint"] = "c" * 64
    elif failure == "control_fingerprint":
        original["evaluation"]["heartbeat"]["environment_fingerprint"] = "c" * 64
    elif failure == "control_heartbeat":
        original["evaluation"]["heartbeat"]["candidate"] = control - 1
    elif failure == "changed_original":
        original.update(source="another original", sha256=proof._digest("another original"))
    elif failure == "missing_control":
        original.pop("evaluation")
    elif failure == "missing_audit":
        primary.update(axioms=None, axiom_status="not_run")
    elif failure == "conflicting_reference":
        primary["heartbeat"]["local_reference"] = control - 1
    monkeypatch.setattr(proof, "_check", lambda *_args, **_kwargs: primary)
    (capsule / "Candidate.lean").write_text("saved")
    task_before = Path(settings["task"]).read_bytes()
    result = proof.finalize(settings, capsule)
    record = json.loads((capsule / "selection.json").read_text())["candidate_records"][0]
    assert Path(settings["task"]).read_bytes() == task_before
    assert record["evaluation"]["heartbeat"]["local_reference"] == primary["heartbeat"]["local_reference"]
    if failure is None:
        assert result["source"] == "saved"
        assert result["score"] == proof._policy(settings).score(tokens=100, heartbeats=200, compatibility_pct=100)
        assert record["native_control_evidence"] == {
            "source": "verified_preparation_original", "task_sha256": settings["task_sha256"],
            "original_sha256": original["sha256"], "heartbeats": control,
            "environment_fingerprint": fingerprint, "environment_guard_sha256": guard}
    else:
        assert result["source"] == original["source"]
        assert record["status"] == "validation_failed"
