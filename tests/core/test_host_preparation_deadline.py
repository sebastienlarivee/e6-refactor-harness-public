"""Run real baseline-preflight routing with fake Lean and multiple environments."""
from dataclasses import replace
import json
from pathlib import Path

import pytest

from e6 import proof
from e6.experiment import DEFAULT_SPEC
from lean_tools import check_budget


@pytest.mark.parametrize("scoring_policy", ["legacy-v1", "arena-v1"])
def test_baseline_preflight_honors_1800_second_host_allowance_in_all_environments(tmp_path, monkeypatch, scoring_policy):
    # Keep prepare, _check, evaluate_candidate and fresh evaluation real: the
    # former regression happened before any Lean launch in compatibility-001.
    row = {"name": "Demo.original", "header": "import Mathlib\n\n", "contexts": [],
           "signature": "theorem Demo.original : True", "src": "theorem Demo.original : True := by trivial",
           "proof_length": 2}
    canonical = tmp_path / "canonical.json"
    canonical.write_text(json.dumps({"schema_version": 1, "row": row, "reference": {"heartbeat": 100}}))
    projects = [tmp_path / label for label in ("primary", "compatibility-1", "compatibility-2")]
    for project in projects:
        project.mkdir()
    metadata = {"task_id": row["name"], "task": str(canonical), "task_sha256": proof.arena.sha256_file(canonical),
                "primary": str(projects[0]), "compatibility": [str(path) for path in projects[1:]],
                "registry_source": str(tmp_path / "source-registry.json"), "original_tokens": 2,
                "original_heartbeats": 100}
    if scoring_policy == "arena-v1":
        metadata.update(scoring_policy=scoring_policy, original_measurement_tokens=3)
    monkeypatch.delenv("E6_BASELINE_CACHE", raising=False)
    monkeypatch.delenv("E6_BASELINE_SEEDS", raising=False)
    monkeypatch.setenv("ELAN_HOME", str(tmp_path / "cached-elan"))
    monkeypatch.setenv("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE", "compile")
    monkeypatch.setattr(proof, "configure_native_environment", lambda **_kwargs: None)
    monkeypatch.setattr(proof, "find_codex", lambda: Path("fake-native-codex"))
    monkeypatch.setattr(proof.arena, "environment_fingerprint_registry_entry",
                        lambda _row, project, *_a, **_k: {
                            "fingerprint": proof.arena.sha256_bytes(str(project).encode()), "guard_sha256": "b" * 64})
    monkeypatch.setattr(proof.arena, "environment_fingerprint_registry_key", lambda _row, project: str(project))
    monkeypatch.setattr(proof.arena, "measurement_environment_fingerprint",
                        lambda _row, project, **_kwargs: proof.arena.sha256_bytes(str(project).encode()))
    monkeypatch.setattr(proof.arena, "persistent_quick_matches_project", lambda _: False)
    calls = []

    def fake_lean(path, project, timeout_seconds, **_kwargs):
        budget = check_budget.current()
        source = path.read_text()
        calls.append({"project": project, "timeout": timeout_seconds,
                      "quick_budget": None if budget is None else budget.seconds})
        assert row["src"] in source
        assert path.name != "Original.lean"  # real evaluator uses admitted snapshots
        if "#count_heartbeats" in source:
            assert budget is None  # exact-primary keeps its process contract
            output = "Used 100 heartbeats, which is less than the current maximum of 1000000000.\n'Demo.original' depends on axioms: [propext, Classical.choice, Quot.sound]"
        else:
            assert budget is not None and 1790 < check_budget.remaining() <= 1800
            output = ""
        return proof.arena.LeanRun(["fake-lean"], 0, 0.01, output)

    monkeypatch.setattr(proof.arena, "run_lean", fake_lean)
    root = tmp_path / "host-preparation"
    settings = proof.prepare(root, "demo", spec=replace(DEFAULT_SPEC, preparation_check_timeout_seconds=1800,
                                                      scoring_policy=scoring_policy), metadata=metadata)
    report = json.loads((root / "baseline-preflight.json").read_text())
    assert report["status"] == "passed" and all(row["passed"] for row in report["compatibility"])
    assert [phase["phase"] for phase in report["phases"]] == ["primary-exact", "compatibility-001-quick", "compatibility-002-quick"]
    assert all(phase["timeout_seconds"] == 1800 and phase["status"] == "passed" for phase in report["phases"])
    assert calls == [{"project": projects[0], "timeout": 1800, "quick_budget": None},
                     {"project": projects[1], "timeout": 1800, "quick_budget": 1800},
                     {"project": projects[2], "timeout": 1800, "quick_budget": 1800}]
    assert settings["initial_best"]["valid"] and settings["initial_best"]["compatibility_pct"] == 100
    assert check_budget.current() is None


@pytest.mark.parametrize("value", [0, -1, True, float("inf"), float("nan")])
def test_trusted_host_budget_still_requires_finite_positive_seconds(value):
    with pytest.raises(ValueError):
        with check_budget.scope(value):
            pytest.fail("invalid host budget admitted")
