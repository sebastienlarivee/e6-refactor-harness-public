"""No inference or Lean subprocesses: original measurements use scripted compiler edges."""
from copy import deepcopy
from dataclasses import replace
import json
from pathlib import Path

import pytest

from e6 import proof
from e6.experiment import DEFAULT_RUN_SPEC
from harness import baselines, doctor, runner
from harness.benchmark import load_benchmark, file_hash
from harness.config import RunConfig
from lean_tools import arena_workflow as arena
from tests.test_product_config import profile
from tests.test_product_original_tokens import synthetic_benchmark, resolve_without_lean, fake_doctor_worker


def prepare_fixture(tmp_path, monkeypatch, *, supplied_tokens=True, supplied_heartbeat=True, compatibility=False):
    benchmark = synthetic_benchmark(tmp_path, published=90, measured=3)
    if not supplied_tokens:
        row = json.loads(benchmark.input_path.read_text())
        row.pop("proof_length")
        benchmark.input_path.write_text(json.dumps(row) + "\n")
    if supplied_heartbeat:
        benchmark.heartbeat_path.write_text(json.dumps({"name": "Synthetic.original", "heartbeat": 900}) + "\n")
    benchmark = load_benchmark(benchmark.input_path, benchmark.heartbeat_path if supplied_heartbeat else None)
    metadata, = resolve_without_lean(tmp_path, monkeypatch, benchmark)
    if compatibility:
        project = str(tmp_path / "compatibility")
        metadata["compatibility"] = [project]
        metadata["environments"].append({**metadata["environments"][0], "path": project})
        registry_path = Path(metadata["registry_source"])
        registry = json.loads(registry_path.read_text())
        _, row = arena.load_task(Path(metadata["task"]))
        entry = next(iter(registry["entries"].values()))
        registry["entries"][arena.environment_fingerprint_registry_key(row, Path(project))] = {
            **entry, "project_root": project}
        registry_path.write_text(json.dumps(registry))
        metadata["registry_source_sha256"] = file_hash(registry_path)
    calls = fake_doctor_worker(monkeypatch, tmp_path)
    evidence = doctor.evaluate_original(metadata, tmp_path / "doctor", environment={"OFFLINE": "1"})
    return metadata, evidence, calls


@pytest.mark.parametrize("supplied_tokens", [False, True])
@pytest.mark.parametrize("supplied_heartbeat", [False, True])
def test_baselines_preserve_supplied_values_and_measure_missing_values(tmp_path, monkeypatch, supplied_tokens, supplied_heartbeat):
    metadata, evidence, calls = prepare_fixture(tmp_path, monkeypatch,
        supplied_tokens=supplied_tokens, supplied_heartbeat=supplied_heartbeat, compatibility=True)
    before_row = json.loads(Path(metadata["task"]).read_text())["row"]
    resolved = baselines.freeze_original_baseline(metadata, evidence, tmp_path / "baselines")
    receipt = baselines.load_original_baseline(resolved)
    assert len(calls) == 2
    assert resolved["original_tokens"] == (90 if supplied_tokens else 3)
    assert resolved["original_heartbeats"] == (900 if supplied_heartbeat else 100)
    assert resolved["baseline_provenance"] == {
        "tokens": {"source": "supplied_proof_length" if supplied_tokens else "measured_original_tokens",
                   "value": 90 if supplied_tokens else 3},
        "heartbeats": {"source": "supplied_heartbeat" if supplied_heartbeat else "measured_original_heartbeat",
                       "value": 900 if supplied_heartbeat else 100}}
    assert json.loads(Path(resolved["task"]).read_text())["row"] == before_row
    assert receipt["evaluations"][0]["heartbeat"]["candidate"] == 100
    assert receipt["evaluations"][0]["heartbeat"]["local_reference"] == resolved["original_heartbeats"]
    assert receipt["evaluations"][0]["heartbeat"]["published_reference"] == (900 if supplied_heartbeat else None)
    assert evidence["environments"][0]["evaluation"]["heartbeat"]["local_reference"] == (900 if supplied_heartbeat else None)
    assert json.loads(Path(evidence["task_path"]).read_text())["reference"]["heartbeat"] == (900 if supplied_heartbeat else None)


@pytest.mark.parametrize("change,match", [
    (lambda value: value["environments"][0]["evaluation"]["heartbeat"].update(candidate=0), "positive"),
    (lambda value: value["environments"][0]["evaluation"].update(axioms=["sorryAx"]), "axiom"),
    (lambda value: value["environments"][0]["evaluation"].update(axiom_status="not_run"), "axiom"),
    (lambda value: value["environments"].clear(), "complete compatibility"),
])
def test_invalid_or_incomplete_original_baselines_fail_before_freezing(tmp_path, monkeypatch, change, match):
    metadata, evidence, _ = prepare_fixture(tmp_path, monkeypatch, supplied_heartbeat=False)
    change(evidence)
    for item in evidence["environments"]:
        Path(item["evidence_path"]).write_text(json.dumps(item["evaluation"]))
        item["evidence_sha256"] = file_hash(Path(item["evidence_path"]))
    with pytest.raises(ValueError, match=match):
        baselines.freeze_original_baseline(metadata, evidence, tmp_path / "baselines")
    assert not (tmp_path / "baselines").exists()


@pytest.mark.parametrize("target", ["receipt", "raw_measurement", "measured_task", "source", "metadata"])
def test_frozen_baseline_reuse_rejects_changed_evidence_or_identity(tmp_path, monkeypatch, target):
    metadata, evidence, _ = prepare_fixture(tmp_path, monkeypatch)
    resolved = baselines.freeze_original_baseline(metadata, evidence, tmp_path / "baselines")
    if target == "receipt":
        path = Path(resolved["baseline_receipt"]["path"])
        path.write_text(path.read_text() + " ")
    elif target == "raw_measurement":
        Path(evidence["environments"][0]["evidence_path"]).write_text("{}")
    elif target == "measured_task":
        Path(evidence["task_path"]).write_text("{}")
    elif target == "source":
        monkeypatch.setattr(baselines, "runtime_source_hashes", lambda: {"instrumentation": "changed"})
    else:
        resolved["original_heartbeats"] += 1
    with pytest.raises(ValueError):
        baselines.load_original_baseline(resolved)


def test_worker_preparation_reuses_exact_and_compatibility_receipt_without_compiler(tmp_path, monkeypatch):
    metadata, evidence, calls = prepare_fixture(tmp_path, monkeypatch,
        supplied_tokens=False, supplied_heartbeat=False, compatibility=True)
    resolved = baselines.freeze_original_baseline(metadata, evidence, tmp_path / "baselines")
    monkeypatch.setenv("ELAN_HOME", resolved["elan_home"])
    monkeypatch.setenv("E6_BASELINE_CACHE", str(tmp_path / "unrelated-cross-run-cache"))
    monkeypatch.setattr(proof, "configure_native_environment", lambda **_: None)
    monkeypatch.setattr(proof, "find_codex", lambda: Path("fake-native-codex"))
    monkeypatch.setattr(proof.arena, "environment_fingerprint_registry_entry", lambda *_a, **_k:
        {"fingerprint": resolved["environments"][0]["fingerprint"], "guard_sha256": "f" * 64})
    monkeypatch.setattr(proof, "_check", lambda *_a, **_k: pytest.fail("validated original must not compile twice"))
    spec = replace(DEFAULT_RUN_SPEC, deterministic_refactoring=False, goal_retrieval=False)
    config = proof.prepare(tmp_path / "cell", resolved["label"], metadata=resolved, spec=spec)
    assert len(calls) == 2
    assert config["initial_best"]["tokens"] == 3
    assert config["initial_best"]["heartbeats"] == 100
    assert config["initial_best"]["score"] == 33.3333
    assert config["initial_best"]["compatibility_complete"]
    assert config["observed_original_baseline"]["heartbeats"] == 100
    report = json.loads((tmp_path / "cell/baseline-preflight.json").read_text())
    assert report["baseline_receipt"]["status"] == "validated_reuse"
    assert all(item["baseline_receipt"]["status"] == "validated_reuse" for item in report["phases"])
    assert not (tmp_path / "unrelated-cross-run-cache").exists()


def test_prepare_run_freezes_receipts_and_resume_load_never_remeasures(tmp_path, monkeypatch):
    metadata, evidence, calls = prepare_fixture(tmp_path, monkeypatch, supplied_heartbeat=False)
    input_path = tmp_path / "input.jsonl"
    mapping = tmp_path / "env.toml"
    public = RunConfig.from_dict({"input": str(input_path), "env_map": str(mapping), "openrouter": profile()})
    monkeypatch.setattr("harness.environments.load_environment_map", lambda _: object())
    monkeypatch.setattr("harness.environments.resolve_benchmark", lambda *_a, **_k: [deepcopy(metadata)])
    monkeypatch.setattr("harness.environments.verify_resolved_metadata", lambda _: None)
    monkeypatch.setattr(doctor, "evaluate_original", lambda *_a, **_k: deepcopy(evidence))
    snapshot = runner.prepare_run(public, tmp_path / "run", doctor=False)
    frozen = snapshot["proofs"][0]
    assert frozen["original_heartbeats"] == 100 and frozen["baseline_receipt"]
    assert set(snapshot["input_hashes"]) == {"input", "env_map"}
    monkeypatch.setattr(doctor, "evaluate_original", lambda *_a, **_k: pytest.fail("resume must not measure"))
    loaded = runner.load_snapshot(tmp_path / "run")
    assert loaded == snapshot and len(calls) == 1
    assert runner.status(tmp_path / "run")["status"] == "prepared"


def test_measurement_source_scope_excludes_transport_repairs(monkeypatch):
    monkeypatch.setattr(baselines, "runtime_source_hashes", lambda: {
        "harness/openrouter/relay.py": "changed transport",
        "e6/run.py": "changed runner",
        "lean_tools/arena_workflow.py": "pinned evaluator",
        "harness/doctor.py": "pinned preflight"})
    assert baselines.measurement_source_hashes() == {
        "lean_tools/arena_workflow.py": "pinned evaluator", "harness/doctor.py": "pinned preflight"}


@pytest.mark.parametrize("changed_reference", [None, 901])
def test_freeze_never_replaces_a_supplied_reference_with_mismatched_metadata(tmp_path, monkeypatch, changed_reference):
    metadata, evidence, _ = prepare_fixture(tmp_path, monkeypatch)
    original_task = Path(metadata["task"]).read_bytes()
    metadata["original_heartbeats"] = changed_reference
    with pytest.raises(ValueError, match="supplied task reference"):
        baselines.freeze_original_baseline(metadata, evidence, tmp_path / "baselines")
    assert Path(metadata["task"]).read_bytes() == original_task
    assert not (tmp_path / "baselines").exists()
