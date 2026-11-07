"""Offline original-token preflight regressions; no Lean process is launched."""
import json
from pathlib import Path
import subprocess

import pytest

from harness import doctor, environments
from harness.benchmark import digest, load_benchmark
from lean_tools import arena_workflow as arena
from lean_tools.measurement_policy import scoring_policy_context

ROOT = Path(__file__).resolve().parents[1]


def resolve_without_lean(tmp_path, monkeypatch, benchmark):
    requirements = {"schema_version": 1, "tasks": {}, "snapshots": {"fixture": {
        "repository": "https://example.com/fixture", "revision": "a" * 40}}}
    requirements_path = tmp_path / "requirements.json"
    requirements_path.write_text(json.dumps(requirements))
    mapping = tmp_path / "env.toml"
    mapping.write_text("offline fixture\n")
    binding = environments.EnvironmentMap(mapping, requirements_path,
        {"fixture": tmp_path / "project"}, requirements, tmp_path / "elan")
    # Snapshot identity checks are unrelated to this source-only regression.
    monkeypatch.setattr(environments, "_selection", lambda row, *_args:
        ("proof-" + digest(row["name"])[:16], {"primary": "fixture", "compatibility": []}))
    monkeypatch.setattr(environments, "validate_snapshot", lambda *_args, **_kwargs:
        {"workspace": {"executable": "offline-version"}})
    monkeypatch.setattr(arena, "environment_fingerprint_guard_material", lambda *_args:
        {"registry_key": "fixture", "instrumentation": "offline-fixture"})
    monkeypatch.setattr(arena, "environment_fingerprint_guard_sha256", lambda *_args: "f" * 64)

    def version(command, **_kwargs):
        assert command == ["offline-version", "--version"]
        return subprocess.CompletedProcess(command, 0, "offline fixture version\n", "")

    monkeypatch.setattr(environments.subprocess, "run", version)
    return environments.resolve_benchmark(benchmark, binding, tmp_path / "resolved")


def synthetic_benchmark(tmp_path, published, measured, body=None):
    # Each skip is one token. by, trivial and the Arena assignment offset add
    # three; these valid synthetic proofs need no released benchmark fixture.
    if body is None:
        body = "by\n" + "  skip\n" * (measured - 3) + "  trivial -- ignored := sorry tokens\n"
    row = {"name": "Synthetic.original", "signature": "theorem Synthetic.original : True",
        "src": "theorem Synthetic.original : True := " + body, "header": "import Mathlib\n",
        "contexts": [], "source": "PutnamBench", "proof_length": published,
        "version_info": [{"v4.29.1": "a" * 40}]}
    task, heartbeat = tmp_path / "input.jsonl", tmp_path / "heartbeats.jsonl"
    task.write_text(json.dumps(row) + "\n")
    heartbeat.write_text(json.dumps({"name": row["name"], "heartbeat": 100}) + "\n")
    return load_benchmark(task, heartbeat)


def fake_doctor_worker(monkeypatch, tmp_path):
    """Keep the fresh evaluator's admission and token measurement real."""
    monkeypatch.setattr(arena, "evaluation_scratch_parent", lambda: tmp_path)
    monkeypatch.setattr(arena, "persistent_quick_matches_project", lambda _project: False)
    calls = []

    def run_worker(command, **kwargs):
        assert command[1:4] == ["-m", "harness.doctor", "--worker"]
        request = json.loads(Path(command[4]).read_text())
        calls.append({"request": request, "parent_timeout": kwargs["timeout"]})
        _, row = arena.load_task(Path(request["task"]))

        def fake_lean(_path, _project, timeout_seconds, **_kwargs):
            assert timeout_seconds == request["timeout_seconds"]
            output = ("Used 100 heartbeats, which is less than the current maximum of 1000000000.\n"
                f"'{row['name']}' depends on axioms: [propext, Classical.choice, Quot.sound]")
            return arena.LeanRun(["fake-lean"], 0, 0.01, output)

        monkeypatch.setattr(arena, "run_lean", fake_lean)
        registry = json.loads(Path(request["registry"]).read_text(encoding="utf-8"))["entries"]
        fingerprint = registry[arena.environment_fingerprint_registry_key(row, Path(request["project"]))]["fingerprint"]
        evaluation = arena.evaluate_candidate_fresh(Path(request["task"]),
            Path(request["candidate"]), Path(request["project"]),
            timeout_seconds=request["timeout_seconds"], quick=request["quick"],
            environment_fingerprint=fingerprint, scoring_policy=request["scoring_policy"])
        Path(request["output"]).write_text(json.dumps(arena.evaluation_payload(evaluation)))
        return subprocess.CompletedProcess(command, 0, "", "")

    monkeypatch.setattr(doctor.subprocess, "run", run_worker)
    return calls


@pytest.mark.parametrize("published,measured,body", [
    (2162, 2162, None), (5464, 5464, None),  # Shapes of the two newly released originals.
    (2, 3, None),                          # Historical published-plus-one convention.
    (100, 3, None),                        # The published denominator is independent.
    (3, 4, "by\n  skip -- comment\r  trivial\n"),  # Fresh admission normalizes lone CRs.
])
def test_original_expectation_uses_fresh_source_count(tmp_path, monkeypatch, published, measured, body):
    benchmark = synthetic_benchmark(tmp_path, published, measured, body)
    # The resolver must use its explicit policy, even in a legacy caller scope.
    with scoring_policy_context("legacy-v1"):
        metadata, = resolve_without_lean(tmp_path, monkeypatch, benchmark)
    assert metadata["original_tokens"] == published
    assert metadata["original_measurement_tokens"] == measured
    assert json.loads(Path(metadata["task"]).read_text())["row"]["proof_length"] == published
    fake_doctor_worker(monkeypatch, tmp_path)
    report = doctor.evaluate_original(metadata, tmp_path / "doctor", environment={"OFFLINE": "1"})
    evaluation = report["environments"][0]["evaluation"]
    assert report["status"] == "passed"
    assert evaluation["length"]["candidate_tokens"] == measured
    assert evaluation["length"]["original_tokens"] == published


def test_doctor_rejects_an_incorrect_original_source_count(tmp_path, monkeypatch):
    benchmark = synthetic_benchmark(tmp_path, published=2162, measured=2162)
    metadata, = resolve_without_lean(tmp_path, monkeypatch, benchmark)
    metadata["original_measurement_tokens"] += 1
    fake_doctor_worker(monkeypatch, tmp_path)
    with pytest.raises(ValueError, match="Original token measurement differs"):
        doctor.evaluate_original(metadata, tmp_path / "doctor", environment={"OFFLINE": "1"})


@pytest.mark.parametrize("quick", [False, True])
@pytest.mark.parametrize("options,expected", [({}, 600), ({"timeout_seconds": 17}, 17)])
def test_doctor_original_timeout_default_and_override(tmp_path, monkeypatch, quick, options, expected):
    benchmark = synthetic_benchmark(tmp_path, published=2, measured=3)
    metadata, = resolve_without_lean(tmp_path, monkeypatch, benchmark)
    calls = fake_doctor_worker(monkeypatch, tmp_path)
    report = doctor.evaluate_original(metadata, tmp_path / "doctor", quick=quick,
        environment={"OFFLINE": "1"}, **options)
    assert report["status"] == "passed"
    call, = calls
    assert call["request"]["quick"] is quick
    assert call["request"]["timeout_seconds"] == expected
    assert call["parent_timeout"] == expected + 30


def test_all_warmup_original_token_expectations_are_unchanged(tmp_path, monkeypatch):
    benchmark = load_benchmark(ROOT / "data/benchmark_data_warmup.jsonl",
        ROOT / "data/benchmark_heartbeats.jsonl")
    proofs = resolve_without_lean(tmp_path, monkeypatch, benchmark)
    frozen = json.loads((ROOT / "data/proofs-arena-v1.json").read_text(encoding="utf-8"))["proofs"].values()
    expected = {entry["task_id"]: entry["original_measurement_tokens"] for entry in frozen}
    assert len(proofs) == len(expected) == 15
    for row, metadata in zip(benchmark.rows, proofs):
        assert metadata["original_tokens"] == row["proof_length"]
        assert metadata["original_measurement_tokens"] == row["proof_length"] + 1 == expected[row["name"]]
