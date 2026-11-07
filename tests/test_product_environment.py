from pathlib import Path
import json
import subprocess

import pytest

from harness import environments
from harness.environments import load_environment_map, validate_snapshot, validate_dependencies, _selection, select_snapshots
from harness.benchmark import digest, load_benchmark
from lean_tools import arena_workflow as arena

ROOT = Path(__file__).resolve().parents[1]


def test_environment_map_never_discovers_missing_binding(tmp_path):
    manifest = tmp_path / "requirements.json"
    manifest.write_text(json.dumps({"schema_version": 1, "snapshots": {}, "tasks": {}}))
    mapping = tmp_path / "env.toml"
    mapping.write_text('schema_version = 1\nrequirements = "requirements.json"\n[paths]\nunknown = "/somewhere"\n')
    with pytest.raises(ValueError, match="no repository/version/revision"):
        load_environment_map(mapping)


def test_environment_map_requires_identity_manifest(tmp_path):
    mapping = tmp_path / "env.toml"
    mapping.write_text('schema_version = 1\n[paths]\n')
    with pytest.raises(ValueError, match="explicit path"):
        load_environment_map(mapping)


def test_missing_snapshot_is_failure_without_setup(tmp_path, monkeypatch):
    manifest = tmp_path / "requirements.json"
    manifest.write_text(json.dumps({"schema_version": 1, "snapshots": {"id": {"repository": "https://github.com/test/repo",
        "lean_version": "v4.29.1", "revision": "a" * 40, "lean_commit": "b" * 40,
        "required_files": {"lean-toolchain": "c" * 64}}}, "tasks": {}}))
    mapping = tmp_path / "env.toml"
    mapping.write_text(f'schema_version = 1\nrequirements = "requirements.json"\n[paths]\nid = {json.dumps(str(tmp_path / "absent"))}\n')
    env = load_environment_map(mapping)
    monkeypatch.setattr("subprocess.run", lambda *a, **k: pytest.fail("must not run setup"))
    with pytest.raises(ValueError, match="Missing prebuilt snapshot"):
        validate_snapshot(env, "id", elan_home=tmp_path)


def test_source_snapshot_requires_explicit_supported_revision(tmp_path):
    manifest = tmp_path / "requirements.json"
    manifest.write_text(json.dumps({"schema_version": 1, "snapshots": {}, "tasks": {}}))
    mapping = tmp_path / "env.toml"
    mapping.write_text('schema_version = 1\nrequirements = "requirements.json"\n[paths]\n')
    env = load_environment_map(mapping)
    row = {"name": "NewTask", "url": "https://github.com/new/repo", "version_info": [{"v4.29.1": "a" * 40}]}
    with pytest.raises(ValueError, match="Unsupported source snapshot"):
        _selection(row, env, "arena-v1")


def test_changed_known_name_uses_row_source_pins_without_archived_task_metadata(tmp_path):
    manifest = ROOT / "data/environment-requirements.json"
    mapping = tmp_path / "env.toml"
    mapping.write_text(f'schema_version = 1\nrequirements = {json.dumps(str(manifest))}\n[paths]\n')
    env = load_environment_map(mapping)
    benchmark = load_benchmark(ROOT / "data/benchmark_data_warmup.jsonl", ROOT / "data/benchmark_heartbeats.jsonl")
    original = benchmark.rows[0]
    row = dict(original)
    row["src"] += "\n-- replacement"
    label, selection = _selection(row, env, "arena-v1")
    assert label == "proof-" + digest(row["name"])[:16]
    assert selection == select_snapshots(original, env.requirements)
    # Legacy support is deliberately separate from the product resolver.
    with pytest.raises(ValueError, match="frozen baseline originals"):
        _selection(row, env, "legacy-v1")


def offline_resolution(tmp_path, monkeypatch, *, supplied_tokens=True, supplied_heartbeat=True):
    row = {"name": "Future.original", "signature": "theorem Future.original : True",
        "src": "theorem Future.original : True := by trivial", "header": "import Mathlib\n",
        "contexts": [], "source": "PutnamBench", "proof_length": 912,
        "url": "https://example.com/fixture.git/",
        "version_info": [{"v4.29.1": "a" * 40}, {"v4.28.0": "b" * 40}]}
    task, heartbeat = tmp_path / "input.jsonl", tmp_path / "heartbeats.jsonl"
    if not supplied_tokens:
        del row["proof_length"]
    task.write_text(json.dumps(row) + "\n")
    heartbeat.write_text(json.dumps({"name": row["name"], "heartbeat": 777}) + "\n")
    benchmark = load_benchmark(task, heartbeat if supplied_heartbeat else None)
    snapshots = {name: {"repository": "https://example.com/fixture", "lean_version": version,
        "revision": revision, "lean_commit": "c" * 40,
        "required_files": {"lean-toolchain": "d" * 64}}
        for name, version, revision in [("primary", "v4.29.1", "a" * 40), ("compat", "v4.28.0", "b" * 40)]}
    # A reused name may have arbitrary old proof metadata. None can affect arena-v1.
    requirements = {"schema_version": 1, "snapshots": snapshots, "tasks": {row["name"]: {
        "label": "old-label", "row_sha256": "0" * 64,
        "arena-v1": {"primary": "wrong", "compatibility": []},
        "environments": {"primary": {"fingerprint": "old", "guard": {}}}}}}
    manifest = tmp_path / "requirements.json"
    manifest.write_text(json.dumps(requirements))
    mapping = tmp_path / "env.toml"
    mapping.write_text("offline fixture\n")
    binding = environments.EnvironmentMap(mapping, manifest,
        {name: tmp_path / name for name in snapshots}, requirements, tmp_path / "elan")
    monkeypatch.setattr(environments, "DATA", tmp_path / "absent-archived-data")
    calls = []
    monkeypatch.setattr(environments, "validate_snapshot", lambda _binding, sid, **_kwargs:
        calls.append(sid) or {"workspace": {"executable": f"offline-{sid}"}})
    monkeypatch.setattr(arena, "environment_fingerprint_guard_material", lambda current, _project:
        {"registry_key": "offline", "instrumentation": "offline-fixture", "source_sha256": digest(current)})
    monkeypatch.setattr(arena, "environment_fingerprint_guard_sha256", lambda current, _project: digest(current))

    def version(command, **_kwargs):
        assert command[1:] == ["--version"]
        return subprocess.CompletedProcess(command, 0, "offline Lean identity\n", "")

    monkeypatch.setattr(environments.subprocess, "run", version)
    metadata, = environments.resolve_benchmark(benchmark, binding, tmp_path / "resolved")
    return row, metadata, calls


def test_generic_resolver_preserves_supplied_metrics_and_current_environment_guards(tmp_path, monkeypatch):
    row, metadata, calls = offline_resolution(tmp_path, monkeypatch)
    assert metadata["label"] == "proof-" + digest(row["name"])[:16]
    assert calls == ["primary", "compat"]
    assert metadata["original_tokens"] == 912
    assert metadata["original_heartbeats"] == metadata["published_reference_heartbeats"] == 777
    assert metadata["original_measurement_tokens"] == 3
    assert metadata["baseline_provenance"] == {
        "tokens": {"source": "supplied_proof_length", "value": 912},
        "heartbeats": {"source": "supplied_heartbeat", "value": 777}}
    assert "original_measurement_evidence" not in metadata
    assert [item["snapshot_id"] for item in metadata["environments"]] == ["primary", "compat"]
    assert all(item["fingerprint"] != "old" and item["guard_sha256"] == digest(row)
        for item in metadata["environments"])
    document = json.loads(Path(metadata["task"]).read_text())
    assert document["row"] == row
    assert document["reference"] == {"heartbeat": 777}
    assert "original_metrics" not in document


def test_generic_resolver_leaves_missing_heartbeat_pending_and_derives_missing_tokens(tmp_path, monkeypatch):
    row, metadata, _calls = offline_resolution(tmp_path, monkeypatch,
        supplied_tokens=False, supplied_heartbeat=False)
    assert "proof_length" not in row
    assert metadata["original_tokens"] == metadata["original_measurement_tokens"] == 3
    assert metadata["original_heartbeats"] is None
    assert metadata["published_reference_heartbeats"] is None
    assert metadata["baseline_provenance"] == {
        "tokens": {"source": "measured_original_tokens", "value": 3},
        "heartbeats": {"source": "pending_original_measurement", "value": None}}
    document = json.loads(Path(metadata["task"]).read_text())
    assert document["row"] == row
    assert document["reference"] == {"heartbeat": None}
    assert document["original_metrics"] == {"tokens": 3, "token_source": "measured_original_tokens"}


def test_snapshot_selection_preserves_requested_order_and_rejects_ambiguity():
    row = {"name": "Unseen", "url": "https://example.com/repo.git/",
        "version_info": [{"v4.29.1": "a" * 40}, {"v4.28.0": "b" * 40}]}
    requirements = {"snapshots": {
        "older": {"repository": "https://example.com/repo/", "lean_version": "v4.28.0", "revision": "b" * 40},
        "newer": {"repository": "https://example.com/repo.git", "lean_version": "v4.29.1", "revision": "a" * 40}}}
    assert select_snapshots(row, requirements) == {"primary": "newer", "compatibility": ["older"]}
    requirements["snapshots"]["ambiguous"] = dict(requirements["snapshots"]["newer"])
    with pytest.raises(ValueError, match="Unsupported source snapshot"):
        select_snapshots(row, requirements)


def test_lean_worker_does_not_inherit_host_credentials(tmp_path, monkeypatch):
    from harness.doctor import _native_environment
    monkeypatch.setenv("OPENROUTER_MANAGEMENT_KEY", "never-copy")
    monkeypatch.setenv("OPENAI_API_KEY", "never-copy")
    monkeypatch.setenv("SOME_ACCESS_TOKEN", "never-copy")
    monkeypatch.setenv("PROXY_PASSWORD", "never-copy")
    environment = _native_environment(tmp_path / "elan", tmp_path / "cache")
    assert not {"OPENROUTER_MANAGEMENT_KEY", "OPENAI_API_KEY", "SOME_ACCESS_TOKEN", "PROXY_PASSWORD"} & environment.keys()
    assert environment["ELAN_HOME"] == str(tmp_path / "elan")
