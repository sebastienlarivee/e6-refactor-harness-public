"""Recipient entrypoints keep fixed runtime policy with input-driven selection."""
from __future__ import annotations

from dataclasses import replace
from decimal import Decimal
import hashlib
import json
from pathlib import Path
import shlex
import shutil
import tomllib
from unittest.mock import Mock

import pytest

from harness.config import RunConfig
from scripts import run_submission as run_entry
from scripts import setup_submission as setup_entry


@pytest.fixture
def submission(tmp_path):
    root = tmp_path / "release"
    (root / "configs/models").mkdir(parents=True)
    (root / "data").mkdir()
    (root / "environment-sources").mkdir()
    source = Path(__file__).resolve().parents[1]
    shutil.copyfile(source / "configs/submission.toml", root / "configs/submission.toml")
    shutil.copyfile(source / "configs/models/sol61.json", root / "configs/models/sol61.json")
    rows = [{"name": f"example_{index}", "source": "strata", "statement": "theorem example : True",
             "src": "theorem example : True := by trivial", "contexts": [], "proof_length": 3,
             "header": "", "file_path": "Example.lean", "url": "https://github.com/example/project",
             "version_info": [{"v4.29.1": "a" * 40}]} for index in range(7)]
    spec = {"repository": "https://github.com/example/project", "lean_version": "v4.29.1",
            "revision": "a" * 40, "lean_commit": "b" * 40,
            "required_files": {"Example.lean": "c" * 64}}
    pack = root / "environment-sources/project.tar.gz"
    pack.write_bytes(b"synthetic source pack; extraction is mocked")
    manifest = {"schema_version": 1, "format": "lean-project-sources-tar-gzip-v1",
                "requirements": {"schema_version": 1, "snapshots": {"project": spec}},
                "snapshots": {"project": {"pack": pack.name, "sha256": hashlib.sha256(pack.read_bytes()).hexdigest(),
                                           "bytes": pack.stat().st_size, "overlays": {}}}, "rows": rows}
    (root / "data/benchmark_data_final.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))
    (root / "data/benchmark_heartbeats_final.jsonl").write_text("".join(
        json.dumps({"name": row["name"], "heartbeat": 100}) + "\n" for row in rows))
    (root / "environment-sources/environment-setup.json").write_text(json.dumps(manifest))
    return root, rows, manifest


@pytest.fixture
def upstream_submission(submission):
    root, rows, manifest = submission
    spec = manifest["requirements"]["snapshots"]["project"]
    manifest["format"] = "lean-project-upstream-v1"
    manifest["snapshots"]["project"] = {
        "source": {"url": spec["repository"], "rev": spec["revision"]},
        "overlays": {
            ".lrh-stage.json": json.dumps({"schema_version": 1, "kind": "repository",
                                            "lean_version": spec["lean_version"], "revision": spec["revision"]}),
            "lean-toolchain": f"leanprover/lean4:{spec['lean_version']}\n",
            "lakefile.toml": 'name = "fixture"\n',
            "lake-manifest.json": json.dumps({"version": "1.1.0", "packagesDir": ".lake/packages",
                                               "packages": [], "name": "fixture", "lakeDir": ".lake"}),
        },
    }
    (root / "environment-sources/project.tar.gz").unlink()
    (root / "environment-sources/environment-setup.json").write_text(json.dumps(manifest))
    return root, rows, manifest


def local_config(root):
    return setup_entry.write_local_config(root, codex=root.parent / "runtime/bin/codex", elan=root.parent / "elan")


def frozen(root, rows):
    return {"identity": "frozen", "root": str(root), "config": RunConfig.load(local_config(root)).to_dict(),
            "proofs": [{"task_id": row["name"], "label": row["name"]} for row in rows]}


def test_missing_optional_references_do_not_block_setup(submission, monkeypatch):
    root, _, _ = submission
    (root / "data/benchmark_heartbeats_final.jsonl").unlink()
    prepare = Mock(return_value={"status": "ready"})
    monkeypatch.setattr(setup_entry, "prepare_environments", prepare)
    assert setup_entry.setup(root)["status"] == "ready"
    prepare.assert_called_once()
    config = RunConfig.load(root / "configs/run.local.toml")
    assert config.heartbeat_path is None


def test_upstream_assets_are_validated_offline_without_source_archives(upstream_submission, monkeypatch):
    import subprocess
    import urllib.request
    root, rows, _ = upstream_submission
    monkeypatch.setattr(urllib.request, "urlopen", lambda *args, **kwargs: pytest.fail("asset validation fetched sources"))
    monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: pytest.fail("asset validation launched a source command"))
    assets = setup_entry.validate_assets(root)
    assert len(assets["benchmark"].rows) == len(rows)
    assert assets["setup"]["format"] == "lean-project-upstream-v1"
    assert list((root / "environment-sources").iterdir()) == [assets["manifest"]]


def test_upstream_setup_delegates_provisioning_once_without_source_pack_requirement(upstream_submission, monkeypatch):
    from scripts import setup_environments
    root, _, _ = upstream_submission
    runtime, elan, downloads = (root.parent / name for name in ("runtime", "elan", "downloads"))
    monkeypatch.setenv("HARNESS_RUNTIME_ROOT", str(runtime))
    monkeypatch.setenv("ELAN_HOME", str(elan))
    monkeypatch.setenv("HARNESS_DOWNLOADS_ROOT", str(downloads))
    install = Mock(return_value={"status": "ready"})
    monkeypatch.setattr(setup_environments, "install", install)

    result = setup_entry.setup(root)
    assert result["status"] == "ready"
    install.assert_called_once_with(root / "environment-sources/environment-setup.json", runtime / "environments",
                                   elan, root / "environments.local.toml", cache_dir=downloads / "mathlib")
    assert RunConfig.load(root / "configs/run.local.toml").codex == runtime / "bin/codex"


def test_upstream_setup_reuses_existing_matching_pack_bindings_without_fetching(upstream_submission, monkeypatch):
    import subprocess
    import urllib.request
    from harness import environments
    from scripts import setup_environments
    root, rows, manifest = upstream_submission
    requirements = root.parent / "old-pack-requirements.json"
    requirements.write_text(json.dumps(manifest["requirements"]))
    mapping = root / "environments.local.toml"
    mapping.write_text(setup_environments.environment_map_text(requirements, root.parent / "elan",
                                                             {"project": root.parent / "prepared"}))
    original = mapping.read_bytes(), mapping.stat().st_mtime_ns
    validate_snapshot, validate_dependencies = Mock(), Mock()
    monkeypatch.setattr(environments, "validate_snapshot", validate_snapshot)
    monkeypatch.setattr(environments, "validate_dependencies", validate_dependencies)
    monkeypatch.setattr(setup_environments, "toolchain_problem", lambda *args: None)
    monkeypatch.setattr(setup_environments, "install", lambda *args, **kwargs: pytest.fail("prepared sources were provisioned again"))
    monkeypatch.setattr(urllib.request, "urlopen", lambda *args, **kwargs: pytest.fail("prepared sources were fetched"))
    monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: pytest.fail("reuse launched a source command"))

    assert setup_entry.setup(root)["environments"]["status"] == "reused"
    assert (mapping.read_bytes(), mapping.stat().st_mtime_ns) == original
    validate_snapshot.assert_called_once()
    assert validate_dependencies.call_count == len(rows)


def test_upstream_run_validates_manifest_without_fetching_sources(upstream_submission, monkeypatch):
    import urllib.request
    import harness.export
    from scripts import setup_environments
    root, rows, _ = upstream_submission
    snapshot = frozen(root, rows)
    monkeypatch.setattr(run_entry.runner, "prepare_run", lambda *args: snapshot)
    monkeypatch.setattr(run_entry.runner, "run", lambda *args, **kwargs: 0)
    monkeypatch.setattr(run_entry.runner, "status", lambda *args: {"status": "completed"})
    monkeypatch.setattr(harness.export, "export_run", lambda *args: {"status": "exported"})
    monkeypatch.setattr(setup_environments, "install", lambda *args, **kwargs: pytest.fail("run provisioned sources"))
    monkeypatch.setattr(urllib.request, "urlopen", lambda *args, **kwargs: pytest.fail("run fetched sources"))
    assert run_entry.run_submission(root.parent / "key", output=root.parent / "run", root=root) == 0


def test_invalid_upstream_source_pin_fails_before_environment_work(upstream_submission, monkeypatch):
    root, _, manifest = upstream_submission
    manifest["snapshots"]["project"]["source"]["rev"] = "f" * 40
    (root / "environment-sources/environment-setup.json").write_text(json.dumps(manifest))
    prepare = Mock()
    monkeypatch.setattr(setup_entry, "prepare_environments", prepare)
    with pytest.raises(ValueError):
        setup_entry.setup(root)
    prepare.assert_not_called()


def test_missing_input_fails_before_runtime_or_model_work(submission, monkeypatch):
    root, _, _ = submission
    (root / "data/benchmark_data_final.jsonl").unlink()
    prepare = Mock()
    monkeypatch.setattr(setup_entry, "prepare_environments", prepare)
    with pytest.raises(ValueError, match="Incomplete submission bundle.*benchmark_data_final"):
        setup_entry.setup(root)
    prepare.assert_not_called()
    assert not (root / "configs/run.local.toml").exists()


def test_input_count_is_not_fixed_and_extra_cached_references_are_allowed(submission):
    root, rows, _ = submission
    (root / "data/benchmark_data_final.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows[:2]))
    assets = setup_entry.validate_assets(root)
    assert len(assets["benchmark"].rows) == 2
    assert len(assets["benchmark"].heartbeats) == len(rows)


def test_input_can_change_name_and_proof_within_included_snapshot_coverage(submission):
    root, _, manifest = submission
    manifest["rows"][0]["src"] += "\n-- changed"
    (root / "environment-sources/environment-setup.json").write_text(json.dumps(manifest))
    assert setup_entry.validate_assets(root)["benchmark"].rows[0]["name"] == "example_0"


def test_missing_source_pack_fails_before_dispatch(submission, monkeypatch):
    root, _, _ = submission
    local_config(root)
    (root / "environment-sources/project.tar.gz").unlink()
    dispatch = Mock()
    monkeypatch.setattr(run_entry.runner, "run", dispatch)
    with pytest.raises(ValueError, match="missing bundled source pack"):
        run_entry.run_submission(root.parent / "key", output=root.parent / "run", root=root)
    dispatch.assert_not_called()


def test_alternative_input_path_uses_its_own_rows_and_optional_references(submission):
    root, rows, _ = submission
    config = RunConfig.load(root / "configs/submission.toml")
    selected = {**rows[0], "name": "new_example", "src": rows[0]["src"] + "\n-- different input"}
    alternate = root.parent / "arbitrary.jsonl"
    alternate.write_text(json.dumps(selected) + "\n")
    assets = setup_entry.validate_assets(root, config=replace(config, input_path=alternate))
    assert [row["name"] for row in assets["benchmark"].rows] == ["new_example"]
    assert assets["benchmark"].heartbeats == {}


def test_unsupported_input_snapshot_fails_before_dispatch(submission, monkeypatch):
    root, rows, _ = submission
    local_config(root)
    alternate = root.parent / "unsupported.jsonl"
    alternate.write_text(json.dumps({**rows[0], "version_info": [{"v4.29.1": "f" * 40}]}) + "\n")
    prepare, dispatch = Mock(), Mock()
    monkeypatch.setattr(run_entry.runner, "prepare_run", prepare)
    monkeypatch.setattr(run_entry.runner, "run", dispatch)
    with pytest.raises(ValueError, match="Unsupported input environment.*does not download environments"):
        run_entry.run_submission(root.parent / "key", output=root.parent / "run", input_path=alternate, root=root)
    prepare.assert_not_called()
    dispatch.assert_not_called()


@pytest.mark.parametrize("change", [
    {"selected_proofs": ("example_0",)}, {"diagnostic_max_passes": 1},
    {"budget_usd": Decimal("2.80")}, {"budget_policy": "provider-key-v1"},
    {"concurrency": 1}, {"optimizer": "off"},
    {"openrouter": {"model_id": "openai/other", "provider": "openai", "default_reasoning_effort": "high"}},
    {"openrouter": {"model_id": "openai/gpt-6.1-sol", "provider": "openai", "default_reasoning_effort": "medium"}},
])
def test_submission_policy_is_fixed(submission, change):
    root, _, _ = submission
    base = RunConfig.load(root / "configs/submission.toml")
    if "budget_usd" in change:
        change = {**change, "openrouter": {**base.openrouter, "budget_usd": str(change["budget_usd"])}}
    config = replace(base, **change)
    with pytest.raises(ValueError, match="Submission policy requires"):
        setup_entry.validate_assets(root, config=config)


def test_run_calls_public_prepare_run_and_independent_export(submission, monkeypatch):
    import harness.export
    root, rows, _ = submission
    snapshot = frozen(root, rows)
    prepare, run, export = Mock(return_value=snapshot), Mock(return_value=0), Mock(return_value={"status": "exported"})
    monkeypatch.setattr(run_entry.runner, "prepare_run", prepare)
    monkeypatch.setattr(run_entry.runner, "run", run)
    monkeypatch.setattr(run_entry.runner, "status", lambda _: {"status": "completed"})
    monkeypatch.setattr(harness.export, "export_run", export)
    output, key = root.parent / "run", root.parent / "host-only-key"
    assert run_entry.run_submission(key, output=output, root=root) == 0
    config, actual_output = prepare.call_args.args
    assert actual_output == output and config.budget_usd == Decimal("2.90")
    assert not config.selected_proofs and config.diagnostic_max_passes is None
    run.assert_called_once_with(output, api_key_file=key, resume=False)
    export.assert_called_once_with(output, output / "submission.jsonl")
    publication = json.loads((output / "submission-status.json").read_text())
    assert publication["status"] == "exported" and publication["run_identity"] == snapshot["identity"]
    assert not key.exists()  # Wrapper never reads, creates, or copies the key.


def test_exclusive_run_key_opt_in_is_frozen_before_dispatch(submission, monkeypatch):
    import harness.export
    root, rows, _ = submission
    snapshot = frozen(root, rows)
    prepare = Mock(return_value=snapshot)
    monkeypatch.setattr(run_entry.runner, "prepare_run", prepare)
    monkeypatch.setattr(run_entry.runner, "run", lambda *_, **__: 0)
    monkeypatch.setattr(run_entry.runner, "status", lambda _: {"status": "completed"})
    monkeypatch.setattr(harness.export, "export_run", lambda *_: {"status": "exported"})
    assert run_entry.run_submission(root.parent / "key", output=root.parent / "run", root=root,
                                    exclusive_run_key=True) == 0
    assert prepare.call_args.args[0].recovery_policy == "exclusive-key-v1"


def test_exclusive_run_key_cannot_be_enabled_on_existing_run(submission, monkeypatch):
    root, rows, _ = submission
    snapshot = frozen(root, rows)
    snapshot["config"].pop("recovery_policy", None)
    monkeypatch.setattr(run_entry.runner, "load_snapshot", lambda _: snapshot)
    dispatch = Mock()
    monkeypatch.setattr(run_entry.runner, "run", dispatch)
    with pytest.raises(ValueError, match="frozen recovery policy"):
        run_entry.run_submission(root.parent / "key", output=root.parent / "run", root=root,
                                resume=True, exclusive_run_key=True)
    dispatch.assert_not_called()


@pytest.mark.parametrize("supplied_references", [False, True])
def test_run_input_override_selects_all_its_rows_without_default_references(submission, monkeypatch, supplied_references):
    import harness.export
    root, rows, _ = submission
    selected = rows[:2]
    alternate = root.parent / "selected.jsonl"
    alternate.write_text("".join(json.dumps(row) + "\n" for row in selected))
    references = root.parent / "selected-heartbeats.jsonl" if supplied_references else None
    if references is not None:
        # Partial references are completed by the core's original-proof preflight.
        references.write_text(json.dumps({"name": selected[0]["name"], "heartbeat": 123}) + "\n")
    snapshot = frozen(root, selected)
    prepare = Mock(return_value=snapshot)
    monkeypatch.setattr(run_entry.runner, "prepare_run", prepare)
    monkeypatch.setattr(run_entry.runner, "run", lambda *_, **__: 0)
    monkeypatch.setattr(run_entry.runner, "status", lambda _: {"status": "completed"})
    monkeypatch.setattr(harness.export, "export_run", lambda *_: {"status": "exported"})
    assert run_entry.run_submission(root.parent / "key", output=root.parent / "run", root=root,
                                   input_path=alternate, heartbeat_path=references) == 0
    config = prepare.call_args.args[0]
    assert config.input_path == alternate
    assert config.heartbeat_path == references
    assert not config.selected_proofs


@pytest.mark.parametrize("code,status", [(1, "needs_attention"), (0, "interrupted")])
def test_export_only_follows_successful_terminal_run(submission, monkeypatch, code, status):
    import harness.export
    root, rows, _ = submission
    snapshot = frozen(root, rows)
    monkeypatch.setattr(run_entry.runner, "prepare_run", lambda *_: snapshot)
    monkeypatch.setattr(run_entry.runner, "run", lambda *_, **__: code)
    monkeypatch.setattr(run_entry.runner, "status", lambda _: {"status": status})
    export = Mock()
    monkeypatch.setattr(harness.export, "export_run", export)
    if code:
        assert run_entry.run_submission(root.parent / "key", output=root.parent / "run", root=root) == code
    else:
        with pytest.raises(RuntimeError, match="did not complete"):
            run_entry.run_submission(root.parent / "key", output=root.parent / "run", root=root)
    export.assert_not_called()


def test_resume_uses_frozen_policy_and_same_run_without_prepare(submission, monkeypatch):
    import harness.export
    root, rows, _ = submission
    snapshot = frozen(root, rows)
    (root / "configs/run.local.toml").write_text("future configuration may differ\n")
    output, key = root.parent / "existing-run", root.parent / "original-key-path"
    monkeypatch.setattr(run_entry.runner, "load_snapshot", lambda path: snapshot)
    prepare, run = Mock(), Mock(return_value=0)
    monkeypatch.setattr(run_entry.runner, "prepare_run", prepare)
    monkeypatch.setattr(run_entry.runner, "run", run)
    monkeypatch.setattr(run_entry.runner, "status", lambda _: {"status": "completed"})
    monkeypatch.setattr(harness.export, "export_run", lambda *_: {"status": "exported"})
    assert run_entry.run_submission(key, output=output, resume=True, root=root) == 0
    prepare.assert_not_called()
    run.assert_called_once_with(output, api_key_file=key, resume=True)
    assert snapshot["config"]["budget_usd"] == "2.90"


@pytest.mark.parametrize("override", ["input_path", "heartbeat_path"])
def test_resume_rejects_changed_input_or_reference_override(submission, monkeypatch, override):
    root, rows, _ = submission
    snapshot = frozen(root, rows)
    monkeypatch.setattr(run_entry.runner, "load_snapshot", lambda path: snapshot)
    prepare, dispatch = Mock(), Mock()
    monkeypatch.setattr(run_entry.runner, "prepare_run", prepare)
    monkeypatch.setattr(run_entry.runner, "run", dispatch)
    with pytest.raises(ValueError, match="cannot change the frozen input/reference"):
        run_entry.run_submission(root.parent / "key", output=root.parent / "run", resume=True,
                                 root=root, **{override: root.parent / "replacement.jsonl"})
    prepare.assert_not_called()
    dispatch.assert_not_called()


@pytest.mark.parametrize("resume", [False, True])
def test_incomplete_frozen_selection_never_dispatches(submission, monkeypatch, resume):
    root, rows, _ = submission
    snapshot = frozen(root, rows)
    snapshot["proofs"] = snapshot["proofs"][:1]
    monkeypatch.setattr(run_entry.runner, "load_snapshot", lambda _: snapshot)
    monkeypatch.setattr(run_entry.runner, "prepare_run", lambda *_: snapshot)
    dispatch = Mock()
    monkeypatch.setattr(run_entry.runner, "run", dispatch)
    with pytest.raises(ValueError, match=f"all {len(rows)} unique selected input names"):
        run_entry.run_submission(root.parent / "key", output=root.parent / "run", resume=resume, root=root)
    dispatch.assert_not_called()


def test_resume_cannot_bind_a_fresh_key_to_reset_budgets(submission, monkeypatch):
    from harness import openrouter
    root, rows, _ = submission
    snapshot = frozen(root, rows)
    run_root = root.parent / "bound-run"
    run_root.mkdir()
    snapshot["root"] = str(run_root)
    monkeypatch.setattr(run_entry.runner, "validate_host_credential_path", lambda path, _: path)
    fingerprint = {"value": "a" * 64}
    monkeypatch.setattr(openrouter, "InferenceKeyFile", lambda _: type("Key", (), {
        "verify": lambda self: {"key_sha256": fingerprint["value"]}})())
    run_entry.runner._credential_arguments(snapshot, api_key_file=root.parent / "key-one")
    original = (run_root / "credential-identity.json").read_bytes()
    fingerprint["value"] = "b" * 64
    with pytest.raises(ValueError, match="immutable"):
        run_entry.runner._credential_arguments(snapshot, api_key_file=root.parent / "key-two")
    assert (run_root / "credential-identity.json").read_bytes() == original


def test_setup_reuses_existing_valid_map_readonly(submission, monkeypatch):
    from harness import environments
    from scripts import setup_environments
    root, _, manifest = submission
    requirement = root.parent / "requirements.json"
    requirement.write_text(json.dumps(manifest["requirements"]))
    mapping = root / "environments.local.toml"
    mapping.write_text(setup_environments.environment_map_text(requirement, root.parent / "elan", {"project": root.parent / "prepared"}))
    original = mapping.read_bytes(), mapping.stat().st_mtime_ns
    validate = Mock()
    monkeypatch.setattr(environments, "validate_snapshot", validate)
    monkeypatch.setattr(environments, "validate_dependencies", Mock())
    monkeypatch.setattr(setup_environments, "toolchain_problem", lambda *_: None)
    install = Mock()
    monkeypatch.setattr(setup_environments, "install", install)
    assert setup_entry.setup(root)["environments"]["status"] == "reused"
    config_mtime = (root / "configs/run.local.toml").stat().st_mtime_ns
    assert setup_entry.setup(root)["environments"]["status"] == "reused"
    assert (mapping.read_bytes(), mapping.stat().st_mtime_ns) == original
    assert (root / "configs/run.local.toml").stat().st_mtime_ns == config_mtime
    assert validate.call_count == 2
    install.assert_not_called()


def test_setup_preserves_unmanaged_mismatched_map(submission, monkeypatch):
    from scripts import setup_environments
    root, _, manifest = submission
    requirements = root.parent / "requirements.json"
    requirements.write_text(json.dumps({**manifest["requirements"], "snapshots": {}}))
    mapping = root / "environments.local.toml"
    mapping.write_text(setup_environments.environment_map_text(requirements, root.parent / "elan", {}))
    original = mapping.read_bytes()
    install = Mock()
    monkeypatch.setattr(setup_environments, "install", install)
    with pytest.raises(ValueError, match="Existing.*does not bind"):
        setup_entry.setup(root)
    assert mapping.read_bytes() == original
    install.assert_not_called()


def test_setup_respects_custom_runtime_home_elan_and_download_paths(submission, monkeypatch):
    from scripts import setup_environments
    root, _, _ = submission
    home, runtime, elan, downloads = (root.parent / name for name in ("operator-home", "custom-runtime", "custom-elan", "download-cache"))
    monkeypatch.setenv("HOME", str(home))
    monkeypatch.setenv("HARNESS_RUNTIME_ROOT", str(runtime))
    monkeypatch.setenv("ELAN_HOME", str(elan))
    monkeypatch.setenv("HARNESS_DOWNLOADS_ROOT", str(downloads))
    install = Mock(return_value={"status": "ready"})
    monkeypatch.setattr(setup_environments, "install", install)
    setup_entry.setup(root)
    install.assert_called_once_with(root / "environment-sources/environment-setup.json", runtime / "environments", elan,
                                    root / "environments.local.toml", cache_dir=downloads / "mathlib")
    config = RunConfig.load(root / "configs/run.local.toml")
    assert config.codex == runtime / "bin/codex" and config.elan_home == elan
    document = tomllib.loads((root / "configs/run.local.toml").read_text())
    assert "api_key" not in json.dumps(document)
    monkeypatch.delenv("HARNESS_RUNTIME_ROOT")
    monkeypatch.delenv("ELAN_HOME")
    monkeypatch.delenv("HARNESS_DOWNLOADS_ROOT")
    assert setup_entry.runtime_root() == home / ".local/share/lean-refactor-harness"
    assert setup_entry.elan_home() == home / ".elan"
    assert setup_entry.downloads_root() == home / ".cache/lean-refactor-harness"


def test_default_output_uses_operator_state_home_outside_checkout(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_STATE_HOME", str(tmp_path))
    assert run_entry.default_output() == tmp_path / "lean-refactor-harness/final"


def test_cli_rejects_relative_key_and_unknown_tuning_flags():
    with pytest.raises(SystemExit):
        run_entry.main(["--api-key-file", "relative-key"])
    with pytest.raises(SystemExit):
        run_entry.main(["--api-key-file", "/host/key", "--proof", "example_0"])


@pytest.mark.parametrize("flag", ["--input", "--heartbeats"])
def test_cli_rejects_relative_input_and_reference_paths(flag, tmp_path):
    with pytest.raises(SystemExit):
        run_entry.main(["--api-key-file", str(tmp_path / "key"), flag, "relative.jsonl"])


def test_failed_preflight_preserves_evidence_and_never_suggests_resuming_unfrozen_output(submission, monkeypatch):
    from harness import doctor, environments
    root, _, _ = submission
    local_config(root)
    output = root.parent / "failed-preflight"
    monkeypatch.setattr(environments, "load_environment_map", lambda _: object())
    def resolve(benchmark, env_map, directory, **kwargs):
        directory.mkdir(parents=True)
        (directory / "Task.json").write_text("retained preparation evidence")
        return [{"label": "example", "task_id": "example_0"}]
    monkeypatch.setattr(environments, "resolve_benchmark", resolve)
    monkeypatch.setattr(doctor, "check", lambda *_, **__: {"status": "failed", "failures": [{"error": "missing tool"}]})
    dispatch = Mock()
    monkeypatch.setattr(run_entry.runner, "run", dispatch)
    with pytest.raises(RuntimeError, match="fresh --output directory"):
        run_entry.run_submission(root.parent / "key", output=output, root=root)
    assert (output / "doctor.json").is_file()
    assert not (output / "resolved-config.json").exists()
    with pytest.raises(FileExistsError, match="fresh --output directory; --resume is unavailable"):
        run_entry.runner.prepare_run(RunConfig.load(root / "configs/run.local.toml"), output)
    with pytest.raises(ValueError, match="cannot be resumed.*fresh --output directory"):
        run_entry.run_submission(root.parent / "key", output=output, root=root, resume=True)
    assert (output / "benchmark/Task.json").read_text() == "retained preparation evidence"
    dispatch.assert_not_called()


def test_interrupted_preflight_explains_fresh_output_recovery(submission, monkeypatch, capsys):
    root, _, _ = submission
    local_config(root)
    monkeypatch.setattr(run_entry.runner, "prepare_run", Mock(side_effect=KeyboardInterrupt()))
    dispatch = Mock()
    monkeypatch.setattr(run_entry.runner, "run", dispatch)
    with pytest.raises(KeyboardInterrupt):
        run_entry.run_submission(root.parent / "key", output=root.parent / "interrupted", root=root)
    assert "No frozen snapshot is available for --resume" in capsys.readouterr().err
    dispatch.assert_not_called()


@pytest.mark.parametrize("error,expected", [(ValueError("compiler failed"), "export_failed"),
                                           (KeyboardInterrupt("signal"), "export_interrupted")])
def test_export_failure_has_inference_free_recovery_and_preserved_status(submission, monkeypatch, capsys, error, expected):
    import harness.export
    root, rows, _ = submission
    snapshot = frozen(root, rows)
    output = root.parent / "run with spaces"
    (output / "submission-retry.jsonl.evidence").mkdir(parents=True)
    monkeypatch.setattr(run_entry.runner, "prepare_run", lambda *_: snapshot)
    dispatch = Mock(return_value=0)
    monkeypatch.setattr(run_entry.runner, "run", dispatch)
    monkeypatch.setattr(run_entry.runner, "status", lambda _: {"status": "completed"})
    def fail(*_):
        assert json.loads((output / "submission-status.json").read_text())["status"] == "exporting"
        raise error
    monkeypatch.setattr(harness.export, "export_run", fail)
    with pytest.raises(KeyboardInterrupt if expected == "export_interrupted" else RuntimeError) as caught:
        run_entry.run_submission(root.parent / "key", output=output, root=root)
    publication = json.loads((output / "submission-status.json").read_text())
    assert publication["status"] == expected and publication["run_identity"] == snapshot["identity"]
    message = capsys.readouterr().err if expected == "export_interrupted" else str(caught.value)
    assert "Retry export without inference:" in message
    command = message.split("Retry export without inference:\n", 1)[1].strip()
    assert shlex.split(command) == [str(root / ".venv/bin/harness"), "export", str(output),
                                     "--output", str(output / "submission-retry-2.jsonl")]
    dispatch.assert_called_once()
