"""Synthetic credential-path boundary checks; no keys, provider calls or paid inference."""
from argparse import Namespace
from pathlib import Path
import json
import os
import subprocess
import sys

import pytest

from harness import cli, runner
from e6 import isolation
from e6.config import REPO_ROOT
from e6.experiment import ExperimentSpec

SENTINEL = "SYNTHETIC_CREDENTIAL_PATH_SENTINEL_ONLY"


@pytest.fixture
def boundary(tmp_path, monkeypatch):
    run = tmp_path / "run"; run.mkdir()
    runtime = tmp_path / "runtime"; (runtime / "bin").mkdir(parents=True)
    package = tmp_path / "tooling/releases/codex-0.164.0"
    codex = package / "bin/codex"; codex.parent.mkdir(parents=True)
    codex.write_text("synthetic binary")
    (package / "codex-package.json").write_text("{}")
    elan = tmp_path / "elan"; (elan / "toolchains").mkdir(parents=True)
    toolchain = tmp_path / "resolved-toolchain"; toolchain.mkdir()
    (elan / "toolchains/pinned").symlink_to(toolchain, target_is_directory=True)
    projects = [tmp_path / f"project-{n}" for n in range(4)]
    for path in projects: path.mkdir()
    private = tmp_path / "host-private"; private.mkdir()
    rows = [{"label": f"proof-{n}", "task_id": f"Task{n}", "task_sha256": str(n),
        "primary": str(projects[n * 2]), "compatibility": [str(projects[n * 2 + 1])]} for n in range(2)]
    snapshot = {"root": str(run), "identity": "synthetic-frozen-run", "proofs": rows,
        "config": {"codex": str(codex), "elan_home": str(elan), "budget_usd": "3"}}
    import e6.config
    monkeypatch.setattr(e6.config, "runtime_root", lambda: runtime)
    monkeypatch.setattr(isolation, "runtime_root", lambda: runtime)
    return Namespace(run=run, runtime=runtime, package=package, codex=codex, elan=elan,
        toolchain=toolchain, projects=projects, private=private, snapshot=snapshot)


def sentinel(path):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(SENTINEL)
    path.chmod(0o600)
    return path


def test_all_selected_project_toolchain_runtime_and_run_files_are_rejected(boundary):
    roots = [*boundary.projects, boundary.elan, boundary.toolchain, boundary.runtime,
        boundary.package, boundary.run]
    for root in roots:
        path = sentinel(root / "synthetic-key.json")
        with pytest.raises(ValueError, match="agent-visible") as error:
            runner.validate_host_credential_path(path, boundary.snapshot)
        assert SENTINEL not in str(error.value)
    outside = sentinel(boundary.private / "keys.json")
    assert runner.validate_host_credential_path(outside, boundary.snapshot) == outside


def test_source_and_fixed_system_mounts_are_protected_before_file_access(boundary):
    for path in (REPO_ROOT / "nonexistent-synthetic-credential.json", Path("/usr/local/nonexistent-synthetic-key.json"),
                 Path("/etc/ssl/nonexistent-synthetic-key.json")):
        with pytest.raises(ValueError, match="agent-visible"):
            runner.validate_host_credential_path(path, boundary.snapshot)


def test_symlinks_into_any_selected_mount_are_resolved_and_rejected(boundary):
    target = sentinel(boundary.projects[-1] / "key.json")
    alias = boundary.private / "linked-key.json"; alias.symlink_to(target)
    with pytest.raises(ValueError, match="agent-visible"):
        runner.validate_host_credential_path(alias, boundary.snapshot)
    alias_dir = boundary.private / "linked-elan"; alias_dir.symlink_to(boundary.elan, target_is_directory=True)
    with pytest.raises(ValueError, match="agent-visible"):
        runner.validate_host_credential_path(alias_dir / "not-created-yet.json", boundary.snapshot)






def test_execution_rejects_exposed_store_before_reading_bindings(boundary, monkeypatch):
    import harness.openrouter
    monkeypatch.setattr(harness.openrouter, "ProofKeyStore", lambda *a, **k: pytest.fail("must reject before reading key bindings"))
    with pytest.raises(ValueError, match="agent-visible"):
        runner._credential_arguments(boundary.snapshot, sentinel(boundary.projects[-1] / "keys.json"))


def test_private_proof_entry_rejects_raw_key_in_any_selected_project_before_preparing(boundary, monkeypatch):
    monkeypatch.setattr(runner, "load_snapshot", lambda *a, **k: boundary.snapshot)
    exposed = sentinel(boundary.projects[-1] / "key.json")
    with pytest.raises(ValueError, match="agent-visible"):
        runner.run_proof(boundary.run, "proof-0", credentials=exposed)
    assert not (boundary.run / "proofs").exists()


def test_guard_and_production_sandbox_share_readonly_mount_policy(boundary, monkeypatch):
    # This assertion catches the original same-UID/0600 exposure using an actual
    # bubblewrap namespace, and checks a genuinely private path stays unreadable.
    if sys.platform != "linux" or isolation.shutil.which("bwrap") is None:
        pytest.skip("native Linux bubblewrap required")
    capsule = boundary.run / "proof/pass-001"; capsule.mkdir(parents=True)
    config = {"root": str(capsule.parent), "primary": str(boundary.projects[0]),
        "compatibility": [str(boundary.projects[1])], "codex": "/usr/bin/true",
        "experiment_spec": ExperimentSpec().to_dict()}
    exposed = sentinel(boundary.projects[0] / "key.json")
    private = sentinel(boundary.private / "key.json")
    probe = "import json,sys; from pathlib import Path; print(json.dumps([Path(p).exists() for p in sys.argv[1:]]))"
    argv, environment = isolation.wrap_command(config, capsule,
        ["/usr/bin/python3", "-c", probe, str(exposed), str(private)], [],
        {**os.environ, "ELAN_HOME": str(boundary.elan)})
    result = subprocess.run(argv, env=environment, capture_output=True, text=True, timeout=20)
    assert result.returncode == 0, result.stderr
    assert json.loads(result.stdout) == [True, False]
    mounted = json.loads((capsule / "isolation.json").read_text())["readonly"]
    assert str(boundary.projects[0]) in mounted and str(boundary.toolchain) in mounted
    for path in (exposed, boundary.toolchain / "not-created-key.json"):
        with pytest.raises(ValueError, match="agent-visible"):
            runner.validate_host_credential_path(path, boundary.snapshot)


def test_standalone_home_bin_does_not_reject_private_siblings_but_protects_future_mount_markers(boundary):
    home = boundary.private / "synthetic-home"
    codex = home / "bin/codex"; codex.parent.mkdir(parents=True); codex.write_text("synthetic binary")
    boundary.snapshot["config"]["codex"] = str(codex)
    safe = sentinel(home / ".config/credentials/key.json")
    assert runner.validate_host_credential_path(safe, boundary.snapshot) == safe
    for protected in (codex.with_name("not-created-sidecar-key.json"), home / "codex-package.json"):
        with pytest.raises(ValueError, match="agent-visible"):
            runner.validate_host_credential_path(protected, boundary.snapshot)


def test_shared_key_is_guarded_before_read_or_verification(boundary, monkeypatch):
    import harness.openrouter
    boundary.snapshot["config"]["budget_policy"] = "local-actual-cost-v1"
    monkeypatch.setattr(harness.openrouter, "InferenceKeyFile",
        lambda *a, **k: pytest.fail("must reject exposed key path first"))
    with pytest.raises(ValueError, match="agent-visible"):
        runner._credential_arguments(boundary.snapshot, api_key_file=boundary.projects[-1] / "key")


def test_shared_run_binds_key_before_workers_and_never_rebinds_on_resume(boundary, monkeypatch):
    import hashlib
    from harness.openrouter import InferenceKeyFile
    boundary.snapshot["config"]["budget_policy"] = "local-actual-cost-v1"
    path = sentinel(boundary.private / "shared.key")
    verifications = []
    def verify(source):
        verifications.append("GET /key")
        return {"key_sha256": hashlib.sha256(source.credential().encode()).hexdigest()}
    monkeypatch.setattr(InferenceKeyFile, "verify", verify)
    argv = runner._credential_arguments(boundary.snapshot, api_key_file=path)
    assert argv == ["--api-key-file", str(path)] and SENTINEL not in repr(argv)
    bound = (boundary.run / "credential-identity.json").read_bytes()
    assert SENTINEL.encode() not in bound
    assert runner._credential_arguments(boundary.snapshot, api_key_file=path) == argv
    assert (boundary.run / "credential-identity.json").read_bytes() == bound
    path.write_text("different-synthetic-key")
    monkeypatch.setattr(runner, "load_snapshot", lambda *a, **k: boundary.snapshot)
    monkeypatch.setattr(runner.subprocess, "Popen", lambda *a, **k: pytest.fail("no worker may dispatch"))
    with pytest.raises(ValueError, match="immutable"):
        runner.run(boundary.run, api_key_file=path, resume=True)
    assert len(verifications) == 3 and (boundary.run / "credential-identity.json").read_bytes() == bound


def test_shared_preflight_checks_later_proof_fingerprint_before_any_dispatch(boundary, monkeypatch):
    from harness.openrouter import InferenceKeyFile
    boundary.snapshot["config"]["budget_policy"] = "local-actual-cost-v1"
    path = sentinel(boundary.private / "shared.key")
    monkeypatch.setattr(InferenceKeyFile, "verify", lambda source: {"key_sha256": "verified-key"})
    billing = runner.proof_root(boundary.run, boundary.snapshot["proofs"][-1]) / "billing"
    billing.mkdir(parents=True)
    (billing / "relay-key-identity.json").write_text(json.dumps({"schema_version": 1, "key_sha256": "different-key"}))
    monkeypatch.setattr(runner, "load_snapshot", lambda *a, **k: boundary.snapshot)
    monkeypatch.setattr(runner.subprocess, "Popen", lambda *a, **k: pytest.fail("no worker may dispatch"))
    with pytest.raises(ValueError, match="Proof credential identity differs"):
        runner.run(boundary.run, api_key_file=path)


def test_credential_sources_and_frozen_policy_must_agree(boundary):
    path = boundary.private / "not-read.key"
    with pytest.raises(ValueError, match="Choose either"):
        runner._credential_arguments(boundary.snapshot, key_store=path, api_key_file=path)
    with pytest.raises(ValueError, match="local-actual-cost-v1"):
        runner._credential_arguments(boundary.snapshot, api_key_file=path)
    boundary.snapshot["config"]["budget_policy"] = "local-actual-cost-v1"
    with pytest.raises(ValueError, match="provider-key-v1"):
        runner._credential_arguments(boundary.snapshot, key_store=path)


def test_public_cli_rejects_legacy_key_store(boundary):
    with pytest.raises(SystemExit) as failure:
        cli.main(["resume", str(boundary.run), "--api-key-file", "unused", "--key-store", "unused"])
    assert failure.value.code == 2


@pytest.mark.parametrize("other_publishing", [False, True])
def test_shared_private_worker_receives_host_provider_without_secret_argv_or_env(boundary, monkeypatch, other_publishing):
    from e6 import run as core
    from harness.openrouter import InferenceKeyFile
    import hashlib
    boundary.snapshot["config"]["budget_policy"] = "local-actual-cost-v1"
    path = sentinel(boundary.private / "shared.key")
    monkeypatch.setattr(InferenceKeyFile, "verify",
        lambda source: {"key_sha256": hashlib.sha256(source.credential().encode()).hexdigest()})
    runner._credential_arguments(boundary.snapshot, api_key_file=path)
    if other_publishing:
        # Another worker's exclusive create precedes its complete JSON write.
        # Worker startup must use the run binding rather than reading that file.
        sibling = runner.proof_root(boundary.run, boundary.snapshot["proofs"][-1]) / "billing"
        sibling.mkdir(parents=True)
        (sibling / "relay-key-identity.json").write_text("")
    monkeypatch.setattr(runner, "load_snapshot", lambda *a, **k: boundary.snapshot)
    def prepare(cell, *args):
        runner.write(cell / "config.json", {"product_schema_version": 1, "tool_preflight_sha256": "synthetic"})
    monkeypatch.setattr(core, "prepare_product", prepare)
    def execute(cell, *, auth_path, credential_provider, resume):
        assert auth_path is None and credential_provider() == SENTINEL and resume is True
        assert all(SENTINEL not in value for value in runner.worker_environment().values())
        return 0
    monkeypatch.setattr(core, "run_product", execute)
    assert runner.run_proof(boundary.run, "proof-0", api_key_file=path, resume=True) == 0


def test_cli_resume_forwards_shared_file_source(boundary, monkeypatch):
    received = []
    monkeypatch.setattr(runner, "run", lambda root, **kwargs: received.append((root, kwargs)) or 0)
    assert cli.main(["resume", str(boundary.run), "--api-key-file", "/host/private/ordinary.key"]) == 0
    assert received == [(boundary.run, {"api_key_file": Path("/host/private/ordinary.key"),
        "key_store": None, "resume": True})]


def test_public_cli_has_no_management_key_provisioning():
    with pytest.raises(SystemExit) as failure:
        cli.main(["keys", "provision", "/unused"])
    assert failure.value.code == 2


def test_public_cli_export_accepts_exactly_one_run(tmp_path, monkeypatch):
    monkeypatch.setattr("harness.export.export_run", lambda *a, **k: pytest.fail("must reject extra roots before export"))
    with pytest.raises(SystemExit) as failure:
        cli.main(["export", str(tmp_path / "a"), str(tmp_path / "b"), "--output", str(tmp_path / "out.jsonl")])
    assert failure.value.code == 2
