"""Portable environment setup checks; all projects and tools are synthetic."""
from __future__ import annotations

import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tarfile
from types import SimpleNamespace
import zipfile

import pytest


def digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def tar_pack(path: Path, members: list[tuple[str, bytes | None, bytes | None]]) -> Path:
    """Write tiny regular files, or a symlink when its link target is supplied."""
    with tarfile.open(path, "w:gz") as stream:
        for name, contents, link in members:
            member = tarfile.TarInfo(name)
            if link is not None:
                member.type = tarfile.SYMTYPE
                member.linkname = link.decode()
                stream.addfile(member)
            else:
                contents = contents or b""
                member.size = len(contents)
                stream.addfile(member, io.BytesIO(contents))
    return path


def source_archive(path: Path, files: dict[str, str], revision: str) -> None:
    """A tiny immutable, codeload-shaped checkout without Git metadata."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(path, "w") as archive:
        for name, contents in files.items():
            archive.writestr("portable-" + revision + "/" + name, contents)


@pytest.fixture
def tiny_environment(tmp_path):
    root = tmp_path / "source-project"
    root.mkdir()
    revision = "a" * 40
    files = {
        "lean-toolchain": "leanprover/lean4:v4.29.1\n",
        "lakefile.toml": 'name = "portable_fixture"\nversion = "0.1.0"\ndefaultTargets = []\n',
        "lake-manifest.json": json.dumps({"version": "1.1.0", "packagesDir": ".lake/packages",
            "packages": [], "name": "portable_fixture", "lakeDir": ".lake"}) + "\n",
        "Example.lean": "theorem example : True := by trivial\n",
    }
    for name, contents in files.items():
        (root / name).write_text(contents)
    (root / ".lrh-stage.json").write_text(json.dumps({"schema_version": 1, "kind": "repository",
        "lean_version": "v4.29.1", "revision": revision}) + "\n")
    spec = {"repository": "https://github.com/example/portable", "lean_version": "v4.29.1",
        "revision": revision, "kind": "repository", "lean_commit": "b" * 40,
        "required_files": {name: digest(contents.encode()) for name, contents in files.items()}}
    requirements = {"schema_version": 1, "snapshots": {"snapshot-fixture": spec}, "tasks": {}}
    requirements_path = tmp_path / "requirements.json"
    requirements_path.write_text(json.dumps(requirements))
    mapping = tmp_path / "environments.toml"
    mapping.write_text('schema_version = 1\n'
        f'elan_home = "{tmp_path / "elan"}"\n'
        'requirements = "requirements.json"\n[paths]\n'
        f'snapshot-fixture = "{root}"\n')
    row = {"name": "example", "source": "strata", "statement": "theorem example : True",
        "src": files["Example.lean"].strip(), "header": "", "file_path": "Example.lean",
        "url": spec["repository"], "start_line": 1, "end_line": 1, "proof_length": 3,
        "num_lines": 1, "version_info": [{"v4.29.1": revision}]}
    benchmark = tmp_path / "benchmark.jsonl"
    benchmark.write_text(json.dumps(row) + "\n")
    archives = tmp_path / "source-archives"
    cached_archive = archives / ("example-portable-" + revision + ".zip")
    source_archive(cached_archive, files, revision)
    return {"root": root, "spec": spec, "requirements": requirements, "mapping": mapping,
        "benchmark": benchmark, "row": row, "files": files, "archives": archives,
        "archive": cached_archive}


def setup_manifest(tmp_path, tiny_environment):
    pack = tar_pack(tmp_path / "fixture.tar.gz", [
        (name, value.encode(), None) for name, value in tiny_environment["files"].items()
    ])
    manifest = {"schema_version": 1, "format": "lean-project-sources-tar-gzip-v1",
        "requirements": tiny_environment["requirements"],
        "rows": [tiny_environment["row"]], "snapshots": {"snapshot-fixture": {
            "pack": pack.name, "sha256": digest(pack.read_bytes()), "bytes": pack.stat().st_size,
            "overlays": {name: contents for name, contents in tiny_environment["files"].items()
                if name != "Example.lean"}}}}
    path = tmp_path / "environment-setup.json"
    path.write_text(json.dumps(manifest))
    return path, manifest


def test_unpack_preserves_project_bytes(tmp_path):
    from scripts.setup_environments import unpack_source

    contents = b"import Init\n-- exact source bytes\n"
    pack = tar_pack(tmp_path / "ok.tar.gz", [("Project/Example.lean", contents, None)])
    destination = tmp_path / "installed"
    unpack_source(pack, destination)
    assert (destination / "Project/Example.lean").read_bytes() == contents


@pytest.mark.parametrize("name", ("../escaped.lean", "/absolute.lean", "safe/../../escaped.lean"))
def test_unpack_rejects_archive_path_escape(tmp_path, name):
    from scripts.setup_environments import unpack_source

    pack = tar_pack(tmp_path / "bad.tar.gz", [(name, b"untrusted", None)])
    with pytest.raises((ValueError, RuntimeError)):
        unpack_source(pack, tmp_path / "installed")
    assert not (tmp_path / "escaped.lean").exists()


@pytest.mark.parametrize("link", (b"../outside", b"inside"))
def test_unpack_rejects_links_even_when_relative(tmp_path, link):
    from scripts.setup_environments import unpack_source

    pack = tar_pack(tmp_path / "link.tar.gz", [("linked", None, link)])
    with pytest.raises((ValueError, RuntimeError)):
        unpack_source(pack, tmp_path / "installed")


def test_unpack_rejects_duplicate_archive_member(tmp_path):
    from scripts.setup_environments import unpack_source

    pack = tar_pack(tmp_path / "duplicate.tar.gz", [
        ("Example.lean", b"first", None), ("Example.lean", b"second", None)])
    with pytest.raises((ValueError, RuntimeError)):
        unpack_source(pack, tmp_path / "installed")


def test_unpack_materializes_required_empty_git_dirs_for_detached_shallow_dependency(tmp_path, source_alias_project):
    from scripts.export_environment_sources import git_metadata
    from scripts.setup_environments import unpack_source

    package, revision = source_alias_project
    env = dict(os.environ, GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL="/dev/null")
    branch = subprocess.check_output(["git", "-C", str(package), "symbolic-ref", "--short", "HEAD"],
                                     env=env, text=True).strip()
    subprocess.run(["git", "-C", str(package), "checkout", "--detach", "-q"], env=env, check=True)
    subprocess.run(["git", "-C", str(package), "branch", "-D", branch], env=env, check=True, capture_output=True)
    (package / ".git/shallow").write_text(revision + "\n")
    url = "https://github.com/example/detached"
    metadata = list(git_metadata(package, revision, url))
    assert not any(name.startswith(".git/refs/") for name, _, _ in metadata)
    pack = tar_pack(tmp_path / "detached.tar.gz", [(name, data, None) for name, data, _ in metadata])
    restored = tmp_path / "restored"
    unpack_source(pack, restored)
    assert (restored / ".git/refs").is_dir()
    assert (restored / ".git/objects").is_dir()
    for arguments, expected in ((["rev-parse", "HEAD"], revision), (["remote", "get-url", "origin"], url)):
        result = subprocess.check_output(["git", "--git-dir", str(restored / ".git"), *arguments],
                                         env=env, text=True).strip()
        assert result == expected


def test_unpack_empty_git_dir_restoration_cannot_follow_archive_alias(tmp_path):
    from scripts.setup_environments import unpack_source

    outside = tmp_path / "outside"
    outside.mkdir()
    pack = tar_pack(tmp_path / "git-alias.tar.gz", [(".git/HEAD", b"ref: refs/heads/main\n", None),
        (".git/objects", None, b"../../outside")])
    with pytest.raises(ValueError, match="links/special files"):
        unpack_source(pack, tmp_path / "restored")
    assert list(outside.iterdir()) == []


@pytest.mark.parametrize("kind", (tarfile.LNKTYPE, tarfile.FIFOTYPE, tarfile.CHRTYPE))
def test_unpack_rejects_hard_links_and_special_files(tmp_path, kind):
    from scripts.setup_environments import unpack_source

    pack = tmp_path / "special.tar.gz"
    with tarfile.open(pack, "w:gz") as archive:
        member = tarfile.TarInfo("special")
        member.type = kind
        member.linkname = "Example.lean"
        archive.addfile(member)
    with pytest.raises((ValueError, RuntimeError)):
        unpack_source(pack, tmp_path / "installed")


def test_setup_manifest_cannot_reference_pack_outside_bundle(tmp_path, tiny_environment):
    from scripts.setup_environments import load_setup

    path, value = setup_manifest(tmp_path, tiny_environment)
    value["snapshots"]["snapshot-fixture"]["pack"] = "../external.tar.gz"
    path.write_text(json.dumps(value))
    with pytest.raises((ValueError, RuntimeError)):
        load_setup(path)


def test_dry_run_does_not_create_output_or_launch_tools(tmp_path, tiny_environment, monkeypatch):
    from scripts.setup_environments import install

    path, _ = setup_manifest(tmp_path, tiny_environment)
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("dry-run launched a process"))
    monkeypatch.setattr(subprocess, "check_output", lambda *a, **k: pytest.fail("dry-run launched a process"))
    output = tmp_path / "generated" / "environments.toml"
    environments = tmp_path / "managed-environments"
    result = install(path, environments, tmp_path / "missing-elan", output, dry_run=True)
    assert result["status"] == "plan"
    assert result["snapshots"][0]["pack_present"] is True
    assert "missing supplied toolchain file" in result["snapshots"][0]["toolchain_problem"]
    assert not output.parent.exists()
    assert not environments.exists()


def test_missing_pack_has_actionable_error_and_no_published_state(tmp_path, tiny_environment, monkeypatch):
    from scripts import setup_environments as setup

    path, value = setup_manifest(tmp_path, tiny_environment)
    (tmp_path / value["snapshots"]["snapshot-fixture"]["pack"]).unlink()
    monkeypatch.setattr(setup, "toolchain_problem", lambda *args: None)
    managed = tmp_path / "managed"
    output = tmp_path / "output.toml"
    with pytest.raises(ValueError, match="Missing bundled source pack.*export_environment_sources"):
        setup.install(path, managed, tmp_path / "elan", output)
    assert not managed.exists()
    assert not output.exists()


def test_corrupt_pack_is_rejected_before_install(tmp_path, tiny_environment, monkeypatch):
    from scripts import setup_environments as setup

    path, value = setup_manifest(tmp_path, tiny_environment)
    pack = tmp_path / value["snapshots"]["snapshot-fixture"]["pack"]
    pack.write_bytes(pack.read_bytes() + b"corruption")
    monkeypatch.setattr(setup, "toolchain_problem", lambda *args: None)
    monkeypatch.setattr(setup, "prepare_snapshot", lambda *args: pytest.fail("corrupt pack reached build"))
    with pytest.raises((ValueError, RuntimeError), match="SHA-256"):
        setup.install(path, tmp_path / "managed", tmp_path / "elan", tmp_path / "output.toml")
    assert not (tmp_path / "output.toml").exists()


def fake_acceptance(monkeypatch):
    from scripts import setup_environments as setup

    monkeypatch.setattr(setup, "toolchain_problem", lambda *args: None)
    monkeypatch.setattr(setup, "validate_snapshot", lambda *args, **kwargs: {})
    monkeypatch.setattr(setup, "validate_dependencies", lambda *args, **kwargs: {})
    return setup


def test_failed_setup_resumes_at_stable_path_and_ready_setup_is_reused(tmp_path, tiny_environment, monkeypatch):
    setup = fake_acceptance(monkeypatch)
    path, _ = setup_manifest(tmp_path, tiny_environment)
    managed = tmp_path / "managed"
    stable_root = managed / "snapshot-fixture"
    output = tmp_path / "output.toml"
    calls = []

    def prepare(root, *args):
        assert root == stable_root
        assert (root / "Example.lean").read_text() == tiny_environment["files"]["Example.lean"]
        calls.append(root)
        if len(calls) == 1:
            # Preserve expensive partial progress across an interrupted build.
            (root / "completed-dependency.olean").write_bytes(b"cached dependency")
            raise RuntimeError("synthetic interrupted build")
        assert (root / "completed-dependency.olean").read_bytes() == b"cached dependency"
        return {"completed": True}

    monkeypatch.setattr(setup, "prepare_snapshot", prepare)
    with pytest.raises(RuntimeError, match="interrupted build"):
        setup.install(path, managed, tmp_path / "elan", output)
    assert not output.exists()
    assert json.loads((stable_root / setup.RECEIPT).read_text())["status"] == "incomplete"
    setup.install(path, managed, tmp_path / "elan", output)
    assert output.is_file()
    assert json.loads((stable_root / setup.RECEIPT).read_text())["status"] == "ready"
    # Publishing another map must revalidate without repeating finished builds.
    setup.install(path, managed, tmp_path / "elan", tmp_path / "second-map.toml")
    assert len(calls) == 2


def test_validation_failure_does_not_publish_map_or_ready_receipt(tmp_path, tiny_environment, monkeypatch):
    setup = fake_acceptance(monkeypatch)
    path, _ = setup_manifest(tmp_path, tiny_environment)
    monkeypatch.setattr(setup, "prepare_snapshot", lambda *args: {})

    def invalid(*args, **kwargs):
        raise ValueError("original import closure is missing")

    monkeypatch.setattr(setup, "validate_dependencies", invalid)
    managed = tmp_path / "managed"
    output = tmp_path / "output.toml"
    with pytest.raises(ValueError, match="import closure"):
        setup.install(path, managed, tmp_path / "elan", output)
    assert not output.exists()
    assert json.loads((managed / "snapshot-fixture" / setup.RECEIPT).read_text())["status"] == "incomplete"


def test_adopted_root_is_read_only_and_does_not_require_source_pack(tmp_path, tiny_environment, monkeypatch):
    setup = fake_acceptance(monkeypatch)
    path, value = setup_manifest(tmp_path, tiny_environment)
    (tmp_path / value["snapshots"]["snapshot-fixture"]["pack"]).unlink()
    source = tiny_environment["root"]
    before = {entry.relative_to(source): entry.read_bytes() for entry in source.rglob("*") if entry.is_file()}
    checked = []
    monkeypatch.setattr(setup, "prepare_snapshot", lambda *args: pytest.fail("adopted root reached build"))
    monkeypatch.setattr(setup, "validate_snapshot", lambda *args, **kwargs: checked.append("snapshot"))
    monkeypatch.setattr(setup, "validate_dependencies", lambda *args, **kwargs: checked.append("dependencies"))
    output = tmp_path / "output.toml"
    result = setup.install(path, tmp_path / "managed", tmp_path / "elan", output,
        reuse_map=tiny_environment["mapping"])
    assert result["snapshots"] == [{"snapshot_id": "snapshot-fixture", "status": "reused"}]
    assert checked == ["snapshot", "dependencies"]
    after = {entry.relative_to(source): entry.read_bytes() for entry in source.rglob("*") if entry.is_file()}
    assert before == after
    assert not (source / setup.RECEIPT).exists()


def test_unmanaged_existing_root_is_preserved(tmp_path, tiny_environment, monkeypatch):
    setup = fake_acceptance(monkeypatch)
    path, _ = setup_manifest(tmp_path, tiny_environment)
    root = tmp_path / "managed" / "snapshot-fixture"
    root.mkdir(parents=True)
    sentinel = root / "user-file"
    sentinel.write_bytes(b"unrelated data")
    monkeypatch.setattr(setup, "prepare_snapshot", lambda *args: pytest.fail("unmanaged root reached build"))
    with pytest.raises(ValueError, match="unmanaged"):
        setup.install(path, root.parent, tmp_path / "elan", tmp_path / "output.toml")
    assert list(root.iterdir()) == [sentinel]
    assert sentinel.read_bytes() == b"unrelated data"


def test_export_keeps_exact_sources_and_excludes_host_state(tmp_path, tiny_environment):
    from scripts.export_environment_sources import export_sources

    root = tiny_environment["root"]
    for name in (".lake/build/lib/lean/Example.olean", ".lake/config/0/lakefile.olean"):
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("host state must not be shipped")
    output = tmp_path / "source-distribution"
    export_sources(tiny_environment["mapping"], output, benchmark_path=tiny_environment["benchmark"],
        source_archives=tiny_environment["archives"])
    manifest_path = output / "environment-setup.json"
    contents = manifest_path.read_text()
    assert str(tmp_path) not in contents
    manifest = json.loads(contents)
    spec = manifest["snapshots"]["snapshot-fixture"]
    pack = output / spec["pack"]
    assert digest(pack.read_bytes()) == spec["sha256"]
    with tarfile.open(pack) as archive:
        names = set(archive.getnames())
        source = archive.extractfile("Example.lean")
        assert source is not None
        assert source.read() == tiny_environment["files"]["Example.lean"].encode()
    assert not any(".lake/build/" in name or ".lake/config/" in name for name in names)
    assert ".git/config" not in names
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        assert spec["overlays"][name] == tiny_environment["files"][name]


def test_export_does_not_overwrite_existing_output(tmp_path, tiny_environment):
    from scripts.export_environment_sources import export_sources

    output = tmp_path / "source-distribution"
    output.mkdir()
    sentinel = output / "unrelated.txt"
    sentinel.write_text("preserve me")
    with pytest.raises((ValueError, RuntimeError, FileExistsError)):
        export_sources(tiny_environment["mapping"], output, benchmark_path=tiny_environment["benchmark"],
            source_archives=tiny_environment["archives"])
    assert sentinel.read_text() == "preserve me"


@pytest.mark.parametrize("damage", ("modified", "untracked", "missing"))
def test_export_authenticates_sources_beyond_required_file_hashes(tmp_path, tiny_environment, damage):
    from scripts.export_environment_sources import export_sources

    root = tiny_environment["root"]
    if damage in {"modified", "missing"}:
        # This file deliberately does not occur in required_files. The pinned
        # archive, rather than the sparse runtime guard, must authenticate it.
        upstream = {**tiny_environment["files"], "Extra.lean": "def extra : Nat := 1\n"}
        source_archive(tiny_environment["archive"], upstream, tiny_environment["spec"]["revision"])
        if damage == "modified":
            (root / "Extra.lean").write_text("def extra : Nat := 2\n")
    else:
        (root / "Untracked.lean").write_text("def untracked : Nat := 1\n")
    output = tmp_path / "source-distribution"
    with pytest.raises(ValueError, match="(?i)(source|archive|tracked|revision|snapshot)"):
        export_sources(tiny_environment["mapping"], output, benchmark_path=tiny_environment["benchmark"],
            source_archives=tiny_environment["archives"])
    assert not (output / "environment-setup.json").exists()


def test_archive_authenticated_export_requires_local_provenance_without_fetching(tmp_path, tiny_environment, monkeypatch):
    from scripts.export_environment_sources import export_sources

    tiny_environment["archive"].unlink()
    monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: pytest.fail("export launched a command"))
    output = tmp_path / "source-distribution"
    with pytest.raises(ValueError, match="Missing unique original source archive.*source-archives"):
        export_sources(tiny_environment["mapping"], output, benchmark_path=tiny_environment["benchmark"],
            source_archives=tiny_environment["archives"])
    assert not (output / "environment-setup.json").exists()


@pytest.mark.parametrize("damage", (None, "modified", "untracked", "missing"))
def test_export_git_dependency_authenticates_code_and_sanitizes_config(tmp_path, tiny_environment, damage):
    from scripts.export_environment_sources import export_sources
    from scripts.setup_environments import unpack_source

    root = tiny_environment["root"]
    package = root / ".lake/packages/testdep"
    package.mkdir(parents=True)
    (package / "lakefile.toml").write_text('name = "testdep"\nversion = "0.1.0"\n')
    (package / "Dependency.lean").write_text("def dependency : Nat := 1\n")
    child = dict(os.environ, GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL="/dev/null")

    def git(*args):
        return subprocess.check_output(["git", "-C", str(package), *args], env=child,
            text=True, stderr=subprocess.PIPE).strip()

    git("init", "-q")
    git("add", "lakefile.toml", "Dependency.lean")
    git("-c", "user.name=Source Fixture", "-c", "user.email=fixture@example.invalid",
        "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgsign=false", "commit", "-qm", "fixture")
    revision = git("rev-parse", "HEAD")
    git("tag", "v0.1.0")
    git("config", "credential.helper", "/private/personal/helper")
    git("config", "include.path", "/private/personal/config")
    (package / ".git/hooks/personal-hook").write_text("personal hook must not be exported")
    root_manifest = json.loads((root / "lake-manifest.json").read_text())
    root_manifest["packages"].append({"name": "testdep", "type": "git",
        "url": "https://github.com/example/testdep", "rev": revision,
        "inputRev": "v0.1.0", "subDir": None})
    encoded_manifest = json.dumps(root_manifest) + "\n"
    (root / "lake-manifest.json").write_text(encoded_manifest)
    requirements = tiny_environment["requirements"]
    requirements["snapshots"]["snapshot-fixture"]["required_files"]["lake-manifest.json"] = digest(encoded_manifest.encode())
    (tmp_path / "requirements.json").write_text(json.dumps(requirements))
    output = tmp_path / "source-distribution"
    if damage:
        if damage == "modified":
            (package / "Dependency.lean").write_text("def dependency : Nat := 2\n")
        elif damage == "missing":
            (package / "Dependency.lean").unlink()
        else:
            (package / "Untracked.lean").write_text("def injected : Nat := 3\n")
        with pytest.raises(ValueError, match="(?i)(source|archive|tracked|revision|blob|HEAD)"):
            export_sources(tiny_environment["mapping"], output, benchmark_path=tiny_environment["benchmark"],
                source_archives=tiny_environment["archives"])
        assert not (output / "environment-setup.json").exists()
        return
    export_sources(tiny_environment["mapping"], output, benchmark_path=tiny_environment["benchmark"],
        source_archives=tiny_environment["archives"])
    setup = json.loads((output / "environment-setup.json").read_text())
    unpacked = tmp_path / "unpacked"
    unpack_source(output / setup["snapshots"]["snapshot-fixture"]["pack"], unpacked)
    restored = unpacked / ".lake/packages/testdep"
    config = (restored / ".git/config").read_text()
    assert "https://github.com/example/testdep" in config
    assert "/private/" not in config and "credential" not in config and "include" not in config
    assert not (restored / ".git/hooks").exists()
    restored_head = subprocess.check_output(["git", "-C", str(restored), "rev-parse", "HEAD"],
        env=child, text=True).strip()
    assert restored_head == revision
    subprocess.run(["git", "-C", str(restored), "cat-file", "-e", revision + "^{commit}"],
        env=child, check=True)
    assert subprocess.check_output(["git", "-C", str(restored), "rev-parse", "v0.1.0"],
        env=child, text=True).strip() == revision


def fixture_release_root(tmp_path):
    from scripts.build_bundle import FILES

    root = tmp_path / "release-source"
    root.mkdir()
    for name in FILES:
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("release fixture\n")
    (root / "configs").mkdir(exist_ok=True)
    return root


def test_contest_bundle_includes_verified_environment_sources(tmp_path, tiny_environment):
    from scripts.build_bundle import build

    path, value = setup_manifest(tmp_path, tiny_environment)
    root = fixture_release_root(tmp_path)
    output = tmp_path / "contest.zip"
    result = build(output, root=root, environment_setup=path)
    assert result["includes_environment_sources"] is True
    with zipfile.ZipFile(output) as archive:
        setup_name = "lean-refactor-harness/environment-sources/environment-setup.json"
        pack_name = "lean-refactor-harness/environment-sources/" + value["snapshots"]["snapshot-fixture"]["pack"]
        assert archive.read(setup_name) == path.read_bytes()
        expected = value["snapshots"]["snapshot-fixture"]["sha256"]
        assert digest(archive.read(pack_name)) == expected
        release = json.loads(archive.read("lean-refactor-harness/release-manifest.json"))
        assert release["includes_environment_sources"] is True
        assert release["files"][pack_name.removeprefix("lean-refactor-harness/")] == expected


@pytest.mark.parametrize("damage", ("missing", "changed"))
def test_bundle_rejects_missing_or_changed_environment_pack(tmp_path, tiny_environment, damage):
    from scripts.build_bundle import build

    path, value = setup_manifest(tmp_path, tiny_environment)
    pack = tmp_path / value["snapshots"]["snapshot-fixture"]["pack"]
    if damage == "missing":
        pack.unlink()
    else:
        pack.write_bytes(pack.read_bytes() + b"alteration")
    root = fixture_release_root(tmp_path)
    output = tmp_path / "contest.zip"
    with pytest.raises(ValueError, match="Missing or changed source pack"):
        build(output, root=root, environment_setup=path)
    assert not output.exists()
    assert not output.with_suffix(".zip.part").exists()


def test_thin_bundle_reports_absence_of_environment_sources(tmp_path):
    from scripts.build_bundle import build

    result = build(tmp_path / "thin.zip", root=fixture_release_root(tmp_path))
    assert result["includes_environment_sources"] is False
    with zipfile.ZipFile(result["archive"]) as archive:
        release = json.loads(archive.read("lean-refactor-harness/release-manifest.json"))
        assert release["includes_environment_sources"] is False
        assert not any("/environment-sources/" in name for name in archive.namelist())


@pytest.fixture
def source_alias_project(tmp_path):
    root = tmp_path / "alias-project"
    root.mkdir()
    (root / "lake-manifest.json").write_text('{"packages": []}\n')
    (root / "canonical").mkdir()
    (root / "canonical/Entry.lean").write_text("def entry : Nat := 7\n")
    (root / "alias").symlink_to("canonical", target_is_directory=True)
    (root / "Entry.lean").symlink_to("canonical/Entry.lean")
    child = dict(os.environ, GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL="/dev/null")

    def git(*args):
        return subprocess.check_output(["git", "-C", str(root), *args], env=child,
                                       text=True, stderr=subprocess.PIPE).strip()

    git("init", "-q")
    git("add", ".")
    git("-c", "user.name=Source Fixture", "-c", "user.email=fixture@example.invalid",
        "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgsign=false", "commit", "-qm", "fixture")
    return root, git("rev-parse", "HEAD")


@pytest.mark.parametrize("authority", ("git", "zip", "zip-link-text"))
def test_export_materializes_authenticated_internal_aliases_as_regular_files(tmp_path, source_alias_project, authority):
    from scripts.export_environment_sources import write_pack
    from scripts.setup_environments import unpack_source

    root, revision = source_alias_project
    archives = tmp_path / "archives"
    archives.mkdir()
    if authority.startswith("zip"):
        with zipfile.ZipFile(archives / ("example-alias-" + revision + ".zip"), "w") as archive:
            for name in ("lake-manifest.json", "canonical/Entry.lean", "alias", "Entry.lean"):
                path = root / name
                item = zipfile.ZipInfo("checkout/" + name)
                item.create_system = 3
                item.external_attr = (0o120777 if path.is_symlink() else 0o100644) << 16
                archive.writestr(item, os.readlink(path).encode() if path.is_symlink() else path.read_bytes())
        # Rename the Git marker to simulate an original extracted source ZIP.
        (root / ".git").rename(tmp_path / "saved-git")
        if authority == "zip-link-text":
            (root / "Entry.lean").unlink()
            (root / "Entry.lean").write_bytes(b"canonical/Entry.lean")
    spec = {"repository": "https://github.com/example/alias", "revision": revision}
    pack = tmp_path / "aliases.tar.gz"
    provenance = write_pack(root, spec, pack, archives)
    expected_aliases = {"alias"} if authority == "zip-link-text" else {"alias", "Entry.lean"}
    assert {item["path"] for item in provenance[0]["materialized_aliases"]} == expected_aliases
    if authority == "zip-link-text":
        assert provenance[0]["archive_link_texts"][0]["path"] == "Entry.lean"
    with tarfile.open(pack) as archive:
        assert all(member.isfile() for member in archive)
    restored = tmp_path / "restored"
    unpack_source(pack, restored)
    for name in ("canonical/Entry.lean", "alias/Entry.lean", "Entry.lean"):
        expected = (b"canonical/Entry.lean" if name == "Entry.lean" and authority == "zip-link-text"
                    else (root / "canonical/Entry.lean").read_bytes())
        assert (restored / name).read_bytes() == expected
        assert not (restored / name).is_symlink()


@pytest.mark.parametrize("damage", ("pointer", "untracked-pointer", "target", "replacement"))
def test_export_rejects_changed_alias_authority_and_target_bytes(tmp_path, source_alias_project, damage):
    from scripts.export_environment_sources import authenticate_tree

    root, revision = source_alias_project
    if damage == "pointer":
        (root / "Entry.lean").unlink()
        (root / "Entry.lean").symlink_to("alias/Entry.lean")
    elif damage == "untracked-pointer":
        (root / "Untracked.lean").symlink_to("canonical/Entry.lean")
    elif damage == "target":
        (root / "canonical/Entry.lean").write_text("def injected : Nat := 8\n")
    else:
        (root / "Entry.lean").unlink()
        (root / "Entry.lean").write_text("def entry : Nat := 7\n")
    with pytest.raises(ValueError, match="(?i)(source|symlink|tracked)"):
        authenticate_tree(root, "https://github.com/example/alias", revision, None)


@pytest.mark.parametrize("target", ("../outside", ".", ".git"))
def test_export_rejects_escape_cycle_and_build_state_aliases(tmp_path, source_alias_project, target):
    from scripts.export_environment_sources import authenticate_tree

    root, revision = source_alias_project
    (tmp_path / "outside").mkdir()
    (root / "alias").unlink()
    (root / "alias").symlink_to(target, target_is_directory=True)
    with pytest.raises((ValueError, RuntimeError)):
        authenticate_tree(root, "https://github.com/example/alias", revision, None)


def test_export_omits_only_the_known_proofwidgets_generated_lock_hash(tmp_path, source_alias_project):
    from scripts.export_environment_sources import authenticate_tree, source_files

    root, revision = source_alias_project
    (root / "widget").mkdir()
    (root / "widget/package-lock.json.hash").write_text("generated Lake input hash")
    authenticate_tree(root, "https://github.com/example/alias", revision, None)
    assert "widget/package-lock.json.hash" not in {name for name, _ in source_files(root)}
    for name in ("widget/package-lock.json", "widget/component.js", "Other.lean", "untracked.hash"):
        path = root / name
        path.write_text("untracked source must still fail")
        with pytest.raises(ValueError, match="untracked source"):
            authenticate_tree(root, "https://github.com/example/alias", revision, None)
        path.unlink()


@pytest.mark.parametrize("damage", (None, "stage-revision", "stage-toolchain", "dependency-revision", "repository"))
def test_generated_putnam_kind_requires_matching_stage_and_mathlib_pins(tmp_path, damage):
    from scripts.export_environment_sources import authenticate_tree, OVERLAYS, project_kind

    root = tmp_path / "generated-putnam"
    root.mkdir()
    revision = "a" * 40
    spec = {"repository": "https://github.com/leanprover-community/mathlib4", "revision": revision,
            "lean_version": "v4.31.0"}  # Older requirement maps omit kind.
    stage = {"kind": "putnam", "lean_version": spec["lean_version"], "mathlib_revision": revision}
    package = {"name": "mathlib", "type": "path", "dir": ".lake/packages/mathlib",
               "url": spec["repository"], "rev": revision}
    if damage == "stage-revision":
        stage["mathlib_revision"] = "b" * 40
    elif damage == "stage-toolchain":
        stage["lean_version"] = "v4.30.0"
    elif damage == "dependency-revision":
        package["rev"] = "b" * 40
    elif damage == "repository":
        spec["repository"] = package["url"] = "https://github.com/example/other"
    (root / ".lrh-stage.json").write_text(json.dumps(stage))
    (root / "lake-manifest.json").write_text(json.dumps({"packages": [package]}))
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.31.0\n")
    if damage:
        with pytest.raises(ValueError, match="matching pinned stage/Mathlib"):
            project_kind(root, spec)
        return
    assert project_kind(root, spec) == "putnam"
    assert authenticate_tree(root, spec["repository"], revision, None,
        overlays=set(OVERLAYS), generated=True) == {"kind": "generated-overlays"}
    (root / "Injected.lean").write_text("def injected : Nat := 1\n")
    with pytest.raises(ValueError, match="unexpected source files"):
        authenticate_tree(root, spec["repository"], revision, None, overlays=set(OVERLAYS), generated=True)


def write_module(root: Path, name: str, contents: str) -> None:
    path = root.joinpath(*name.split(".")).with_suffix(".lean")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents)


def write_graph_manifest(root: Path, packages: list[dict]) -> None:
    root.mkdir(parents=True, exist_ok=True)
    (root / "lake-manifest.json").write_text(json.dumps({"name": "graph_fixture",
        "packagesDir": ".lake/packages", "packages": packages}))


def test_module_build_order_is_dependency_first_across_root_and_package(tmp_path):
    from scripts.setup_environments import module_build_order

    root = tmp_path / "graph"
    write_graph_manifest(root, [{"name": "dep", "type": "path", "dir": "vendor/dep", "subDir": "lean"}])
    dependency = root / "vendor/dep/lean"
    write_module(root, "Top", "import Mid\nimport Dep.Base\nimport Init\n")
    write_module(root, "Mid", "import Dep.Shared\nimport Lean\n")
    write_module(dependency, "Dep.Base", "import Dep.Shared\n")
    write_module(dependency, "Dep.Shared", "import Init\n")
    order = module_build_order(root, ["Top", "Mid"])
    names = [name for _, name, _ in order]
    assert set(names) == {"Top", "Mid", "Dep.Base", "Dep.Shared"}
    assert len(names) == len(set(names))
    assert names.index("Dep.Shared") < names.index("Mid") < names.index("Top")
    assert names.index("Dep.Shared") < names.index("Dep.Base") < names.index("Top")
    assert [(package, name) for package, name, _ in order if name.startswith("Dep.")] == [
        ("dep", "Dep.Shared"), ("dep", "Dep.Base")]
    binaries = {name: binary for _, name, binary in order}
    assert binaries["Top"] == root / ".lake/build/lib/lean/Top.olean"
    assert binaries["Dep.Shared"] == dependency / ".lake/build/lib/lean/Dep/Shared.olean"


def test_module_build_order_rejects_source_import_cycles(tmp_path):
    from scripts.setup_environments import module_build_order

    root = tmp_path / "graph"
    write_graph_manifest(root, [])
    write_module(root, "A", "import B\n")
    write_module(root, "B", "import A\n")
    with pytest.raises(ValueError, match="Cyclic source imports"):
        module_build_order(root, ["A"])


def mathlib_graph(tmp_path):
    root = tmp_path / "graph"
    write_graph_manifest(root, [{"name": "mathlib", "type": "path", "dir": ".lake/packages/mathlib"}])
    mathlib = root / ".lake/packages/mathlib"
    write_module(root, "Local.Entry", "import Mathlib.Top\nimport Init\n")
    write_module(mathlib, "Mathlib.Top", "import Mathlib.Foundation\n")
    write_module(mathlib, "Mathlib.Foundation", "import Init\n")
    return root, mathlib


def test_module_build_order_includes_mathlib_transitive_imports_for_cache_fallback(tmp_path):
    from scripts.setup_environments import module_build_order

    root, mathlib = mathlib_graph(tmp_path)
    order = module_build_order(root, ["Local.Entry"])
    assert [(package, name) for package, name, _ in order] == [
        ("mathlib", "Mathlib.Foundation"), ("mathlib", "Mathlib.Top"), (None, "Local.Entry")]
    assert order[0][2] == mathlib / ".lake/build/lib/lean/Mathlib/Foundation.olean"


def test_import_targets_bounds_cache_arguments_at_first_mathlib_import(tmp_path, monkeypatch):
    from scripts import setup_environments as setup

    root, _ = mathlib_graph(tmp_path)
    monkeypatch.setattr(setup.lean_source, "exact_source_prefix",
        lambda *args: SimpleNamespace(text="import Local.Entry\n"))
    assert setup.import_targets(root, [{"name": "synthetic-proof", "statement": "theorem synthetic : True",
        "src": "theorem synthetic : True := by trivial"}]) == [
        (None, "Local.Entry"), ("mathlib", "Mathlib.Top")]
