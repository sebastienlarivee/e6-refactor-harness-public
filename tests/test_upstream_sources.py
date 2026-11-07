"""Pinned upstream setup tests use tiny local Git repositories, never the network."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

import pytest

from scripts import setup_environments as setup
from scripts import source_fetch as fetch


def git(root: Path, *arguments: str) -> str:
    return subprocess.check_output(["git", "-C", str(root), *arguments], text=True).strip()


def repository(root: Path, files: dict[str, str]) -> str:
    root.mkdir()
    git(root, "init", "-q")
    for name, content in files.items():
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content)
    git(root, "add", ".")
    git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "fixture")
    return git(root, "rev-parse", "HEAD")


@pytest.fixture
def upstream(tmp_path, monkeypatch):
    root, dependency = tmp_path / "origin", tmp_path / "dependency"
    root_revision = repository(root, {"Example.lean": "theorem example : True := by trivial\n",
                                      "README.md": "upstream source\n"})
    (root / "docs").mkdir()
    (root / "docs/README.md").symlink_to("../README.md")
    git(root, "add", ".")
    git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "alias")
    root_revision = git(root, "rev-parse", "HEAD")
    dep_revision = repository(dependency, {"Library.lean": "-- pinned library\n",
        "hax-lib/proof-libs/lean/lakefile.toml": 'name = "hax"\n', "README.md": "whole repository\n"})
    # The advertised repository's current branch advances beyond the requested pin.
    (dependency / "Library.lean").write_text("-- later branch contents\n")
    git(dependency, "add", ".")
    git(dependency, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "later")
    urls = {"https://github.com/example/project": root,
            "https://github.com/leanprover-community/mathlib4": dependency}
    calls = []
    real_fetch = fetch._fetch

    def local_fetch(destination, source):
        calls.append(dict(source))
        # Only the transport is redirected; exact commit fetch/checkout is real Git.
        real_fetch(destination, {**source, "url": str(urls[source["url"]])})

    monkeypatch.setattr(fetch, "_fetch", local_fetch)
    packages = [
        {"name": "mathlib", "type": "path", "dir": ".lake/packages/mathlib",
         "url": "https://github.com/leanprover-community/mathlib4.git", "rev": dep_revision,
         "subDir": None, "inputRev": "main"},
        {"name": "«Hax»", "type": "git", "url": "https://github.com/leanprover-community/mathlib4",
         "rev": dep_revision, "subDir": "hax-lib/proof-libs/lean", "inputRev": "main"},
    ]
    spec = {"repository": "https://github.com/example/project", "revision": root_revision,
        "lean_version": "v4.31.0", "lean_commit": "a" * 40,
        "required_files": {"Example.lean": hashlib.sha256((root / "Example.lean").read_bytes()).hexdigest()}}
    item = {"source": {"url": spec["repository"], "rev": root_revision}, "overlays": {
        "lean-toolchain": "leanprover/lean4:v4.31.0\n", "lakefile.toml": 'name = "fixture"\n',
        "lake-manifest.json": json.dumps({"name": "fixture", "packagesDir": ".lake/packages", "packages": packages}),
        ".lrh-stage.json": json.dumps({"schema_version": 1, "kind": "repository",
                                      "lean_version": spec["lean_version"], "revision": root_revision})}}
    row = {"name": "example", "source": "strata", "statement": "theorem example : True",
        "src": "theorem example : True := by trivial", "header": "", "contexts": [],
        "file_path": "Example.lean", "url": spec["repository"], "start_line": 1,
        "version_info": [{spec["lean_version"]: root_revision}]}
    manifest = {"schema_version": 1, "format": setup.UPSTREAM_FORMAT,
        "requirements": {"schema_version": 1, "snapshots": {"fixture": spec}, "tasks": {}},
        "snapshots": {"fixture": item}, "rows": [row]}
    path = tmp_path / "environment-setup.json"
    path.write_text(json.dumps(manifest))
    return {"spec": spec, "item": item, "manifest": manifest, "path": path, "calls": calls, "git_fetch": real_fetch,
            "root_revision": root_revision, "dep_revision": dep_revision, "dependency": dependency}


def save(upstream):
    upstream["path"].write_text(json.dumps(upstream["manifest"]))


def test_manifest_validation_and_plan_do_not_fetch(upstream, tmp_path, monkeypatch):
    monkeypatch.setattr(setup, "toolchain_problem", lambda *args: None)
    assert setup.load_setup(upstream["path"])["format"] == setup.UPSTREAM_FORMAT
    result = setup.install(upstream["path"], tmp_path / "environments", tmp_path / "elan",
                           tmp_path / "map.toml", dry_run=True)
    assert result["snapshots"][0]["source_mode"] == "upstream"
    assert upstream["calls"] == []
    assert not (tmp_path / "environments").exists()


def test_checkout_pins_full_commits_reuses_cache_and_preserves_package_layout(upstream, tmp_path):
    project, cache = tmp_path / "project", tmp_path / "cache"
    fetch.materialize(project, upstream["spec"], upstream["item"], cache)
    assert git(project, "rev-parse", "HEAD") == upstream["root_revision"]
    assert git(project, "remote", "get-url", "origin") == "https://github.com/example/project"
    assert (project / "docs/README.md").is_symlink()
    assert (project / "docs/README.md").read_text() == "upstream source\n"
    for name in ("mathlib", "Hax"):
        package = project / ".lake/packages" / name
        assert git(package, "rev-parse", "HEAD") == upstream["dep_revision"]
        assert (package / "Library.lean").read_text() == "-- pinned library\n"
        assert (package / "README.md").is_file()
        assert not (package / ".git/objects/info/alternates").exists()
    assert (project / ".lake/packages/Hax/hax-lib/proof-libs/lean/lakefile.toml").is_file()
    assert len(upstream["calls"]) == 2  # One root and one shared dependency commit.
    fetch.materialize(tmp_path / "second", upstream["spec"], upstream["item"], cache)
    assert len(upstream["calls"]) == 2


def test_generated_putnam_root_uses_overlays_and_only_fetches_packages(upstream, tmp_path):
    revision = upstream["dep_revision"]
    spec = {**upstream["spec"], "repository": "https://github.com/leanprover-community/mathlib4", "revision": revision}
    item = {"source": None, "overlays": dict(upstream["item"]["overlays"])}
    item["overlays"][".lrh-stage.json"] = json.dumps({"schema_version": 1, "kind": "putnam",
                                                     "lean_version": spec["lean_version"], "revision": revision})
    project = tmp_path / "generated"
    fetch.materialize(project, spec, item, tmp_path / "cache")
    assert not (project / ".git").exists()
    assert not (project / "Example.lean").exists()
    assert (project / ".lake/packages/mathlib/Library.lean").is_file()
    assert len(upstream["calls"]) == 1


@pytest.mark.parametrize("url", ["file:///tmp/source", "https://user:password@github.com/example/project",
    "https://github.com/example/project?token=secret", "https://example.invalid/example/project",
    "https://github.com/example/../project", "ssh://git@github.com/example/project"])
def test_rejects_nonpublic_or_credentialed_source_urls(url):
    with pytest.raises(ValueError, match="public HTTPS GitHub"):
        fetch.coordinate({"url": url, "rev": "a" * 40})


@pytest.mark.parametrize("revision", ["main", "v4.31.0", "a" * 8, "a" * 39, "A" * 40])
def test_rejects_moving_or_short_source_revisions(revision):
    with pytest.raises(ValueError, match="full 40-character"):
        fetch.coordinate({"url": "https://github.com/example/project", "rev": revision})


@pytest.mark.parametrize("change", ["wrong_root", "missing_source", "null_repository", "package_branch",
                                    "package_escape", "package_overlap", "subdir_escape", "missing_stage"])
def test_manifest_rejects_invalid_source_plans_before_fetch(upstream, change):
    item = upstream["item"]
    packages = json.loads(item["overlays"]["lake-manifest.json"])
    if change == "wrong_root":
        item["source"]["rev"] = "f" * 40
    elif change == "missing_source":
        del item["source"]
    elif change == "null_repository":
        item["source"] = None
    elif change == "package_branch":
        packages["packages"][0]["rev"] = "main"
    elif change == "package_escape":
        packages["packages"][0]["dir"] = "../outside"
    elif change == "package_overlap":
        packages["packages"][0]["dir"] = ".lake/packages/Hax"
    elif change == "subdir_escape":
        packages["packages"][1]["subDir"] = "../outside"
    elif change == "missing_stage":
        del item["overlays"][".lrh-stage.json"]
    item["overlays"]["lake-manifest.json"] = json.dumps(packages)
    save(upstream)
    with pytest.raises(ValueError):
        setup.load_setup(upstream["path"])
    assert upstream["calls"] == []


def mocked_preparation(monkeypatch, *, prepare=None):
    monkeypatch.setattr(setup, "toolchain_problem", lambda *args: None)
    monkeypatch.setattr(setup, "prepare_snapshot", prepare or (lambda *args: {"built_targets": 0}))
    monkeypatch.setattr(setup, "validate_snapshot", lambda *args, **kwargs: {})
    monkeypatch.setattr(setup, "validate_dependencies", lambda *args, **kwargs: {})


def test_install_reuses_ready_owned_roots_and_external_bare_source_cache(upstream, tmp_path, monkeypatch):
    preparations = []
    mocked_preparation(monkeypatch, prepare=lambda *args: preparations.append(args[0]) or {})
    source_cache = tmp_path / "source-downloads"
    monkeypatch.setenv("HARNESS_SOURCE_CACHE_ROOT", str(source_cache))
    env_root, output = tmp_path / "environments", tmp_path / "map.toml"
    setup.install(upstream["path"], env_root, tmp_path / "elan", output)
    root = env_root / "fixture"
    assert (root / "lean-toolchain").read_text() == "leanprover/lean4:v4.31.0\n"
    assert json.loads((root / setup.RECEIPT).read_text())["status"] == "ready"
    assert len(upstream["calls"]) == 2 and len(preparations) == 1
    assert list(source_cache.glob("*/.lrh-source.json"))
    assert not (env_root / "download-cache/sources").exists()
    setup.install(upstream["path"], env_root, tmp_path / "elan", tmp_path / "second-map.toml")
    assert len(upstream["calls"]) == 2 and len(preparations) == 1


def test_failed_fetch_leaves_no_partial_snapshot_and_can_resume(upstream, tmp_path, monkeypatch):
    mocked_preparation(monkeypatch)
    real_fetch = fetch._fetch
    failed = False

    def interrupted(destination, source):
        nonlocal failed
        if not failed and source["url"].endswith("mathlib4"):
            failed = True
            destination.mkdir()
            raise RuntimeError("synthetic interrupted fetch")
        real_fetch(destination, source)

    monkeypatch.setattr(fetch, "_fetch", interrupted)
    env_root, output = tmp_path / "environments", tmp_path / "map.toml"
    with pytest.raises(RuntimeError, match="interrupted fetch"):
        setup.install(upstream["path"], env_root, tmp_path / "elan", output)
    assert not (env_root / "fixture").exists() and not output.exists()
    assert not list((env_root / "download-cache/sources").glob(".fetch-*"))
    setup.install(upstream["path"], env_root, tmp_path / "elan", output)
    assert output.is_file()
    assert len(upstream["calls"]) == 2  # Completed root fetch survived the failure.


def test_failed_build_resumes_owned_source_root_without_redownloading(upstream, tmp_path, monkeypatch):
    def failed(*args):
        raise RuntimeError("synthetic interrupted build")

    mocked_preparation(monkeypatch, prepare=failed)
    env_root, output = tmp_path / "environments", tmp_path / "map.toml"
    with pytest.raises(RuntimeError, match="interrupted build"):
        setup.install(upstream["path"], env_root, tmp_path / "elan", output)
    assert json.loads((env_root / "fixture" / setup.RECEIPT).read_text())["status"] == "incomplete"
    assert not output.exists()
    mocked_preparation(monkeypatch)
    setup.install(upstream["path"], env_root, tmp_path / "elan", output)
    assert len(upstream["calls"]) == 2 and output.is_file()


def test_install_preserves_unmanaged_root_without_fetching(upstream, tmp_path, monkeypatch):
    mocked_preparation(monkeypatch)
    root = tmp_path / "environments/fixture"
    root.mkdir(parents=True)
    (root / "operator-file").write_text("keep me")
    with pytest.raises(ValueError, match="unmanaged"):
        setup.install(upstream["path"], root.parent, tmp_path / "elan", tmp_path / "map.toml")
    assert (root / "operator-file").read_text() == "keep me"
    assert upstream["calls"] == []


def test_checkout_rejects_external_source_symlinks(upstream, tmp_path):
    root = tmp_path / "unsafe-origin"
    revision = repository(root, {"README.md": "source\n"})
    (root / "outside").symlink_to("../operator-file")
    git(root, "add", ".")
    git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "unsafe alias")
    revision = git(root, "rev-parse", "HEAD")
    # Add this synthetic origin to the same offline transport boundary.
    fetch_source = {"url": "https://github.com/example/project", "rev": revision}
    with pytest.MonkeyPatch.context() as patch:
        patch.setattr(fetch, "_fetch", lambda destination, source: upstream["git_fetch"](
            destination, {**source, "url": str(root)}))
        with pytest.raises(ValueError, match="symlink escapes"):
            fetch.checkout(fetch_source, tmp_path / "unsafe-checkout", tmp_path / "cache")
