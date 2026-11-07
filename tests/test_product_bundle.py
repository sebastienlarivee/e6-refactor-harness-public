from pathlib import Path
import hashlib
import json
import zipfile
import pytest

from scripts.build_bundle import FILES, MAINTAINER_FILES, build, source_files
from e6.config import REPO_ROOT, source_paths


def fixture_root(tmp_path, *, include_tests=False):
    root = tmp_path / "source"
    root.mkdir()
    for name in (*FILES, *(MAINTAINER_FILES if include_tests else ())):
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("release fixture\n")
    (root / "configs").mkdir(exist_ok=True)
    return root


def upstream_manifest(path):
    revision = "a" * 40
    spec = {"repository": "https://github.com/example/project", "revision": revision,
            "lean_version": "v4.29.1", "lean_commit": "b" * 40,
            "required_files": {"Example.lean": "c" * 64}}
    value = {"schema_version": 1, "format": "lean-project-upstream-v1",
             "requirements": {"schema_version": 1, "snapshots": {"project": spec}},
             "rows": [{"name": "example", "url": spec["repository"], "version_info": [{"v4.29.1": revision}]}],
             "snapshots": {"project": {
                 "source": {"url": spec["repository"], "rev": revision},
                 "overlays": {
                     ".lrh-stage.json": json.dumps({"schema_version": 1, "kind": "repository",
                                                     "lean_version": spec["lean_version"], "revision": revision}),
                     "lean-toolchain": "leanprover/lean4:v4.29.1\n",
                     "lakefile.toml": 'name = "fixture"\n',
                     "lake-manifest.json": json.dumps({"version": "1.1.0", "packagesDir": ".lake/packages",
                                                        "packages": [], "name": "fixture", "lakeDir": ".lake"}),
                 },
             }}}
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value))
    return value


def test_release_preserves_every_frozen_runtime_input():
    selected = {path.resolve() for path in source_files()}
    expected = set(source_paths("control-efficient-v1"))
    assert expected <= selected
    prompt_files = {path for path in selected if "prompts/runtime" in path.as_posix()}
    assert prompt_files == {path.resolve() for path in expected if "prompts/runtime" in path.as_posix()}
    for name in ("e6/deterministic_native_support/Inventory.lean.inc",
                 "e6/deterministic_native_support/SemanticSearch.lean.inc",
                 "e6/deterministic_native_support/DictionaryCensus.lean.inc"):
        assert REPO_ROOT / name in selected


def test_zip_is_deterministic_and_manifest_matches_bytes(tmp_path):
    root = fixture_root(tmp_path)
    a, b = tmp_path / "a.zip", tmp_path / "b.zip"
    first, second = build(a, root=root), build(b, root=root)
    assert first["sha256"] == second["sha256"]
    with zipfile.ZipFile(a) as archive:
        manifest = json.loads(archive.read("lean-refactor-harness/release-manifest.json"))
        assert manifest["files"]
        for name, expected in manifest["files"].items():
            assert hashlib.sha256(archive.read("lean-refactor-harness/" + name)).hexdigest() == expected
        setup = archive.getinfo("lean-refactor-harness/setup.sh")
        assert (setup.external_attr >> 16) & 0o777 == 0o755
    with pytest.raises(ValueError, match="overwrite"):
        build(a, root=root)


def test_default_upstream_manifest_builds_deterministic_small_organizer_bundle_offline(tmp_path, monkeypatch):
    import subprocess
    import urllib.request
    root = fixture_root(tmp_path)
    setup_path = root / "environment-sources/environment-setup.json"
    upstream_manifest(setup_path)
    # Old local downloads are not release inputs for upstream mode.
    (setup_path.parent / "old-source.tar.gz").write_bytes(b"local archive must not ship")
    monkeypatch.setattr(urllib.request, "urlopen", lambda *args, **kwargs: pytest.fail("builder fetched sources"))
    monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: pytest.fail("builder launched a source command"))

    first = build(tmp_path / "upstream-a.zip", root=root)
    second = build(tmp_path / "upstream-b.zip", root=root)
    assert first["sha256"] == second["sha256"]
    assert first["includes_environment_setup"] is True
    assert first["includes_environment_sources"] is False
    assert first["environment_setup_format"] == "lean-project-upstream-v1"
    with zipfile.ZipFile(first["archive"]) as archive:
        names = {name.removeprefix("lean-refactor-harness/") for name in archive.namelist()}
        manifest = json.loads(archive.read("lean-refactor-harness/release-manifest.json"))
        assert archive.read("lean-refactor-harness/environment-sources/environment-setup.json") == setup_path.read_bytes()
    assert {name for name in names if name.startswith("environment-sources/")} == {"environment-sources/environment-setup.json"}
    assert "scripts/source_fetch.py" in names
    assert set(MAINTAINER_FILES).isdisjoint(names)
    assert not any(name.startswith("tests/") for name in names)
    assert manifest["includes_environment_setup"] is True
    assert manifest["includes_environment_sources"] is False
    assert manifest["environment_setup_format"] == "lean-project-upstream-v1"


def test_explicit_upstream_manifest_does_not_require_archives(tmp_path):
    root = fixture_root(tmp_path)
    supplied = tmp_path / "upstream/environment-setup.json"
    upstream_manifest(supplied)
    result = build(tmp_path / "explicit.zip", root=root, environment_setup=supplied)
    with zipfile.ZipFile(result["archive"]) as archive:
        assert archive.read("lean-refactor-harness/environment-sources/environment-setup.json") == supplied.read_bytes()
    assert result["includes_environment_setup"] is True
    assert result["includes_environment_sources"] is False


def test_default_legacy_manifest_still_bundles_verified_source_packs(tmp_path):
    root = fixture_root(tmp_path)
    setup_path = root / "environment-sources/environment-setup.json"
    value = upstream_manifest(setup_path)
    pack = setup_path.parent / "project.tar.gz"
    pack.write_bytes(b"synthetic source pack")
    overlays = value["snapshots"]["project"]["overlays"]
    value["format"] = "lean-project-sources-tar-gzip-v1"
    value["snapshots"]["project"] = {"pack": pack.name, "sha256": hashlib.sha256(pack.read_bytes()).hexdigest(),
                                       "bytes": pack.stat().st_size, "overlays": overlays}
    setup_path.write_text(json.dumps(value))

    result = build(tmp_path / "legacy.zip", root=root)
    assert result["includes_environment_sources"] is True
    assert result["environment_setup_format"] == value["format"]
    with zipfile.ZipFile(result["archive"]) as archive:
        assert archive.read("lean-refactor-harness/environment-sources/project.tar.gz") == pack.read_bytes()


def test_invalid_default_upstream_manifest_fails_before_writing_archive(tmp_path):
    root = fixture_root(tmp_path)
    setup_path = root / "environment-sources/environment-setup.json"
    value = upstream_manifest(setup_path)
    value["snapshots"]["project"]["source"]["rev"] = "f" * 40
    setup_path.write_text(json.dumps(value))
    output = tmp_path / "invalid.zip"
    with pytest.raises(ValueError):
        build(output, root=root)
    assert not output.exists()
    assert not output.with_suffix(".zip.part").exists()


def test_default_setup_manifest_must_not_be_a_symlink(tmp_path):
    root = fixture_root(tmp_path)
    outside = tmp_path / "outside/environment-setup.json"
    upstream_manifest(outside)
    local = root / "environment-sources/environment-setup.json"
    local.parent.mkdir()
    local.symlink_to(outside)
    with pytest.raises(ValueError, match="must not be a symlink"):
        build(tmp_path / "linked.zip", root=root)


def test_local_settings_caches_and_runs_are_excluded(tmp_path):
    root = fixture_root(tmp_path)
    for name in ("configs/private.local.json", "configs/model.local.toml",
                 "harness/__pycache__/secret.py", "harness/.hidden/secret.py",
                 "configs/models/model.evidence.json", "runs/results.json", ".env", ".git/config",
                 "environments.local.toml", "research/evidence.json", "docs/build-spec.md",
                 "docs/regression-coverage.md", "prompts/control-editable/manifest.json"):
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("machine-only")
    assert not any(path.read_text() == "machine-only" for path in source_files(root))


def test_release_includes_operational_docs_scripts_and_model_profiles(tmp_path):
    root = fixture_root(tmp_path)
    profile = root / "configs/models/final.json"
    profile.parent.mkdir()
    profile.write_text('{"model_id": "example/model"}\n')
    with zipfile.ZipFile(build(tmp_path / "release.zip", root=root)["archive"]) as archive:
        names = set(archive.namelist())
    assert {
        "lean-refactor-harness/" + name for name in (
            "MANIFEST.in", "docs/setup.md", "docs/operations.md", "docs/lean-dependencies.md",
            "docs/provenance.json", "scripts/monitor.py", "scripts/setup_runtime.py",
            "configs/models/final.json",
        )
    } <= names


@pytest.mark.parametrize("name", ("docs/setup.md", "docs/operations.md", "docs/lean-dependencies.md"))
def test_release_requires_operational_docs(tmp_path, name):
    root = fixture_root(tmp_path)
    (root / name).unlink()
    with pytest.raises(ValueError, match="Required release file"):
        source_files(root)


def test_secret_shaped_payload_fails_closed(tmp_path):
    root = fixture_root(tmp_path)
    (root / "configs" / "model.json").write_text("sk-or-v1-" + "a" * 40)
    with pytest.raises(ValueError, match="Credential-shaped"):
        build(tmp_path / "bad.zip", root=root)
    assert not (tmp_path / "bad.zip").exists()


def test_symlink_and_missing_required_source_fail_closed(tmp_path):
    root = fixture_root(tmp_path)
    external = tmp_path / "external.py"
    external.write_text("outside")
    linked = root / "configs" / "external.py"
    linked.symlink_to(external)
    with pytest.raises(ValueError, match="symlink"):
        source_files(root)
    linked.unlink()
    (root / "README.md").unlink()
    with pytest.raises(ValueError, match="Required release file"):
        source_files(root)


def test_organizer_bundle_omits_developer_tools_and_opt_in_bundle_preserves_them(tmp_path):
    root = fixture_root(tmp_path, include_tests=True)
    helper = root / "tests/support/verify_product_native.py"
    helper.parent.mkdir(parents=True)
    helper.write_text("# offline developer helper\n")
    test = root / "tests/test_native.py"
    test.write_text("from tests.support import verify_product_native\n")
    developer_files = {*MAINTAINER_FILES, "tests/support/verify_product_native.py", "tests/test_native.py"}
    for include_tests in (False, True):
        result = build(tmp_path / f"bundle-{include_tests}.zip", root=root, include_tests=include_tests)
        with zipfile.ZipFile(result["archive"]) as archive:
            names = {name.removeprefix("lean-refactor-harness/") for name in archive.namelist()}
            manifest = json.loads(archive.read("lean-refactor-harness/release-manifest.json"))
        assert manifest["includes_tests"] is include_tests
        if include_tests:
            assert developer_files <= names
        else:
            assert developer_files.isdisjoint(names)


def test_offline_verification_helpers_remain_developer_only():
    organizer = set(source_files())
    developer = set(source_files(include_tests=True))
    helpers = {REPO_ROOT / "tests/support" / f"verify_product_{name}.py"
               for name in ("native", "pipeline", "dictionary")}
    assert helpers <= developer
    assert helpers.isdisjoint(organizer)
    assert {REPO_ROOT / name for name in MAINTAINER_FILES} <= developer
