"""Offline runtime installation failures preserve downloads and foreign state."""
from __future__ import annotations

import hashlib
import io
import os
from pathlib import Path
import tarfile

import pytest
import zstandard

from scripts import setup_runtime as setup


@pytest.fixture
def cached_runtime(tmp_path, monkeypatch):
    runtime, downloads = tmp_path / "runtime", tmp_path / "downloads"
    archive = downloads / f"codex-{setup.VERSION}" / setup.ASSET
    archive.parent.mkdir(parents=True)
    contents = io.BytesIO()
    with tarfile.open(fileobj=contents, mode="w") as stream:
        for name, data, mode in (
            ("native/codex", f"#!/bin/sh\nprintf 'codex-cli {setup.VERSION}\\n'\n".encode(), 0o755),
            ("native/support.txt", b"complete package support\n", 0o644),
        ):
            member = tarfile.TarInfo(name)
            member.size, member.mode = len(data), mode
            stream.addfile(member, io.BytesIO(data))
    archive.write_bytes(zstandard.ZstdCompressor().compress(contents.getvalue()))
    monkeypatch.setattr(setup, "SHA256", hashlib.sha256(archive.read_bytes()).hexdigest())
    monkeypatch.setattr(setup.urllib.request, "urlopen", lambda *args, **kwargs: pytest.fail("unexpected download"))
    return runtime, downloads, archive


def archive_identity(archive: Path):
    info = archive.stat()
    return archive.read_bytes(), info.st_ino, info.st_mtime_ns


def test_interrupted_extraction_retries_same_paths_without_redownloading(cached_runtime, monkeypatch):
    runtime, downloads, archive = cached_runtime
    original = archive_identity(archive)
    extract = tarfile.TarFile.extract

    def interrupted(stream, *args, **kwargs):
        extract(stream, *args, **kwargs)
        raise KeyboardInterrupt("interrupted after the first file")

    monkeypatch.setattr(tarfile.TarFile, "extract", interrupted)
    with pytest.raises(KeyboardInterrupt, match="first file"):
        setup.setup(runtime, downloads)
    assert not (runtime / f"codex-{setup.VERSION}").exists()
    assert not (runtime / "bin/codex").exists()
    assert list(runtime.iterdir()) == []
    assert archive_identity(archive) == original

    monkeypatch.setattr(tarfile.TarFile, "extract", extract)
    result = setup.setup(runtime, downloads)
    assert result["version"] == f"codex-cli {setup.VERSION}"
    assert (runtime / "bin/codex").resolve() == Path(result["binary"])
    assert Path(result["binary"]).with_name("support.txt").read_bytes() == b"complete package support\n"
    assert archive_identity(archive) == original


def test_abandoned_stage_from_killed_process_is_untouched_and_does_not_block_retry(cached_runtime):
    runtime, downloads, archive = cached_runtime
    abandoned = runtime / f".codex-{setup.VERSION}-abandoned" / "package"
    abandoned.mkdir(parents=True)
    sentinel = abandoned / "partial-file"
    sentinel.write_bytes(b"preserve interrupted extractor state")
    original = archive_identity(archive)

    assert setup.setup(runtime, downloads)["activated"] is True
    assert sentinel.read_bytes() == b"preserve interrupted extractor state"
    assert archive_identity(archive) == original


@pytest.mark.parametrize("kind", ["empty-directory", "partial-directory", "file", "symlink", "broken-symlink"])
def test_unmanaged_final_path_is_never_changed(cached_runtime, kind):
    runtime, downloads, archive = cached_runtime
    runtime.mkdir()
    package = runtime / f"codex-{setup.VERSION}"
    outside = runtime.parent / "foreign"
    outside.mkdir()
    (outside / "sentinel").write_bytes(b"foreign package")
    if kind.endswith("directory"):
        package.mkdir()
        if kind == "partial-directory":
            (package / "sentinel").write_bytes(b"old unmarked extraction")
    elif kind == "file":
        package.write_bytes(b"foreign file")
    else:
        package.symlink_to(outside if kind == "symlink" else outside / "missing", target_is_directory=True)
    original = package.lstat(), archive_identity(archive)

    with pytest.raises(RuntimeError, match="unmanaged|Incomplete runtime"):
        setup.setup(runtime, downloads)
    assert package.lstat() == original[0]
    assert archive_identity(archive) == original[1]
    assert (outside / "sentinel").read_bytes() == b"foreign package"
    if kind == "partial-directory":
        assert (package / "sentinel").read_bytes() == b"old unmarked extraction"
    assert not (runtime / "bin").exists()


def test_atomic_publication_does_not_replace_a_concurrently_created_empty_directory(cached_runtime, monkeypatch):
    runtime, downloads, archive = cached_runtime
    publish = setup.publish_package
    foreign = []

    def raced(staged, package):
        package.mkdir()
        foreign.append((package, package.stat().st_ino))
        publish(staged, package)

    monkeypatch.setattr(setup, "publish_package", raced)
    original = archive_identity(archive)
    with pytest.raises(FileExistsError):
        setup.setup(runtime, downloads)
    package, inode = foreign[0]
    assert package.stat().st_ino == inode
    assert list(package.iterdir()) == []
    assert archive_identity(archive) == original
    assert list(runtime.iterdir()) == [package]


def test_invalid_binary_fails_before_publishing_package(cached_runtime, monkeypatch):
    runtime, downloads, archive = cached_runtime
    original = archive_identity(archive)
    monkeypatch.setattr(setup.subprocess, "check_output", lambda *args, **kwargs: "codex-cli wrong-version\n")
    with pytest.raises(RuntimeError, match="version mismatch"):
        setup.setup(runtime, downloads)
    assert list(runtime.iterdir()) == []
    assert archive_identity(archive) == original


def test_ready_runtime_is_reused_without_reextracting_or_changing_package(cached_runtime, monkeypatch):
    runtime, downloads, archive = cached_runtime
    first = setup.setup(runtime, downloads)
    package = runtime / f"codex-{setup.VERSION}"
    original = {path.relative_to(package): (path.read_bytes(), path.stat().st_ino, path.stat().st_mtime_ns)
                for path in package.rglob("*") if path.is_file()}
    monkeypatch.setattr(tarfile.TarFile, "extract", lambda *args, **kwargs: pytest.fail("ready package was extracted"))

    second = setup.setup(runtime, downloads)
    assert second["binary"] == first["binary"]
    assert original == {path.relative_to(package): (path.read_bytes(), path.stat().st_ino, path.stat().st_mtime_ns)
                        for path in package.rglob("*") if path.is_file()}


def test_staging_new_version_preserves_active_older_runtime(cached_runtime):
    runtime, downloads, _ = cached_runtime
    older = runtime / "codex-0.163.0"
    older.mkdir(parents=True)
    (older / ".archive-sha256").write_text("a" * 64 + "\n")
    (older / "codex").write_bytes(b"preserve active executable")
    link = runtime / "bin/codex"
    link.parent.mkdir()
    link.symlink_to("../codex-0.163.0/codex")
    receipt = runtime / "runtime.json"
    receipt.write_bytes(b"preserve active receipt")
    original = os.readlink(link), link.lstat().st_ino

    result = setup.setup(runtime, downloads, stage_only=True)
    assert result["activated"] is False
    assert (os.readlink(link), link.lstat().st_ino) == original
    assert (older / "codex").read_bytes() == b"preserve active executable"
    assert receipt.read_bytes() == b"preserve active receipt"
