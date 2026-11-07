#!/usr/bin/env python3
"""Install and explicitly activate the pinned native Codex version.

Cache archives separately; native binaries and Python stay on the Linux filesystem.
No login or model call is performed. Older installed packages are preserved.
"""
from __future__ import annotations

import argparse
import ctypes
import datetime
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import tarfile
import tempfile
import urllib.request
import uuid

import zstandard

VERSION = "0.164.0"
ASSET = "codex-package-x86_64-unknown-linux-musl.tar.zst"
SHA256 = "7801ae47316395e3a638fb61964a9f28f84a6647c1b1ed90332e4d6b6da046d8"
URL = f"https://github.com/openai/codex/releases/download/rust-v{VERSION}/{ASSET}"


def sha(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def managed_link_target(link: Path, runtime: Path) -> Path | None:
    """Accept only an installed, marked versioned package in this runtime root."""
    if not link.is_symlink():
        if link.exists():
            raise RuntimeError("Refusing to overwrite an existing Codex executable")
        return None
    try:
        target = link.resolve(strict=True)
        relative = target.relative_to(runtime)
        if len(relative.parts) < 2:
            raise ValueError("Codex link is not inside a versioned package")
        package = runtime / relative.parts[0]
        marker = package / ".archive-sha256"
        managed = (len(relative.parts) >= 2
                   and re.fullmatch(r"codex-\d+\.\d+\.\d+", package.name)
                   and not package.is_symlink() and target.is_file() and target.name == "codex"
                   and marker.is_file() and re.fullmatch(r"[0-9a-f]{64}", marker.read_text().strip()))
    except (OSError, ValueError, RuntimeError):
        managed = False
    if not managed:
        raise RuntimeError("Refusing to replace a foreign or broken Codex link")
    return target


def checked_binary(package: Path) -> tuple[Path, str]:
    candidates = [path for path in package.rglob("codex") if path.is_file()]
    if len(candidates) != 1:
        raise RuntimeError(f"Expected one native Codex binary, found {len(candidates)}")
    binary = candidates[0]
    version = subprocess.check_output([str(binary), "--version"], text=True).strip()
    if version != f"codex-cli {VERSION}":
        raise RuntimeError(f"Native runtime version mismatch: {version}")
    return binary, version


def publish_package(staged: Path, package: Path) -> None:
    """Atomically publish on Linux without replacing even an empty foreign root."""
    rename = ctypes.CDLL(None, use_errno=True).renameat2
    rename.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
    rename.restype = ctypes.c_int
    # AT_FDCWD and RENAME_NOREPLACE; ordinary rename can overwrite an empty dir.
    if rename(-100, os.fsencode(staged), -100, os.fsencode(package), 1):
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error), str(package))


def extract_package(archive: Path, package: Path) -> tuple[Path, str]:
    """Failed stages are private; even a killed extractor cannot block retry."""
    package.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=f".codex-{VERSION}-", dir=package.parent) as temporary:
        staged = Path(temporary) / "package"
        staged.mkdir()
        with archive.open("rb") as compressed, zstandard.ZstdDecompressor().stream_reader(compressed) as reader:
            with tarfile.open(fileobj=reader, mode="r|") as stream:
                for member in stream:
                    entry = PurePosixPath(member.name)
                    if entry.is_absolute() or ".." in entry.parts or not (member.isfile() or member.isdir()):
                        raise RuntimeError(f"Unexpected runtime archive entry: {member.name}")
                    stream.extract(member, staged, filter="data")
        binary, version = checked_binary(staged)
        (staged / ".archive-sha256").write_text(SHA256 + "\n", encoding="utf-8")
        publish_package(staged, package)
        return package / binary.relative_to(staged), version


def setup(runtime: Path, downloads: Path, *, activate: bool = False, stage_only: bool = False) -> dict:
    if activate and stage_only:
        raise ValueError("--activate and --stage-only are mutually exclusive")
    runtime, downloads = runtime.expanduser().resolve(), downloads.expanduser().resolve()
    if str(runtime).startswith("/mnt/"):
        raise ValueError("Native runtime must live on the Linux filesystem")
    link = runtime / "bin/codex"
    previous_target = managed_link_target(link, runtime)
    package = runtime / f"codex-{VERSION}"
    if (previous_target is not None and not previous_target.is_relative_to(package)
            and not (activate or stage_only)):
        raise RuntimeError("Another managed Codex version is active; use --stage-only or --activate")
    archive = downloads / f"codex-{VERSION}" / ASSET
    archive.parent.mkdir(parents=True, exist_ok=True)
    if not archive.is_file() or sha(archive) != SHA256:
        temporary = archive.with_suffix(archive.suffix + ".part")
        request = urllib.request.Request(URL, headers={"User-Agent": "lean-refactor-harness-setup"})
        with urllib.request.urlopen(request, timeout=60) as response, temporary.open("wb") as output:
            shutil.copyfileobj(response, output, length=1024 * 1024)
        if sha(temporary) != SHA256:
            raise RuntimeError("Native Codex archive digest mismatch; partial artifact retained")
        temporary.replace(archive)
    marker = package / ".archive-sha256"
    if package.is_symlink() or (package.exists() and not package.is_dir()):
        raise RuntimeError("Refusing to change an unmanaged native runtime path")
    if not marker.exists():
        if package.exists():
            raise RuntimeError("Incomplete runtime directory exists; preserve it and use a fresh runtime root")
        binary, version = extract_package(archive, package)
    else:
        if marker.read_text().strip() != SHA256:
            raise RuntimeError("Existing native runtime has a different archive identity")
        binary, version = checked_binary(package)
    clean_home = runtime / "codex-home"
    clean_home.mkdir(parents=True, exist_ok=True)
    os.chmod(clean_home, 0o700)
    if (clean_home / "auth.json").exists():
        raise RuntimeError("The model runtime home must not contain host credentials")
    receipt = {"installed_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
               "version": version, "binary": str(binary.resolve()), "binary_sha256": sha(binary),
               "archive_url": URL, "archive": str(archive), "archive_sha256": SHA256,
               "runtime_root": str(runtime), "clean_codex_home": str(clean_home),
               "files": {str(path.relative_to(package)): sha(path) for path in sorted(package.rglob("*")) if path.is_file()},
               "model_calls": 0, "account_login_used": False, "activated": not stage_only}
    if not stage_only:
        # Validate again immediately before the atomic switch, after every install check.
        current_target = managed_link_target(link, runtime)
        if current_target != previous_target:
            raise RuntimeError("Active Codex changed during installation; refusing to replace it")
        link.parent.mkdir(parents=True, exist_ok=True)
        temporary_link = link.with_name(f".codex-{uuid.uuid4().hex}")
        try:
            temporary_link.symlink_to(os.path.relpath(binary, link.parent))
            temporary_link.replace(link)
        finally:
            temporary_link.unlink(missing_ok=True)
        (runtime / "runtime.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    (runtime / f"runtime-{VERSION}.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--runtime", type=Path, default=Path.home() / ".local/share/lean-refactor-harness")
    parser.add_argument("--downloads", type=Path, default=Path.home() / ".cache/lean-refactor-harness")
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--activate", action="store_true", help="Allow replacing an older managed Codex link")
    action.add_argument("--stage-only", action="store_true", help="Install and verify without changing the active CLI")
    args = parser.parse_args()
    receipt = setup(args.runtime, args.downloads, activate=args.activate, stage_only=args.stage_only)
    print(json.dumps({key: receipt[key] for key in ("version", "binary", "binary_sha256", "clean_codex_home", "activated")}))


if __name__ == "__main__":
    main()
