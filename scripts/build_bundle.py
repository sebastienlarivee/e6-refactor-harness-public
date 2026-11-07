#!/usr/bin/env python3
"""Build a deterministic source ZIP without machine bindings, credentials or run data."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
TREES = ("harness", "e6", "lean_tools", "transport", "data", "configs", "prompts/runtime", "LICENSES")
FILES = ("LICENSE", "THIRD_PARTY_NOTICES.md", "README.md", "pyproject.toml", "MANIFEST.in", "uv.lock", "setup.sh", "run.sh",
         "docs/setup.md", "docs/operations.md", "docs/lean-dependencies.md", "docs/provenance.json",
         "scripts/setup_runtime.py", "scripts/monitor.py", "scripts/setup_environments.py",
         "scripts/source_fetch.py", "scripts/setup_submission.py", "scripts/run_submission.py")
MAINTAINER_FILES = ("scripts/build_bundle.py", "scripts/export_environment_sources.py")
SUFFIXES = (".py", ".lean", ".lean.inc", ".json", ".jsonl", ".toml", ".md", ".mjs", ".ts", ".txt")
SECRET = re.compile(rb"(?:sk-or-(?:v1|v2|admin)-[A-Za-z0-9_-]{16,}|sk-proj-[A-Za-z0-9_-]{16,})")


def source_files(root: Path = ROOT, *, include_tests: bool = False) -> list[Path]:
    root = root.resolve()
    selected = []
    for name in (*FILES, *(MAINTAINER_FILES if include_tests else ())):
        path = root / name
        if path.is_file():
            selected.append(path)
        else:
            raise ValueError(f"Required release file is missing: {name}")
    trees = (*TREES, *(("tests",) if include_tests else ()))
    for name in trees:
        directory = root / name
        if not directory.exists():
            if name == "configs":
                raise ValueError("Release configurations are missing")
            continue
        for path in directory.rglob("*"):
            relative = path.relative_to(root)
            if any(part.startswith(".") or part == "__pycache__" for part in relative.parts):
                continue
            if ".local." in path.name or path.name.endswith(".evidence.json") or not path.name.endswith(SUFFIXES):
                continue
            if path.is_symlink():
                raise ValueError(f"Release file must not be a symlink: {relative}")
            if path.is_file():
                selected.append(path)
    result = sorted(set(selected), key=lambda p: p.relative_to(root).as_posix())
    for path in result:
        if not path.resolve().is_relative_to(root):
            raise ValueError("Release source escaped its root")
        if SECRET.search(path.read_bytes()):
            raise ValueError(f"Credential-shaped content in release file: {path.relative_to(root)}")
    return result


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def build(output: Path, *, root: Path = ROOT, include_tests: bool = False,
          environment_setup: Path | None = None) -> dict:
    root = root.resolve()
    output = output.expanduser().resolve()
    if output.exists():
        raise ValueError("Refusing to overwrite an existing release archive")
    files = source_files(root, include_tests=include_tests)
    if output in files:
        raise ValueError("Release archive would overwrite a source")
    entries = {path.relative_to(root).as_posix(): path for path in files}
    if environment_setup is None:
        default_setup = root / "environment-sources/environment-setup.json"
        if default_setup.is_symlink():
            raise ValueError("Default environment setup manifest must not be a symlink")
        if default_setup.is_file():
            environment_setup = default_setup
    setup_format = None
    includes_source_packs = False
    if environment_setup is not None:
        from scripts.setup_environments import PACK_FORMAT, load_setup
        setup_path = Path(environment_setup).expanduser().resolve()
        setup_value = load_setup(setup_path)
        setup_format = setup_value["format"]
        if SECRET.search(setup_path.read_bytes()):
            raise ValueError("Credential-shaped content in environment setup manifest")
        entries["environment-sources/environment-setup.json"] = setup_path
        if setup_format == PACK_FORMAT:
            includes_source_packs = True
            for sid, item in setup_value["snapshots"].items():
                pack = setup_path.parent / item["pack"]
                if (pack.is_symlink() or not pack.resolve().is_relative_to(setup_path.parent)
                        or not pack.is_file() or file_sha256(pack) != item["sha256"]):
                    raise ValueError(f"Missing or changed source pack for {sid}")
                entries["environment-sources/" + item["pack"]] = pack
    manifest = {"schema_version": 1, "format": "source-zip", "setup": "./setup.sh",
                "includes_tests": include_tests, "includes_environment_sources": includes_source_packs,
                "includes_environment_setup": environment_setup is not None, "environment_setup_format": setup_format,
                "files": {name: file_sha256(path) for name, path in sorted(entries.items())}}
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(output.suffix + ".part")
    if temporary.exists():
        raise ValueError("Partial release already exists; choose a new output path")
    try:
        with zipfile.ZipFile(temporary, "x", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
            for name, path in sorted(entries.items()):
                info = zipfile.ZipInfo("lean-refactor-harness/" + name,
                                       date_time=(1980, 1, 1, 0, 0, 0))
                info.create_system = 3
                info.external_attr = (0o100755 if path.name in {"setup.sh", "run.sh"} else 0o100644) << 16
                info.compress_type = zipfile.ZIP_DEFLATED
                with path.open("rb") as source, archive.open(info, "w", force_zip64=True) as destination:
                    shutil.copyfileobj(source, destination, length=1024 * 1024)
            info = zipfile.ZipInfo("lean-refactor-harness/release-manifest.json",
                                   date_time=(1980, 1, 1, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        temporary.replace(output)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise
    return {"archive": str(output), "bytes": output.stat().st_size,
            "sha256": file_sha256(output), "files": len(entries), "includes_tests": include_tests,
            "includes_environment_sources": includes_source_packs,
            "includes_environment_setup": environment_setup is not None, "environment_setup_format": setup_format}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--include-tests", action="store_true")
    parser.add_argument("--environment-setup", type=Path,
                        help="Use this setup manifest (default: environment-sources/environment-setup.json if present); include archives only for source-pack manifests")
    args = parser.parse_args()
    print(json.dumps(build(args.output, include_tests=args.include_tests,
                           environment_setup=args.environment_setup), indent=2))


if __name__ == "__main__":
    main()
