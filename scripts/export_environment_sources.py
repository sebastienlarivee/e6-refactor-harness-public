#!/usr/bin/env python3
"""Export existing pinned Lean project/package sources for portable setup.

This command never downloads, builds, or changes the input projects. Generated
source packs can be large; select an archive output directory on suitable storage.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import urllib.parse
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from harness.environments import load_environment_map
from scripts.setup_environments import (PACK_FORMAT, RECEIPT, atomic_json, repository,
                                        sha256, source_roots, verify_source)

SECRET = re.compile(rb"(?:sk-or-(?:v1|v2|admin)-[A-Za-z0-9_-]{16,}|sk-proj-[A-Za-z0-9_-]{16,})")
OVERLAYS = ("lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json")
GIT_ENV = {**os.environ, "GIT_NO_LAZY_FETCH": "1", "GIT_TERMINAL_PROMPT": "0"}


def included_source_name(name: str) -> bool:
    parts = Path(name).parts
    if any(part in {".git", ".lake", ".venv", "node_modules", "__pycache__"} for part in parts):
        return False
    if any(parts[index] == ".lake" and parts[index + 1] in {"build", "config", "packages"}
           for index in range(len(parts) - 1)):
        return False
    leaf = parts[-1]
    # Lake's ProofWidgets input_file target writes this beside package-lock.json.
    # It is generated build metadata, unlike the lock file itself.
    return not (name == "widget/package-lock.json.hash"
                or leaf in {RECEIPT, ".lrh-stage.json", ".DS_Store", ".env"}
                or leaf.startswith((".lrh-setup", ".env.")) or ".local." in leaf
                or leaf.endswith((".pyc", ".olean", ".ilean", ".trace"))
                or (len(parts) > 1 and parts[-2:] == (".lake", "package-overrides.json")))


def source_files(root: Path, *, exclude_paths: set[Path] | None = None):
    """Yield regular source bytes, materializing authenticated internal aliases."""
    root = root.resolve()
    for directory, dirs, files in os.walk(root, followlinks=True):
        directory = Path(directory)
        resolved = directory.resolve()
        if not resolved.is_relative_to(root):
            raise ValueError(f"Source symlink escapes its project: {directory}")
        if directory != root and any(resolved == parent.resolve() for parent in directory.parents
                                     if parent == root or parent.is_relative_to(root)):
            raise ValueError(f"Cyclic source directory symlink: {directory}")
        dirs[:] = sorted(name for name in dirs if name not in {".git", ".lake", ".venv", "node_modules", "__pycache__"}
                         and not (directory.name == ".lake" and name in {"build", "config", "packages"})
                         and (directory / name).resolve() not in (exclude_paths or set()))
        for name in sorted(files):
            path = directory / name
            relative = path.relative_to(root)
            if not included_source_name(relative.as_posix()):
                continue
            if path.is_symlink() and not path.resolve().is_relative_to(root):
                raise ValueError(f"Source symlink escapes its project: {relative}")
            if not included_source_name(path.resolve().relative_to(root).as_posix()):
                raise ValueError(f"Source symlink aliases excluded host/build state: {relative}")
            if path.is_file():
                yield relative.as_posix(), path


def source_links(root: Path, *, exclude_paths: set[Path] | None = None) -> dict[str, str]:
    """Read pointer bytes separately; source authentication must pin every alias."""
    root = root.resolve()
    links = {}
    for directory, dirs, files in os.walk(root, followlinks=False):
        directory = Path(directory)
        dirs[:] = sorted(name for name in dirs
                         if included_source_name((directory / name).relative_to(root).as_posix())
                         and (directory / name).resolve() not in (exclude_paths or set()))
        for name in [*dirs, *files]:
            path = directory / name
            relative = path.relative_to(root).as_posix()
            if path.is_symlink() and included_source_name(relative):
                target = path.resolve()
                if not target.is_relative_to(root) or not target.exists():
                    raise ValueError(f"Source symlink escapes its project or is dangling: {relative}")
                if not included_source_name(target.relative_to(root).as_posix()):
                    raise ValueError(f"Source symlink aliases excluded host/build state: {relative}")
                links[relative] = os.readlink(path)
    return links


def git_metadata(package: Path, expected: str | None, url: str | None):
    """Export actual Git objects plus a public origin, never local configuration."""
    marker = package / ".git"
    if not marker.exists():
        if expected:
            raise ValueError(f"Git package has no revision evidence: {package}")
        return
    if not marker.is_dir():
        raise ValueError(f"Export Git worktrees through a standalone checkout first: {package}")
    if ((marker / "objects/info/alternates").exists() or (marker / "commondir").exists()
            or any((marker / "objects/pack").glob("*.promisor"))):
        raise ValueError(f"Git package depends on external object storage: {package}")
    if expected:
        result = subprocess.run(["git", "-C", str(package), "rev-parse", "HEAD"],
                                capture_output=True, text=True, check=True, env=GIT_ENV)
        if result.stdout.strip() != expected:
            raise ValueError(f"Git package revision differs from manifest: {package}")
        subprocess.run(["git", "-C", str(package), "cat-file", "-e", expected + "^{commit}"], check=True,
                                stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, env=GIT_ENV)
    if not url or not url.startswith("https://") or "@" in url or "?" in url or "#" in url:
        raise ValueError(f"Git package needs a public HTTPS origin for export: {package}")
    for top in ("HEAD", "packed-refs", "shallow", "refs", "objects"):
        path = marker / top
        paths = sorted(path.rglob("*")) if path.is_dir() else [path]
        for item in paths:
            if item.is_symlink():
                raise ValueError(f"Git metadata symlink is unsupported: {item}")
            if item.is_file():
                if top == "objects" and "info" in item.relative_to(marker).parts:
                    continue
                yield ".git/" + item.relative_to(marker).as_posix(), item.read_bytes(), 0o644
    config = ('[core]\n\trepositoryformatversion = 0\n\tfilemode = true\n\tbare = false\n'
              '[remote "origin"]\n\turl = ' + url + '\n\tfetch = +refs/heads/*:refs/remotes/origin/*\n')
    yield ".git/config", config.encode(), 0o644


def write_member(archive: tarfile.TarFile, name: str, data: bytes, mode: int = 0o644) -> None:
    if SECRET.search(data):
        raise ValueError(f"Credential-shaped source pack content: {name}")
    info = tarfile.TarInfo(name)
    info.size, info.mode, info.mtime, info.uid, info.gid = len(data), mode, 0, 0, 0
    archive.addfile(info, io.BytesIO(data))


def authenticate_tree(root: Path, url: str, revision: str, source_archives: Path | None,
                      *, overlays: set[str] | None = None, exclude_paths: set[Path] | None = None,
                      generated: bool = False) -> dict:
    """Reject edited/untracked code, including files absent from required_files.

    Existing extracted root/Mathlib trees have no usable Git history. Compare
    those against the original cached public source ZIP, without fetching it.
    """
    files = list(source_files(root, exclude_paths=exclude_paths))
    links = source_links(root, exclude_paths=exclude_paths)
    overlays = overlays or set()
    def check_missing(expected: dict) -> None:
        present = {name for name, _ in files} | set(links)
        for name in expected:
            path = (root / name).resolve()
            excluded = any(path.is_relative_to(base) for base in (exclude_paths or set()))
            if included_source_name(name) and not excluded and name not in overlays and name not in present:
                raise ValueError(f"Pinned source file is missing: {root}/{name}")
    if generated:
        if links or any(name not in overlays for name, _ in files):
            raise ValueError(f"Generated project contains unexpected source files: {root}")
        return {"kind": "generated-overlays"}
    head = subprocess.run(["git", "-C", str(root), "rev-parse", "--verify", "HEAD"],
                          capture_output=True, text=True, env=GIT_ENV) if (root / ".git").exists() else None
    if head is not None and head.returncode == 0:
        if head.stdout.strip() != revision:
            raise ValueError(f"Source Git revision differs from pin: {root}")
        listing = subprocess.run(["git", "-C", str(root), "ls-tree", "-rz", "--full-tree", revision],
                                 capture_output=True, check=True, env=GIT_ENV).stdout
        expected, expected_links = {}, {}
        for record in listing.split(b"\0"):
            if not record:
                continue
            metadata, name = record.split(b"\t", 1)
            mode, kind, blob = metadata.split()
            if kind != b"blob":
                continue
            (expected_links if mode == b"120000" else expected)[name.decode("utf-8")] = blob.decode()
        check_missing({**expected, **expected_links})
        for name, target in links.items():
            data = os.fsencode(target)
            pointer_hash = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            if expected_links.get(name) != pointer_hash:
                raise ValueError(f"Modified or untracked source symlink differs from pinned Git tree: {root}/{name}")
        if any(included_source_name(name) and name not in links for name in expected_links):
            raise ValueError(f"Pinned Git source symlink is missing or replaced: {root}")
        for name, path in files:
            if name in overlays:
                continue
            digest = hashlib.sha1()
            digest.update(b"blob " + str(path.stat().st_size).encode() + b"\0")
            with path.open("rb") as stream:
                for block in iter(lambda: stream.read(1024 * 1024), b""):
                    digest.update(block)
            canonical = path.resolve().relative_to(root.resolve()).as_posix()
            if expected.get(canonical) != digest.hexdigest():
                raise ValueError(f"Modified or untracked source differs from pinned Git tree: {root}/{name}")
        return {"kind": "git-tree", "revision": revision,
                "materialized_aliases": [{"path": name, "target": target,
                    "canonical_target": (root / name).resolve().relative_to(root.resolve()).as_posix()}
                    for name, target in sorted(links.items())]}
    coordinates = urllib.parse.urlsplit(url)
    parts = coordinates.path.strip("/").removesuffix(".git").split("/")
    if coordinates.scheme != "https" or coordinates.netloc != "github.com" or len(parts) != 2:
        raise ValueError(f"Archive authentication needs an exact HTTPS GitHub repository: {url}")
    archive_name = "-".join(parts) + "-" + revision + ".zip"
    candidates = list(Path(source_archives).rglob(archive_name)) if source_archives else []
    if len(candidates) != 1:
        raise ValueError(f"Missing unique original source archive {archive_name}; supply --source-archives (no download is performed)")
    archive = candidates[0]
    expected, expected_links = {}, {}
    with zipfile.ZipFile(archive) as bundle:
        members = [item for item in bundle.infolist() if not item.is_dir()]
        prefixes = {item.filename.split("/", 1)[0] for item in members}
        if len(prefixes) != 1:
            raise ValueError(f"Unexpected original source archive layout: {archive_name}")
        for item in members:
            name = item.filename.split("/", 1)[1]
            digest = hashlib.sha256()
            with bundle.open(item) as stream:
                for block in iter(lambda: stream.read(1024 * 1024), b""):
                    digest.update(block)
            if name in expected or name in expected_links:
                raise ValueError(f"Duplicate original source archive member: {name}")
            (expected_links if (item.external_attr >> 16) & 0o170000 == 0o120000 else expected)[name] = digest.hexdigest()
    check_missing({**expected, **expected_links})
    for name, target in links.items():
        if expected_links.get(name) != hashlib.sha256(os.fsencode(target)).hexdigest():
            raise ValueError(f"Modified or untracked source symlink differs from original archive: {root}/{name}")
    # ZIP extraction commonly preserves a symlink entry as a regular file whose
    # exact bytes are its target text. Keep that authenticated representation;
    # actual filesystem links above are instead materialized to target bytes.
    archive_link_texts = []
    for name, expected_hash in expected_links.items():
        if not included_source_name(name) or name in links:
            continue
        path = root / name
        if not path.is_file() or path.is_symlink() or sha256(path) != expected_hash:
            raise ValueError(f"Pinned archive source symlink is missing or replaced: {root}/{name}")
        expected[name] = expected_hash
        archive_link_texts.append({"path": name, "sha256": expected_hash,
                                   "representation": "original-archive-link-text"})
    for name, path in files:
        canonical = path.resolve().relative_to(root.resolve()).as_posix()
        if name not in overlays and expected.get(canonical) != sha256(path):
            raise ValueError(f"Modified or untracked source differs from original archive: {root}/{name}")
    return {"kind": "public-source-zip", "filename": archive_name, "sha256": sha256(archive),
            "archive_link_texts": archive_link_texts,
            "materialized_aliases": [{"path": name, "target": target,
                "canonical_target": (root / name).resolve().relative_to(root.resolve()).as_posix()}
                for name, target in sorted(links.items())]}


def project_kind(root: Path, spec: dict) -> str:
    """Recognize overlay-only Putnam roots from matching pinned local evidence."""
    stage_path = root / ".lrh-stage.json"
    stage = json.loads(stage_path.read_text()) if stage_path.is_file() else {}
    if spec.get("kind") != "putnam" and stage.get("kind") != "putnam":
        return spec.get("kind", "repository")
    manifest = json.loads((root / "lake-manifest.json").read_text())
    mathlib = [entry for entry in manifest["packages"] if entry.get("name") == "mathlib"
               and entry.get("type") == "path"
               and repository(entry.get("url", "")) == repository(spec["repository"])
               and entry.get("rev") == spec["revision"]]
    if (stage.get("kind") != "putnam" or stage.get("lean_version") != spec["lean_version"]
            or stage.get("revision", stage.get("mathlib_revision")) != spec["revision"]
            or repository(spec["repository"]) != "https://github.com/leanprover-community/mathlib4"
            or len(mathlib) != 1):
        raise ValueError(f"Generated Putnam root lacks matching pinned stage/Mathlib identity: {root}")
    return "putnam"


def write_pack(root: Path, spec: dict, output: Path, source_archives: Path | None = None) -> list[dict]:
    if output.exists():
        raise ValueError(f"Refusing to overwrite source pack: {output}")
    temporary = output.with_suffix(output.suffix + ".part")
    output.parent.mkdir(parents=True, exist_ok=True)
    if temporary.exists():
        raise ValueError(f"Partial source pack already exists: {temporary}; choose a fresh export directory")
    try:
        manifest = json.loads((root / "lake-manifest.json").read_text())
        packages_dir = root / manifest.get("packagesDir", ".lake/packages")
        package_bases = [(entry, (root / entry["dir"] if entry["type"] == "path"
                                else packages_dir / entry["name"].strip("«»"))) for entry in manifest["packages"]]
        provenance = [authenticate_tree(root, spec["repository"], spec["revision"], source_archives,
            overlays=set(OVERLAYS), exclude_paths={base.resolve() for _, base in package_bases},
            generated=project_kind(root, spec) == "putnam")]
        for entry, base in package_bases:
            # Existing normalized Mathlib path declarations retain url/rev.
            if not entry.get("url") or not entry.get("rev"):
                raise ValueError(f"Export requires source URL/revision for path package: {entry['name']}")
            provenance.append({"package": entry["name"], **authenticate_tree(
                base, entry["url"], entry["rev"], source_archives)})
        with temporary.open("xb") as raw, gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as compressed, \
                tarfile.open(fileobj=compressed, mode="w|") as archive:
            for relative, path in source_files(root, exclude_paths={base.resolve() for _, base in package_bases}):
                write_member(archive, relative, path.read_bytes(), 0o755 if path.stat().st_mode & 0o111 else 0o644)
            for entry, base in package_bases:
                if not base.is_dir():
                    raise ValueError(f"Package source is missing: {base}")
                for relative, path in source_files(base):
                    name = (base.relative_to(root) / relative).as_posix()
                    write_member(archive, name, path.read_bytes(), 0o755 if path.stat().st_mode & 0o111 else 0o644)
                # Path Mathlib snapshots intentionally use an unborn Git stub.
                # Preserve its public origin too, because cache/release tools use it.
                expected = entry.get("rev") if entry["type"] == "git" else None
                url = entry.get("url")
                if (base / ".git").exists() and not url:
                    result = subprocess.run(["git", "-C", str(base), "remote", "get-url", "origin"],
                                            capture_output=True, text=True, check=True, env=GIT_ENV)
                    url = result.stdout.strip()
                for name, data, mode in git_metadata(base, expected, url):
                    write_member(archive, (base.relative_to(root) / name).as_posix(), data, mode)
        temporary.replace(output)
        return provenance
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def export_sources(env_map_path: Path, output_dir: Path, benchmark_path: Path | None = None,
                   source_archives: Path | None = None) -> dict:
    binding = load_environment_map(env_map_path)
    output_dir = Path(output_dir).expanduser().resolve()
    if output_dir.exists():
        raise ValueError(f"Refusing to overwrite source export directory: {output_dir}")
    for root in binding.paths.values():
        if output_dir.is_relative_to(root) or root.is_relative_to(output_dir):
            raise ValueError("Source export must be separate from every input project")
    benchmark = Path(benchmark_path) if benchmark_path else ROOT / "data/benchmark_data_warmup.jsonl"
    rows = [json.loads(line) for line in benchmark.read_text(encoding="utf-8").splitlines() if line.strip()]
    # Every supplied row/version must be represented; a partial-source submission
    # should be produced from an explicitly selected benchmark input instead.
    for row in rows:
        url = repository(row.get("url") or "https://github.com/leanprover-community/mathlib4")
        for version in row["version_info"]:
            lean, revision = next(iter(version.items()))
            matches = [sid for sid in binding.paths if (
                repository(binding.requirements["snapshots"][sid]["repository"]) == url
                and binding.requirements["snapshots"][sid]["lean_version"] == lean
                and binding.requirements["snapshots"][sid]["revision"] == revision)]
            if len(matches) != 1:
                raise ValueError(f"No unique source binding for {row['name']} {lean}@{revision}")
    for sid, root in binding.paths.items():
        verify_source(root, binding.requirements["snapshots"][sid])
        source_roots(root)  # Reject package paths outside the included project.
    output_dir.mkdir(parents=True)
    snapshots = {}
    for sid, root in sorted(binding.paths.items()):
        spec = binding.requirements["snapshots"][sid]
        pack_name = "packs/" + sid + ".tar.gz"
        provenance = write_pack(root, spec, output_dir / pack_name, source_archives)
        overlays = {name: (root / name).read_text(encoding="utf-8") for name in OVERLAYS if (root / name).is_file()}
        overlays[".lrh-stage.json"] = json.dumps({"schema_version": 1, "kind": project_kind(root, spec),
            "lean_version": spec["lean_version"], "revision": spec["revision"]}, indent=2) + "\n"
        snapshots[sid] = {"pack": pack_name, "sha256": sha256(output_dir / pack_name),
                          "bytes": (output_dir / pack_name).stat().st_size, "overlays": overlays,
                          "source_provenance": provenance}
    value = {"schema_version": 1, "format": PACK_FORMAT, "requirements": binding.requirements,
             "rows": rows, "snapshots": snapshots}
    manifest = output_dir / "environment-setup.json"
    atomic_json(manifest, value)
    return {"manifest": str(manifest), "snapshots": len(snapshots), "rows": len(rows),
            "source_pack_bytes": sum(item["bytes"] for item in snapshots.values())}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--env-map", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--benchmark", type=Path)
    parser.add_argument("--source-archives", type=Path,
                        help="Cached original GitHub ZIPs for extracted projects/path dependencies; never fetched")
    args = parser.parse_args()
    print(json.dumps(export_sources(args.env_map, args.output_dir, args.benchmark, args.source_archives), indent=2))


if __name__ == "__main__":
    main()
