#!/usr/bin/env python3
"""Prepare pinned Lean project sources using already installed exact toolchains."""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from harness.environments import EnvironmentMap, load_environment_map, validate_dependencies, validate_snapshot
from lean_tools import lean_launch, lean_source
from lean_tools.proof_example_search import imported_modules
from lean_tools.task import normalize_arena_row

RECEIPT = ".lrh-setup.json"
PACK_FORMAT = "lean-project-sources-tar-gzip-v1"
UPSTREAM_FORMAT = "lean-project-upstream-v1"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def atomic_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", prefix="." + path.name,
                                     suffix=".part", dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        try:
            json.dump(value, stream, indent=2, ensure_ascii=False)
            stream.write("\n")
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def relative_path(value: object) -> PurePosixPath:
    if not isinstance(value, str) or not value or "\\" in value:
        raise ValueError("Expected a nonempty portable relative path")
    path = PurePosixPath(value)
    if path.is_absolute() or any(part in {"", ".", ".."} for part in value.split("/")) or ":" in value:
        raise ValueError(f"Unsafe relative path: {value}")
    return path


def load_setup(path: Path) -> dict:
    value = json.loads(Path(path).read_text(encoding="utf-8"))
    requirements = value.get("requirements", {})
    snapshots = value.get("snapshots")
    if (value.get("schema_version") != 1 or value.get("format") not in {PACK_FORMAT, UPSTREAM_FORMAT}
            or requirements.get("schema_version") != 1
            or not isinstance(requirements.get("snapshots"), dict)
            or not isinstance(snapshots, dict) or not snapshots
            or set(snapshots) - requirements["snapshots"].keys()
            or not isinstance(value.get("rows"), list)):
        raise ValueError("Unsupported environment setup manifest")
    names = set()
    for row in value["rows"]:
        if not isinstance(row, dict) or not isinstance(row.get("name"), str) or row["name"] in names:
            raise ValueError("Setup rows require unique names")
        names.add(row["name"])
    for sid, item in snapshots.items():
        spec = requirements["snapshots"][sid]
        if (not re.fullmatch(r"[A-Za-z0-9._-]+", sid) or sid in {".", ".."}
                or not isinstance(item, dict) or not isinstance(spec, dict)
                or not isinstance(spec.get("repository"), str) or not spec["repository"].startswith("https://")
                or not re.fullmatch(r"v4\.\d+\.\d+(?:-rc\d+)?", spec.get("lean_version", ""))
                or any(not re.fullmatch(r"[0-9a-f]{40}", spec.get(key, "")) for key in ("revision", "lean_commit"))
                or not isinstance(spec.get("required_files"), dict) or not spec["required_files"]):
            raise ValueError(f"Invalid pinned source requirement: {sid}")
        if not isinstance(item.get("overlays"), dict):
            raise ValueError(f"Invalid source overlays: {sid}")
        if value["format"] == PACK_FORMAT:
            relative_path(item.get("pack"))
            if not re.fullmatch(r"[0-9a-f]{64}", item.get("sha256", "")):
                raise ValueError(f"Invalid source pack identity/overlays: {sid}")
        for name, expected in spec["required_files"].items():
            relative_path(name)
            if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
                raise ValueError(f"Invalid required file hash: {sid}/{name}")
        for name, content in item["overlays"].items():
            relative_path(name)
            if name not in {"lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json", ".lrh-stage.json"} or not isinstance(content, str):
                raise ValueError(f"Unsupported source overlay: {sid}/{name}")
        if value["format"] == UPSTREAM_FORMAT:
            from scripts.source_fetch import source_plan
            source_plan(spec, item)
    for row in value["rows"]:
        if not isinstance(row.get("version_info"), list) or not row["version_info"]:
            raise ValueError(f"Setup row has no pinned version_info: {row['name']}")
        url = repository(row.get("url") or "https://github.com/leanprover-community/mathlib4")
        for entry in row["version_info"]:
            if not isinstance(entry, dict) or len(entry) != 1:
                raise ValueError(f"Malformed version_info: {row['name']}")
            lean, revision = next(iter(entry.items()))
            matches = [sid for sid in snapshots if (
                repository(requirements["snapshots"][sid]["repository"]) == url
                and requirements["snapshots"][sid]["lean_version"] == lean
                and requirements["snapshots"][sid]["revision"] == revision)]
            if len(matches) != 1:
                raise ValueError(f"Setup row lacks a unique included snapshot: {row['name']} {lean}@{revision}")
    return value


def unpack_source(pack: Path, destination: Path) -> None:
    """Extract only regular files/directories, rejecting links and path tricks."""
    destination = Path(destination)
    if destination.exists():
        raise ValueError(f"Source extraction destination already exists: {destination}")
    destination.mkdir(parents=True)
    seen = set()
    try:
        with tarfile.open(pack, "r:gz") as archive:
            for member in archive:
                name = relative_path(member.name)
                if str(name) in seen or str(name) == RECEIPT:
                    raise ValueError(f"Duplicate/reserved source pack member: {member.name}")
                seen.add(str(name))
                target = destination.joinpath(*name.parts)
                if not (member.isfile() or member.isdir()):
                    raise ValueError(f"Source pack links/special files are forbidden: {member.name}")
                if member.isdir():
                    target.mkdir(parents=True, exist_ok=True)
                else:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    source = archive.extractfile(member)
                    assert source is not None
                    with source, target.open("xb") as out:
                        shutil.copyfileobj(source, out)
                    target.chmod(0o755 if member.mode & 0o111 else 0o644)
        # File-only packs cannot encode empty Git directories. Detached/shallow
        # checkouts may have no refs files, but Git still requires refs/ and
        # objects/ to recognize their included HEAD/config/object evidence.
        for marker in destination.rglob(".git"):
            if marker.is_dir() and (marker / "HEAD").is_file():
                for name in ("refs", "objects"):
                    (marker / name).mkdir(exist_ok=True)
    except BaseException:
        shutil.rmtree(destination)
        raise


def verify_source(root: Path, spec: dict) -> None:
    for relative, expected in spec["required_files"].items():
        target = (root / relative).resolve()
        if not target.is_relative_to(root.resolve()) or not target.is_file() or sha256(target) != expected:
            raise ValueError(f"Pinned source/configuration changed or missing: {relative}")


def repository(value: str) -> str:
    return value.rstrip("/").removesuffix(".git")


def rows_for_snapshot(value: dict, sid: str) -> list[dict]:
    spec = value["requirements"]["snapshots"][sid]
    result = []
    for row in value["rows"]:
        url = row.get("url") or "https://github.com/leanprover-community/mathlib4"
        if repository(url) == repository(spec["repository"]) and any(
                entry.get(spec["lean_version"]) == spec["revision"] for entry in row.get("version_info", [])):
            result.append(normalize_arena_row(row))
    return result


def toolchain_problem(elan_home: Path, spec: dict) -> str | None:
    install = elan_home / "toolchains" / ("leanprover/lean4:" + spec["lean_version"]).replace("/", "--").replace(":", "---")
    for relative in ("bin/lean", "bin/lake", "lib/lean/Init.olean", "include/lean/version.h", "src/lean/Init.lean"):
        if not (install / relative).is_file():
            return f"missing supplied toolchain file: {install / relative}"
    with (install / "lib/lean/Init.olean").open("rb") as stream:
        prefix = stream.read(128)
    if not prefix.startswith(b"olean") or spec["lean_commit"].encode() not in prefix:
        return f"compiler commit mismatch: {install}"
    if '#define LEAN_PLATFORM_TARGET "x86_64-unknown-linux-gnu"' not in (install / "include/lean/version.h").read_text():
        return f"toolchain is not native Linux x86_64: {install}"
    for relative in ("bin/elan", "bin/lean", "bin/lake"):
        if not (elan_home / relative).is_file() or not os.access(elan_home / relative, os.X_OK):
            return f"missing supplied elan launcher: {elan_home / relative}"
    return None


def source_roots(root: Path) -> list[tuple[str | None, Path]]:
    manifest = json.loads((root / "lake-manifest.json").read_text())
    packages_dir = root / manifest.get("packagesDir", ".lake/packages")
    result = [(None, root)]
    for entry in manifest["packages"]:
        base = root / entry["dir"] if entry["type"] == "path" else packages_dir / entry["name"].strip("«»")
        result.append((entry["name"], base / (entry.get("subDir") or "")))
    for _, path in result:
        if not path.resolve().is_relative_to(root.resolve()):
            raise ValueError(f"Package source escapes the managed snapshot: {path}")
    return result


def import_targets(root: Path, rows: list[dict]) -> list[tuple[str | None, str]]:
    roots = source_roots(root)
    pending = []
    for row in rows:
        pending.extend(imported_modules(lean_source.exact_source_prefix(normalize_arena_row(row), root).text))
    targets, seen = set(), set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        relative = Path(*module.split(".")).with_suffix(".lean")
        found = next(((package, source / relative) for package, source in roots if (source / relative).is_file()), None)
        if found is None:
            continue  # Lean/Lake standard-library imports are supplied by the toolchain.
        package, source = found
        targets.add((package, module))
        if package == "mathlib":
            continue  # Mathlib's cache CLI computes this transitive closure.
        pending.extend(imported_modules(source.read_text(encoding="utf-8")))
    return sorted(targets, key=lambda item: (item[0] or "", item[1]))


def module_build_order(root: Path, modules: list[str]) -> list[tuple[str | None, str, Path]]:
    """Dependency-first module targets, including Mathlib only when needed.

    Serial Lake invocations alone do not constrain the jobs inside an import
    graph. Building missing module artifacts in this order avoids scheduling
    many missing Lean imports in one invocation during cache fallback.
    """
    roots = source_roots(root)
    seen, visiting, order = set(), set(), []

    def visit(module: str) -> None:
        if module in seen:
            return
        if module in visiting:
            raise ValueError(f"Cyclic source imports involving {module}")
        relative = Path(*module.split(".")).with_suffix(".lean")
        found = next(((package, source, source / relative) for package, source in roots
                      if (source / relative).is_file()), None)
        if found is None:
            seen.add(module)  # Standard-library source/artifacts are supplied.
            return
        package, source_root, source = found
        visiting.add(module)
        for dependency in imported_modules(source.read_text(encoding="utf-8")):
            visit(dependency)
        visiting.remove(module)
        seen.add(module)
        order.append((package, module, source_root / ".lake/build/lib/lean" / relative.with_suffix(".olean")))

    for module in modules:
        visit(module)
    return order


def prepare_snapshot(root: Path, spec: dict, rows: list[dict], elan_home: Path, cache_dir: Path) -> dict:
    """The only build/download boundary; normal harness execution never calls it."""
    toolchain = "leanprover/lean4:" + spec["lean_version"]
    lake = elan_home / "bin/lake"
    child = {key: value for key, value in os.environ.items()
             if not key.startswith(("LEAN_", "LAKE_", "ELAN_"))}
    child.update(ELAN_HOME=str(elan_home), ELAN_TOOLCHAIN=toolchain,
                 PATH=str(elan_home / "bin") + os.pathsep + child.get("PATH", ""),
                 LEAN_NUM_THREADS="1", OMP_NUM_THREADS="1", RAYON_NUM_THREADS="1",
                 LAKE_JOBS="1",
                 MATHLIB_CACHE_DIR=str(cache_dir))
    commands = root / ".lrh-setup-commands.jsonl"
    # Verify materialization before invoking Lake, which otherwise may try to
    # repair a missing Git dependency by fetching it from the network.
    roots = source_roots(root)
    manifest = json.loads((root / "lake-manifest.json").read_text())
    packages = root / manifest.get("packagesDir", ".lake/packages")
    for entry, (_, package_root) in zip(manifest["packages"], roots[1:]):
        if not package_root.is_dir():
            raise ValueError(f"Bundled package sources missing: {package_root}")
        if entry["type"] == "git" and lean_launch._git_head(packages / entry["name"].strip("«»")) != entry["rev"]:
            raise ValueError(f"Bundled package revision differs: {entry['name']}")
        base = root / entry["dir"] if entry["type"] == "path" else packages / entry["name"].strip("«»")
        if (base / ".git").is_dir():
            head = subprocess.run(["git", "-C", str(base), "rev-parse", "--verify", "HEAD"],
                                  env=child, capture_output=True, text=True)
            if head.returncode == 0:
                # Packs omit checkout-specific index stat data. Reconstruct it
                # from the included real commit objects before Lake asks Git
                # whether the dependency has local changes.
                indexed = subprocess.run(["git", "-C", str(base), "read-tree", "HEAD"],
                                         env=child, capture_output=True, text=True)
                if indexed.returncode:
                    raise ValueError(f"Bundled package Git objects are incomplete: {entry['name']}\n{indexed.stderr}")

    def run(arguments: list[str], *, optional: bool = False) -> subprocess.CompletedProcess:
        arguments = ["--keep-toolchain", *arguments]
        print(f"[{root.name}] lake {' '.join(arguments)}", file=sys.stderr, flush=True)
        result = subprocess.run(["/usr/bin/nice", "-n", "10", str(lake), *arguments], cwd=root,
                                env=child, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        with commands.open("a", encoding="utf-8") as stream:
            stream.write(json.dumps({"lake_args": arguments, "returncode": result.returncode,
                                     "output": result.stdout}) + "\n")
        verify_source(root, spec)
        if result.returncode and not optional:
            raise RuntimeError(f"Environment setup failed: lake {' '.join(arguments)}\n{result.stdout[-4000:]}")
        return result

    # Reconfigure at the stable final path; this creates the correct version's
    # per-package or workspace-indexed compiled lakefile artifacts and traces.
    run(["-R", "env", "lean", "--version"])
    targets = import_targets(root, rows)
    cache_modules = sorted({module for package, module in targets
                            if package == "mathlib" and (module == "Mathlib" or module.startswith("Mathlib."))})
    cache_result = None
    built = 0

    def build_missing(modules: list[str]) -> None:
        nonlocal built
        for package, module, binary in module_build_order(root, modules):
            if binary.is_file():
                continue  # Exact source packs and matching cache keys are fixed.
            target = (f"@{package}/" if package else "") + f"+{module}:olean"
            run(["build", target])
            built += 1

    if cache_modules:
        cache_dir.mkdir(parents=True, exist_ok=True)
        build_missing(["Cache.Main"])
        # The pinned CLI accepts module arguments throughout this source matrix.
        # An unavailable cache is recorded, then Lake builds the requested imports.
        cache_result = run(["exe", "cache", "get", *cache_modules], optional=True).returncode
    # Prefix imports avoid compiling the original proof/source-file tail.
    # Missing source modules are built dependency-first, one target at a time.
    direct = set()
    for row in rows:
        for module in imported_modules(lean_source.exact_source_prefix(row, root).text):
            direct.add(module)
    build_missing(sorted(direct))
    # Cache scripts can reconfigure dependency options. Compile/validate the
    # final configuration using the pinned Lake, never by editing trace JSON.
    run(["env", "lean", "--version"])
    return {"cache_returncode": cache_result, "import_targets": len(targets), "built_targets": built}


def environment_map_text(requirements: Path, elan_home: Path, paths: dict[str, Path]) -> str:
    return ('schema_version = 1\nelan_home = ' + json.dumps(str(elan_home)) + '\nrequirements = '
            + json.dumps(str(requirements)) + '\n\n[paths]\n'
            + "".join(json.dumps(sid) + " = " + json.dumps(str(root)) + "\n" for sid, root in sorted(paths.items())))


def install(manifest_path: Path, env_root: Path, elan_home: Path, output_map: Path,
            *, reuse_map: Path | None = None, dry_run: bool = False, cache_dir: Path | None = None) -> dict:
    manifest_path = Path(manifest_path).resolve()
    value = load_setup(manifest_path)
    upstream = value["format"] == UPSTREAM_FORMAT
    env_root, elan_home, output_map = (Path(p).expanduser().resolve() for p in (env_root, elan_home, output_map))
    cache_dir = Path(cache_dir).expanduser().resolve() if cache_dir else env_root / "download-cache"
    source_cache = Path(os.environ.get("HARNESS_SOURCE_CACHE_ROOT", cache_dir / "sources")).expanduser().resolve()
    reuse = load_environment_map(reuse_map) if reuse_map else None
    paths, plan = {}, []
    identity = sha256(manifest_path)
    for sid, item in value["snapshots"].items():
        spec = value["requirements"]["snapshots"][sid]
        adopted = reuse is not None and sid in reuse.paths
        if adopted and reuse.requirements["snapshots"].get(sid) != spec:
            raise ValueError(f"Reuse requirement differs from setup manifest: {sid}")
        root = reuse.paths[sid] if adopted else env_root / sid
        pack = None if upstream else manifest_path.parent / str(relative_path(item["pack"]))
        if pack is not None and not pack.resolve().is_relative_to(manifest_path.parent):
            raise ValueError("Source pack escaped its manifest directory")
        problem = toolchain_problem(elan_home, spec)
        paths[sid] = root
        plan.append({"snapshot_id": sid, "action": "reuse" if adopted else "prepare", "root": str(root),
                     **({"source_mode": "upstream"} if upstream else {"pack_present": pack.is_file()}),
                     "toolchain_problem": problem,
                     "rows": len(rows_for_snapshot(value, sid))})
    if dry_run:
        return {"status": "plan", "snapshots": plan, "output_map": str(output_map)}
    # No incomplete setup may replace a previously published map.
    if output_map.exists():
        raise ValueError(f"Refusing to overwrite environment map: {output_map}; choose a new output")
    for item in plan:
        if item["toolchain_problem"]:
            raise ValueError(item["toolchain_problem"])
        if item["action"] != "reuse" and not upstream and not item["pack_present"]:
            raise ValueError(f"Missing bundled source pack for {item['snapshot_id']}; run export_environment_sources.py first")
    env_root.mkdir(parents=True, exist_ok=True)
    requirements_path = env_root / ("requirements-" + identity[:20] + ".json")
    if not requirements_path.exists():
        atomic_json(requirements_path, value["requirements"])
    elif json.loads(requirements_path.read_text()) != value["requirements"]:
        raise ValueError("Existing generated requirements differ")
    binding = EnvironmentMap(output_map, requirements_path, paths, value["requirements"], elan_home)
    results = []
    for entry in plan:
        sid, root = entry["snapshot_id"], paths[entry["snapshot_id"]]
        print(f"[{sid}] {entry['action']} {root}", file=sys.stderr, flush=True)
        spec, item = value["requirements"]["snapshots"][sid], value["snapshots"][sid]
        rows = rows_for_snapshot(value, sid)
        if entry["action"] == "reuse":
            # Explicit adoption is read-only, including on validation failure.
            validate_snapshot(binding, sid, elan_home=elan_home)
            for row in rows:
                validate_dependencies(row, root, elan_home=elan_home)
            results.append({"snapshot_id": sid, "status": "reused"})
            continue
        lock_path = env_root / ".locks" / (sid + ".lock")
        lock_path.parent.mkdir(exist_ok=True)
        with lock_path.open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            if not upstream:
                pack = manifest_path.parent / item["pack"]
                if sha256(pack) != item["sha256"]:
                    raise ValueError(f"Source pack SHA-256 mismatch: {sid}")
            receipt = {"schema_version": 1, "setup_sha256": identity, "snapshot_id": sid, "status": "incomplete"}
            if root.exists() or root.is_symlink():
                state = root / RECEIPT
                if root.is_symlink() or not state.is_file() or any(json.loads(state.read_text()).get(key) != receipt[key]
                                              for key in ("schema_version", "setup_sha256", "snapshot_id")):
                    raise ValueError(f"Refusing to change an unmanaged or different setup root: {root}")
            else:
                with tempfile.TemporaryDirectory(prefix=".source-", dir=env_root) as temporary:
                    staged = Path(temporary) / "project"
                    if upstream:
                        from scripts.source_fetch import materialize
                        materialize(staged, spec, item, source_cache)
                    else:
                        unpack_source(pack, staged)
                    for name, content in item["overlays"].items():
                        target = staged / name
                        if target.is_symlink() or not target.resolve().is_relative_to(staged.resolve()):
                            raise ValueError(f"Source overlay aliases another file: {name}")
                        target.write_text(content, encoding="utf-8")
                    verify_source(staged, spec)
                    atomic_json(staged / RECEIPT, receipt)
                    staged.rename(root)
            verify_source(root, spec)
            prior = json.loads((root / RECEIPT).read_text())
            if prior.get("status") != "ready":
                details = prepare_snapshot(root, spec, rows, elan_home, cache_dir)
            else:
                details = prior.get("preparation", {})
            validate_snapshot(binding, sid, elan_home=elan_home)
            for row in rows:
                validate_dependencies(row, root, elan_home=elan_home)
            atomic_json(root / RECEIPT, {**receipt, "status": "ready", "preparation": details})
            results.append({"snapshot_id": sid, "status": "ready"})
    output_map.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", prefix="." + output_map.name,
                                     suffix=".part", dir=output_map.parent, delete=False) as stream:
        temporary_map = Path(stream.name)
        stream.write(environment_map_text(requirements_path, elan_home, paths))
    try:
        os.link(temporary_map, output_map)  # Atomic publication without overwrite.
    finally:
        temporary_map.unlink(missing_ok=True)
    return {"status": "ready", "snapshots": results, "output_map": str(output_map),
            "next": "Run harness doctor with this environment map before preparing a run."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--env-root", type=Path, required=True)
    parser.add_argument("--elan-home", type=Path, required=True)
    parser.add_argument("--output-map", type=Path, required=True)
    parser.add_argument("--cache-dir", type=Path)
    parser.add_argument("--reuse-map", type=Path)
    parser.add_argument("--dry-run", "--plan", action="store_true")
    args = parser.parse_args()
    print(json.dumps(install(args.manifest, args.env_root, args.elan_home, args.output_map,
                             reuse_map=args.reuse_map, dry_run=args.dry_run, cache_dir=args.cache_dir), indent=2))


if __name__ == "__main__":
    main()
