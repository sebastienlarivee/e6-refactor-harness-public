"""Explicit, read-only bindings to pinned prebuilt Lean snapshots."""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import re
from pathlib import Path
import subprocess
import tomllib
from typing import Any

from lean_tools import arena_workflow as arena
from lean_tools import lean_launch, lean_source
from lean_tools.proof_example_search import imported_modules
from .benchmark import Benchmark, digest, file_hash

DATA = Path(__file__).resolve().parents[1] / "data"


@dataclass(frozen=True)
class EnvironmentMap:
    path: Path
    requirements_path: Path
    paths: dict[str, Path]
    requirements: dict
    elan_home: Path | None = None

    @property
    def identity(self) -> str:
        return digest({"map_sha256": file_hash(self.path),
            "requirements_sha256": file_hash(self.requirements_path),
            "paths": {key: str(value) for key, value in self.paths.items()}})


def _explicit_path(value: Any, base: Path, label: str) -> Path:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{label}: an explicit path is required")
    path = Path(value).expanduser()
    return (base / path).resolve() if not path.is_absolute() else path.resolve()


def load_environment_map(path: str | Path) -> EnvironmentMap:
    path = Path(path).resolve()
    with path.open("rb") as stream:
        value = tomllib.load(stream)
    if value.get("schema_version") != 1 or not isinstance(value.get("paths"), dict):
        raise ValueError("Environment map requires schema_version=1 and [paths]")
    unexpected = set(value) - {"schema_version", "requirements", "elan_home", "paths"}
    if unexpected:
        raise ValueError(f"Unknown environment map fields: {', '.join(sorted(unexpected))}")
    requirements_path = _explicit_path(value.get("requirements"), path.parent, "requirements")
    requirements = json.loads(requirements_path.read_text(encoding="utf-8"))
    if requirements.get("schema_version") != 1 or not isinstance(requirements.get("snapshots"), dict) or not isinstance(requirements.get("tasks", {}), dict):
        raise ValueError("Unsupported environment requirements manifest")
    for name, spec in requirements["snapshots"].items():
        if (not re.fullmatch(r"[A-Za-z0-9._-]+", name) or not isinstance(spec, dict)
                or not isinstance(spec.get("repository"), str) or not spec["repository"].startswith("https://")
                or not isinstance(spec.get("lean_version"), str)
                or not re.fullmatch(r"v4\.\d+\.\d+(?:-rc\d+)?", spec["lean_version"])
                or any(not isinstance(spec.get(key), str) or not re.fullmatch(r"[0-9a-f]{40}", spec[key])
                    for key in ("revision", "lean_commit"))
                or not isinstance(spec.get("required_files"), dict) or not spec["required_files"]):
            raise ValueError(f"Snapshot {name} requires repository, pinned release/revision/compiler and source hashes")
        for relative, expected in spec["required_files"].items():
            if (not isinstance(relative, str) or Path(relative).is_absolute() or ".." in Path(relative).parts
                    or not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected)):
                raise ValueError(f"Snapshot {name} has an invalid source/configuration hash requirement")
    paths = {name: _explicit_path(item, path.parent, f"paths.{name}") for name, item in value["paths"].items()}
    if set(paths) - requirements["snapshots"].keys():
        raise ValueError("Environment map contains a snapshot with no repository/version/revision requirement")
    if len(set(paths.values())) != len(paths):
        raise ValueError("Two snapshot identities cannot bind the same project root")
    elan_home = _explicit_path(value["elan_home"], path.parent, "elan_home") if value.get("elan_home") else None
    return EnvironmentMap(path, requirements_path, paths, requirements, elan_home)


def _elan(env_map: EnvironmentMap, elan_home: Path | None) -> Path:
    result = Path(elan_home).resolve() if elan_home is not None else env_map.elan_home
    if result is None:
        raise ValueError("An explicit elan_home is required; environment discovery is disabled")
    return result


def validate_snapshot(env_map: EnvironmentMap, snapshot_id: str, *, elan_home: Path | None = None) -> dict:
    """Read identities and compiled Lake config traces; never invoke Lake setup."""
    spec = env_map.requirements["snapshots"].get(snapshot_id)
    if not isinstance(spec, dict) or snapshot_id not in env_map.paths:
        raise ValueError(f"Missing explicit binding for snapshot {snapshot_id}")
    root = env_map.paths[snapshot_id]
    if not root.is_dir():
        raise ValueError(f"Missing prebuilt snapshot {snapshot_id}: {root}; provision it before run")
    stage = root / ".lrh-stage.json"
    if stage.is_file():
        staged = json.loads(stage.read_text())
        actual_revision = staged.get("revision", staged.get("mathlib_revision"))
        if staged.get("lean_version") != spec["lean_version"] or actual_revision != spec["revision"]:
            raise ValueError(f"Snapshot repository revision/version differs from requirement: {snapshot_id}")
    else:
        # Organizer prebuilt Git snapshots do not need the internal extraction marker.
        result = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"], capture_output=True, text=True, timeout=10)
        if result.returncode or result.stdout.strip() != spec["revision"]:
            raise ValueError(f"Snapshot lacks pinned revision evidence: {snapshot_id}")
    required = spec.get("required_files")
    if not isinstance(required, dict) or not required:
        raise ValueError(f"Snapshot lacks explicit source/configuration hashes: {snapshot_id}")
    for relative, expected in required.items():
        target = (root / relative).resolve()
        if not target.is_relative_to(root) or not target.is_file() or file_hash(target) != expected:
            raise ValueError(f"Pinned snapshot source/configuration changed or missing: {snapshot_id}/{relative}")
    environment = {"ELAN_HOME": str(_elan(env_map, elan_home))}
    guard = lean_launch.workspace_guard(root, environment)
    if guard["toolchain"] != "leanprover/lean4:" + spec["lean_version"] or guard["githash"] != spec["lean_commit"]:
        raise ValueError(f"Pinned compiler identity differs: {snapshot_id}")
    if guard["platform"] != "x86_64-unknown-linux-gnu":
        raise ValueError(f"Unsupported prebuilt compiler platform: {guard['platform']}")
    return {"snapshot_id": snapshot_id, "project_root": str(root),
        "repository": spec["repository"], "revision": spec["revision"],
        "lean_version": spec["lean_version"], "lean_commit": spec["lean_commit"],
        "workspace_guard_sha256": digest(guard), "workspace": guard}


def _roots(project: Path, elan_home: Path) -> list[tuple[Path, Path]]:
    manifest = json.loads((project / "lake-manifest.json").read_text())
    packages = project / manifest.get("packagesDir", ".lake/packages")
    roots = [(project, project / ".lake/build/lib/lean")]
    for package in manifest["packages"]:
        root = (project / package["dir"] if package["type"] == "path" else packages / package["name"].strip("«»")) / (package.get("subDir") or "")
        roots.append((root.resolve(), root / ".lake/build/lib/lean"))
    name = (project / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
    toolchain = (elan_home / "toolchains" / name).resolve()
    roots.extend([(toolchain / "src/lean", toolchain / "lib/lean"),
                  (toolchain / "src/lean/lake", toolchain / "lib/lean")])
    return roots


def validate_dependencies(row: dict, project: Path, *, elan_home: Path) -> dict:
    """Check the exact prefix's recursive source imports and existing .olean files.

    Source bytes and compiled header/size identities are frozen in the report.
    This is materialization validation, not an exhaustive hash of a large cache.
    Lean execution in doctor independently validates the original declaration.
    """
    roots = _roots(project.resolve(), elan_home.resolve())
    prefix = lean_source.exact_source_prefix(row, project)
    pending, seen, sources, compiled = imported_modules(prefix.text), set(), [], []
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        relative = Path(*module.split(".")).with_suffix(".lean")
        found = next(((source / relative, binary / relative.with_suffix(".olean"))
                      for source, binary in roots if (source / relative).is_file()), None)
        if found is None:
            raise ValueError(f"Missing cached source dependency {module} for {row['name']}")
        source, binary = found
        if not binary.is_file():
            raise ValueError(f"Missing compiled dependency {module}: {binary}; rebuild is disabled")
        with binary.open("rb") as stream:
            header = stream.read(128)
        if not header.startswith(b"olean"):
            raise ValueError(f"Invalid compiled Lean dependency header: {binary}")
        text = source.read_text(encoding="utf-8")
        sources.append({"module": module, "sha256": hashlib.sha256(text.encode()).hexdigest()})
        compiled.append({"module": module, "size": binary.stat().st_size,
            "header_sha256": hashlib.sha256(header).hexdigest()})
        pending.extend(imported_modules(text))
    return {"source_modules": len(sources), "compiled_modules": len(compiled),
        "source_closure_sha256": digest(sorted(sources, key=lambda x: x["module"])),
        "compiled_materialization_sha256": digest(sorted(compiled, key=lambda x: x["module"]))}


def _repository_url(value: str) -> str:
    return value.rstrip("/").removesuffix(".git")


def select_snapshots(row: dict, requirements: dict) -> dict:
    """Select explicit prebuilt snapshots from the input's source pins alone."""
    repository = _repository_url(row.get("url") or "https://github.com/leanprover-community/mathlib4")
    snapshots = []
    for entry in row["version_info"]:
        version, revision = next(iter(entry.items()))
        matches = [name for name, spec in requirements["snapshots"].items()
            if _repository_url(spec["repository"]) == repository
            and spec.get("lean_version") == version and spec.get("revision") == revision]
        if len(matches) != 1:
            raise ValueError(f"Unsupported source snapshot for {row['name']}: {repository}@{revision} ({version}); add explicit requirements and binding")
        snapshots.append(matches[0])
    return {"primary": snapshots[0], "compatibility": snapshots[1:]}


def _selection(row: dict, env_map: EnvironmentMap, scoring_policy: str) -> tuple[str, dict]:
    if scoring_policy == "legacy-v1":
        task = env_map.requirements.get("tasks", {}).get(row["name"])
        if task is None or digest(row) != task.get("row_sha256"):
            raise ValueError("Legacy scoring is only available for the frozen baseline originals")
        return task["label"], task[scoring_policy]
    return "proof-" + digest(row["name"])[:16], select_snapshots(row, env_map.requirements)


def resolve_benchmark(benchmark: Benchmark, env_map: EnvironmentMap | str | Path,
        output_dir: str | Path, *, scoring_policy: str = "arena-v1",
        selected: tuple[str, ...] | list[str] = (), elan_home: Path | None = None,
        validate: bool = True) -> list[dict]:
    """Materialize original task documents and per-proof, explicit host metadata."""
    if scoring_policy not in {"arena-v1", "legacy-v1"}:
        raise ValueError("Unsupported scoring policy")
    env_map = load_environment_map(env_map) if not isinstance(env_map, EnvironmentMap) else env_map
    elan_home = _elan(env_map, elan_home)
    output = Path(output_dir).resolve()
    selections = [(row, *_selection(row, env_map, scoring_policy)) for row in benchmark.rows]
    known = {row["name"] for row, _, _ in selections} | {label for _, label, _ in selections}
    if set(selected) - known:
        raise ValueError(f"Unknown selected proofs: {', '.join(sorted(set(selected) - known))}")
    if selected:
        selections = [item for item in selections if item[0]["name"] in selected or item[1] in selected]
    output.mkdir(parents=True, exist_ok=True)
    # Historical baseline catalogs are supported only by the explicit legacy API.
    catalog = json.loads((DATA / "proofs.json").read_text())["proofs"] if scoring_policy == "legacy-v1" else {}
    checked, versions, proofs = {}, {}, []
    for row, label, selection in selections:
        original = env_map.requirements.get("tasks", {}).get(row["name"], {}) if scoring_policy == "legacy-v1" else {}
        metadata = dict(catalog.get(label, {}))
        heartbeat = benchmark.heartbeats.get(row["name"])
        if scoring_policy == "legacy-v1":
            if not metadata:
                raise ValueError("Legacy scoring is only available for the frozen baseline originals")
            if heartbeat != metadata.get("published_reference_heartbeats", heartbeat):
                raise ValueError(f"{row['name']}: heartbeat reference differs from the frozen published value")
        task_path = output / "tasks" / f"{label}.json"
        task_path.parent.mkdir(exist_ok=True)
        task_document = {"schema_version": 1, "source": {"benchmark_sha256": benchmark.input_sha256,
            "heartbeat_sha256": benchmark.heartbeat_sha256, "row_sha256": digest(row)},
            "reference": {"heartbeat": heartbeat}, "row": row}
        if scoring_policy == "arena-v1":
            original_source = lean_source.candidate_text_from_bytes(
                lean_source.render_candidate_scaffold(row).encode("utf-8"))
            _, original_body = lean_source.extract_candidate_declaration(row, original_source)
            measured_tokens = lean_source.candidate_proof_token_count(original_body, scoring_policy)
            supplied_tokens = "proof_length" in row
            original_tokens = row["proof_length"] if supplied_tokens else measured_tokens
            token_source = "supplied_proof_length" if supplied_tokens else "measured_original_tokens"
            if not supplied_tokens:
                task_document["original_metrics"] = {"tokens": original_tokens, "token_source": token_source}
            metadata.update(scoring_policy=scoring_policy, original_tokens=original_tokens,
                original_measurement_tokens=measured_tokens, original_heartbeats=heartbeat,
                baseline_provenance={
                    "tokens": {"source": token_source, "value": original_tokens},
                    "heartbeats": {"source": "supplied_heartbeat" if heartbeat is not None else "pending_original_measurement",
                        "value": heartbeat}})
        task_path.write_text(json.dumps(task_document, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        entries, identities = {}, []
        snapshot_ids = [selection["primary"], *selection["compatibility"]]
        for sid in snapshot_ids:
            if sid not in env_map.paths:
                raise ValueError(f"Missing explicit binding for snapshot {sid}")
            project = env_map.paths[sid]
            if validate and sid not in checked:
                checked[sid] = validate_snapshot(env_map, sid, elan_home=elan_home)
            guard = arena.environment_fingerprint_guard_material(row, project)
            guard.pop("registry_key")
            frozen = original.get("environments", {}).get(sid)
            if frozen:
                if guard != frozen["guard"]:
                    raise ValueError(f"{row['name']}: source/environment guard differs for {sid}")
                fingerprint, lean_version = frozen["fingerprint"], frozen["lean_version"]
            else:
                # Bind this input to the validated source and compiler identities.
                if sid not in checked:
                    checked[sid] = validate_snapshot(env_map, sid, elan_home=elan_home)
                if sid not in versions:
                    result = subprocess.run([checked[sid]["workspace"]["executable"], "--version"], capture_output=True, text=True, timeout=10, check=True)
                    versions[sid] = result.stdout.strip()
                lean_version = versions[sid]
                material = {"schema": guard["instrumentation"], "lean_version": lean_version,
                    **{key: value for key, value in guard.items() if key not in {"schema_version", "instrumentation"}}}
                if material.get("measurement_helper_lean_args") == []:
                    material.pop("measurement_helper_lean_args")
                fingerprint = digest(material)
            key = arena.environment_fingerprint_registry_key(row, project)
            entry = {"task_id": row["name"], "project_root": str(project), "fingerprint": fingerprint,
                "lean_version": lean_version, "guard_sha256": arena.environment_fingerprint_guard_sha256(row, project)}
            entries[key] = entry
            identities.append({"snapshot_id": sid, "path": str(project), "fingerprint": fingerprint,
                "guard_sha256": entry["guard_sha256"], "repository": env_map.requirements["snapshots"][sid]["repository"],
                "revision": env_map.requirements["snapshots"][sid]["revision"],
                "snapshot_requirement_sha256": digest(env_map.requirements["snapshots"][sid])})
        registry = output / f"{label}-environment-fingerprints.json"
        registry.write_text(json.dumps({"schema_version": arena.FINGERPRINT_REGISTRY_SCHEMA_VERSION, "entries": entries}, indent=2) + "\n")
        if isinstance(metadata.get("original_measurement_evidence"), dict):
            evidence = dict(metadata["original_measurement_evidence"])
            evidence["path"] = str(DATA / "original-controls" / f"{label}.json")
            if file_hash(Path(evidence["path"])) != evidence["sha256"]:
                raise ValueError("Frozen original measurement evidence changed")
            metadata["original_measurement_evidence"] = evidence
        metadata.update(label=label, task_id=row["name"], task=str(task_path), task_sha256=file_hash(task_path),
            row_sha256=digest(row), primary=str(env_map.paths[selection["primary"]]),
            compatibility=[str(env_map.paths[sid]) for sid in selection["compatibility"]],
            registry_source=str(registry), environments=identities,
            environment_map_identity=env_map.identity, benchmark_identity=benchmark.identity,
            environment_map_path=str(env_map.path), environment_map_sha256=file_hash(env_map.path),
            environment_requirements_path=str(env_map.requirements_path),
            environment_requirements_sha256=file_hash(env_map.requirements_path),
            registry_source_sha256=file_hash(registry), elan_home=str(elan_home), published_reference_heartbeats=heartbeat)
        proofs.append(metadata)
    (output / "benchmark.json").write_text(json.dumps({**benchmark.to_dict(), "proofs": proofs}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return proofs


def verify_resolved_metadata(metadata: dict) -> dict:
    """Recheck explicit snapshot and source bindings before run, resume or export."""
    for path_key, hash_key in (("environment_map_path", "environment_map_sha256"),
            ("environment_requirements_path", "environment_requirements_sha256"),
            ("registry_source", "registry_source_sha256"), ("task", "task_sha256")):
        if file_hash(Path(metadata[path_key])) != metadata[hash_key]:
            raise ValueError(f"Frozen environment/input changed: {path_key}")
    binding = load_environment_map(metadata["environment_map_path"])
    if binding.identity != metadata["environment_map_identity"]:
        raise ValueError("Frozen environment map identity changed")
    _, row = arena.load_task(Path(metadata["task"]))
    if digest(row) != metadata["row_sha256"] or row["name"] != metadata["task_id"]:
        raise ValueError("Frozen original row identity changed")
    for environment in metadata["environments"]:
        sid = environment["snapshot_id"]
        if (binding.paths.get(sid) != Path(environment["path"])
                or digest(binding.requirements["snapshots"][sid]) != environment["snapshot_requirement_sha256"]):
            raise ValueError("Frozen snapshot binding or requirement changed")
        validate_snapshot(binding, sid, elan_home=Path(metadata["elan_home"]))
        entry = arena.environment_fingerprint_registry_entry(row, Path(environment["path"]),
            Path(metadata["registry_source"]), validate_guard=True)
        if any(entry[key] != environment[key] for key in ("fingerprint", "guard_sha256")):
            raise ValueError("Frozen environment guard changed")
    return {"status": "passed", "task_id": metadata["task_id"],
        "environment_count": len(metadata["environments"])}
