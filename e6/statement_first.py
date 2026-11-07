"""Host-built statement-only task and read-only first-pass project overlays.

The real task, original incumbent, and cached environments stay unchanged. The
overlays are mounted only in the first agent's filesystem namespace.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re

from lean_tools import arena_workflow as arena, lean_source, lean_launch


def statement_row(row: dict) -> dict:
    keys = ("name", "statement", "signature", "header", "contexts",
            "file_path", "proof_length", "version_info")
    result = {key: row[key] for key in keys if key in row}
    result["src"] = row["signature"] + " := by\n  skip\n"
    return result


def _module_imports(source: str) -> set[str]:
    return {name for match in re.finditer(
        r"(?m)^\s*(?:(?:public|meta)\s+)*import[ \t]+([^\r\n]+)",
        lean_source.lean_code_mask(source)) for name in match[1].split()}


def _dependent_modules(project: Path, file_path: str) -> set[str]:
    """Mask target and downstream proof data, preserving all prefix imports."""
    target = str(Path(file_path).with_suffix("")).replace(os.sep, ".")
    imports = {}
    for directory, children, names in os.walk(project):
        children[:] = [name for name in children if name not in {".lake", ".git"}]
        for name in names:
            if name.endswith(".lean"):
                path = Path(directory) / name
                module = str(path.relative_to(project).with_suffix("")).replace(os.sep, ".")
                imports[module] = _module_imports(path.read_text(encoding="utf-8"))
    excluded = {target}
    while True:
        expanded = excluded | {name for name, dependencies in imports.items() if dependencies & excluded}
        if expanded == excluded:
            return excluded
        excluded = expanded


def prepare_view(config: dict) -> dict:
    """Create a private immutable view before starting the first agent."""
    root = Path(config["root"]) / "preparation/statement-first"
    manifest = root / "view.json"
    if manifest.exists():
        return load_view(config)
    root.mkdir(parents=True, exist_ok=True)
    _, original_row = arena.load_task(Path(config["task"]))
    row = statement_row(original_row)
    registry = json.loads(Path(config["fingerprint_registry"]).read_text(encoding="utf-8"))
    overlays, directories, hidden_files, git_overlays = [], [], [], []
    empty = root / "empty"
    empty.write_text("", encoding="utf-8")
    for index, value in enumerate([config["primary"], *config["compatibility"]]):
        project = Path(value).resolve()
        guard = arena.environment_fingerprint_guard_material(row, project)
        if arena.is_project_resident(original_row):
            if ".lake" in Path(original_row["file_path"]).parts:
                raise ValueError("Statement-first source masking requires a target in the project source tree")
            source_path = arena.project_source_path(original_row, project)
            prefix = lean_source.exact_source_prefix(original_row, project).text
            redacted_source = prefix + row["src"]
            overlay = root / f"project-{index:03d}.lean"
            overlay.write_text(redacted_source, encoding="utf-8")
            overlays.append({"source": str(overlay), "target": str(source_path),
                             "sha256": arena.sha256_file(overlay)})
            guard["project_source_sha256"] = arena.sha256_bytes(redacted_source.encode("utf-8"))
            for module in _dependent_modules(project, original_row["file_path"]):
                relative = Path(*module.split("."))
                for build in (project / ".lake/build/lib/lean", project / ".lake/build/ir"):
                    parent = build / relative.parent
                    hidden_files.extend(str(path.resolve()) for path in parent.glob(relative.name + ".*")
                                        if path.is_file())
        # Git object stores can recover the original even after source masking.
        # The launcher still requires detached HEAD metadata for manifest pins.
        for directory, children, names in os.walk(project):
            if ".git" in children or ".git" in names:
                package = Path(directory)
                head = lean_launch._git_head(package, allow_unborn=True)
                git = root / f"git-{len(git_overlays):04d}"
                git.mkdir()
                (git / "HEAD").write_text((head or "ref: refs/heads/unborn") + "\n", encoding="utf-8")
                (git / "objects").mkdir()
                (git / "refs").mkdir()
                if ".git" in children:
                    target = str(package / ".git")
                    children.remove(".git")
                else:
                    pointer = root / f"git-pointer-{len(git_overlays):04d}"
                    pointer.write_text(f"gitdir: {git}\n", encoding="utf-8")
                    overlays.append({"source": str(pointer), "target": str(package / ".git"),
                                     "sha256": arena.sha256_file(pointer)})
                    target = str(git)
                git_overlays.append({"source": str(git), "target": target,
                                     "head": (git / "HEAD").read_text(encoding="utf-8")})
            # Executables/archives may embed project metadata or proof data.
            if Path(directory) == project / ".lake/build" and "bin" in children:
                directories.append(str((Path(directory) / "bin").resolve()))
                children.remove("bin")
        key = arena.environment_fingerprint_registry_key(row, project)
        # The legal elaboration prefix and Lean installation are unchanged.
        # Retain their canonical fingerprint/helper cache, with an explicit
        # view-specific guard. These agent verdicts never bless host finalists.
        registry["entries"][key]["guard_sha256"] = arena.sha256_bytes(
            json.dumps(guard, sort_keys=True, separators=(",", ":")).encode("utf-8"))
    task = {"schema_version": 1, "statement_first": True,
            "original_metrics": {"tokens": config["original_tokens"], "heartbeats": config["original_heartbeats"]},
            "reference": {"heartbeat": config["original_heartbeats"]}, "row": row,
            "local_baselines": [{"environment_fingerprint": config["initial_best"]["evaluation"]["heartbeat"]["environment_fingerprint"],
                                 "heartbeat": config.get("observed_original_baseline", {}).get("heartbeats",
                                      config.get("original_measurement_heartbeats", config["original_heartbeats"]))}]}
    if config.get("scoring_policy") == "arena-v1":
        task["scoring_policy"] = "arena-v1"
    arena.write_json_atomic(root / "Task.json", task)
    arena.write_json_atomic(root / "environment-fingerprints.json", registry)
    view = {"schema_version": 1, "task": str(root / "Task.json"),
            "registry": str(root / "environment-fingerprints.json"), "empty": str(empty),
            "overlays": overlays, "git_overlays": git_overlays, "hidden_directories": sorted(set(directories)),
            "hidden_files": sorted(set(hidden_files)),
            "task_sha256": arena.sha256_file(root / "Task.json"),
            "registry_sha256": arena.sha256_file(root / "environment-fingerprints.json")}
    arena.write_json_atomic(manifest, view)
    return view


def load_view(config: dict) -> dict:
    root = Path(config["root"]) / "preparation/statement-first"
    view = json.loads((root / "view.json").read_text(encoding="utf-8"))
    for key in ("task", "registry"):
        if Path(view[key]) != root / ("Task.json" if key == "task" else "environment-fingerprints.json"):
            raise ValueError("Statement-first view escaped its preparation root")
        if arena.sha256_file(Path(view[key])) != view[key + "_sha256"]:
            raise ValueError("Statement-first view changed before agent launch")
    if Path(view["empty"]) != root / "empty" or Path(view["empty"]).read_bytes() != b"":
        raise ValueError("Statement-first empty mask changed")
    projects = [Path(value).resolve() for value in [config["primary"], *config["compatibility"]]]
    for overlay in view["overlays"]:
        if (not Path(overlay["source"]).is_relative_to(root)
                or arena.sha256_file(Path(overlay["source"])) != overlay["sha256"]):
            raise ValueError("Statement-first source overlay changed")
    for overlay in view["git_overlays"]:
        source, target = Path(overlay["source"]), Path(overlay["target"])
        if (not source.is_relative_to(root) or (source / "HEAD").read_text(encoding="utf-8") != overlay["head"]
                or set(path.name for path in source.iterdir()) != {"HEAD", "objects", "refs"}
                or any((source / "objects").iterdir()) or any((source / "refs").iterdir())
                or not (target == source or any(target.is_relative_to(project) for project in projects))):
            raise ValueError("Statement-first Git metadata changed or escaped its view")
    for target in [*(item["target"] for item in view["overlays"]),
                   *view["hidden_files"], *view["hidden_directories"]]:
        if not any(Path(target).is_relative_to(project) for project in projects):
            raise ValueError("Statement-first mask escaped the supplied projects")
    return view
