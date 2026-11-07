"""Strict ingestion of the contest's original Arena and heartbeat JSONL."""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
from typing import Any

from lean_tools.task import normalize_arena_row


def digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
        separators=(",", ":")).encode("utf-8")).hexdigest()


def file_hash(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _jsonl(path: Path, *, allow_empty: bool = False) -> list[dict]:
    rows = []
    for number, line in enumerate(path.read_text(encoding="utf-8-sig").splitlines(), 1):
        if not line.strip():
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            raise ValueError(f"{path}:{number}: invalid JSON: {error.msg}") from error
        if not isinstance(value, dict):
            raise ValueError(f"{path}:{number}: expected a JSON object")
        rows.append(value)
    if not rows and not allow_empty:
        raise ValueError(f"{path}: no benchmark rows")
    return rows


@dataclass(frozen=True)
class Benchmark:
    input_path: Path
    heartbeat_path: Path | None
    rows: tuple[dict, ...]
    heartbeats: dict[str, int]
    input_sha256: str
    heartbeat_sha256: str | None

    @property
    def identity(self) -> str:
        return digest({"input_sha256": self.input_sha256,
            "heartbeat_sha256": self.heartbeat_sha256,
            "rows": [{"name": row["name"], "sha256": digest(row),
                "heartbeat": self.heartbeats.get(row["name"])} for row in self.rows]})

    def to_dict(self) -> dict:
        return {"input_path": str(self.input_path), "heartbeat_path": str(self.heartbeat_path) if self.heartbeat_path is not None else None,
            "input_sha256": self.input_sha256, "heartbeat_sha256": self.heartbeat_sha256,
            "identity": self.identity, "row_count": len(self.rows)}


def load_benchmark_rows(input_path: str | Path) -> tuple[dict, ...]:
    """Read strict original rows for environment preparation without score references."""
    raw = _jsonl(Path(input_path).resolve())
    rows, names = [], set()
    for original in raw:
        row = normalize_arena_row(original)
        name = row["name"]
        if name in names:
            raise ValueError(f"Duplicate benchmark name: {name}")
        names.add(name)
        if "proof_length" in row and (type(row["proof_length"]) is not int or row["proof_length"] <= 0):
            raise ValueError(f"{name}: original proof_length must be a positive integer")
        if not isinstance(row.get("source"), str) or not row["source"]:
            raise ValueError(f"{name}: original source is required")
        if not isinstance(row.get("contexts"), list) or any(not isinstance(c, str) for c in row["contexts"]):
            raise ValueError(f"{name}: contexts must be an ordered list of strings")
        if not isinstance(row.get("header", ""), str):
            raise ValueError(f"{name}: header must be a string")
        source_file = row.get("file_path", "")
        if not isinstance(source_file, str) or (source_file and (
                PurePosixPath(source_file).is_absolute() or ".." in PurePosixPath(source_file).parts
                or "\\" in source_file)):
            raise ValueError(f"{name}: file_path must stay within the snapshot")
        if row["source"].lower().replace("-", "") == "leanpool" and (
                not isinstance(row.get("url"), str) or not row["url"] or not source_file):
            raise ValueError(f"{name}: LeanPool requires an explicit repository url and project file_path")
        versions = row.get("version_info")
        if not isinstance(versions, list) or not versions:
            raise ValueError(f"{name}: explicit version_info snapshot pins are required")
        seen = set()
        for version in versions:
            if not isinstance(version, dict) or len(version) != 1:
                raise ValueError(f"{name}: version_info entries must each contain one version/revision")
            release, revision = next(iter(version.items()))
            if not isinstance(release, str) or not re.fullmatch(r"v4\.\d+\.\d+(?:-rc\d+)?", release) or not isinstance(revision, str) or not re.fullmatch(r"[0-9a-f]{40}", revision):
                raise ValueError(f"{name}: version_info requires pinned Lean releases and full revisions")
            if release in seen:
                raise ValueError(f"{name}: duplicate Lean version {release}")
            seen.add(release)
        rows.append(row)
    return tuple(rows)


def load_benchmark(input_path: str | Path, heartbeat_path: str | Path | None = None) -> Benchmark:
    """Read original contest rows and any supplied, possibly partial references."""
    input_path = Path(input_path).resolve()
    heartbeat_path = Path(heartbeat_path).resolve() if heartbeat_path is not None else None
    rows = load_benchmark_rows(input_path)
    references = {}
    for value in _jsonl(heartbeat_path, allow_empty=True) if heartbeat_path is not None else ():
        name, heartbeat = value.get("name"), value.get("heartbeat")
        if not isinstance(name, str) or not name or type(heartbeat) is not int or heartbeat <= 0:
            raise ValueError("Heartbeat rows require name and positive integer heartbeat")
        if name in references:
            raise ValueError(f"Duplicate heartbeat reference: {name}")
        references[name] = heartbeat
    return Benchmark(input_path, heartbeat_path, rows, references,
        file_hash(input_path), file_hash(heartbeat_path) if heartbeat_path is not None else None)
