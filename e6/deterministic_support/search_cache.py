"""Small, optional host caches; cache data never supplies validation evidence.

Negative entries require an explicit normal Lean compiler rejection. Search
snapshots only remember traversal; the engine separately verifies their immutable
checkpoint before it can reuse a winner.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re

SCHEMA_VERSION = 1
MAX_NEGATIVES = 4096
MAX_SNAPSHOT_BYTES = 16 * 1024 * 1024
COMPILE_STAGES = {"candidate compile", "measured project compile", "measured compile and axiom audit"}


def digest(value) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
        allow_nan=False, separators=(",", ":")).encode("utf-8")).hexdigest()


def tool_identity(root: Path) -> str:
    """Bind both generators and the complete evaluator/scorer implementation."""
    material = {}
    for package in ("e6", "lean_tools"):
        for path in sorted((root / package).rglob("*")):
            if path.is_file() and (path.suffix in {".py", ".lean"} or path.name.endswith(".lean.inc")):
                material[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return digest(material)


def compile_rejection(error: BaseException, lean_compile_error: type) -> dict | None:
    # Other exceptions, including audit and intake failures, are not evidence
    # that Lean deterministically rejected the admitted source.
    if not isinstance(error, lean_compile_error):
        return None
    label = re.search(r": ([^:\n]+) failed with exit 1$", str(error).partition("\n")[0])
    if label is None or label[1] not in COMPILE_STAGES:
        # Measurement helpers and separate axiom-audit programs are tooling,
        # even when Lean itself exits normally with a syntax/type error.
        return None
    result = getattr(error, "result", None)
    if (result is None or getattr(result, "timed_out", None) is not False
            or type(getattr(result, "returncode", None)) is not int
            or result.returncode != 1):
        return None
    output = str(getattr(result, "output", ""))
    # Lean reports a heartbeat/depth/resource exhaustion with ordinary exit 1;
    # it is not reusable proof invalidity under a different admission budget.
    if any(marker in output.lower() for marker in (
            "maximum number of heartbeats", "maxheartbeats", "maxrecdepth", "deeprecursion", "timeout",
            "maximum recursion depth", "out of memory", "interrupted", "cancelled",
            "canceled", "resource exhausted", "stack overflow", "(deterministic) timeout",
            "unknown module prefix", "no such file", "permission denied", "failed to open file",
            "failed to load dynamic library", "object file", "lean.unknownmodule", "lean.unknownpackage")):
        return None
    # Lean 4.31+ may attach a diagnostic code, e.g.
    # `Candidate.lean:1:0: error(lean.unknownIdentifier): ...`. Require an actual
    # source-positioned compiler diagnostic rather than an `error:` substring
    # in a wrapper message, warning, or quoted source. When the launch command
    # is available, every error must belong to its supplied Lean input; errors
    # in imported/tooling sources are not reusable candidate invalidity.
    diagnostics = list(re.finditer(
        r"(?m)^(?P<source>[^\r\n]+\.lean):\d+:\d+:\s*"
        r"error(?:\((?P<code>[A-Za-z0-9_.-]+)\))?:", output))
    if not diagnostics:
        return None
    command = getattr(result, "command", None)
    if command is not None and not isinstance(command, (list, tuple)):
        return None
    if isinstance(command, (list, tuple)):
        def normalized(path):
            return os.path.normcase(os.path.normpath(str(path))).replace("\\", "/")
        inputs = {normalized(arg) for arg in command if str(arg).endswith(".lean")}
        if not inputs or any(normalized(item["source"]) not in inputs for item in diagnostics):
            return None
    return {"kind": "lean_compile_invalid", "stage": label[1], "returncode": 1, "timed_out": False,
            "message": str(error)[:256], "output_tail": output[-512:],
            "diagnostic_codes": sorted({item["code"] for item in diagnostics if item["code"]}),
            "diagnostic_sources": sorted({item["source"] for item in diagnostics})}


class SearchCache:
    """One bounded negative table and one bounded snapshot per seed/policy."""

    def __init__(self, directory: Path, binding: dict, search_binding: dict):
        self.binding = digest(binding)
        self.search_binding = digest({"validation": self.binding, **search_binding})
        self.directory = Path(directory) / self.binding
        self.negatives = self._load("negative.json", self.binding).get("entries", {})
        if not isinstance(self.negatives, dict):
            self.negatives = {}
        self.negatives = dict(list(self.negatives.items())[-MAX_NEGATIVES:])

    def _load(self, name: str, binding: str) -> dict:
        path = self.directory / name
        try:
            if path.stat().st_size > MAX_SNAPSHOT_BYTES:
                return {}
            value = json.loads(path.read_text(encoding="utf-8"))
            return value if (isinstance(value, dict) and value.get("schema_version") == SCHEMA_VERSION
                and value.get("binding_sha256") == binding) else {}
        except (OSError, ValueError, TypeError):
            return {}

    def _save(self, name: str, binding: str, value: dict) -> bool:
        payload = {"schema_version": SCHEMA_VERSION, "binding_sha256": binding, **value}
        encoded = json.dumps(payload, ensure_ascii=False, allow_nan=False, separators=(",", ":"))
        if len(encoded.encode("utf-8")) > MAX_SNAPSHOT_BYTES:
            return False
        self.directory.mkdir(parents=True, exist_ok=True)
        path = self.directory / name
        temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
        try:
            temporary.write_text(encoded, encoding="utf-8")
            temporary.replace(path)
        finally:
            temporary.unlink(missing_ok=True)
        return True

    def negative(self, source_sha256: str) -> dict | None:
        value = self.negatives.get(source_sha256)
        if (isinstance(value, dict) and value.get("kind") == "lean_compile_invalid"
                and value.get("stage") in COMPILE_STAGES
                and value.get("returncode") == 1 and value.get("timed_out") is False):
            return dict(value)
        return None

    def remember_invalid(self, source_sha256: str, receipt: dict) -> None:
        if (receipt.get("kind") != "lean_compile_invalid" or receipt.get("returncode") != 1
                or receipt.get("stage") not in COMPILE_STAGES
                or receipt.get("timed_out") is not False):
            raise ValueError("Negative cache requires deterministic compiler invalidity")
        self.negatives.pop(source_sha256, None)
        self.negatives[source_sha256] = dict(receipt)
        while len(self.negatives) > MAX_NEGATIVES:
            self.negatives.pop(next(iter(self.negatives)))
        self._save("negative.json", self.binding, {"entries": self.negatives})

    def load_search(self) -> dict:
        return self._load(f"search-{self.search_binding}.json", self.search_binding).get("state", {})

    def save_search(self, state: dict) -> bool:
        return self._save(f"search-{self.search_binding}.json", self.search_binding, {"state": state})
