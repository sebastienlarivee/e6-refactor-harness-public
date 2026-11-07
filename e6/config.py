"""Portable paths and frozen E6 experiment settings."""
from __future__ import annotations

import os
import json
from pathlib import Path
import re

from .experiment import DEFAULT_SPEC

REPO_ROOT = Path(__file__).resolve().parents[1]
DATA_ROOT = REPO_ROOT / "data"
TOOLS_ROOT = REPO_ROOT / "lean_tools"
PROOFS = DATA_ROOT / "proofs.json"
ARENA_PROOFS = DATA_ROOT / "proofs-arena-v1.json"
MODEL_CATALOG = DATA_ROOT / "model-catalog.json"
MODEL = DEFAULT_SPEC.model
REASONING_EFFORT = DEFAULT_SPEC.reasoning_effort
AGENT_BACKENDS = ("codex", "pi")
STOPPING_POLICIES = ("screening", "convergence", "cost")


def _saved_configs(root: Path):
    for filename in ("panel-config.json", "config.json"):
        path = root / filename
        if path.exists():
            value = json.loads(path.read_text(encoding="utf-8-sig"))
            if not isinstance(value, dict):
                raise ValueError(f"Invalid frozen E6 configuration: {path}")
            yield value


def resolve_backend(root: Path, requested: str | None = None) -> str:
    """Use Codex for new roots; honor explicitly selected frozen backends."""
    if requested is not None and requested not in AGENT_BACKENDS:
        raise ValueError(f"Unsupported E6 agent backend: {requested}")
    values = [value.get("agent_backend", "codex") for value in _saved_configs(root)]
    if any(not isinstance(value, str) or value not in AGENT_BACKENDS for value in values):
        raise ValueError("Frozen E6 configurations have invalid or conflicting backends")
    saved = set(values)
    if len(saved) > 1:
        raise ValueError("Frozen E6 configurations have invalid or conflicting backends")
    frozen = next(iter(saved), None)
    if frozen is not None and requested is not None and requested != frozen:
        raise ValueError("Requested backend differs from the frozen E6 configuration")
    return frozen or requested or "codex"


def resolve_stopping_policy(root: Path, requested: str | None = None) -> str:
    """Freeze stopping semantics; historical configurations retain cost gating."""
    if requested is not None and requested not in STOPPING_POLICIES:
        raise ValueError(f"Unsupported E6 stopping policy: {requested}")
    values = []
    for value in _saved_configs(root):
        snapshot = value.get("experiment_spec", {})
        if not isinstance(snapshot, dict):
            raise ValueError("Frozen E6 configurations have invalid experiment specs")
        values.append(value.get("stopping_policy", snapshot.get("stopping_policy", "cost")))
    if any(not isinstance(value, str) or value not in STOPPING_POLICIES for value in values):
        raise ValueError("Frozen E6 configurations have invalid or conflicting stopping policies")
    saved = set(values)
    if len(saved) > 1:
        raise ValueError("Frozen E6 configurations have invalid or conflicting stopping policies")
    frozen = next(iter(saved), None)
    from .experiment import experiment_spec
    for value in _saved_configs(root):
        if "experiment_spec" in value:
            experiment_spec(value)
    if frozen is not None and requested is not None and requested != frozen:
        raise ValueError("Requested stopping policy differs from the frozen E6 configuration")
    return frozen or requested or "convergence"


def resolve_auth_path(root: Path, backend: str, requested: Path | None = None) -> Path:
    """Select host-only credentials without opening an authentication file."""
    backend = resolve_backend(root, backend)
    saved = {str(Path(value["auth_path"]).expanduser().resolve())
             for value in _saved_configs(root) if value.get("auth_path")}
    if len(saved) > 1:
        raise ValueError("Frozen E6 configurations have conflicting authentication paths")
    frozen = next(iter(saved), None)
    explicit = str(requested.expanduser().resolve()) if requested is not None else None
    if frozen is not None and explicit is not None and explicit != frozen:
        raise ValueError("Requested auth path differs from the frozen E6 configuration")
    default = Path.home() / (".pi/agent/auth.json" if backend == "pi" else ".codex/auth.json")
    return Path(frozen or explicit or default).expanduser().resolve()


def _root(name: str, default: Path) -> Path:
    return Path(os.environ.get(name, str(default))).expanduser().resolve()


def runtime_root() -> Path:
    return _root("E6_RUNTIME_ROOT", Path.home() / ".local/share/lean-e6")


def environments_root() -> Path:
    return _root("E6_ENVIRONMENTS_ROOT", Path.home() / "lean-e6-env")


def runs_root() -> Path:
    return _root("E6_RUNS_ROOT", Path.home() / "lean-e6-runs")


def codex_home() -> Path:
    return _root("E6_CODEX_HOME", runtime_root() / "codex-home")


def _native_path(value: str) -> bool:
    """Accept absolute Linux paths and exclude inherited Windows mount entries."""
    return (bool(value) and "\\" not in value and ";" not in value
            and Path(value).expanduser().is_absolute()
            and re.match(r"^/mnt/[A-Za-z](?:/|$)", value) is None)


def configure_native_environment(*, elan_home: str | None = None) -> dict[str, str]:
    """Set native launcher discovery without creating directories or reading auth."""
    default = environments_root() / "elan"
    configured = elan_home if elan_home is not None else os.environ.get("ELAN_HOME", "")
    elan = default
    if _native_path(configured):
        override = Path(configured).expanduser().resolve()
        if _native_path(str(override)) and all(
                (override / "bin" / name).is_file() and os.access(override / "bin" / name, os.X_OK)
                for name in ("elan", "lean", "lake")):
            elan = override
    if elan_home is not None and elan != Path(elan_home).expanduser().resolve():
        raise ValueError("Prepared native ELAN_HOME no longer has executable elan, lean and lake launchers")
    roots = [str(elan / "bin"), str(runtime_root() / "bin")]
    inherited = [value for value in os.environ.get("PATH", os.defpath).split(os.pathsep)
                 if _native_path(value)]
    values = {"ELAN_HOME": str(elan), "PATH": os.pathsep.join(dict.fromkeys([*roots, *inherited]))}
    os.environ.update(values)
    return values


def find_codex() -> Path:
    configured = os.environ.get("E6_CODEX_EXECUTABLE")
    value = configured or str(runtime_root() / "bin/codex")
    if _native_path(value):
        path = Path(value).expanduser().resolve()
        if (_native_path(str(path)) and path.is_file() and os.access(path, os.X_OK)
                and path.suffix != ".exe"):
            return path
    raise FileNotFoundError("Native Linux Codex CLI is absent; install the pinned CLI under E6_RUNTIME_ROOT/bin or set E6_CODEX_EXECUTABLE to a native executable")


def resolve_metadata(metadata: dict) -> dict:
    """Resolve catalog locations without reading any prior proof or run source."""
    result = dict(metadata)
    task = Path(metadata["task"])
    base = DATA_ROOT if task.parts and task.parts[0] == "tasks" else REPO_ROOT
    result["task"] = str((base / task).resolve())
    result["primary"] = str((environments_root() / metadata["primary"]).resolve())
    result["compatibility"] = [str((environments_root() / value).resolve()) for value in metadata["compatibility"]]
    registry = Path(metadata["registry_source"])
    base = REPO_ROOT if registry.parts and registry.parts[0] in {"data", "research"} else environments_root()
    result["registry_source"] = str((base / registry).resolve())
    if isinstance(result.get("original_measurement_evidence"), dict):
        evidence = dict(result["original_measurement_evidence"])
        path = Path(evidence["path"])
        base = environments_root() if path.parts and path.parts[0] == "original-controls" else REPO_ROOT
        evidence["path"] = str((base / path).resolve())
        result["original_measurement_evidence"] = evidence
    return result


def source_paths(prompt_variant: str = "control-efficient-v1") -> list[Path]:
    paths = [*(REPO_ROOT / "e6").glob("*.py"), *(REPO_ROOT / "e6").glob("*.mjs"),
             *(REPO_ROOT / "e6").glob("*.ts"), *TOOLS_ROOT.glob("*.py"),
             *(REPO_ROOT / "transport").glob("*.py"),
             *(REPO_ROOT / "harness").rglob("*.py"), *DATA_ROOT.rglob("*.json"),
             REPO_ROOT / "pyproject.toml"]
    # Native optimizer helpers are runtime code and must share the frozen
    # source guard. Compiled caches live outside the checkout.
    for directory in ("deterministic_support", "deterministic_native_support"):
        paths.extend(path for path in (REPO_ROOT / "e6" / directory).rglob("*")
                     if path.suffix in {".py", ".lean", ".inc"})
    from .prompt_bundle import source_paths as prompt_source_paths
    paths.extend(prompt_source_paths(prompt_variant))
    return sorted(set(path.resolve() for path in paths if path.is_file()))
