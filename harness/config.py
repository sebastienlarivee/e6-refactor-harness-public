"""Validated public configuration and content identities; credentials stay host-only."""
from __future__ import annotations

from dataclasses import dataclass, replace
from decimal import Decimal, InvalidOperation
import hashlib
import json
from pathlib import Path
import tomllib
from typing import Mapping

SCHEMA_VERSION = 1
CLI_VERSION = "0.164.0"
EFFICIENT_WORKFLOW = "efficient-v1"


def digest(value) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
        separators=(",", ":")).encode("utf-8")).hexdigest()


def file_hash(path: Path) -> str:
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _path(value, base: Path, label: str) -> Path:
    if not isinstance(value, (str, Path)) or not str(value):
        raise ValueError(f"{label} requires an explicit path")
    path = Path(value).expanduser()
    return (base / path).resolve() if not path.is_absolute() else path.resolve()


def _no_secrets(value, parent="configuration"):
    if isinstance(value, Mapping):
        for key, item in value.items():
            if any(word in str(key).lower() for word in ("api_key", "credential", "authorization", "management_key", "inference_key", "secret", "access_token")):
                raise ValueError(f"{parent}.{key}: credentials belong in an explicit host-only key file")
            _no_secrets(item, f"{parent}.{key}")
    elif isinstance(value, list):
        for item in value:
            _no_secrets(item, parent)


@dataclass(frozen=True)
class RunConfig:
    input_path: Path
    heartbeat_path: Path | None
    env_map: Path
    openrouter: dict
    concurrency: int = 2
    optimizer: str = "compact"
    budget_usd: Decimal = Decimal("3")
    selected_proofs: tuple[str, ...] = ()
    diagnostic_max_passes: int | None = None
    codex: Path = Path.home() / ".local/share/lean-refactor-harness/bin/codex"
    elan_home: Path = Path.home() / ".elan"
    model_profile_source: dict | None = None
    workflow_policy: str = EFFICIENT_WORKFLOW
    budget_policy: str = "local-actual-cost-v1"
    recovery_policy: str = "generation-v1"

    def __post_init__(self):
        if not isinstance(self.budget_policy, str) or self.budget_policy not in ("local-actual-cost-v1", "provider-key-v1"):
            raise ValueError("budget_policy must be local-actual-cost-v1 or provider-key-v1")
        if not isinstance(self.recovery_policy, str) or self.recovery_policy not in ("none", "generation-v1", "exclusive-key-v1"):
            raise ValueError("recovery_policy must be none, generation-v1 or exclusive-key-v1")
        if self.recovery_policy == "exclusive-key-v1" and self.budget_policy != "local-actual-cost-v1":
            raise ValueError("exclusive-key-v1 recovery requires budget_policy=local-actual-cost-v1")
        if self.workflow_policy != EFFICIENT_WORKFLOW:
            raise ValueError("workflow_policy must be efficient-v1; historical workflows must use their original frozen release")
        if type(self.concurrency) is not int or self.concurrency not in (1, 2):
            raise ValueError("concurrency must be exactly 1 or 2")
        if self.optimizer not in ("compact", "off"):
            raise ValueError("optimizer must be compact or off")
        try:
            budget = Decimal(str(self.budget_usd))
        except InvalidOperation as error:
            raise ValueError("budget_usd must be a positive finite decimal") from error
        if not budget.is_finite() or budget <= 0 or budget > 3:
            raise ValueError("budget_usd must be a positive finite decimal no greater than 3")
        object.__setattr__(self, "budget_usd", budget)
        if self.diagnostic_max_passes is not None and (type(self.diagnostic_max_passes) is not int or self.diagnostic_max_passes <= 0):
            raise ValueError("diagnostic_max_passes must be a positive integer")
        if len(set(self.selected_proofs)) != len(self.selected_proofs):
            raise ValueError("proof selection contains duplicates")
        for name in ("input_path", "heartbeat_path", "env_map", "codex", "elan_home"):
            value = getattr(self, name)
            if name != "heartbeat_path" or value is not None:
                object.__setattr__(self, name, Path(value).expanduser().resolve())
        _no_secrets(self.openrouter)
        profile = dict(self.openrouter)
        if "budget_usd" in profile and Decimal(str(profile["budget_usd"])) != budget:
            raise ValueError("OpenRouter profile budget differs from run budget")
        profile["budget_usd"] = str(budget)
        if not profile.get("model_id") or not profile.get("provider"):
            raise ValueError("[openrouter] requires explicit model_id and provider")
        object.__setattr__(self, "openrouter", profile)

    @classmethod
    def load(cls, path: Path, **overrides):
        path = Path(path).expanduser().resolve()
        with path.open("rb") as stream:
            return cls.from_dict(tomllib.load(stream), base=path.parent, **overrides)

    @classmethod
    def from_dict(cls, document: Mapping, *, base: Path | None = None, **overrides):
        base = Path(base or Path.cwd())
        _no_secrets(document)
        allowed = {"schema_version", "run", "benchmark", "runtime", "openrouter", "input", "input_path", "heartbeats", "heartbeat_path", "env_map", "concurrency", "optimizer", "budget_usd", "profile", "proofs", "selected_proofs", "diagnostic_max_passes", "codex", "elan_home", "model_profile_source", "workflow_policy", "budget_policy", "recovery_policy"}
        unknown = set(document) - allowed
        if unknown:
            raise ValueError(f"Unknown configuration fields: {sorted(unknown)}")
        if document.get("schema_version", 1) != SCHEMA_VERSION:
            raise ValueError("Unsupported configuration schema_version")
        sections = {
            "run": {"input", "input_path", "heartbeats", "heartbeat_path", "env_map", "concurrency", "optimizer", "budget_usd", "profile", "proofs", "selected_proofs", "diagnostic_max_passes", "codex", "elan_home", "workflow_policy", "budget_policy", "recovery_policy"},
            "benchmark": {"input", "input_path", "heartbeats", "heartbeat_path", "env_map"},
            "runtime": {"codex", "elan_home"},
        }
        for section, names in sections.items():
            if not isinstance(document.get(section, {}), Mapping):
                raise ValueError(f"[{section}] must be a table")
            unknown = set(document.get(section, {})) - names
            if unknown:
                raise ValueError(f"Unknown [{section}] fields: {sorted(unknown)}")
        run = {**document.get("run", {}), **{k: v for k, v in document.items() if k not in {"run", "benchmark", "runtime", "schema_version", "openrouter"}}}
        if run.get("profile", "final") not in {"development", "final"}:
            raise ValueError("run.profile must be development or final")
        selected = run.get("selected_proofs", run.get("proofs", ()))
        if isinstance(selected, str) or not isinstance(selected, (list, tuple)) or any(not isinstance(item, str) or not item for item in selected):
            raise ValueError("proofs must be a list of proof labels or names")
        benchmark = document.get("benchmark", {})
        runtime = document.get("runtime", {})
        openrouter = dict(document.get("openrouter", {}))
        profile_source = document.get("model_profile_source")
        if "profile" in openrouter:
            profile_path = _path(openrouter.pop("profile"), base, "openrouter.profile")
            loaded_profile = json.loads(profile_path.read_text(encoding="utf-8-sig"))
            if not isinstance(loaded_profile, dict):
                raise ValueError("OpenRouter profile must be a JSON object")
            _no_secrets(loaded_profile)
            # A prepared profile describes model capabilities; the run owns its cap.
            loaded_profile.pop("budget_usd", None)
            openrouter = {**loaded_profile, **openrouter}
            profile_source = {"path": str(profile_path), "sha256": file_hash(profile_path)}
        values = {
            "input_path": run.get("input_path", run.get("input", benchmark.get("input_path", benchmark.get("input")))),
            "heartbeat_path": run.get("heartbeat_path", run.get("heartbeats", benchmark.get("heartbeat_path", benchmark.get("heartbeats")))),
            "env_map": run.get("env_map", benchmark.get("env_map")),
            "openrouter": openrouter, "model_profile_source": profile_source,
            "concurrency": run.get("concurrency", 2), "optimizer": run.get("optimizer", "compact"),
            "budget_usd": run.get("budget_usd", "1.5" if run.get("profile") == "development" else "3"),
            "selected_proofs": tuple(run.get("selected_proofs", run.get("proofs", ()))),
            "diagnostic_max_passes": run.get("diagnostic_max_passes"),
            "workflow_policy": run.get("workflow_policy", EFFICIENT_WORKFLOW),
            "budget_policy": run.get("budget_policy", "local-actual-cost-v1"),
            "recovery_policy": run.get("recovery_policy", "generation-v1"),
            "codex": runtime.get("codex", run.get("codex", cls.__dataclass_fields__["codex"].default)),
            "elan_home": runtime.get("elan_home", run.get("elan_home", cls.__dataclass_fields__["elan_home"].default)),
        }
        values.update({key: value for key, value in overrides.items() if value is not None})
        for name in ("input_path", "heartbeat_path", "env_map", "codex", "elan_home"):
            if name != "heartbeat_path" or values[name] is not None:
                values[name] = _path(values[name], base, name)
        if isinstance(values["selected_proofs"], str):
            raise ValueError("selected_proofs must be a list")
        values["selected_proofs"] = tuple(values["selected_proofs"])
        return cls(**values)

    @classmethod
    def from_frozen_dict(cls, document: Mapping):
        """Resume the production workflow; historical workflows need their release."""
        if "workflow_policy" not in document:
            raise ValueError("Frozen configuration lacks workflow_policy; must use its original frozen release")
        return cls.from_dict({**document,
            "budget_policy": document.get("budget_policy", "provider-key-v1"),
            "recovery_policy": document.get("recovery_policy", "none")})

    def to_dict(self) -> dict:
        return {"schema_version": SCHEMA_VERSION,
            "input_path": str(self.input_path), "heartbeat_path": str(self.heartbeat_path) if self.heartbeat_path is not None else None,
            "env_map": str(self.env_map), "openrouter": dict(self.openrouter),
            "concurrency": self.concurrency, "optimizer": self.optimizer,
            "budget_usd": str(self.budget_usd), "selected_proofs": list(self.selected_proofs),
            "diagnostic_max_passes": self.diagnostic_max_passes,
            "codex": str(self.codex), "elan_home": str(self.elan_home),
            "model_profile_source": self.model_profile_source,
            "workflow_policy": self.workflow_policy,
            **({"budget_policy": self.budget_policy} if self.budget_policy != "provider-key-v1" else {}),
            **({"recovery_policy": self.recovery_policy} if self.recovery_policy != "none" else {})}

    resolved = to_dict

    def experiment_spec(self):
        from e6.experiment import DEFAULT_RUN_SPEC
        enabled = self.optimizer == "compact"
        return replace(DEFAULT_RUN_SPEC, model=self.openrouter["model_id"],
            model_display_name=self.openrouter.get("model_display_name", self.openrouter["model_id"]),
            reasoning_effort=self.openrouter.get("default_reasoning_effort", "high"),
            cumulative_budget_usd=self.budget_usd, stopping_policy="cost",
            proof_cell_capacity=self.concurrency, max_passes=self.diagnostic_max_passes,
            deterministic_refactoring=enabled,
            **({"deterministic_policy": "compact", "deterministic_budget_seconds": 1200,
                "deterministic_late_budget_seconds": 300, "deterministic_cache": True,
                "deterministic_regenerate": True} if enabled else {}))


def runtime_source_hashes() -> dict[str, str]:
    from e6.config import REPO_ROOT, source_paths
    paths = source_paths("control-efficient-v1")
    return {str(path.relative_to(REPO_ROOT)): file_hash(path) for path in sorted(paths)}


def verify_source_hashes(expected: Mapping[str, str]):
    actual = runtime_source_hashes()
    if dict(expected) != actual:
        changed = sorted(set(expected) ^ set(actual) | {key for key in set(expected) & set(actual) if expected[key] != actual[key]})
        raise RuntimeError(f"Frozen harness source changed: {', '.join(changed[:8])}")
