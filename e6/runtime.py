"""Resolved per-proof paths and small environment adapters for E6."""
from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
import os
from pathlib import Path
from typing import Mapping

from .experiment import DEFAULT_SPEC, ExperimentSpec, experiment_spec


@contextmanager
def scoped_environment(values: Mapping[str, str], *, remove=()):
    """Restore only the environment entries this scope owns, including on error."""
    names = set(values) | set(remove)
    previous = {name: os.environ.get(name) for name in names}
    for name in remove:
        os.environ.pop(name, None)
    os.environ.update(values)
    try:
        yield
    finally:
        for name, value in previous.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value


def queue_environment_names(environment: Mapping[str, str]) -> tuple[str, ...]:
    """Admission delays consume neither proof time nor model budget."""
    return tuple(name for name in environment if
        (name.startswith("LEAN_REFACTOR_") and name.endswith("_QUEUE_TIMEOUT")) or name in {
            "LEAN_REFACTOR_COLD_LEAN_GATE", "LEAN_REFACTOR_COLD_LEAN_CAPACITY",
            "LEAN_REFACTOR_MODEL_GATE", "LEAN_REFACTOR_MODEL_CAPACITY"})


def create_environment_directories(values: Mapping[str, str], *, checkpoint=False) -> None:
    endings = ("ROOT", "SPOOL", "CACHE", "GATE", "DIR") if checkpoint else ("ROOT", "SPOOL", "CACHE", "GATE")
    for name, value in values.items():
        if name.startswith("LEAN_REFACTOR_") and name.endswith(endings):
            Path(value).mkdir(parents=True, exist_ok=True)


@dataclass(frozen=True)
class RuntimeContext:
    root: Path
    spec: ExperimentSpec = DEFAULT_SPEC

    def __post_init__(self):
        object.__setattr__(self, "root", Path(self.root).resolve())

    @classmethod
    def resolve(cls, root: Path, config: Mapping | None = None) -> RuntimeContext:
        return cls(root, experiment_spec(config))

    @property
    def preparation_cache(self) -> Path:
        return self.root / "preparation/evaluation-cache"

    @property
    def validation_cache(self) -> Path:
        return self.root / "preparation/host-final-validation-cache"

    def environment(self, capsule: Path | None = None, *, broker=False, registry: Path | None = None) -> dict[str, str]:
        work = self.root / "warm-broker" if broker else capsule or self.root / "preparation"
        values = {
            "LEAN_NUM_THREADS": str(self.spec.lean_threads), "OMP_NUM_THREADS": str(self.spec.omp_threads),
            "LEAN_REFACTOR_SCORING_POLICY": self.spec.scoring_policy,
            "LEAN_REFACTOR_LEAN_GATE": str(self.root.parent / "lean-gate"),
            "LEAN_REFACTOR_LEAN_CAPACITY": str(self.spec.lean_capacity),
            "LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE": self.spec.lean_timeout_scope,
            "LEAN_REFACTOR_LEAN_PRIORITY": str(self.spec.lean_priority),
            "LEAN_REFACTOR_SCRATCH_ROOT": str(work / "scratch"),
            "LEAN_REFACTOR_ARTIFACT_ROOT": str(work),
            "LEAN_REFACTOR_EVENT_SPOOL": str(work / "event-spool"),
            "LEAN_REFACTOR_EVALUATION_CACHE": str(work / ("private-evaluation-cache" if broker else "evaluation-cache")),
            "LEAN_REFACTOR_FINGERPRINT_REGISTRY": str(registry or (capsule or self.root) / "environment-fingerprints.json"),
            "LEAN_REFACTOR_CHECKPOINT_DIR": str(work / "valid-candidates"),
        }
        if not broker:
            values.update(LEAN_REFACTOR_BROKER_STARTUP_GATE=str(self.root.parent / "broker-startup-gate"),
                          LEAN_REFACTOR_BROKER_STARTUP_CAPACITY=str(self.spec.broker_startup_capacity))
        if capsule is not None:
            values["LEAN_REFACTOR_LAUNCH_CACHE"] = str(capsule / "launch-cache")
        return values

    def shared_gates(self) -> dict:
        return {name: {"root": str(self.root.parent / directory), "capacity": capacity}
                for name, directory, capacity in (
                    ("lean", "lean-gate", self.spec.lean_capacity),
                    ("broker_startup", "broker-startup-gate", self.spec.broker_startup_capacity))}
