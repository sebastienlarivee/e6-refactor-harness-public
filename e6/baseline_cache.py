"""Host-only reuse of canonical original evaluations, never candidate archives.

Only the exact content-addressed entry needed for a guarded original request is
read. Preparation copies that entry to its private evaluator cache and continues
through arena.evaluate_candidate, preserving the evaluator's quick/exact views.
"""
from __future__ import annotations

import json
import math
import os
from pathlib import Path
import stat

from lean_tools import arena_workflow as arena
from lean_tools.measurement_policy import resolve_scoring_policy, scoring_policy_context


def environment_settings() -> tuple[Path | None, list[Path]]:
    """Opt in with E6_BASELINE_CACHE and an explicit JSON array of seed roots."""
    configured = os.environ.get("E6_BASELINE_CACHE")
    raw_seeds = os.environ.get("E6_BASELINE_SEEDS", "[]")
    try:
        seeds = json.loads(raw_seeds)
    except json.JSONDecodeError as error:
        raise ValueError("E6_BASELINE_SEEDS must be a JSON array of absolute cache roots") from error
    if not isinstance(seeds, list) or any(not isinstance(value, str) or not value for value in seeds):
        raise ValueError("E6_BASELINE_SEEDS must be a JSON array of absolute cache roots")
    roots = [Path(value) for value in seeds]
    root = Path(configured) if configured else None
    if any(not path.is_absolute() for path in ([root] if root else []) + roots):
        raise ValueError("Canonical baseline cache and seed roots must be absolute")
    if roots and root is None:
        raise ValueError("E6_BASELINE_SEEDS requires E6_BASELINE_CACHE")
    return root.resolve() if root else None, [path.resolve() for path in roots]


def _finite_nonnegative(value: object) -> bool:
    return type(value) in (int, float) and math.isfinite(value) and value >= 0


class OriginalBaselineCache:
    """A prepare-only importer/publisher with no broad discovery or source reads."""

    def __init__(self, root: Path | None, seed_roots: list[Path], private_root: Path):
        self.root = root.resolve() if root else None
        self.seeds = list(dict.fromkeys(path.resolve() for path in seed_roots))
        self.private = private_root.resolve()
        if self.root and (self.private.is_relative_to(self.root) or self.root.is_relative_to(self.private)):
            raise ValueError("Canonical original cache must be separate from the private preparation cache")

    def request(self, config: dict, candidate: Path, project: Path, *, quick: bool) -> dict:
        task = Path(config["task"])
        if arena.sha256_file(task) != config["task_sha256"]:
            raise ValueError("Frozen original task changed before baseline cache reuse")
        _, row = arena.load_task(task)
        if row["name"] != config["task_id"]:
            raise ValueError("Original baseline cache task identity differs")
        source = candidate.read_text(encoding="utf-8")
        original = arena.render_candidate_scaffold(row)
        if source.replace("\r\n", "\n") != original.replace("\r\n", "\n"):
            raise ValueError("Canonical baseline cache accepts only the unchanged rendered original")
        declaration, _ = arena.extract_candidate_declaration(row, source)
        entry = arena.environment_fingerprint_registry_entry(
            row, project, Path(config["fingerprint_registry"]), validate_guard=True)
        fingerprint = entry["fingerprint"]
        mode = "quick" if quick else "exact"
        policy = resolve_scoring_policy(config.get("scoring_policy", "legacy-v1"))
        with scoring_policy_context(policy):
            key = arena.evaluation_cache_key(task, row, declaration, fingerprint, mode)
            exact_key = arena.evaluation_cache_key(task, row, declaration, fingerprint, "exact")
        return {"mode": mode, "task_id": row["name"], "task_sha256": config["task_sha256"],
                "scoring_policy": policy,
                "environment": str(project.resolve()), "environment_fingerprint": fingerprint,
                "environment_guard_sha256": entry["guard_sha256"],
                "declaration_sha256": arena.sha256_bytes(declaration.encode("utf-8")),
                "key": key, "exact_key": exact_key,
                "original_tokens": config["original_tokens"],
                "original_measurement_tokens": (config["original_measurement_tokens"] if policy == "arena-v1"
                                                else config["original_tokens"]),
                "original_heartbeats": config["original_heartbeats"],
                "expected_original_heartbeats": config.get("original_measurement_heartbeats", config["original_heartbeats"]),
                "primary": project.resolve() == Path(config["primary"]).resolve()}

    def _read(self, root: Path, request: dict, mode: str) -> tuple[dict | None, dict]:
        key = request["exact_key"] if mode == "exact" else request["key"]
        path = arena.evaluation_cache_path(root, mode, key)
        evidence = {"path": str(path), "mode": mode, "key": key}
        if not path.exists():
            return None, {**evidence, "status": "missing"}
        try:
            info = path.lstat()
            if (not stat.S_ISREG(info.st_mode) or info.st_size > 262144
                    or not path.resolve().is_relative_to(root.resolve())):
                raise ValueError("Baseline entry must be a bounded regular file within its explicit cache root")
            payload = json.loads(path.read_text(encoding="utf-8"))
            self._validate(payload, request, mode, key)
            return payload, {**evidence, "status": "accepted", "entry_sha256": arena.sha256_file(path)}
        except (OSError, ValueError, TypeError, KeyError) as error:
            return None, {**evidence, "status": "rejected", "reason": str(error)}

    @staticmethod
    def _validate(payload: dict, request: dict, mode: str, key: str) -> None:
        expected = {"schema_version": arena.EVALUATION_CACHE_SCHEMA_VERSION,
                    "evaluator_revision": arena.EVALUATOR_CACHE_REVISION, "key": key, "mode": mode,
                    "environment_fingerprint": request["environment_fingerprint"],
                    "declaration_sha256": request["declaration_sha256"]}
        if not isinstance(payload, dict) or any(payload.get(name) != value for name, value in expected.items()):
            raise ValueError("Original cache identity, mode, evaluator revision, or fingerprint mismatch")
        fields = payload.get("evaluation")
        if not isinstance(fields, dict):
            raise ValueError("Original cache evaluation is absent")
        # Construction rejects unknown fields or incomplete evaluator records.
        evaluation = arena.Evaluation(**fields)
        arena_policy = request.get("scoring_policy", "legacy-v1") == "arena-v1"
        measurement_tokens = request.get("original_measurement_tokens", request["original_tokens"])
        expected_token_reduction = (round(100 * (request["original_tokens"] - measurement_tokens)
                                         / request["original_tokens"], 2) if arena_policy else 0)
        if (evaluation.valid is not True or evaluation.task_id != request["task_id"]
                or evaluation.scoring_policy != request.get("scoring_policy", "legacy-v1")
                or (arena_policy and (evaluation.candidate_token_offset != 1
                                      or evaluation.original_body_tokens != measurement_tokens - 1))
                or evaluation.environment_fingerprint != request["environment_fingerprint"]
                or type(evaluation.original_local_tokens) is not int
                or type(evaluation.candidate_local_tokens) is not int
                or evaluation.original_local_tokens != request["original_tokens"]
                or evaluation.candidate_local_tokens != measurement_tokens
                or evaluation.local_token_reduction_pct != expected_token_reduction
                or not _finite_nonnegative(evaluation.compile_seconds)):
            raise ValueError("Original cache validity or frozen token semantics mismatch")
        if mode == "exact":
            expected_reference = (request["original_heartbeats"] if arena_policy else evaluation.heartbeat)
            expected_hb_reduction = (round(100 * (expected_reference - evaluation.heartbeat)
                                          / expected_reference, 2)
                                     if arena_policy and type(evaluation.heartbeat) is int else 0)
            if (not _finite_nonnegative(evaluation.axiom_audit_seconds)
                    or not isinstance(evaluation.axioms, list)
                    or any(not isinstance(axiom, str) or axiom not in arena.ALLOWED_AXIOMS
                           for axiom in evaluation.axioms)
                    or type(evaluation.heartbeat) is not int or evaluation.heartbeat < 0
                    or type(evaluation.local_reference_heartbeat) is not int
                    or evaluation.local_reference_heartbeat != expected_reference
                    or evaluation.heartbeat_reduction_pct != expected_hb_reduction
                    or (arena_policy and evaluation.heartbeat <= 0)
                    or (not arena_policy and request["primary"] and evaluation.heartbeat != request.get(
                        "expected_original_heartbeats", request["original_heartbeats"]))):
                raise ValueError("Original exact cache lacks matching baseline heartbeat and axiom evidence")
        elif any(value is not None for value in (
                evaluation.axiom_audit_seconds, evaluation.axioms, evaluation.heartbeat,
                evaluation.heartbeat_reduction_pct, evaluation.axiom_audit_shares_compile)):
            raise ValueError("Original quick cache contains exact-only measurement fields")

    def stage(self, request: dict) -> dict:
        """Validate and copy at most one original entry into the private cache."""
        report = {"status": "disabled" if self.root is None else "miss", "request": request,
                  "canonical_root": str(self.root) if self.root else None,
                  "private_root": str(self.private), "attempts": []}
        if self.root is None:
            return report
        modes = [request["mode"]] + (["exact"] if request["mode"] == "quick" else [])
        for root in [self.private, self.root, *self.seeds]:
            for mode in modes:
                payload, evidence = self._read(root, request, mode)
                report["attempts"].append(evidence)
                if payload is None:
                    if root == self.private and evidence["status"] == "rejected":
                        raise ValueError(f"Private preparation baseline cache is invalid: {evidence['reason']}")
                    continue
                key = payload["key"]
                if root != self.root:
                    arena.write_json_atomic(arena.evaluation_cache_path(self.root, mode, key), payload)
                if root != self.private:
                    arena.write_json_atomic(arena.evaluation_cache_path(self.private, mode, key), payload)
                report.update(status="hit", source=str(evidence["path"]), source_mode=mode,
                              entry_sha256=evidence["entry_sha256"])
                return report
        return report

    def publish(self, request: dict) -> dict:
        """Publish only a fully validated original result generated on a miss."""
        if self.root is None:
            return {"status": "disabled"}
        modes = [request["mode"]] + (["exact"] if request["mode"] == "quick" else [])
        for mode in modes:
            payload, evidence = self._read(self.private, request, mode)
            if payload is not None:
                path = arena.evaluation_cache_path(self.root, mode, payload["key"])
                arena.write_json_atomic(path, payload)
                return {"status": "published", "path": str(path), "source": evidence}
        raise ValueError("Completed original check did not produce a valid private baseline cache entry")
