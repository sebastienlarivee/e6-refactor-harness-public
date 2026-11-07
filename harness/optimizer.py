"""Crash-safe product boundary around compact and a bounded instance-cache sweep.

The transaction owns the original agent input and a separately host-validated
output. Neither a source hash nor a search-cache receipt admits a saved winner.
Publishing Selected.lean and selection.json is replayable in either order.
The 1200/300-second schedule bounds compact; the one-shot dictionary stage has
its own allowance. Independent host verification is timed separately. A verified
compact checkpoint survives dictionary failure and boundary recovery.
"""
from __future__ import annotations

from contextlib import contextmanager
from dataclasses import replace
import hashlib
import json
import math
import os
from pathlib import Path
import re
import tempfile
import time

from e6 import deterministic, proof
from e6.experiment import experiment_spec
from e6.deterministic_support.search_cache import tool_identity

SCHEMA_VERSION = 2
MODES = ("compact", "off")
EARLY_BUDGET_SECONDS = 1200
LATE_BUDGET_SECONDS = 300


class OptimizerBoundaryError(ValueError):
    """Saved transaction, caller, or frozen identity no longer agrees."""


def budget_seconds(pass_number: int, mode: str = "compact") -> int:
    if type(pass_number) is not int or pass_number < 1:
        raise ValueError("Pass number must be a positive integer")
    if mode not in MODES:
        raise ValueError("Optimizer must be compact or off")
    return 0 if mode == "off" else EARLY_BUDGET_SECONDS if pass_number <= 2 else LATE_BUDGET_SECONDS


def engine_config(config: dict, pass_number: int) -> dict:
    """Derive compact engine settings without mutating the frozen run config."""
    budget_seconds(pass_number)
    spec = replace(experiment_spec(config), deterministic_refactoring=True,
        deterministic_policy="compact", deterministic_cache=True,
        deterministic_regenerate=True, deterministic_budget_seconds=EARLY_BUDGET_SECONDS,
        deterministic_late_budget_seconds=LATE_BUDGET_SECONDS,
        deterministic_beam_width=1, deterministic_beam_score_drop=0.1)
    result = {**config, "experiment_spec": spec.to_dict()}
    for name in spec.__dataclass_fields__:
        if name.startswith("deterministic_"):
            result[name] = getattr(spec, name)
    return result


def _digest(value) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
        allow_nan=False, separators=(",", ":")).encode("utf-8")).hexdigest()


def _read(path: Path) -> dict:
    if path.is_symlink() or not path.is_file():
        raise OptimizerBoundaryError(f"Optimizer artifact is not a regular file: {path}")
    try:
        result = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise OptimizerBoundaryError(f"Cannot read optimizer transaction: {path}") from error
    if not isinstance(result, dict):
        raise OptimizerBoundaryError("Optimizer transaction must be an object")
    return result


def _atomic_bytes(path: Path, content: bytes) -> None:
    """Durable file replacement; no partially published source or receipt."""
    if path.is_symlink():
        raise OptimizerBoundaryError(f"Optimizer artifact must not be a symlink: {path}")
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as document:
            document.write(content)
            document.flush()
            os.fsync(document.fileno())
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        Path(temporary).unlink(missing_ok=True)


def _write(path: Path, value: dict) -> None:
    _atomic_bytes(path, (json.dumps(value, sort_keys=True, ensure_ascii=False,
        allow_nan=False, indent=2) + "\n").encode("utf-8"))


@contextmanager
def _locked(path: Path):
    import fcntl
    if path.is_symlink():
        raise OptimizerBoundaryError("Optimizer lock must not be a symlink")
    with path.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def _identity(config: dict, effective: dict, capsule: Path, mode: str) -> dict:
    files = {}
    for key, expected in (("task", "task_sha256"),
                          ("fingerprint_registry", "fingerprint_registry_sha256")):
        path = Path(config[key])
        if path.is_symlink() or not path.is_file():
            raise OptimizerBoundaryError(f"Frozen optimizer {key} is not a regular file")
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != config[expected]:
            raise OptimizerBoundaryError(f"Frozen optimizer {key} changed")
        files[key] = {"path": str(path.resolve()), "sha256": actual}
    return {"schema_version": SCHEMA_VERSION, "config_sha256": _digest(config),
        "effective_config_sha256": _digest(effective), "files": files,
        "primary": config["primary"], "compatibility": config["compatibility"],
        "engine_sha256": tool_identity(Path(deterministic.__file__).resolve().parents[1]),
        "boundary_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "mode": mode, "pass_name": capsule.name, "capsule": str(capsule),
        "budget_seconds": budget_seconds(int(capsule.name.removeprefix("pass-")), mode),
        "settings": deterministic._settings(effective) if mode == "compact" else {},
        "dictionary_settings": deterministic.dictionary_settings() if mode == "compact" else {}}


def _candidate_identity(candidate: dict) -> dict:
    # Publication paths and a caller's attached receipt do not change a proof.
    # Measurement and compatibility evidence remain part of the identity.
    return {key: value for key, value in candidate.items()
            if key not in {"selected_path", "deterministic_refactoring", "candidate_records",
                           "validation_healthy", "unique_candidate_count"}}


def _same_candidate(left: dict, right: dict) -> bool:
    return _candidate_identity(left) == _candidate_identity(right)


def _verify_again(config: dict, candidate: dict, path: Path, *, require_all_versions: bool = False) -> dict:
    """Independently consult host evaluation, including its guarded exact cache."""
    proof._verify_incumbent(config, candidate)
    if proof._source(path) != candidate["source"]:
        raise OptimizerBoundaryError("Saved optimizer source differs from its candidate")
    _, row = proof.arena.load_task(Path(config["task"]))
    declaration, _ = proof.arena.extract_candidate_declaration(row, candidate["source"])
    if len(declaration) > experiment_spec(config).candidate_intake_characters:
        raise ValueError("Optimizer boundary source exceeds the contest declaration intake limit")
    checks = []
    with proof._host_validation_cache(config):
        for index, environment in enumerate([config["primary"], *config["compatibility"]]):
            evaluation = proof._check(config, path, Path(environment), quick=index > 0)
            if proof._validation_infrastructure_failure(evaluation):
                raise proof._ValidationInfrastructureError("Optimizer boundary verification has infrastructure failure")
            if index == 0 and evaluation.get("valid") is not True:
                raise ValueError("Optimizer boundary source failed independent host verification")
            if evaluation.get("source_sha256") not in {None, candidate["sha256"]}:
                raise ValueError("Optimizer verification returned evidence for another source")
            checks.append({"environment": environment, "passed": evaluation.get("valid") is True, "evaluation": evaluation})
    primary = checks[0]["evaluation"]
    compatibility = 100 * sum(check["passed"] for check in checks) / len(checks)
    if (primary.get("measurement_mode") != "exact" or primary.get("axiom_status") != "measured"
            or not isinstance(primary.get("axioms"), list)
            or any(axiom not in proof.arena.ALLOWED_AXIOMS for axiom in primary["axioms"])
            or type(candidate.get("tokens")) is not int or candidate["tokens"] < 0
            or type(candidate.get("heartbeats")) is not int or candidate["heartbeats"] < 0
            or primary.get("length", {}).get("candidate_tokens") != candidate["tokens"]
            or primary.get("heartbeat", {}).get("candidate") != candidate["heartbeats"]
            or candidate.get("compatibility_pct") != compatibility
            or (require_all_versions and compatibility != 100)):
        raise ValueError("Optimizer boundary lacks matching exact measurements and axiom audit")
    reference = primary.get("heartbeat", {}).get("local_reference")
    control = proof._original_control_heartbeats(config)
    if experiment_spec(config).scoring_policy == "arena-v1" or reference != control:
        if experiment_spec(config).scoring_policy != "arena-v1" and reference is not None:
            raise ValueError("Optimizer boundary native control changed")
        _, row = proof.arena.load_task(Path(config["task"]))
        proof._native_control_evidence(config, row, primary)
    return {"candidate_sha256": candidate["sha256"], "checks": checks,
            "verification": "independent_host_exact_and_compatibility"}


def _summary(best: dict) -> dict:
    return {key: best.get(key) for key in ("sha256", "score", "tokens", "heartbeats", "compatibility_pct")}


def _failure(report: dict, error: Exception, phase: str) -> dict:
    """Keep engine diagnostics, especially negative-cache/parser failures, visible."""
    counts = dict(report.get("health_counts", {}))
    counts["boundary_failures"] = counts.get("boundary_failures", 0) + 1
    return {**report, "engine_status": report.get("engine_status", report.get("status")),
        "status": "failed_retained_incumbent", "health_status": "degraded",
        "health_counts": counts,
        "warnings": list(dict.fromkeys([*report.get("warnings", []), phase])),
        "errors": [*report.get("errors", []), {"phase": phase,
            "type": type(error).__name__, "message": str(error)[:512]}], "model_calls": 0}


def _promotion_checkpoint(stage: str, directory: Path) -> None:
    """An intentionally empty fault-injection seam for durable promotion tests."""


def _check_improvement(config: dict, candidate: dict, incumbent: dict) -> None:
    proof._verify_incumbent(config, candidate)
    if candidate["score"] < incumbent["score"]:
        raise ValueError("Deterministic optimizer regressed the verified incumbent")
    if candidate["sha256"] != incumbent["sha256"] and candidate["score"] <= incumbent["score"]:
        raise ValueError("Deterministic optimizer changed source without a strict score gain")
    if candidate["sha256"] == incumbent["sha256"] and not _same_candidate(candidate, incumbent):
        raise ValueError("Deterministic optimizer changed measurements for the unchanged source")


def _merge_dictionary_report(compact: dict, dictionary: dict) -> dict:
    counts = dict(compact.get("health_counts", {}))
    for name, count in dictionary.get("health_counts", {}).items():
        counts[name] = counts.get(name, 0) + count
    statuses = {compact.get("health_status"), dictionary.get("health_status")}
    return {**compact, "dictionary_cache": dictionary, "health_counts": counts,
        "health_status": "degraded" if "degraded" in statuses else "limited" if "limited" in statuses else compact.get("health_status", "healthy"),
        "warnings": list(dict.fromkeys([*compact.get("warnings", []), *dictionary.get("warnings", [])])),
        "errors": [*compact.get("errors", []), *[{**error, "phase": "dictionary/" + str(error.get("phase", "unknown"))}
                    for error in dictionary.get("errors", [])]],
        "evaluated_candidates": compact.get("evaluated_candidates", 0) + dictionary.get("evaluated_candidates", 0),
        "accepted_candidates": compact.get("accepted_candidates", 0) + dictionary.get("accepted_candidates", 0)}


def _recovered_search_seconds(report: dict) -> float:
    """Include recorded worker work when recovery consumes its saved boundary."""
    seconds = report.get("wall_seconds", 0)
    return float(seconds) if (report.get("reused") is True and type(seconds) in (int, float)
        and math.isfinite(seconds) and seconds >= 0) else 0.0


def _seal(transaction: dict) -> dict:
    value = {key: item for key, item in transaction.items() if key != "transaction_sha256"}
    return {**value, "transaction_sha256": _digest(value)}


def _publish(capsule: Path, directory: Path, transaction: dict) -> tuple[dict, dict, dict]:
    best = {**transaction["output"], "selected_path": str(capsule / "Selected.lean")}
    report = transaction["report"]
    selection = {**transaction["input_selection"], **best, "deterministic_refactoring": report}
    _promotion_checkpoint("before_source", directory)
    _atomic_bytes(capsule / "Selected.lean", best["source"].encode("utf-8"))
    _promotion_checkpoint("after_source", directory)
    _write(capsule / "selection.json", selection)
    _promotion_checkpoint("after_selection", directory)
    _write(directory / "transaction.json", _seal({**transaction, "stage": "committed"}))
    _promotion_checkpoint("after_commit", directory)
    return best, selection, report


def optimize_pass_result(config, root, capsule, best, selection):
    """Optimize or finish a saved transaction; accepts its input or its output.

    The caller must retire model credentials and finalize host selection first.
    Recovery calls this same function before launching another native pass.
    Ordinary engine failures retain the verified input. Corrupt or incompatible
    saved transactions raise OptimizerBoundaryError and are never overwritten.
    """
    started = time.monotonic()
    search_seconds = verification_seconds = prior_seconds = recovered_seconds = 0.0
    root, capsule = Path(root).resolve(), Path(capsule).resolve()
    if (root != Path(config["root"]).resolve() or capsule.parent != root
            or not re.fullmatch(r"pass-0*[1-9][0-9]*", capsule.name) or not capsule.is_dir()):
        raise OptimizerBoundaryError("Optimizer requires a numbered pass capsule under the frozen proof root")
    pass_number = int(capsule.name.removeprefix("pass-"))
    mode = config.get("optimizer", "compact")
    allowance = budget_seconds(pass_number, mode)
    proof._verify_incumbent(config, best)
    if selection.get("validation_healthy") is False:
        raise OptimizerBoundaryError("Optimizer requires a healthy host-finalized selection")
    effective = engine_config(config, pass_number) if mode == "compact" else dict(config)
    parent = root / "optimizer-boundaries"
    if parent.is_symlink():
        raise OptimizerBoundaryError("Optimizer transaction directory must not be a symlink")
    parent.mkdir(exist_ok=True)
    with _locked(parent / f".{capsule.name}.lock"):
        directory = parent / capsule.name
        if directory.is_symlink():
            raise OptimizerBoundaryError("Optimizer pass directory must not be a symlink")
        directory.mkdir(exist_ok=True)
        identity = _identity(config, effective, capsule, mode)
        path = directory / "transaction.json"
        replay = path.exists()
        if replay:
            transaction = _read(path)
            if (transaction != _seal(transaction) or transaction.get("identity") != identity
                    or transaction.get("stage") not in {"prepared", "compact_verified", "verified", "committed"}):
                raise OptimizerBoundaryError("Optimizer transaction or frozen identity changed")
            if _read(directory / "agent-selection.json") != transaction["input_selection"]:
                raise OptimizerBoundaryError("Saved optimizer agent selection changed")
            original = transaction["input"]
            if not (_same_candidate(best, original)
                    or ("output" in transaction and _same_candidate(best, transaction["output"]))):
                raise OptimizerBoundaryError("Optimizer caller is neither the saved input nor the saved output")
            try:
                _verify_again(config, original, directory / "Input.lean")
            except Exception as error:
                raise OptimizerBoundaryError("Saved optimizer input failed independent verification") from error
        else:
            original = dict(best)
            if not _same_candidate(selection, original):
                raise OptimizerBoundaryError("Optimizer incumbent differs from host selection")
            _atomic_bytes(directory / "Input.lean", original["source"].encode("utf-8"))
            _write(directory / "agent-selection.json", dict(selection))
            transaction = _seal({"identity": identity, "stage": "prepared",
                "input": original, "input_selection": dict(selection)})
            _write(path, transaction)
            _promotion_checkpoint("after_prepare", directory)
        if transaction["stage"] in {"verified", "committed"}:
            output = transaction["output"]
            try:
                _verify_again(config, output, directory / "Output.lean",
                    require_all_versions=output["sha256"] != original["sha256"])
                _check_improvement(config, output, original)
            except Exception as error:
                raise OptimizerBoundaryError("Saved optimizer output failed independent verification") from error
            # Replaying publication also repairs a crash between Selected and its receipt.
            return _publish(capsule, directory, transaction)
        if transaction["stage"] == "compact_verified":
            compact = transaction["compact"]
            output, report = dict(compact["output"]), dict(compact["report"])
            run_dictionary = compact["run_dictionary"]
            search_seconds, verification_seconds = compact["search_seconds"], compact["verification_seconds"]
            prior_seconds = compact["elapsed_seconds"]
            verification_started = time.monotonic()
            try:
                _check_improvement(config, output, original)
                verification = _verify_again(config, output, directory / "Compact.lean",
                    require_all_versions=output["sha256"] != original["sha256"])
            except Exception as error:
                raise OptimizerBoundaryError("Saved compact output failed independent verification") from error
            finally:
                verification_seconds += time.monotonic() - verification_started
        else:
            report = {"status": "disabled", "health_status": "disabled", "health_counts": {},
                      "warnings": [], "errors": [], "model_calls": 0, "cost_usd": 0}
            output = dict(original)
            run_dictionary = mode == "compact"
            if mode == "compact":
                search_started = time.monotonic()
                try:
                    candidate, report = deterministic.optimize(effective, capsule, original)
                    _promotion_checkpoint("after_engine", directory)
                    _check_improvement(config, candidate, original)
                    output = dict(candidate)
                except Exception as error:
                    report = _failure(report, error, "boundary_engine_failure")
                    run_dictionary = False
                finally:
                    recovered_seconds += _recovered_search_seconds(report)
                    search_seconds = time.monotonic() - search_started + recovered_seconds
            _atomic_bytes(directory / "Compact.lean", output["source"].encode("utf-8"))
            verification = {"verification": "unchanged_host_verified_input", "candidate_sha256": original["sha256"]}
            if output["sha256"] != original["sha256"]:
                verification_started = time.monotonic()
                try:
                    verification = _verify_again(config, output, directory / "Compact.lean", require_all_versions=True)
                except Exception as error:
                    report = _failure(report, error, "boundary_output_verification_failure")
                    output, run_dictionary = dict(original), False
                    _atomic_bytes(directory / "Compact.lean", output["source"].encode("utf-8"))
                    verification = {"verification": "unchanged_host_verified_input", "candidate_sha256": original["sha256"]}
                finally:
                    verification_seconds = time.monotonic() - verification_started
            transaction = _seal({**transaction, "stage": "compact_verified", "compact": {
                "output": output, "report": report, "verification": verification,
                "run_dictionary": run_dictionary, "search_seconds": search_seconds,
                "verification_seconds": verification_seconds,
                "elapsed_seconds": time.monotonic() - started + recovered_seconds}})
            _write(path, transaction)
            _promotion_checkpoint("after_compact_verify", directory)

        compact_output = dict(output)
        dictionary_report = {"status": "disabled" if mode == "off" else "skipped",
            "reason": "optimizer_disabled" if mode == "off" else "compact_stage_failure",
            "health_status": "disabled", "health_counts": {}, "warnings": [], "errors": [],
            "model_calls": 0, "cost_usd": 0}
        dictionary_seconds = 0.0
        if run_dictionary:
            dictionary_started = time.monotonic()
            try:
                candidate, dictionary_report = deterministic.optimize_dictionary(effective, capsule, compact_output)
                _promotion_checkpoint("after_dictionary", directory)
                _check_improvement(config, candidate, compact_output)
                output = dict(candidate)
            except Exception as error:
                dictionary_report = _failure(dictionary_report, error, "boundary_dictionary_failure")
                output = dict(compact_output)
            finally:
                recovered = _recovered_search_seconds(dictionary_report)
                recovered_seconds += recovered
                dictionary_seconds = time.monotonic() - dictionary_started + recovered
                search_seconds += dictionary_seconds
        _atomic_bytes(directory / "Output.lean", output["source"].encode("utf-8"))
        if output["sha256"] != compact_output["sha256"]:
            verification_started = time.monotonic()
            try:
                verification = _verify_again(config, output, directory / "Output.lean", require_all_versions=True)
            except Exception as error:
                dictionary_report = _failure(dictionary_report, error, "boundary_dictionary_verification_failure")
                output = dict(compact_output)
                _atomic_bytes(directory / "Output.lean", output["source"].encode("utf-8"))
            finally:
                verification_seconds += time.monotonic() - verification_started
        dictionary_report = {**dictionary_report, "before": _summary(compact_output), "after": _summary(output),
            "improved": output["score"] > compact_output["score"], "boundary_search_seconds": round(dictionary_seconds, 6),
            "effective_budget_seconds": deterministic.DICTIONARY_BUDGET_SECONDS if mode == "compact" else 0}
        report = _merge_dictionary_report(report, dictionary_report)
        report = {**report, "before": _summary(original), "after": _summary(output),
            "improved": output["score"] > original["score"], "optimizer": mode,
            "effective_budget_seconds": allowance, "boundary_schema_version": SCHEMA_VERSION,
            "boundary_path": str(path), "boundary_binding_sha256": _digest(identity),
            "search_seconds": round(search_seconds, 6),
            "verification_seconds": round(verification_seconds, 6),
            "total_seconds": round(prior_seconds + recovered_seconds + time.monotonic() - started, 6),
            "boundary_wall_seconds": round(time.monotonic() - started, 6),
            "recovered_search_seconds": round(recovered_seconds, 6),
            "stage_order": ["compact", "dictionary_cache"] if mode == "compact" else [],
            "dictionary_budget_seconds": deterministic.DICTIONARY_BUDGET_SECONDS if mode == "compact" else 0,
            "agent_selection_path": str(directory / "agent-selection.json"), "model_calls": 0}
        transaction = _seal({**transaction, "stage": "verified", "output": output,
            "verification": verification, "report": report})
        _write(path, transaction)
        _promotion_checkpoint("after_verify", directory)
        return _publish(capsule, directory, transaction)
