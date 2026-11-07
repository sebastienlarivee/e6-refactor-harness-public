"""Bounded, model-free host optimization of a verified pass incumbent.

Only this module's private worker writes search artifacts.  The caller owns
promotion into the experiment's selection files; a killed worker can therefore
leave, at worst, an incomplete candidate beside its last verified checkpoint.
"""
from __future__ import annotations

import argparse
import hashlib
from itertools import zip_longest
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import time

from lean_tools import process_memory
from . import proof
from .experiment import experiment_spec
from .runtime import RuntimeContext, create_environment_directories, scoped_environment
from .signals import defer_termination

SCHEMA_VERSION = 1
CANDIDATE_TIMEOUT_SECONDS = 90
COMPACT_VALIDATION_RESERVE_SECONDS = 120
DICTIONARY_STAGE = "dictionary_cache"
DICTIONARY_BUDGET_SECONDS = 900
DICTIONARY_SETTINGS = {
    "stage": DICTIONARY_STAGE, "budget_seconds": DICTIONARY_BUDGET_SECONDS,
    "max_candidates": 4, "generator_timeout_seconds": 180,
    "censuses": 1, "regenerate": False, "beam_width": 1, "search_cache": False,
}


def dictionary_settings() -> dict:
    """Return the fixed production finisher settings for identity bindings."""
    return dict(DICTIONARY_SETTINGS)
# The successful overnight narrow arm: native solver discovery plus bounded
# source formatting, followed by the ordinary all-version validator.
COMPACT_DISCOVERY_SETTINGS = {
    "max_sites": 16, "scan_seconds": 45, "solver_heartbeats": 10000,
    "site_order": "span_short_first", "discovery_timeout_seconds": 240,
    "max_candidates": 64,
}


def _json_digest(value: dict) -> str:
    return proof._digest(json.dumps(value, sort_keys=True, ensure_ascii=False, allow_nan=False))


def _read(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"Expected JSON object: {path}")
    return value


def _immutable_source(path: Path, source: str) -> None:
    if path.exists():
        if proof._source(path) != source:
            raise ValueError("Immutable deterministic source changed")
        return
    with path.open("x", encoding="utf-8", newline="") as document:
        document.write(source)
    path.chmod(0o444)


def _summary(best: dict) -> dict:
    return {key: best.get(key) for key in (
        "sha256", "score", "tokens", "heartbeats", "compatibility_pct", "selected_path")}


def _improved(best: dict, original: dict) -> bool:
    return (best.get("sha256") != original.get("sha256")
            and isinstance(best.get("score"), (int, float))
            and isinstance(original.get("score"), (int, float))
            and best["score"] > original["score"])


def _error(error: BaseException, *, phase: str) -> dict:
    return {"phase": phase, **proof._preparation_error(error)}


def _settings(config: dict) -> dict:
    spec = experiment_spec(config)
    values = {name: getattr(spec, name) for name in (
        "deterministic_refactoring", "deterministic_budget_seconds",
        "deterministic_max_candidates", "deterministic_rounds")}
    # Preserve historical request bindings when every new feature is disabled.
    for name, default in (("deterministic_policy", "legacy"), ("deterministic_cache", False),
                          ("deterministic_regenerate", False), ("deterministic_late_budget_seconds", None),
                          ("deterministic_beam_width", 1), ("deterministic_beam_score_drop", 0.1)):
        value = getattr(spec, name, default)
        if value != default:
            values[name] = value
    return values


def _budget(config: dict, pass_name: str) -> int:
    spec = experiment_spec(config)
    if hasattr(spec, "deterministic_budget_for_pass"):
        return spec.deterministic_budget_for_pass(int(pass_name.removeprefix("pass-")))
    return spec.deterministic_budget_seconds


def _resource_limit(value) -> bool:
    """Recognize explicit compiler/admission caps without making them verdicts."""
    if isinstance(value, (TimeoutError, proof.arena.LeanTimeoutError, _CandidateResourceLimit)):
        return True
    if isinstance(value, BaseException):
        return _resource_limit(proof._preparation_error(value))
    if isinstance(value, dict):
        if (value.get("timed_out") is True or value.get("returncode") in (-9, 137)
                or value.get("type") in {"TimeoutError", "LeanTimeoutError"}
                or value.get("error_type") in {"TimeoutError", "LeanTimeoutError"}
                or value.get("status") in {"timeout", "timed_out", "resource_limit", "resource_exhausted"}):
            return True
        for key, item in value.items():
            if isinstance(item, (dict, list)) and _resource_limit(item):
                return True
            if key in {"message", "output", "output_tail"} and isinstance(item, str):
                diagnostic = item.lower()
                if any(marker in diagnostic for marker in (
                        "maximum number of heartbeats", "maximum recursion depth", "deep recursion detected",
                        "out of memory", "resource exhausted", "stack overflow", "(deterministic) timeout")):
                    return True
                if re.search(r"(?:maxheartbeats|maxrecdepth|deeprecursion)\b[^\n]{0,40}"
                             r"(?:exceeded|exhausted|reached)", diagnostic):
                    return True
        return False
    if isinstance(value, list):
        return any(_resource_limit(item) for item in value)
    return False


def _failure_kind(error: BaseException, deadline: float) -> str:
    # This diagnostic classification is independent of negative-cache admission.
    if isinstance(error, _GeneratorInvalid):
        return "generator_invalid"
    if _resource_limit(error):
        return "budget" if time.monotonic() >= deadline else "resource_limit"
    from .deterministic_support.search_cache import compile_rejection
    if compile_rejection(error, proof.arena.LeanCompileError) is not None:
        return "candidate_invalid"
    if (isinstance(error, proof.arena.WorkflowError)
            and not proof._validation_exception_is_infrastructure(error)
            and not isinstance(error, proof.arena.LeanCompileError)):
        return "candidate_invalid"
    # Unexpected parser/helper exceptions cannot establish proof invalidity.
    return "infrastructure"


def _health(report: dict) -> dict:
    """Bounded receipt diagnostics; full compiler details stay in report.json."""
    reason = report.get("termination_reason")
    if reason is None and report.get("status") == "timed_out":
        reason = "wall_deadline"  # Receipts written before explicit termination reasons.
    counts = {key: 0 for key in (
        "candidate_invalid", "generator_invalid", "candidate_infrastructure_failures",
        "candidate_resource_limits", "candidate_budget_stops", "generator_failures",
        "generator_resource_limits", "generator_budget_stops", "generation_skips")}
    for record in report.get("candidate_records", []):
        kind = record.get("failure_kind", record.get("error_kind"))
        if kind == "infrastructure" and _resource_limit(record.get("error")):
            kind = "resource_limit"
        key = {"candidate_invalid": "candidate_invalid", "generator_invalid": "generator_invalid",
               "infrastructure": "candidate_infrastructure_failures", "resource_limit": "candidate_resource_limits",
               "budget": "candidate_budget_stops"}.get(kind)
        if key is None and record.get("status") in {"primary_invalid", "compatibility_failed"}:
            key = "candidate_invalid"
        if key is not None:
            counts[key] += 1
    for record in report.get("generator_records", []):
        if record.get("status") == "failed":
            kind = record.get("failure_kind")
            if kind is None:
                kind = "resource_limit" if _resource_limit(record.get("error")) else "infrastructure"
            counts[{"resource_limit": "generator_resource_limits", "budget": "generator_budget_stops"}
                   .get(kind, "generator_failures")] += 1
        elif record.get("status") == "skipped" or record.get("incomplete") is True:
            counts["generation_skips"] += 1
    counts["cache_errors"] = report.get("cache_error_count", len(report.get("cache_errors", [])))
    counts["infrastructure_errors"] = sum(not (
        reason == "wall_deadline" and item.get("phase") in {"search", "worker"}
        and item.get("type") in {"TimeoutError", "LeanTimeoutError"}) for item in report.get("errors", []))
    warnings = [key for key in ("candidate_infrastructure_failures", "generator_invalid",
                               "generator_failures", "cache_errors", "infrastructure_errors") if counts[key]]
    partial = warnings + [key for key in ("candidate_resource_limits", "candidate_budget_stops",
        "generator_resource_limits", "generator_budget_stops", "generation_skips") if counts[key]]
    if reason and reason not in {"frontier_exhausted", "cached_frontier_exhausted", "unsupported_shape"}:
        partial.append(reason)
    if report.get("cache_snapshot_skipped"):
        partial.append("cache_snapshot_" + report["cache_snapshot_skipped"])
    status = report.get("status")
    if status == "infrastructure_failure":
        warnings.append("search_infrastructure_failure")
        partial.append("search_infrastructure_failure")
    elif status in {"timed_out", "interrupted"} and not reason:
        partial.append("wall_deadline" if status == "timed_out" else "interrupted")
    return {"health_status": ("disabled" if status == "disabled" else "degraded" if warnings
                              else "limited" if partial else "healthy"),
            "health_counts": counts, "warnings": warnings,
            "partial_reasons": list(dict.fromkeys(partial))}


def _compact(report: dict, directory: Path | None = None) -> dict:
    result = {key: report.get(key) for key in (
        "schema_version", "status", "binding_sha256", "config_sha256", "pass_name",
        "seed_sha256", "before", "after", "improved", "evaluated_candidates",
        "accepted_candidates", "rounds_completed", "wall_seconds", "model_calls", "cost_usd")}
    result.update({key: report.get(key) for key in (
        "negative_cache_hits", "search_reused", "search_resumed", "search_exhausted",
        "cache_binding_sha256", "cache_search_binding_sha256", "timing_clock",
        "effective_budget_seconds", "termination_reason", "pending_candidates", "pending_parents",
        "retryable_candidates", "incomplete_generations", "frontier_alternatives",
        "frontier_admissions", "frontier_pruned", "generation_limit", "generated_parents",
        "frontier_telemetry_complete", "fixed_stage", "dictionary_telemetry") if key in report})
    result["candidate_timeout_seconds"] = CANDIDATE_TIMEOUT_SECONDS
    if report.get("status") == "timed_out" and not report.get("termination_reason"):
        result["termination_reason"] = "wall_deadline"
    if directory is not None:
        result.update(report_path=str(directory / "report.json"),
                      checkpoint_path=str(directory / "checkpoint.json"),
                      selection_before_path=str(directory / "selection-before.json")
                      if (directory / "selection-before.json").exists() else None)
    result.update(_health(report))
    result["errors"] = [{"phase": item.get("phase"), "type": item.get("type"),
                         "message": str(item.get("message", ""))[:512]}
                        for item in report.get("errors", [])[-8:]]
    return result


def _checkpoint(config: dict, directory: Path, binding: str, incumbent: dict) -> dict:
    value = _read(directory / "checkpoint.json")
    if value.get("binding_sha256") != binding:
        raise ValueError("Deterministic checkpoint belongs to another invocation")
    return _verified_checkpoint_best(config, directory, incumbent, value["best"])


def _verified_checkpoint_best(config: dict, directory: Path, incumbent: dict, best: dict) -> dict:
    """Verify source and complete evidence before writing or recovering a win."""
    if not isinstance(best, dict):
        raise ValueError("Deterministic checkpoint lacks a verified incumbent object")
    proof._verify_incumbent(config, best)
    selected = Path(best["selected_path"])
    if (selected.parent not in {directory, directory / "validated"}
            or proof._source(selected) != best["source"]
            or best["score"] < incumbent["score"]):
        raise ValueError("Deterministic checkpoint lacks its immutable verified source")
    if best["sha256"] != incumbent["sha256"]:
        checks = best.get("compatibility", [])
        projects = [config["primary"], *config["compatibility"]]
        if (best["score"] <= incumbent["score"] or not isinstance(checks, list) or len(checks) != len(projects)
                or best.get("compatibility_pct") != 100
                or any(not isinstance(check, dict) or not isinstance(check.get("evaluation"), dict)
                       or check.get("environment") != project or check.get("passed") is not True
                       or check.get("evaluation", {}).get("valid") is not True
                       for check, project in zip(checks, projects))):
            raise ValueError("Deterministic checkpoint lacks full compatibility evidence")
        primary = checks[0]["evaluation"]
        if (type(best.get("tokens")) is not int or type(best.get("heartbeats")) is not int
                or best["tokens"] < 0 or best["heartbeats"] < 0
                or primary.get("measurement_mode") != "exact" or primary.get("axiom_status") != "measured"
                or not isinstance(primary.get("axioms"), list)
                or any(axiom not in proof.arena.ALLOWED_AXIOMS for axiom in primary["axioms"])
                or primary.get("length", {}).get("candidate_tokens") != best.get("tokens")
                or primary.get("heartbeat", {}).get("candidate") != best.get("heartbeats")
                or any(check["evaluation"].get("source_sha256") not in {None, best["sha256"]} for check in checks)):
            raise ValueError("Deterministic checkpoint lacks exact source-bound measurements and axiom audit")
    return best


def _environment(config: dict, directory: Path) -> dict[str, str]:
    environment = {name: value for name, value in os.environ.items()
                   if not any(part in name.upper() for part in (
                       "TOKEN", "API_KEY", "SECRET", "PASSWORD", "AUTH"))}
    runtime = RuntimeContext.resolve(Path(config["root"]), config)
    values = runtime.environment(directory, registry=Path(config["fingerprint_registry"]))
    # Respect enclosing panel admission and thread limits.  Work products and
    # validation caches still belong exclusively to this host operation.
    for name in values:
        if name in environment and (name.endswith(("_GATE", "_CAPACITY", "_QUEUE_TIMEOUT"))
                                    or name in {"LEAN_NUM_THREADS", "OMP_NUM_THREADS"}):
            values[name] = environment[name]
    values["LEAN_REFACTOR_EVALUATION_CACHE"] = str(runtime.validation_cache)
    # Unlike model passes, this operation's hard wall budget includes queues.
    values["LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE"] = "request"
    create_environment_directories(values, checkpoint=True)
    environment.update(values)
    return environment


def _worker_command(directory: Path) -> list[str]:
    return [sys.executable, "-m", "e6.deterministic", "worker",
            "--config", str(directory / "config.json"),
            "--seed", str(directory / "incumbent-before.json"), "--out", str(directory)]


def _launch_worker(config: dict, directory: Path, deadline: float) -> dict:
    with (directory / "worker.log").open("a", encoding="utf-8") as log:
        process = None
        result = {"returncode": None, "timed_out": False}
        try:
            with defer_termination():
                process = subprocess.Popen(_worker_command(directory),
                    cwd=Path(__file__).resolve().parents[1], env=_environment(config, directory),
                    stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
                    start_new_session=os.name != "nt")
                process_memory.capture_process_identity(process)
            try:
                result["returncode"] = process.wait(timeout=max(0.0, deadline - time.monotonic()))
            except subprocess.TimeoutExpired:
                result["timed_out"] = True
        finally:
            # This runs for SIGINT/SIGTERM translated by the controller as well
            # as deadlines and ordinary errors. Only the registered child and
            # its identity-pinned descendants belong to this operation.
            if process is not None and process.poll() is None:
                proof.arena.terminate_process_tree(process)
                try:
                    process.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait(timeout=2)
        result["returncode"] = process.returncode
        return result


def optimize(config: dict, capsule: Path, incumbent: dict) -> tuple[dict, dict]:
    """Optimize only the supplied verified source, with a hard host wall limit.

    Native pass health and selection files are never changed here.  Reports and
    checkpoints are idempotent for this frozen config, pass, and starting source.
    Infrastructure failures preserve the last completely verified checkpoint.
    """
    return _optimize(config, capsule, incumbent)


def optimize_dictionary(config: dict, capsule: Path, incumbent: dict) -> tuple[dict, dict]:
    """Run one fixed dictionary sweep after compact, in its own host allowance."""
    return _optimize(config, capsule, incumbent, fixed_stage=DICTIONARY_STAGE)


def _optimize(config: dict, capsule: Path, incumbent: dict, *, fixed_stage: str | None = None) -> tuple[dict, dict]:
    """Shared durable boundary and owned-worker lifecycle for fixed stages."""
    started = time.monotonic()
    best, directory = dict(incumbent), None
    report = {"schema_version": SCHEMA_VERSION, "status": "infrastructure_failure",
              "before": _summary(incumbent), "after": _summary(incumbent), "improved": False,
              "evaluated_candidates": 0, "accepted_candidates": 0, "rounds_completed": 0,
              "model_calls": 0, "cost_usd": 0, "errors": [], "wall_seconds": 0}
    owns_directory = False
    try:
        proof._verify_incumbent(config, incumbent)
        if fixed_stage not in {None, DICTIONARY_STAGE}:
            raise ValueError("Unknown deterministic optimizer stage")
        settings = dictionary_settings() if fixed_stage else _settings(config)
        if fixed_stage is None and not settings["deterministic_refactoring"]:
            report["status"] = "disabled"
            return best, _compact(report)
        root, capsule = Path(config["root"]).resolve(), Path(capsule).resolve()
        if capsule.parent != root or not re.fullmatch(r"pass-\d+", capsule.name):
            raise ValueError("Deterministic optimizer requires a pass capsule directly under its proof root")
        directory = root / ("deterministic-dictionary" if fixed_stage else "deterministic") / capsule.name
        config_sha = _json_digest(config)
        report.update(config_sha256=config_sha, pass_name=capsule.name, seed_sha256=incumbent["sha256"])
        request = {"schema_version": SCHEMA_VERSION, "config_sha256": config_sha,
                   "capsule": str(capsule), "seed_sha256": incumbent["sha256"],
                   "incumbent_sha256": _json_digest(incumbent), "settings": settings}
        if fixed_stage:
            request["fixed_stage"] = fixed_stage
            report.update(fixed_stage=fixed_stage, effective_budget_seconds=DICTIONARY_BUDGET_SECONDS)
        binding = _json_digest(request)
        report["binding_sha256"] = binding
        if (directory / "request.json").exists():
            saved = _read(directory / "request.json")
            saved_binding = _json_digest(saved)
            if saved != request:
                # A resumed caller may already hold the verified result of this
                # exact boundary.  It must not run a second search from that win.
                previous = _read(directory / "report.json")
                if (saved.get("config_sha256") != config_sha or saved.get("capsule") != str(capsule)
                        or saved.get("fixed_stage") != fixed_stage or saved.get("settings") != settings
                        or previous.get("binding_sha256") != saved_binding
                        or previous.get("after", {}).get("sha256") != incumbent["sha256"]):
                    raise ValueError("Deterministic boundary is already bound to another config or source")
            original = _read(directory / "incumbent-before.json")
            best = _checkpoint(config, directory, saved_binding, original)
            if (directory / "report.json").exists():
                report = _read(directory / "report.json")
                if report.get("binding_sha256") != saved_binding:
                    raise ValueError("Deterministic report binding changed")
            else:
                # Recover telemetry from the same frozen search as well as its
                # verified checkpoint. A host interruption must not turn real
                # search work into a zero-duration, zero-candidate receipt.
                progress_path = directory / "progress.json"
                if progress_path.exists():
                    progress = _read(progress_path)
                    if progress.get("binding_sha256") == saved_binding:
                        report = progress
                report.update(binding_sha256=saved_binding, status="interrupted",
                              termination_reason="host_interrupted", search_exhausted=False,
                              after=_summary(best), improved=best["score"] > original["score"])
                # An interrupted boundary is deliberately consumed rather than
                # silently granting another search allowance after a restart.
                proof._write(directory / "report.json", report)
            result = _compact(report, directory)
            result["reused"] = True
            return best, result
        if directory.exists():
            if directory.is_symlink() or any(path.name != "agent-selection.json" or path.is_symlink()
                                             for path in directory.iterdir()):
                raise ValueError("Unexpected artifacts in an unbound deterministic boundary")
            raw_selection = directory / "agent-selection.json"
            if raw_selection.exists():
                saved_selection = _read(raw_selection)
                proof._verify_incumbent(config, saved_selection)
                if saved_selection["sha256"] != incumbent["sha256"]:
                    raise ValueError("Saved agent selection differs from the deterministic incumbent")
        directory.mkdir(parents=True, exist_ok=True)
        owns_directory = True
        proof._write(directory / "request.json", request)
        proof._write(directory / "config.json", config)
        proof._write(directory / "incumbent-before.json", incumbent)
        _immutable_source(directory / "source-before.lean", incumbent["source"])
        best["selected_path"] = str(directory / "source-before.lean")
        selection = capsule / "selection.json"
        if selection.exists():
            raw = selection.read_bytes()
            (directory / "selection-before.json").write_bytes(raw)
            report["selection_before_sha256"] = hashlib.sha256(raw).hexdigest()
        proof._write(directory / "checkpoint.json", {"binding_sha256": binding, "best": best})
        report.update(status="running", candidate_timeout_seconds=CANDIDATE_TIMEOUT_SECONDS)
        proof._write(directory / "progress.json", report)
        allowance = DICTIONARY_BUDGET_SECONDS if fixed_stage else _budget(config, capsule.name)
        launch = _launch_worker(config, directory, started + allowance)
        if (directory / "progress.json").exists():
            progress = _read(directory / "progress.json")
            if progress.get("binding_sha256") == binding:
                report = progress
        best = _checkpoint(config, directory, binding, incumbent)
        committed = _read(directory / "checkpoint.json").get("report", {})
        if committed.get("accepted_candidates", 0) > report.get("accepted_candidates", 0):
            report = committed
        report["worker"] = launch
        if launch["timed_out"]:
            report["status"] = "timed_out"
            report.update(termination_reason="wall_deadline", search_exhausted=False)
            if settings.get("deterministic_policy") == "deep":
                report["frontier_telemetry_complete"] = False
            report["errors"].append({"phase": "worker", "type": "TimeoutError",
                "message": "Deterministic wall deadline expired, including queue time"})
        elif launch["returncode"] != 0:
            report["status"] = "infrastructure_failure"
            report.update(termination_reason="worker_failure", search_exhausted=False)
            if settings.get("deterministic_policy") == "deep":
                report["frontier_telemetry_complete"] = False
            report["errors"].append({"phase": "worker", "type": "WorkerExit",
                                     "message": f"Worker exited with status {launch['returncode']}"})
        elif report.get("status") == "running" or (report.get("status") == "infrastructure_failure" and not report.get("errors")):
            raise ValueError("Worker returned without a completed search receipt")
    except Exception as error:
        report["status"] = "infrastructure_failure"
        report["termination_reason"] = "host_failure"
        report.setdefault("errors", []).append(_error(error, phase="host"))
        # A broken report must never make an unverified checkpoint a fallback.
        best = dict(incumbent)
        if owns_directory:
            try:
                best = _checkpoint(config, directory, report["binding_sha256"], incumbent)
            except Exception:
                pass
    report.update(after=_summary(best), improved=_improved(best, incumbent),
                  wall_seconds=round(time.monotonic() - started, 6))
    report.update(_health(report))
    if owns_directory:
        try:
            proof._write(directory / "report.json", report)
        except OSError as error:
            report["errors"].append(_error(error, phase="report"))
            report.update(_health(report))
    return best, _compact(report, directory)


def _generators(config: dict, source: str, signature: str, directory: Path,
                deadline: float, maximum: int, records: list) -> list[dict]:
    from . import deterministic_candidates, deterministic_native
    collections = []
    search_policy = getattr(experiment_spec(config), "deterministic_policy", "legacy")
    deep = search_policy == "deep"
    compact = search_policy == "compact"
    native_policy = "prioritized" if compact else search_policy
    generation_started = time.monotonic()
    generators = (("pure", "native", "compiler_simp") if deep else
                  ("pure", "native", "semantic_compact") if compact else ("pure", "native"))
    for name in generators:
        started = time.monotonic()
        record = {"generator": name, "parent_sha256": proof._digest(source), "model_calls": 0}
        try:
            if started >= deadline:
                raise TimeoutError("Deterministic generation deadline expired")
            generation_remaining = deadline - started
            if compact and name != "pure":
                generation_remaining -= COMPACT_VALIDATION_RESERVE_SECONDS
                record["validation_reserve_seconds"] = COMPACT_VALIDATION_RESERVE_SECONDS
                if generation_remaining <= 0:
                    record.update(status="skipped", incomplete=True, count=0,
                                  skip_reason="validation_reserve", wall_seconds=0,
                                  generation_started_offset_seconds=round(started - generation_started, 6),
                                  generation_finished_offset_seconds=round(time.monotonic() - generation_started, 6))
                    collections.append([])
                    records.append(record)
                    continue
            if name == "pure":
                values = deterministic_candidates.generate(source, signature, max_candidates=min(256, maximum),
                    **({"deep": True} if deep else {}))
            elif name == "native":
                values = deterministic_native.generate(config, source, directory,
                    timeout_seconds=min(90, generation_remaining), max_candidates=min(128, maximum),
                    **({"policy": native_policy, "policy_maximum": maximum} if search_policy != "legacy" else {}))
            elif name == "semantic_compact":
                from .deterministic_support import semantic_compact
                # Override research-only discovery knobs on a private copy; the
                # frozen production policy always reproduces the narrow arm.
                discovery_config = {**config, "optimizer_v5_generator": dict(COMPACT_DISCOVERY_SETTINGS),
                    **{"semantic_search_" + key: value for key, value in COMPACT_DISCOVERY_SETTINGS.items()},
                    "semantic_search_solvers": None}
                values = semantic_compact.generate_candidates(config=discovery_config, source=source,
                    signature=signature, workdir=directory / "semantic-compact",
                    timeout_seconds=min(COMPACT_DISCOVERY_SETTINGS["discovery_timeout_seconds"], generation_remaining),
                    max_candidates=min(COMPACT_DISCOVERY_SETTINGS["max_candidates"], maximum),
                    family="semantic_solvers")
            else:
                from .deterministic_support import compiler_simp
                values = compiler_simp.generate(config, source, directory / "compiler-simp",
                    timeout_seconds=min(90, deadline - started), max_candidates=min(32, maximum))
            if not isinstance(values, list):
                raise TypeError("Deterministic generator must return a list of source candidates")
            # Compact expansion has at most 3x64 rows. Keep the expanded,
            # shortest-first inventory until deduplication and scheduling.
            collections.append(values if compact else values[:maximum])
            record.update(status="generated", count=len(collections[-1]))
        except Exception as error:
            collections.append([])
            kind = _failure_kind(error, deadline)
            record.update(status="failed", error=_error(error, phase="generation"), count=0,
                          failure_kind=kind if kind in {"budget", "resource_limit"} else "infrastructure")
        record["wall_seconds"] = round(time.monotonic() - started, 6)
        record["generation_started_offset_seconds"] = round(started - generation_started, 6)
        record["generation_finished_offset_seconds"] = round(time.monotonic() - generation_started, 6)
        records.append(record)
    values = [candidate for pair in zip_longest(*collections) for candidate in pair if candidate is not None]
    from .deterministic_support.search_policy import order_candidates
    return order_candidates(values, policy=search_policy, maximum=maximum)


class _GeneratorInvalid(ValueError):
    """A proposal failed source intake before any compiler request."""


class _CandidateResourceLimit(proof._ValidationInfrastructureError):
    """The validator reached a cap without establishing proof invalidity."""


def _preflight(config: dict, row: dict, source: str) -> str:
    try:
        declaration, _ = proof.arena.extract_candidate_declaration(row, source)
        if len(declaration) > experiment_spec(config).candidate_intake_characters:
            raise ValueError("Deterministic candidate exceeds the contest declaration intake limit")
    except (ValueError, proof.arena.WorkflowError) as error:
        raise _GeneratorInvalid(str(error)) from error
    return declaration


def _validate(config: dict, row: dict, source: str, candidate: Path,
              incumbent: dict, deadline: float, record: dict, *, minimum_score: float | None = None) -> dict | None:
    spec, policy = experiment_spec(config), proof._policy(config)
    if spec.deterministic_policy == "compact":
        from lean_tools import lean_source
        from lean_tools.measurement_policy import scoring_policy_context
        with scoring_policy_context(policy.scoring_policy):
            # Enforce exact statement, frozen environment, forbidden source and
            # intake guards before deriving any source-only score bound.
            declaration = _preflight(config, row, source)
            _, body = lean_source.extract_candidate_declaration(row, source)
            source_tokens = lean_source.candidate_proof_token_count(body, policy=policy.scoring_policy)
        upper = policy.optimistic_score(tokens=source_tokens)
        record.update(declaration_sha256=proof._digest(declaration),
            source_tokens=source_tokens, token_measurement_mode="exact_source_lexer",
            score_upper_bound=upper, score_bound={"source_sha256": proof._digest(source),
                "declaration_sha256": proof._digest(declaration), "scoring_policy": policy.scoring_policy,
                "tokens": source_tokens, "assumed_heartbeats": 0, "assumed_compatibility_pct": 100,
                "optimistic_score": upper, "incumbent_score": incumbent["score"],
                "selection_policy": "strict_score_gain"})
        if (upper <= incumbent["score"] if minimum_score is None else upper < minimum_score):
            record.update(status="score_bound_pruned", valid=None, validity="unknown",
                          native_validation_started=False,
                          pruning_reason="rounded_score_upper_bound_cannot_strictly_improve")
            return None
        record["native_validation_started"] = True
    else:
        declaration = _preflight(config, row, source)
    record["declaration_sha256"] = proof._digest(declaration)
    candidate.write_text(source, encoding="utf-8", newline="")

    def check(project: str, *, quick: bool) -> dict:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise TimeoutError("Deterministic validation deadline expired")
        result = proof._check(config, candidate, Path(project), quick=quick,
                              timeout_seconds=min(CANDIDATE_TIMEOUT_SECONDS, spec.check_timeout_seconds, remaining))
        def cancelled(value):
            if isinstance(value, dict):
                return (value.get("cancelled") is True or value.get("canceled") is True
                    or value.get("status") in {"cancelled", "canceled", "interrupted"}
                    or value.get("error_kind") in {"cancelled", "canceled", "interrupted"}
                    or value.get("type") in {"CancelledError", "CanceledError", "KeyboardInterrupt"}
                    or value.get("error_type") in {"CancelledError", "CanceledError", "KeyboardInterrupt"}
                    or any(cancelled(item) for item in value.values()))
            return isinstance(value, list) and any(cancelled(item) for item in value)
        if isinstance(result, dict) and result.get("valid") is not True and _resource_limit(result):
            raise _CandidateResourceLimit("Deterministic validation reached a resource limit")
        if proof._validation_infrastructure_failure(result) or cancelled(result):
            raise proof._ValidationInfrastructureError("Deterministic validation returned an infrastructure failure")
        return result

    primary = check(config["primary"], quick=False)
    record["evaluation"] = primary
    if primary.get("valid") is not True:
        record.update(valid=False, status="primary_invalid")
        return None
    if (primary.get("measurement_mode") != "exact" or primary.get("axiom_status") != "measured"
            or not isinstance(primary.get("axioms"), list)
            or any(axiom not in proof.arena.ALLOWED_AXIOMS for axiom in primary["axioms"])):
        raise proof._ValidationInfrastructureError("Deterministic candidate lacks an exact measured axiom audit")
    tokens, heartbeats = primary["length"]["candidate_tokens"], primary["heartbeat"]["candidate"]
    if type(tokens) is not int or tokens < 0 or type(heartbeats) is not int or heartbeats < 0:
        raise proof._ValidationInfrastructureError("Deterministic candidate lacks exact token or heartbeat measurements")
    reference, control = primary["heartbeat"]["local_reference"], proof._original_control_heartbeats(config)
    if spec.scoring_policy == "arena-v1" or reference != control:
        if spec.scoring_policy != "arena-v1" and reference is not None:
            raise proof._ValidationInfrastructureError("Deterministic native-control reference does not match")
        try:
            record["native_control_evidence"] = proof._native_control_evidence(config, row, primary)
        except ValueError as error:
            raise proof._ValidationInfrastructureError(str(error)) from error
    optimistic = policy.score(tokens=tokens, heartbeats=heartbeats, compatibility_pct=100)
    record.update(tokens=tokens, heartbeats=heartbeats, optimistic_score=optimistic)
    if (optimistic <= incumbent["score"] if minimum_score is None else optimistic < minimum_score):
        record.update(valid=True, status="no_improvement")
        return None
    compatibility = [{"environment": config["primary"], "passed": True, "evaluation": primary}]
    record["compatibility"] = compatibility
    for project in config["compatibility"]:
        evaluation = check(project, quick=True)
        compatibility.append({"environment": project, "passed": evaluation.get("valid") is True,
                              "evaluation": evaluation})
    if not all(item["passed"] for item in compatibility):
        record.update(valid=True, status="compatibility_failed", compatibility_complete=True,
                      compatibility_pct=100 * sum(item["passed"] for item in compatibility) / len(compatibility))
        return None
    record.update(valid=True, status="accepted" if optimistic > incumbent["score"] else "frontier_validated", score=optimistic,
                  compatibility_complete=True, compatibility_pct=100)
    return {**proof._incumbent_metadata(config), **record, "source": source,
            "sha256": proof._digest(source)}


def _search_cache(config: dict, row: dict, settings: dict, incumbent: dict):
    from .deterministic_support.search_cache import SearchCache, tool_identity
    root = Path(config["root"]).resolve()

    def portable(value, field=None):
        if isinstance(value, dict):
            return {key: portable(item, key) for key, item in value.items() if key != "selected_path"}
        if isinstance(value, list):
            return [portable(item, field) for item in value]
        if (field not in {"primary", "compatibility", "canonical_task", "registry_source", "elan_home"}
                and isinstance(value, str) and (value == str(root) or value.startswith(str(root) + os.sep))):
            return "$PROOF_ROOT" + value[len(str(root)):]
        return value

    # The explicit guarded fingerprints are read-only; this never invokes Lean
    # or repairs/rebuilds an environment. A changed guard disables cache use.
    environments = [proof.arena.measurement_environment_fingerprint(row, Path(project),
        registry_path=Path(config["fingerprint_registry"]))
        for project in [config["primary"], *config["compatibility"]]]
    # A migration receipt authenticates a lifecycle transition, not a changed
    # generator or evaluator. Its per-invocation digest contains artifact paths
    # and timestamps; _verify_config has already verified it independently.
    semantic_config = {key: value for key, value in config.items() if key != "source_migration"}
    binding = {"config": portable(semantic_config), "environments": environments,
               "task_sha256": proof.arena.sha256_file(Path(config["task"])),
               "tools_sha256": tool_identity(Path(__file__).resolve().parents[1]),
               "candidate_timeout_seconds": CANDIDATE_TIMEOUT_SECONDS}
    return SearchCache(Path(os.environ.get("E6_DETERMINISTIC_CACHE_ROOT", root / "deterministic/search-cache")),
        binding, {"seed": {key: value for key, value in _summary(incumbent).items() if key != "selected_path"},
                  "settings": {key: value for key, value in settings.items()
                  if key not in {"deterministic_budget_seconds", "deterministic_late_budget_seconds"}}})


def _restore_search(config: dict, incumbent: dict, state: dict) -> tuple[dict, dict, dict, set]:
    """Restore traversal only after independently checking its old checkpoint."""
    if not isinstance(state, dict) or not state:
        raise ValueError("No cached search state")
    old = Path(state["checkpoint_directory"])
    if old.parent.name != "deterministic" or not re.fullmatch(r"pass-\d+", old.name):
        raise ValueError("Cached checkpoint is outside a deterministic boundary")
    old_request = _read(old / "request.json")
    if (old_request.get("seed_sha256") != incumbent["sha256"]
            or _json_digest(old_request) != state.get("checkpoint_binding_sha256")):
        raise ValueError("Cached search checkpoint request changed")
    original = _read(old / "incumbent-before.json")
    proof._verify_incumbent(config, original)
    if original["sha256"] != incumbent["sha256"] or original["score"] != incumbent["score"]:
        raise ValueError("Cached search has another verified seed")
    best = _checkpoint(config, old, state["checkpoint_binding_sha256"], original)
    if best["sha256"] != state.get("best_sha256"):
        raise ValueError("Cached search checkpoint changed after the traversal snapshot")
    inventories, offsets = state.get("inventories"), state.get("offsets")
    completed = state.get("completed_sources")
    if (not isinstance(inventories, dict) or not isinstance(offsets, dict)
            or not isinstance(completed, list)
            or len(inventories) > (4097 if "deep_parent_binding_sha256" in state else 128)
            or len(completed) > 8192
            or set(inventories) != set(offsets)
            or any(not isinstance(sha, str) or not re.fullmatch(r"[a-f0-9]{64}", sha) for sha in completed)):
        raise ValueError("Malformed cached traversal")
    for sha, inventory in inventories.items():
        if (not isinstance(inventory, list) or len(inventory) > 8192
                or type(offsets[sha]) is not int or not 0 <= offsets[sha] <= len(inventory)
                or any(not isinstance(item, dict) or not isinstance(item.get("source"), str) for item in inventory)):
            raise ValueError("Malformed cached candidate inventory")
        if any(proof._digest(item["source"]) not in completed for item in inventory[:offsets[sha]]):
            raise ValueError("Cached traversal skips a source without a completed verdict")
        for item in inventory:
            item["proposal_from_cache"] = True
            item["proposal_ready_seconds"] = 0.0
    if state.get("exhausted") is True and (best["sha256"] not in inventories
            or any(offsets[sha] < len(values) for sha, values in inventories.items())):
        raise ValueError("Cached exhausted search still has unseen candidates")
    return best, inventories, offsets, set(completed)


def _verify_frontier_parent(config: dict, value: dict, directory: Path, seed: dict) -> None:
    """Check immutable, exact, all-version evidence before reusing a beam parent."""
    proof._verify_incumbent(config, value)
    selected = Path(value["selected_path"])
    if (selected.parent not in {directory, directory / "validated"}
            or proof._source(selected) != value["source"]):
        raise ValueError("Deep frontier parent lacks immutable source")
    if value["sha256"] == seed["sha256"]:
        if value["source"] != seed["source"] or value["score"] != seed["score"]:
            raise ValueError("Deep frontier seed changed")
        return
    checks = value.get("compatibility")
    projects = [config["primary"], *config["compatibility"]]
    if (not isinstance(checks, list) or len(checks) != len(projects)
            or value.get("compatibility_pct") != 100
            or any(not isinstance(check, dict) or check.get("environment") != project
                   or check.get("passed") is not True or not isinstance(check.get("evaluation"), dict)
                   or check["evaluation"].get("valid") is not True
                   or check["evaluation"].get("source_sha256") not in {None, value["sha256"]}
                   for check, project in zip(checks, projects))):
        raise ValueError("Deep frontier parent lacks complete compatibility evidence")
    primary = checks[0]["evaluation"]
    if (primary.get("measurement_mode") != "exact" or primary.get("axiom_status") != "measured"
            or not isinstance(primary.get("axioms"), list)
            or any(axiom not in proof.arena.ALLOWED_AXIOMS for axiom in primary["axioms"])
            or primary.get("length", {}).get("candidate_tokens") != value.get("tokens")
            or primary.get("heartbeat", {}).get("candidate") != value.get("heartbeats")):
        raise ValueError("Deep frontier parent lacks exact measured axiom audit")


def _deep_search(config: dict, incumbent: dict, directory: Path, request: dict, *,
                 started: float, deadline: float, best: dict, report: dict, settings: dict) -> None:
    """Anytime finite frontier; rounds are telemetry, never a deep-search cutoff.

    Each admitted source is generated at most once per invocation. Every proposal
    advances an inventory offset, and every new validation spends the global
    candidate allowance. Resource failures remain retryable at a later boundary;
    they are never retried in place. Beam parents carry full verification evidence
    in the atomic checkpoint, while only a strict improvement can become ``best``.
    """
    from collections import deque
    from .deterministic_support.search_cache import compile_rejection

    binding = _json_digest(request)
    maximum = settings["deterministic_max_candidates"]
    width = settings.get("deterministic_beam_width", 1)
    score_drop = settings.get("deterministic_beam_score_drop", 0.1)
    generation_limit = maximum + 1
    seed_sha = incumbent["sha256"]
    parents, strict_parents = {best["sha256"]: best}, {best["sha256"]}
    alternatives, inventories, offsets = [], {}, {}
    completed, seen = {seed_sha}, {seed_sha}
    retry_offsets, incomplete, generated = {}, set(), set()
    queue = deque([best["sha256"]])
    cache = None
    fallback_best = best
    missing_item = object()
    report.update(status="running", candidate_records=[], generator_records=[], errors=[],
                  evaluated_candidates=0, accepted_candidates=0, rounds_completed=0,
                  negative_cache_hits=0, search_reused=False, search_resumed=False,
                  search_exhausted=False, effective_budget_seconds=_budget(config, directory.name),
                  timing_clock="worker_monotonic_elapsed_seconds", termination_reason=None,
                  frontier_admissions=0, frontier_pruned=0, generation_limit=generation_limit,
                  frontier_telemetry_complete=False)

    def elapsed():
        return round(time.monotonic() - started, 6)

    def cache_error(error):
        report["cache_error_count"] = report.get("cache_error_count", 0) + 1
        report.setdefault("cache_errors", []).append(_error(error, phase="cache"))
        report["cache_errors"] = report["cache_errors"][-8:]

    def commit(*, promoted=False):
        # A traversal snapshot alone never authenticates an internal parent.
        # Its matching atomic checkpoint owns every immutable source and audit.
        proof._write(directory / "checkpoint.json", {"binding_sha256": binding, "best": best,
            "deep_parents": parents, "deep_strict_parents": sorted(strict_parents),
            "deep_parent_binding_sha256": _json_digest(parents),
            "report": {**report, "after": _summary(best), "improved": best["score"] > incumbent["score"],
                       "accepted_candidates": report["accepted_candidates"] + int(promoted)}})

    def has_work(sha):
        return sha not in generated or offsets.get(sha, 0) < len(inventories.get(sha, []))

    def enqueue(sha, *, first=False):
        if sha in parents and has_work(sha):
            try:
                queue.remove(sha)
            except ValueError:
                pass
            (queue.appendleft if first else queue.append)(sha)

    def telemetry():
        pending = set()
        for sha, values in inventories.items():
            for item in values[offsets[sha]:]:
                if isinstance(item, dict) and isinstance(item.get("source"), str):
                    digest = proof._digest(item["source"])
                    if digest not in completed:
                        pending.add(digest)
        retryable = {proof._digest(item["source"])
            for sha, values in inventories.items() for item in values[:offsets[sha]]
            if isinstance(item, dict) and isinstance(item.get("source"), str)
            and proof._digest(item["source"]) not in completed}
        report.update(pending_candidates=len(pending),
            pending_parents=sum(has_work(sha) or sha in incomplete or sha in retry_offsets for sha in parents),
            retryable_candidates=len(retryable), incomplete_generations=len(incomplete),
            frontier_alternatives=len(alternatives), generated_parents=report["rounds_completed"],
            retained_parent_inventories=len(inventories))

    def save():
        telemetry()
        report.update(after=_summary(best), improved=best["score"] > incumbent["score"], wall_seconds=elapsed())
        if cache is not None:
            try:
                reusable = {sha: values for sha, values in inventories.items() if sha not in incomplete}
                state = {"checkpoint_directory": str(directory), "checkpoint_binding_sha256": binding,
                    "best_sha256": best["sha256"], "deep_parent_binding_sha256": _json_digest(parents),
                    "inventories": reusable,
                    "offsets": {sha: min(offsets[sha], retry_offsets.get(sha, offsets[sha])) for sha in reusable},
                    "completed_sources": sorted(completed), "exhausted": report["search_exhausted"],
                    "deep_alternatives": alternatives, "deep_queue": list(queue)}
                if not cache.save_search(state):
                    report["cache_snapshot_skipped"] = "size_limit"
            except (OSError, ValueError, TypeError) as error:
                cache_error(error)
        report.update(_health(report))
        proof._write(directory / "progress.json", report)

    def prune_frontier():
        nonlocal alternatives
        ordered = sorted(alternatives, key=lambda sha: -parents[sha]["score"])
        keep = [sha for sha in ordered if parents[sha]["score"] >= best["score"] - score_drop][:width - 1]
        for sha in alternatives:
            if sha not in keep:
                report["frontier_pruned"] += 1
                parents.pop(sha, None)
                inventories.pop(sha, None)
                offsets.pop(sha, None)
                retry_offsets.pop(sha, None)
                incomplete.discard(sha)
                try:
                    queue.remove(sha)
                except ValueError:
                    pass
        alternatives = keep

    try:
        proof._verify_config(config)
        proof._verify_incumbent(config, incumbent)
        _, row = proof.arena.load_task(Path(config["task"]))
        (directory / "candidates").mkdir(exist_ok=True)
        (directory / "validated").mkdir(exist_ok=True)
        if settings.get("deterministic_cache", False):
            try:
                cache = _search_cache(config, row, settings, incumbent)
                report.update(cache_binding_sha256=cache.binding, cache_search_binding_sha256=cache.search_binding)
                state = cache.load_search()
                if state:
                    restored, old_inventories, old_offsets, old_completed = _restore_search(config, incumbent, state)
                    old = Path(state["checkpoint_directory"])
                    checkpoint = _read(old / "checkpoint.json")
                    old_parents = checkpoint.get("deep_parents")
                    old_strict = checkpoint.get("deep_strict_parents")
                    old_alternatives = state.get("deep_alternatives")
                    old_queue = state.get("deep_queue")
                    if (not isinstance(old_parents, dict) or not 1 <= len(old_parents) <= 4097
                            or _json_digest(old_parents) != state.get("deep_parent_binding_sha256")
                            or checkpoint.get("deep_parent_binding_sha256") != state.get("deep_parent_binding_sha256")
                            or not isinstance(old_strict, list) or not isinstance(old_alternatives, list)
                            or len(old_alternatives) >= width or not isinstance(old_queue, list)
                            or len(old_queue) > 4097 or len(old_queue) != len(set(old_queue))
                            or set(old_parents) != set(old_strict) | set(old_alternatives)
                            or set(old_strict) & set(old_alternatives)
                            or restored["sha256"] not in old_strict
                            or not set(old_inventories) <= set(old_parents)
                            or not set(old_queue) <= set(old_parents)):
                        raise ValueError("Malformed cached deep frontier")
                    copied = {}
                    for sha, value in old_parents.items():
                        if not isinstance(value, dict) or value.get("sha256") != sha:
                            raise ValueError("Cached deep parent source binding changed")
                        _verify_frontier_parent(config, value, old, incumbent)
                        if sha in old_alternatives and not restored["score"] - score_drop <= value["score"] <= restored["score"]:
                            raise ValueError("Cached deep alternative is outside the beam score bound")
                        selected = directory / "validated" / f"{sha}.lean"
                        _immutable_source(selected, value["source"])
                        copied[sha] = {**value, "selected_path": str(selected)}
                    parents, strict_parents = copied, set(old_strict)
                    best = parents[restored["sha256"]]
                    alternatives, inventories, offsets = old_alternatives, old_inventories, old_offsets
                    completed, seen = old_completed, set(old_completed)
                    generated = set(inventories)
                    queue = deque(old_queue)
                    # Failure or in-flight snapshots may not have enqueued their
                    # retry yet. Reconstruct missing eligible work explicitly.
                    for sha in parents:
                        if has_work(sha) and sha not in queue:
                            queue.append(sha)
                    if state.get("exhausted") is True and any(has_work(sha) for sha in parents):
                        raise ValueError("Cached exhausted deep frontier still has work")
                    commit()
                    report.update(search_resumed=state.get("exhausted") is not True,
                                  search_reused=state.get("exhausted") is True)
                    if state.get("exhausted") is True:
                        report.update(status="completed", search_exhausted=True,
                                      termination_reason="frontier_exhausted")
                        return
            except (OSError, ValueError, TypeError, KeyError) as error:
                cache_error(error)
                # A corrupt traversal must not install a winner or parent.
                best = fallback_best
                report.update(search_resumed=False, search_reused=False, search_exhausted=False)
                parents, strict_parents = {best["sha256"]: best}, {best["sha256"]}
                alternatives, inventories, offsets = [], {}, {}
                completed, seen, generated = {seed_sha}, {seed_sha}, set()
                queue = deque([best["sha256"]])
        commit()
        while queue:
            if time.monotonic() >= deadline:
                report["termination_reason"] = "wall_deadline"
                break
            if report["evaluated_candidates"] >= maximum:
                report["termination_reason"] = "candidate_limit"
                break
            parent_sha = queue.popleft()
            if parent_sha not in parents:
                continue
            if parent_sha not in generated:
                if report["rounds_completed"] >= generation_limit:
                    report["termination_reason"] = "generation_limit"
                    enqueue(parent_sha, first=True)
                    break
                generated.add(parent_sha)
                generation_started = elapsed()
                old_record_count = len(report["generator_records"])
                try:
                    inventories[parent_sha] = _generators(config, parents[parent_sha]["source"], row["signature"],
                        directory / f"native-deep-{report['rounds_completed'] + 1:04d}", deadline, maximum,
                        report["generator_records"])
                except Exception:
                    incomplete.add(parent_sha)
                    raise
                generation_finished = elapsed()
                for record in report["generator_records"][old_record_count:]:
                    record.update(generation_started_seconds=round(generation_started +
                        record.pop("generation_started_offset_seconds", 0), 6),
                        generation_finished_seconds=round(generation_started +
                        record.pop("generation_finished_offset_seconds", generation_finished - generation_started), 6))
                    if record.get("status") == "failed" or record.get("incomplete") is True:
                        incomplete.add(parent_sha)
                for item in inventories[parent_sha]:
                    if isinstance(item, dict):
                        item["proposal_ready_seconds"] = generation_finished
                offsets[parent_sha] = 0
                report["rounds_completed"] += 1
                save()
            inventory = inventories[parent_sha]
            # Duplicate proposals advance without spending validation allowance.
            item = missing_item
            while offsets[parent_sha] < len(inventory):
                item_index = offsets[parent_sha]
                proposal = inventory[item_index]
                offsets[parent_sha] += 1
                if not (isinstance(proposal, dict) and isinstance(proposal.get("source"), str)
                        and proof._digest(proposal["source"]) in seen):
                    item = proposal
                    break
            if item is missing_item:
                save()
                continue
            if time.monotonic() >= deadline:
                # Generation and duplicate scanning share the host wall cap.
                # Leave this proposal completely unconsumed for continuation.
                offsets[parent_sha] = item_index
                enqueue(parent_sha, first=True)
                report["termination_reason"] = "wall_deadline"
                break
            enqueue(parent_sha)
            record = {"round": report["rounds_completed"], "parent_sha256": parent_sha,
                      "model_calls": 0, "cost_usd": 0, "incumbent_before": _summary(best)}
            before, sha, terminal = time.monotonic(), None, False
            report["candidate_records"].append(record)
            report["evaluated_candidates"] += 1
            try:
                if not isinstance(item, dict) or not isinstance(item.get("source"), str):
                    raise _GeneratorInvalid("Generated candidate lacks source text")
                source, sha = item["source"], proof._digest(item["source"])
                seen.add(sha)
                record.update(id=str(item.get("id", "")), family=str(item.get("family", "")), sha256=sha,
                    proposal_ready_seconds=item.get("proposal_ready_seconds", elapsed()),
                    proposal_from_cache=item.get("proposal_from_cache", False))
                candidate = directory / "candidates" / f"{sha}.lean"
                record["origin"] = str(candidate)
                retry_offsets[parent_sha] = min(item_index, retry_offsets.get(parent_sha, item_index))
                save()
                record["declaration_sha256"] = proof._digest(_preflight(config, row, source))
                negative = None
                if cache is not None:
                    try:
                        negative = cache.negative(sha)
                    except (OSError, ValueError, TypeError) as error:
                        cache_error(error)
                if negative is not None:
                    record.update(valid=False, status="negative_cache_hit", error_kind="candidate_invalid",
                                  cached_compile_rejection=negative)
                    report["negative_cache_hits"] += 1
                    terminal = True
                    continue
                record["validation_started_seconds"] = elapsed()
                result = _validate(config, row, source, candidate, best, deadline, record,
                    **({"minimum_score": best["score"] - score_drop} if width > 1 else {}))
                record["validation_finished_seconds"] = elapsed()
                terminal = True
                if result is not None:
                    selected = directory / "validated" / f"{sha}.lean"
                    _immutable_source(selected, source)
                    result["selected_path"] = record["selected_path"] = str(selected)
                    proof._verify_incumbent(config, result)
                    _verify_frontier_parent(config, result, directory, incumbent)
                    promoted = result["score"] > best["score"]
                    old_best, old_parents = best, dict(parents)
                    old_strict, old_alternatives = set(strict_parents), list(alternatives)
                    old_inventories, old_offsets = dict(inventories), dict(offsets)
                    old_retry, old_incomplete, old_queue = dict(retry_offsets), set(incomplete), deque(queue)
                    try:
                        parents[sha] = result
                        if promoted:
                            best = result
                            strict_parents.add(sha)
                            if sha in alternatives:
                                alternatives.remove(sha)
                            record["accepted_seconds"] = elapsed()
                            result.update(accepted_seconds=record["accepted_seconds"],
                                          validation_finished_seconds=record["validation_finished_seconds"])
                        else:
                            alternatives.append(sha)
                        prune_frontier()
                        admitted = sha in parents
                        if admitted:
                            commit(promoted=promoted)
                    except Exception:
                        best, parents, strict_parents, alternatives = old_best, old_parents, old_strict, old_alternatives
                        inventories, offsets = old_inventories, old_offsets
                        retry_offsets, incomplete, queue = old_retry, old_incomplete, old_queue
                        raise
                    if promoted:
                        record["checkpoint_committed_seconds"] = elapsed()
                        report["accepted_candidates"] += 1
                    elif admitted:
                        record["status"] = "frontier_admitted"
                        report["frontier_admissions"] += 1
                    else:
                        record["status"] = "frontier_discarded"
                    if admitted:
                        enqueue(sha, first=True)
            except Exception as error:
                terminal = False
                if "validation_started_seconds" in record:
                    record["validation_finished_seconds"] = elapsed()
                generator_invalid = isinstance(error, _GeneratorInvalid)
                rejection = compile_rejection(error, proof.arena.LeanCompileError)
                record.update(valid=False, status="generator_invalid" if generator_invalid else "validation_failed",
                    error=_error(error, phase="intake" if generator_invalid else "candidate"),
                    failure_kind=_failure_kind(error, deadline),
                    error_kind="generator_invalid" if generator_invalid else
                    "infrastructure" if proof._validation_exception_is_infrastructure(error)
                    or isinstance(error, proof.arena.LeanCompileError) and rejection is None else "candidate_invalid")
                terminal = generator_invalid or rejection is not None
                if rejection is not None and cache is not None and sha is not None:
                    try:
                        cache.remember_invalid(sha, rejection)
                        record["negative_cache_stored"] = True
                    except (OSError, ValueError, TypeError) as error:
                        cache_error(error)
            finally:
                if terminal and sha is not None:
                    completed.add(sha)
                    if retry_offsets.get(parent_sha) == item_index:
                        retry_offsets.pop(parent_sha, None)
                record["wall_seconds"] = round(time.monotonic() - before, 6)
                record["incumbent_after"] = _summary(best)
                save()
        telemetry()
        exhausted = not any(has_work(sha) for sha in parents) and not incomplete and not retry_offsets
        report["search_exhausted"] = exhausted
        if time.monotonic() >= deadline:
            report.update(termination_reason="wall_deadline", search_exhausted=False)
        elif report["termination_reason"] is None:
            report["termination_reason"] = ("frontier_exhausted" if exhausted else "generation_failure"
                if incomplete else "retryable_validation_failure")
        report["status"] = "timed_out" if report["termination_reason"] == "wall_deadline" else "completed"
    except Exception as error:
        report.update(status="timed_out" if isinstance(error, TimeoutError) else "infrastructure_failure",
                      termination_reason="wall_deadline" if isinstance(error, TimeoutError) else "infrastructure_failure",
                      search_exhausted=False)
        report["errors"].append(_error(error, phase="search"))
    finally:
        report["frontier_telemetry_complete"] = True
        save()


def _search(config: dict, incumbent: dict, directory: Path, request: dict) -> None:
    """Worker implementation, also directly exercised by isolated unit tests."""
    started = time.monotonic()
    settings = _settings(config)
    binding = _json_digest(request)
    report = _read(directory / "progress.json")
    if (request.get("config_sha256") != _json_digest(config)
            or request.get("seed_sha256") != incumbent.get("sha256")
            or request.get("incumbent_sha256") != _json_digest(incumbent)
            or request.get("settings") != settings or report.get("binding_sha256") != binding):
        raise ValueError("Deterministic worker input binding changed")
    # The parent enforces the original wall deadline. This local deadline keeps
    # individual validators bounded even when invoked without the parent.
    effective_budget = _budget(config, directory.name)
    deadline = started + effective_budget
    best = _checkpoint(config, directory, binding, incumbent)
    if settings.get("deterministic_policy") == "deep":
        _deep_search(config, incumbent, directory, request, started=started, deadline=deadline,
                     best=best, report=report, settings=settings)
        return
    report.update(status="running", candidate_records=[], generator_records=[], errors=[],
                  evaluated_candidates=0, accepted_candidates=0, rounds_completed=0,
                  negative_cache_hits=0, search_reused=False, search_resumed=False,
                  search_exhausted=False, effective_budget_seconds=effective_budget,
                  timing_clock="worker_monotonic_elapsed_seconds", termination_reason=None)
    seen, completed, inventories, offsets = {incumbent["sha256"]}, {incumbent["sha256"]}, {}, {}
    cache, retry_offsets, incomplete_inventories = None, {}, set()

    def elapsed():
        return round(time.monotonic() - started, 6)

    def cache_error(error):
        report["cache_error_count"] = report.get("cache_error_count", 0) + 1
        report.setdefault("cache_errors", []).append(_error(error, phase="cache"))
        report["cache_errors"] = report["cache_errors"][-8:]

    def save():
        report.update(after=_summary(best), improved=best["score"] > incumbent["score"],
                      wall_seconds=elapsed())
        if settings.get("deterministic_policy") == "compact":
            report["incomplete_generations"] = len(incomplete_inventories)
        if cache is not None:
            try:
                # An in-flight/failed check is deliberately left unseen for the
                # next boundary. Never turn a killed admission into a verdict.
                reusable = {sha: values for sha, values in inventories.items() if sha not in incomplete_inventories}
                saved = cache.save_search({"checkpoint_directory": str(directory),
                    "checkpoint_binding_sha256": binding, "best_sha256": best["sha256"],
                    "inventories": reusable,
                    "offsets": {sha: min(offsets[sha], retry_offsets.get(sha, offsets[sha])) for sha in reusable},
                    "completed_sources": sorted(completed), "exhausted": report["search_exhausted"]})
                if not saved:
                    report["cache_snapshot_skipped"] = "size_limit"
            except (OSError, ValueError, TypeError) as error:
                cache_error(error)
        report.update(_health(report))
        proof._write(directory / "progress.json", report)

    try:
        proof._verify_config(config)
        proof._verify_incumbent(config, incumbent)
        _, row = proof.arena.load_task(Path(config["task"]))
        signature = row["signature"]
        (directory / "candidates").mkdir(exist_ok=True)
        (directory / "validated").mkdir(exist_ok=True)
        if settings.get("deterministic_cache", False):
            try:
                cache = _search_cache(config, row, settings, incumbent)
                report.update(cache_binding_sha256=cache.binding, cache_search_binding_sha256=cache.search_binding)
                state = cache.load_search()
                if state:
                    restored, inventories, offsets, completed = _restore_search(config, incumbent, state)
                    seen = set(completed)
                    if restored["sha256"] != best["sha256"]:
                        selected = directory / "validated" / f"{restored['sha256']}.lean"
                        _immutable_source(selected, restored["source"])
                        restored = {**restored, "selected_path": str(selected)}
                        proof._verify_incumbent(config, restored)
                        proof._write(directory / "checkpoint.json", {"binding_sha256": binding, "best": restored})
                        best = restored
                        report["checkpoint_reuse"] = {**_summary(best), "accepted_seconds": elapsed(),
                                                       "checkpoint_committed_seconds": elapsed()}
                    report.update(search_reused=state.get("exhausted") is True,
                                  search_resumed=state.get("exhausted") is not True,
                                  search_exhausted=state.get("exhausted") is True)
                    if report["search_reused"]:
                        report.update(status="completed", termination_reason="cached_frontier_exhausted")
                        return
            except (OSError, ValueError, TypeError, KeyError) as error:
                cache_error(error)
                # No traversal or promotion from an incomplete/corrupt cache.
                inventories, offsets, completed = {}, {}, {incumbent["sha256"]}
                seen = set(completed)
        maximum, rounds = settings["deterministic_max_candidates"], settings["deterministic_rounds"]
        retain_frontier = settings.get("deterministic_cache", False) or settings.get("deterministic_regenerate", False)

        def pending_parent():
            return next((sha for sha, values in inventories.items() if offsets[sha] < len(values)), None)

        for round_index in range(rounds):
            remaining = maximum - report["evaluated_candidates"]
            if remaining <= 0 or time.monotonic() >= deadline:
                break
            parent_sha = best["sha256"]
            if (retain_frontier and parent_sha in inventories
                    and offsets[parent_sha] >= len(inventories[parent_sha])):
                parent_sha = pending_parent() or parent_sha
            if parent_sha not in inventories:
                generation_started = elapsed()
                old_record_count = len(report["generator_records"])
                inventories[parent_sha] = _generators(config, best["source"], signature,
                    directory / f"native-round-{round_index + 1:03d}", deadline, maximum,
                    report["generator_records"])
                generation_finished = elapsed()
                for record in report["generator_records"][old_record_count:]:
                    record.update(generation_started_seconds=round(generation_started +
                                      record.pop("generation_started_offset_seconds", 0), 6),
                                  generation_finished_seconds=round(generation_started +
                                      record.pop("generation_finished_offset_seconds", generation_finished - generation_started), 6))
                    if record.get("status") == "failed" or record.get("incomplete") is True:
                        incomplete_inventories.add(parent_sha)
                for item in inventories[parent_sha]:
                    if isinstance(item, dict):
                        item["proposal_ready_seconds"] = generation_finished
                offsets[parent_sha] = 0
                save()
            if retain_frontier and offsets[parent_sha] >= len(inventories[parent_sha]):
                parent_sha = pending_parent() or parent_sha
            inventory = inventories[parent_sha]
            quota = math.ceil(remaining / (rounds - round_index))
            evaluated = 0
            while offsets[parent_sha] < len(inventory) and evaluated < quota:
                if time.monotonic() >= deadline:
                    raise TimeoutError("Deterministic search deadline expired")
                item_index = offsets[parent_sha]
                item = inventory[item_index]
                offsets[parent_sha] += 1
                record = {"round": round_index + 1, "parent_sha256": parent_sha,
                          "model_calls": 0, "cost_usd": 0, "incumbent_before": _summary(best)}
                before = time.monotonic()
                terminal, rebased = False, False
                sha = None
                try:
                    if not isinstance(item, dict) or not isinstance(item.get("source"), str):
                        raise _GeneratorInvalid("Generated candidate lacks source text")
                    source, sha = item["source"], proof._digest(item["source"])
                    record.update(id=str(item.get("id", "")), family=str(item.get("family", "")), sha256=sha,
                                  proposal_ready_seconds=item.get("proposal_ready_seconds", elapsed()),
                                  proposal_from_cache=item.get("proposal_from_cache", False))
                    if settings.get("deterministic_policy") == "compact":
                        record.update({key: item[key] for key in (
                            "compaction", "semantic_candidate_sha256", "edits") if key in item})
                    if sha in seen:
                        continue
                    seen.add(sha)
                    candidate = directory / "candidates" / f"{sha}.lean"
                    record["origin"] = str(candidate)
                    report["candidate_records"].append(record)
                    # The cap is global, including invalid exact candidates.
                    report["evaluated_candidates"] += 1
                    evaluated += 1
                    retry_offsets[parent_sha] = min(item_index, retry_offsets.get(parent_sha, item_index))
                    save()
                    record["declaration_sha256"] = proof._digest(_preflight(config, row, source))
                    negative = None
                    if cache is not None:
                        try:
                            negative = cache.negative(sha)
                        except (OSError, ValueError, TypeError) as error:
                            cache_error(error)
                    if negative is not None:
                        record.update(valid=False, status="negative_cache_hit", error_kind="candidate_invalid",
                                      cached_compile_rejection=negative)
                        report["negative_cache_hits"] += 1
                        terminal = True
                        continue
                    record["validation_started_seconds"] = elapsed()
                    result = _validate(config, row, source, candidate, best, deadline, record)
                    record["validation_finished_seconds"] = elapsed()
                    terminal = True
                    if result is not None:
                        selected = directory / "validated" / f"{sha}.lean"
                        _immutable_source(selected, source)
                        result["selected_path"] = str(selected)
                        record["selected_path"] = str(selected)
                        record["wall_seconds"] = round(time.monotonic() - before, 6)
                        proof._verify_incumbent(config, result)
                        record["accepted_seconds"] = elapsed()
                        result.update(accepted_seconds=record["accepted_seconds"],
                                      validation_finished_seconds=record["validation_finished_seconds"])
                        # Commit only after primary, audit, and every supplied
                        # compatibility version have completely passed.
                        committed = {**report, "accepted_candidates": report["accepted_candidates"] + 1,
                                     "after": _summary(result), "improved": True}
                        proof._write(directory / "checkpoint.json", {"binding_sha256": binding, "best": result,
                                                                    "report": committed})
                        record["checkpoint_committed_seconds"] = elapsed()
                        best = result
                        report["accepted_candidates"] += 1
                        rebased = settings.get("deterministic_regenerate", False) and round_index + 1 < rounds
                except Exception as error:
                    if "validation_started_seconds" in record:
                        record["validation_finished_seconds"] = elapsed()
                    generator_invalid = isinstance(error, _GeneratorInvalid)
                    record.update(valid=False, status="generator_invalid" if generator_invalid else "validation_failed",
                        error=_error(error, phase="intake" if generator_invalid else "candidate"),
                        failure_kind=_failure_kind(error, deadline),
                        error_kind="generator_invalid" if generator_invalid else
                        "infrastructure" if proof._validation_exception_is_infrastructure(error) else "candidate_invalid")
                    from .deterministic_support.search_cache import compile_rejection
                    rejection = compile_rejection(error, proof.arena.LeanCompileError)
                    if isinstance(error, proof.arena.LeanCompileError) and rejection is None:
                        record["error_kind"] = "infrastructure"
                    terminal = generator_invalid or rejection is not None
                    if rejection is not None and cache is not None and sha is not None:
                        try:
                            cache.remember_invalid(sha, rejection)
                            record["negative_cache_stored"] = True
                        except (OSError, ValueError, TypeError) as cache_failure:
                            cache_error(cache_failure)
                    if record not in report["candidate_records"]:
                        report["candidate_records"].append(record)
                finally:
                    if terminal and sha is not None:
                        completed.add(sha)
                        if retry_offsets.get(parent_sha) == item_index:
                            retry_offsets.pop(parent_sha, None)
                    record["wall_seconds"] = round(time.monotonic() - before, 6)
                    record["incumbent_after"] = _summary(best)
                    save()
                if rebased:
                    break
            report["rounds_completed"] = round_index + 1
            save()
            if (offsets[parent_sha] >= len(inventory) and best["sha256"] == parent_sha
                    and (not retain_frontier or pending_parent() is None)):
                break
        report["status"] = "timed_out" if time.monotonic() >= deadline else "completed"
        report["search_exhausted"] = (best["sha256"] in inventories
            and not incomplete_inventories and not retry_offsets
            and all(offsets[sha] >= len(values) for sha, values in inventories.items()))
        report["termination_reason"] = ("wall_deadline" if report["status"] == "timed_out" else
            "frontier_exhausted" if report["search_exhausted"] else
            "candidate_limit" if report["evaluated_candidates"] >= maximum else
            "generation_incomplete" if incomplete_inventories else
            "retryable_validation_failure" if retry_offsets else "round_limit")
    except Exception as error:
        report["status"] = "timed_out" if isinstance(error, TimeoutError) else "infrastructure_failure"
        report["termination_reason"] = "wall_deadline" if isinstance(error, TimeoutError) else "infrastructure_failure"
        report["errors"].append(_error(error, phase="search"))
    finally:
        save()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["worker"])
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--seed", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    directory = args.out.resolve()
    config, incumbent = _read(args.config), _read(args.seed)
    request = _read(directory / "request.json")
    with scoped_environment(_environment(config, directory)), proof._host_validation_cache(config):
        stage = request.get("fixed_stage")
        if stage is None:
            _search(config, incumbent, directory, request)
        elif stage == DICTIONARY_STAGE:
            from .deterministic_support.dictionary_search import search
            search(config, incumbent, directory, request)
        else:
            raise ValueError("Unknown deterministic worker stage")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
