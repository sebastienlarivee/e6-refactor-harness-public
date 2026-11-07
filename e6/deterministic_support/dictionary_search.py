"""One bounded dictionary inventory, using the ordinary verified worker boundary."""
from __future__ import annotations

from pathlib import Path
import time

from .. import deterministic as engine, proof
from . import dictionary_cache


def _discovery_telemetry(directory: Path, source_sha: str) -> dict:
    receipt = engine._read(directory / "dictionary-proposals.json")
    if (receipt.get("source_sha256") != source_sha
            or receipt.get("status") not in {"completed", "unsupported_shape", "failed"}):
        raise ValueError("Dictionary generator receipt is not bound to the current source")
    analysis = receipt.get("analysis", {})
    if not isinstance(analysis, dict):
        raise ValueError("Dictionary generator analysis summary is malformed")
    result = {key: receipt[key] for key in (
        "status", "candidate_count", "max_candidates", "compiler_seconds", "hard_limits",
        "native_capture_calls", "partial_candidates_discarded", "error_type", "error") if key in receipt}
    result.update(unsupported_shape=receipt["status"] == "unsupported_shape",
                  completed_empty=receipt["status"] == "completed" and receipt.get("candidate_count") == 0,
                  candidate_cap_reached=receipt.get("candidate_count", 0) >= engine.DICTIONARY_SETTINGS["max_candidates"],
                  analysis=analysis)
    return result


def _generation_failure(error: BaseException, directory: Path, deadline: float) -> tuple[str, dict]:
    diagnostics = {}
    for name in ("capture-run.json", "dictionary-census.json"):
        path = directory / name
        if path.exists():
            try:
                value = engine._read(path)
                # Full captures remain on disk; only bounded diagnostics are
                # needed to distinguish a cap from a rejected candidate.
                diagnostics[name] = value.get("run", value.get("analysis", value))
                if isinstance(diagnostics[name], dict) and isinstance(diagnostics[name].get("error"), str):
                    diagnostics[name] = {**diagnostics[name], "message": diagnostics[name]["error"]}
            except (OSError, ValueError, TypeError):
                pass
    log = directory / "capture.log"
    if log.exists():
        try:
            with log.open("rb") as stream:
                stream.seek(max(0, log.stat().st_size - 8192))
                diagnostics["capture_log"] = {"output_tail": stream.read(8192).decode("utf-8", errors="replace")}
        except OSError:
            pass
    resource = engine._resource_limit(error) or engine._resource_limit(diagnostics)
    kind = "budget" if time.monotonic() >= deadline else "resource_limit" if resource else "infrastructure"
    return kind, diagnostics


def search(config: dict, incumbent: dict, directory: Path, request: dict) -> None:
    """Private worker entry point; never promotes a pass selection."""
    started = time.monotonic()
    binding = engine._json_digest(request)
    report = engine._read(directory / "progress.json")
    root, capsule = Path(config["root"]).resolve(), Path(request.get("capsule", "")).resolve()
    if (request.get("schema_version") != engine.SCHEMA_VERSION
            or request.get("fixed_stage") != engine.DICTIONARY_STAGE
            or request.get("settings") != engine.dictionary_settings()
            or request.get("config_sha256") != engine._json_digest(config)
            or request.get("seed_sha256") != incumbent.get("sha256")
            or request.get("incumbent_sha256") != engine._json_digest(incumbent)
            or report.get("binding_sha256") != binding
            or capsule.parent != root or not engine.re.fullmatch(r"pass-\d+", capsule.name)
            or directory.resolve() != root / "deterministic-dictionary" / capsule.name):
        raise ValueError("Dictionary worker input binding changed")
    deadline = started + engine.DICTIONARY_BUDGET_SECONDS
    best = engine._checkpoint(config, directory, binding, incumbent)
    report.update(status="running", fixed_stage=engine.DICTIONARY_STAGE,
                  candidate_records=[], generator_records=[], errors=[],
                  evaluated_candidates=0, accepted_candidates=0, rounds_completed=0,
                  search_exhausted=False, effective_budget_seconds=engine.DICTIONARY_BUDGET_SECONDS,
                  timing_clock="worker_monotonic_elapsed_seconds", termination_reason=None,
                  dictionary_telemetry={"status": "not_started"})
    seen = {incumbent["sha256"]}
    retryable, generated = 0, False

    def elapsed():
        return round(time.monotonic() - started, 6)

    def save():
        report.update(after=engine._summary(best), improved=engine._improved(best, incumbent),
                      wall_seconds=elapsed(), retryable_candidates=retryable)
        report.update(engine._health(report))
        proof._write(directory / "progress.json", report)

    try:
        proof._verify_config(config)
        proof._verify_incumbent(config, incumbent)
        _, row = proof.arena.load_task(Path(config["task"]))
        for name in ("candidates", "validated"):
            (directory / name).mkdir(exist_ok=True)
        discovery = directory / "dictionary-census"
        generator = {"generator": engine.DICTIONARY_STAGE, "parent_sha256": incumbent["sha256"],
                     "model_calls": 0, "cost_usd": 0, "generation_started_seconds": elapsed()}
        report["generator_records"].append(generator)
        save()
        try:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("Dictionary generation deadline expired")
            values = dictionary_cache.generate_candidates(config=config, source=incumbent["source"],
                signature=row["signature"], workdir=discovery,
                timeout_seconds=min(engine.DICTIONARY_SETTINGS["generator_timeout_seconds"], remaining),
                max_candidates=engine.DICTIONARY_SETTINGS["max_candidates"], family="census_dictionary_cache")
            if not isinstance(values, list) or len(values) > engine.DICTIONARY_SETTINGS["max_candidates"]:
                raise engine._GeneratorInvalid("Dictionary generator exceeded its bounded inventory")
            telemetry = _discovery_telemetry(discovery, incumbent["sha256"])
            if telemetry["status"] == "failed" or telemetry.get("candidate_count") != len(values):
                raise engine._GeneratorInvalid("Dictionary generator receipt differs from its inventory")
            report["dictionary_telemetry"] = telemetry
            generator.update(status="generated", count=len(values))
            generated = True
        except Exception as error:
            kind, diagnostics = _generation_failure(error, discovery, deadline)
            generator.update(status="failed", count=0, failure_kind=kind,
                             error=engine._error(error, phase="generation"), diagnostics=diagnostics)
            if kind == "infrastructure":
                report["errors"].append(engine._error(error, phase="generation"))
            try:
                report["dictionary_telemetry"] = _discovery_telemetry(discovery, incumbent["sha256"])
            except (OSError, ValueError, TypeError):
                report["dictionary_telemetry"] = {"status": "failed"}
            report["dictionary_telemetry"]["failure_kind"] = kind
            report.update(status="timed_out" if kind == "budget" else "completed" if kind == "resource_limit"
                          else "infrastructure_failure", termination_reason="wall_deadline" if kind == "budget"
                          else "generation_resource_limit" if kind == "resource_limit" else "generation_failure")
            return
        finally:
            generator["generation_finished_seconds"] = elapsed()
            generator["wall_seconds"] = round(generator["generation_finished_seconds"] - generator["generation_started_seconds"], 6)
            save()
        for index, item in enumerate(values):
            if time.monotonic() >= deadline:
                raise TimeoutError("Dictionary search deadline expired")
            record = {"round": 1, "index": index, "parent_sha256": incumbent["sha256"],
                      "model_calls": 0, "cost_usd": 0, "incumbent_before": engine._summary(best)}
            before = time.monotonic()
            try:
                if not isinstance(item, dict) or not isinstance(item.get("source"), str):
                    raise engine._GeneratorInvalid("Generated dictionary candidate lacks source text")
                source, sha = item["source"], proof._digest(item["source"])
                record.update(id=str(item.get("id", "")), family=str(item.get("family", "")), sha256=sha,
                              proposal_ready_seconds=generator["generation_finished_seconds"])
                if sha in seen:
                    record.update(status="duplicate_source", valid=None)
                    continue
                seen.add(sha)
                candidate = directory / "candidates" / f"{sha}.lean"
                record["origin"] = str(candidate)
                report["evaluated_candidates"] += 1
                report["candidate_records"].append(record)
                save()
                record["validation_started_seconds"] = elapsed()
                result = engine._validate(config, row, source, candidate, best, deadline, record)
                record["validation_finished_seconds"] = elapsed()
                if result is not None:
                    # _validate enforces a strict gain and all-version exact
                    # acceptance. The checkpoint remains the final guard.
                    if not engine._improved(result, best):
                        raise ValueError("Dictionary validator returned a nonimproving candidate")
                    selected = directory / "validated" / f"{sha}.lean"
                    engine._immutable_source(selected, source)
                    result["selected_path"] = str(selected)
                    record["selected_path"] = str(selected)
                    proof._verify_incumbent(config, result)
                    record["accepted_seconds"] = elapsed()
                    result.update(accepted_seconds=record["accepted_seconds"],
                                  validation_finished_seconds=record["validation_finished_seconds"])
                    committed = {**report, "accepted_candidates": report["accepted_candidates"] + 1,
                                 "after": engine._summary(result), "improved": True}
                    # Use the shared recovery verifier before committing, so
                    # incomplete compatibility/audit evidence cannot survive.
                    engine._verified_checkpoint_best(config, directory, incumbent, result)
                    value = {"binding_sha256": binding, "best": result, "report": committed}
                    proof._write(directory / "checkpoint.json", value)
                    best = result
                    record["checkpoint_committed_seconds"] = elapsed()
                    report["accepted_candidates"] += 1
            except Exception as error:
                if "validation_started_seconds" in record:
                    record["validation_finished_seconds"] = elapsed()
                kind = engine._failure_kind(error, deadline)
                record.update(valid=False, status="generator_invalid" if isinstance(error, engine._GeneratorInvalid)
                              else "validation_failed", failure_kind=kind,
                              error=engine._error(error, phase="candidate"))
                if kind in {"infrastructure", "resource_limit", "budget"}:
                    retryable += 1
                if record not in report["candidate_records"]:
                    report["candidate_records"].append(record)
            finally:
                record.update(wall_seconds=round(time.monotonic() - before, 6), incumbent_after=engine._summary(best))
                save()
        report.update(rounds_completed=1, status="completed", search_exhausted=generated and not retryable,
                      termination_reason="retryable_validation_failure" if retryable else
                      "unsupported_shape" if report["dictionary_telemetry"]["unsupported_shape"] else "frontier_exhausted")
    except Exception as error:
        report.update(status="timed_out" if isinstance(error, TimeoutError) else "infrastructure_failure",
                      termination_reason="wall_deadline" if isinstance(error, TimeoutError) else "infrastructure_failure",
                      search_exhausted=False)
        report["errors"].append(engine._error(error, phase="search"))
    finally:
        save()
