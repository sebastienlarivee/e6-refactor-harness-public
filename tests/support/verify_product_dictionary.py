#!/usr/bin/env python3
"""Exercise the production dictionary stage on an authenticated saved source.

This offline test driver alone accepts an external research seed directory.
Production modules and workers use only copied task/source/receipt inputs and
existing cached Lean projects. No model, account auth or environment setup runs.
Use --case admission for a bounded compiler/generator check, or --case worker
for fresh seed/final scoring, the real host worker and durable replay. Optional
--repeat-cached runs a second NEW boundary from the first winner's exact bytes.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from copy import deepcopy
from dataclasses import replace
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import time

REPO = Path(__file__).resolve().parents[2]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))


def require(value, message: str) -> None:
    if not value:
        raise AssertionError(message)


def read(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"Expected a JSON object: {path}")
    return value


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fresh_output(source: Path, output: Path, projects: list[Path]) -> None:
    require(source.is_dir(), "--input must be an existing authenticated seed directory")
    require(not output.exists(), "--out must be a fresh nonexistent artifact directory")
    for protected in (REPO, source, *projects):
        require(not output.is_relative_to(protected) and not protected.is_relative_to(output),
            f"Artifact output overlaps a protected input: {protected}")


@contextmanager
def offline_environment(elan_home: str):
    """Drop credential-bearing ambient state before any native process exists."""
    from e6.config import configure_native_environment
    previous = dict(os.environ)
    allowed = {"PATH", "LANG", "LC_ALL", "TERM", "SHELL", "E6_RUNTIME_ROOT"}
    clean = {key: value for key, value in previous.items() if key in allowed or
        (key.startswith("LEAN_REFACTOR_") and key.endswith(("_GATE", "_CAPACITY", "_QUEUE_TIMEOUT")))}
    clean.update(LEAN_NUM_THREADS="1", OMP_NUM_THREADS="1", PYTHONDONTWRITEBYTECODE="1")
    os.environ.clear()
    os.environ.update(clean)
    try:
        configure_native_environment(elan_home=elan_home)
        yield
    finally:
        os.environ.clear()
        os.environ.update(previous)


def project_seed(source: Path, root: Path, *, incumbent: dict | None = None) -> tuple[dict, dict, Path]:
    """Bind portable test metadata to local copies, without importing research."""
    from e6 import prompt_bundle, proof
    from e6.experiment import DEFAULT_SPEC
    saved, original_seed, origin = (read(source / name) for name in
        ("config.json", "incumbent-before.json", "origin.json"))
    text = (source / "source-before.lean").read_text(encoding="utf-8")
    require(original_seed.get("source") == text and original_seed.get("sha256") == proof._digest(text)
        and origin.get("source_sha256") == proof._digest(text),
        "Saved source lacks its incumbent/origin authentication binding")
    require(digest(source / "Task.json") == saved["task_sha256"]
        and digest(source / "environment-fingerprints.json") == saved["fingerprint_registry_sha256"],
        "Saved task or environment registry changed")
    seed = deepcopy(incumbent if incumbent is not None else original_seed)
    require(seed.get("sha256") == proof._digest(seed["source"]), "Incoming seed source changed")
    root.mkdir(parents=True, exist_ok=False)
    for name in ("Task.json", "Original.lean", "environment-fingerprints.json"):
        shutil.copyfile(source / name, root / name)
    task, registry = root / "Task.json", root / "environment-fingerprints.json"
    metadata = {key: deepcopy(saved[key]) for key in (
        "task_id", "task_sha256", "primary", "compatibility", "original_tokens", "original_heartbeats")}
    for key in ("scoring_policy", "original_measurement_tokens", "published_reference_heartbeats", "arena_reference"):
        if key in saved:
            metadata[key] = deepcopy(saved[key])
    metadata.update(task=str(task), registry_source=str(registry))
    spec = replace(DEFAULT_SPEC, scoring_policy=saved.get("scoring_policy", "legacy-v1"),
        goal_retrieval=False, search_extensions=False,
        deterministic_refactoring=True, deterministic_policy="compact",
        deterministic_cache=False, deterministic_regenerate=False)
    config = {**metadata, **spec.proof_settings(), "root": str(root), "label": saved["label"],
        "canonical_task": str(task), "task": str(task), "fingerprint_registry": str(registry),
        "fingerprint_registry_sha256": digest(registry), "product_metadata": metadata,
        "proof_metadata_sha256": proof._metadata_digest(saved["label"], metadata),
        "elan_home": saved["elan_home"]}
    identity = proof._incumbent_metadata(config)
    original = deepcopy(saved["initial_best"])
    original.update(identity, selected_path=str(root / "Original.lean"))
    require(original["source"] == (root / "Original.lean").read_text(encoding="utf-8"),
        "Saved original baseline differs from the copied original")
    config["prompt_bundle"] = prompt_bundle.snapshot(spec.prompt_variant)
    config["initial_best"] = original
    for key in ("observed_original_baseline", "original_measurement_heartbeats"):
        if key in saved:
            config[key] = deepcopy(saved[key])
    capsule = root / "pass-001"
    capsule.mkdir()
    selected = capsule / "Selected.lean"
    selected.write_text(seed["source"], encoding="utf-8", newline="")
    seed.update(identity, selected_path=str(selected))
    proof._verify_config(config)
    proof._verify_incumbent(config, original)
    proof._verify_incumbent(config, seed)
    proof._write(root / "config.json", config)
    proof._write(capsule / "selection.json", seed)
    return config, seed, capsule


def fresh_measure(config: dict, seed: dict, candidate: Path, output: Path) -> dict:
    from e6 import proof
    from lean_tools.evaluation import evaluate_candidate_fresh
    from lean_tools import arena_workflow as arena
    _, row = arena.load_task(Path(config["task"]))
    checks = []
    for index, project in enumerate((config["primary"], *config["compatibility"])):
        fingerprint = arena.measurement_environment_fingerprint(row, Path(project),
            registry_path=Path(config["fingerprint_registry"]))
        evaluation = evaluate_candidate_fresh(Path(config["task"]), candidate, Path(project),
            timeout_seconds=600, quick=index != 0, environment_fingerprint=fingerprint,
            scoring_policy=config.get("scoring_policy", "legacy-v1"))
        payload = arena.evaluation_payload(evaluation)
        checks.append({"environment": project, "passed": payload.get("valid") is True, "evaluation": payload})
        proof._write(output, {"source_sha256": digest(candidate), "compatibility": checks})
        require(payload.get("valid") is True, f"Fresh validation rejected {candidate} in {project}")
    primary = checks[0]["evaluation"]
    require(primary.get("source_sha256") == seed["sha256"] and primary.get("measurement_mode") == "exact"
        and primary.get("axiom_status") == "measured" and isinstance(primary.get("axioms"), list)
        and all(axiom in arena.ALLOWED_AXIOMS for axiom in primary["axioms"]),
        "Fresh result lacks its exact source-bound axiom audit")
    tokens, heartbeats = primary["length"]["candidate_tokens"], primary["heartbeat"]["candidate"]
    require(type(tokens) is int and type(heartbeats) is int, "Fresh result omitted exact metrics")
    measured = {**seed, "tokens": tokens, "heartbeats": heartbeats, "evaluation": primary,
        "compatibility": checks, "valid": True, "compatibility_complete": True, "compatibility_pct": 100,
        "score": proof._policy(config).score(tokens=tokens, heartbeats=heartbeats, compatibility_pct=100)}
    proof._verify_incumbent(config, measured)
    return measured


def worker_case(config: dict, seed: dict, capsule: Path, *, expect_improvement=False,
                expect_unsupported=False) -> tuple[dict, dict]:
    from e6 import deterministic as engine, proof
    root = Path(config["root"])
    seed = fresh_measure(config, seed, Path(seed["selected_path"]), root / "seed-validation.json")
    proof._write(capsule / "selection.json", seed)
    selection_sha = digest(capsule / "selection.json")
    best, receipt = engine.optimize_dictionary(config, capsule, seed)
    proof._write(root / "result-incumbent.json", best)
    proof._write(root / "worker-receipt.json", receipt)
    require(receipt.get("status") == "completed" and not receipt.get("errors"),
        f"Production dictionary worker failed: {receipt}")
    require(receipt.get("model_calls") == 0 and receipt.get("cost_usd") == 0
        and receipt.get("effective_budget_seconds") == 900, "Dictionary stage changed its fixed zero-model allowance")
    require(digest(capsule / "selection.json") == selection_sha, "Worker mutated the caller's selection")
    require(best["score"] >= seed["score"] and
        (best["sha256"] == seed["sha256"] or best["score"] > seed["score"]), "Worker regressed or accepted a tied source")
    if expect_improvement:
        require(best["sha256"] != seed["sha256"] and receipt.get("improved") is True,
            "Known positive source did not improve")
    full = read(Path(receipt["report_path"]))
    telemetry = full.get("dictionary_telemetry", {})
    if expect_unsupported:
        require(telemetry.get("status") == "unsupported_shape" and best["sha256"] == seed["sha256"],
            "Unsupported source did not abstain with the original fallback")
    final = fresh_measure(config, best, Path(best["selected_path"]), root / "final-validation.json")
    require((final["tokens"], final["heartbeats"], final["score"]) ==
        (best["tokens"], best["heartbeats"], best["score"]), "Fresh final measurements differ from the committed winner")
    boundary = root / "deterministic-dictionary" / capsule.name
    frozen = {str(path.relative_to(boundary)): digest(path) for path in boundary.rglob("*") if path.is_file()}
    replay, replay_receipt = engine.optimize_dictionary(config, capsule, best)
    require(replay_receipt.get("reused") is True and replay["sha256"] == best["sha256"],
        "Same-boundary replay failed to reuse its durable checkpoint")
    require(frozen == {str(path.relative_to(boundary)): digest(path)
        for path in boundary.rglob("*") if path.is_file()}, "Replay changed the consumed search artifacts")
    return best, {"before": engine._summary(seed), "after": engine._summary(best),
        "worker": receipt, "dictionary_telemetry": telemetry, "durable_replay": True,
        "fresh_final_verified": True, "selection_unchanged": True}


def admission_case(config: dict, seed: dict, *, expect_unsupported=False) -> dict:
    from e6.deterministic_support import dictionary_cache as generator
    root = Path(config["root"])
    _, row = generator.arena.load_task(Path(config["task"]))
    workdir = root / "generation"
    rows = generator.generate_candidates(config=config, source=seed["source"], signature=row["signature"],
        workdir=workdir, timeout_seconds=180, max_candidates=4)
    generator.arena.write_json_atomic(root / "inventory.json", {"candidates": rows})
    receipt = read(workdir / "dictionary-proposals.json")
    require(receipt["status"] in {"completed", "unsupported_shape"}
        and receipt["source_sha256"] == seed["sha256"] and len(rows) <= 4,
        "Generator omitted a bounded source-bound completion receipt")
    if expect_unsupported:
        require(receipt["status"] == "unsupported_shape" and not rows and receipt["native_capture_calls"] == 0,
            "Unsupported shape launched a native census or emitted proposals")
    result = {"generation": receipt, "candidate_sha256": [row["source_sha256"] for row in rows],
        "scope": "Compiler and source generation admission; candidate scores are not asserted."}
    if receipt["status"] == "unsupported_shape":
        prefix = generator.lean_source.exact_source_prefix(row, Path(config["primary"]))
        _, module = generator.lean_source.import_header_end(prefix.text)
        helper = (generator.SUPPORT / "DictionaryCensus.lean.inc").read_text(encoding="utf-8")
        harness = prefix.text + "\nmeta section\n" + helper + "\nend\n"
        point, _ = generator.lean_source.import_header_end(harness)
        harness = harness[:point] + ("\npublic meta import Lean\n" if module else "\nimport Lean\n") + harness[point:]
        path = root / "HelperOnly.lean"
        path.write_text(harness, encoding="utf-8", newline="")
        run = generator.native._run(path, Path(config["primary"]), time.monotonic() + 180, root / "helper-only.log")
        result["helper_only_control"] = {"run": run, "harness_sha256": digest(path),
            "scope": "Compiler API control only; unsupported source did not undergo dictionary census."}
        require(run["returncode"] == 0 and not run["timed_out"], "Helper-only compiler API control failed")
    return result


def verify(source: Path, output: Path, *, case="worker", repeat_cached=False,
           expect_improvement=False, expect_unsupported=False) -> dict:
    from e6 import proof
    from e6.deterministic_support import dictionary_cache
    from e6.runtime import RuntimeContext, create_environment_directories, scoped_environment
    saved = read(source / "config.json")
    fresh_output(source, output, [Path(path).resolve() for path in (saved["primary"], *saved["compatibility"])])
    output.mkdir(parents=True)
    started = time.monotonic()
    report = {"schema_version": 1, "kind": "offline-native-product-dictionary-validation", "status": "running",
        "input": str(source), "out": str(output), "case": case, "model_calls": 0, "external_inference_calls": 0,
        "cost_usd": 0, "account_auth_loaded": False, "environment_rebuilds": 0,
        "input_files": {path.name: digest(path) for path in source.iterdir() if path.is_file()},
        "code_sha256": {name: digest(REPO / name) for name in (*dictionary_cache.GENERATOR_FILES,
            "e6/deterministic.py", "e6/deterministic_support/dictionary_search.py", "tests/support/verify_product_dictionary.py")},
        "cases": []}
    try:
        with offline_environment(saved["elan_home"]):
            config, seed, capsule = project_seed(source, output / "initial")
            values = RuntimeContext.resolve(Path(config["root"]), config).environment(capsule,
                registry=Path(config["fingerprint_registry"]))
            values = {key: os.environ.get(key, value) for key, value in values.items()}
            create_environment_directories(values, checkpoint=True)
            with scoped_environment(values):
                if case == "worker":
                    best, result = worker_case(config, seed, capsule,
                        expect_improvement=expect_improvement, expect_unsupported=expect_unsupported)
                    report["cases"].append({"kind": "initial-worker", **result})
                else:
                    result = admission_case(config, seed, expect_unsupported=expect_unsupported)
                    report["cases"].append({"kind": "generator-admission", **result})
            if repeat_cached:
                require(case == "worker", "--repeat-cached requires --case worker")
                config, seed, capsule = project_seed(source, output / "already-cached", incumbent=best)
                values = RuntimeContext.resolve(Path(config["root"]), config).environment(capsule,
                    registry=Path(config["fingerprint_registry"]))
                values = {key: os.environ.get(key, value) for key, value in values.items()}
                create_environment_directories(values, checkpoint=True)
                with scoped_environment(values):
                    _, result = worker_case(config, seed, capsule)
                    report["cases"].append({"kind": "new-boundary-from-first-winner", **result})
        require(report["input_files"] == {path.name: digest(path) for path in source.iterdir() if path.is_file()},
            "Validation changed an external input")
        require(report["code_sha256"] == {name: digest(REPO / name) for name in report["code_sha256"]},
            "Production code changed during native validation")
        report["status"] = "passed"
        return report
    except BaseException as error:
        report.update(status="failed", error={"type": type(error).__name__, "message": str(error)})
        raise
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        proof._write(output / "report.json", report)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="Saved source/config/incumbent/origin seed directory")
    parser.add_argument("--out", type=Path, required=True, help="Fresh nonexistent directory outside source and cached projects")
    parser.add_argument("--case", choices=("worker", "admission"), default="worker")
    parser.add_argument("--repeat-cached", action="store_true")
    parser.add_argument("--expect-improvement", action="store_true")
    parser.add_argument("--expect-unsupported", action="store_true")
    args = parser.parse_args()
    if args.repeat_cached and args.case != "worker":
        parser.error("--repeat-cached requires --case worker")
    if args.expect_improvement and (args.expect_unsupported or args.case != "worker"):
        parser.error("--expect-improvement requires a supported worker case")
    result = verify(args.input.expanduser().resolve(), args.out.expanduser().resolve(), case=args.case,
        repeat_cached=args.repeat_cached, expect_improvement=args.expect_improvement,
        expect_unsupported=args.expect_unsupported)
    print(json.dumps({key: result[key] for key in ("status", "out", "case", "model_calls", "cost_usd", "elapsed_seconds")}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
