"""Fresh solo capsules and host selection; imports the established tools read-only."""
from __future__ import annotations

import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import stat
import sys
from contextlib import contextmanager

from lean_tools import arena_workflow as arena
from lean_tools import feedback_workflow as feedback
from lean_tools import capsule as swarm
from lean_tools.validation_policy import OriginalDenominatorScorePolicy
from lean_tools.measurement_policy import scoring_policy_context
from .baseline_cache import OriginalBaselineCache, environment_settings
from .config import REPO_ROOT as REPOSITORY, TOOLS_ROOT as SCRIPTS, PROOFS, ARENA_PROOFS, find_codex, resolve_metadata, configure_native_environment, runtime_root
from .experiment import DEFAULT_SPEC, ExperimentSpec, experiment_spec, resolve_spec
from .runtime import RuntimeContext, scoped_environment
from .stopping import policy_for_config

CHECK_TIMEOUT = DEFAULT_SPEC.check_timeout_seconds
PREPARATION_CHECK_TIMEOUT = DEFAULT_SPEC.preparation_check_timeout_seconds


def _write(path: Path, value: dict) -> None:
    arena.write_json_atomic(path, value)


def _digest(source: str) -> str:
    return hashlib.sha256(source.encode("utf-8")).hexdigest()


def _metadata(label: str, scoring_policy: str = "legacy-v1") -> dict:
    if scoring_policy not in {"legacy-v1", "arena-v1"}:
        raise ValueError("Unsupported E6 scoring policy")
    manifest = ARENA_PROOFS if scoring_policy == "arena-v1" else PROOFS
    document = json.loads(manifest.read_text(encoding="utf-8-sig"))
    if document.get("schema_version") != 1 or not isinstance(document.get("proofs"), dict):
        raise ValueError("Unsupported proof metadata manifest")
    if label not in document["proofs"]:
        raise ValueError(f"Unknown proof label: {label}")
    metadata = document["proofs"][label]
    if not isinstance(metadata, dict):
        raise ValueError("Proof metadata must be a mapping")
    for key in ("task_id", "task", "task_sha256", "primary", "registry_source"):
        if not isinstance(metadata.get(key), str) or not metadata[key]:
            raise ValueError(f"Proof metadata lacks {key}")
    compatibility = metadata.get("compatibility")
    if not isinstance(compatibility, list) or any(not isinstance(path, str) or not path for path in compatibility):
        raise ValueError("Proof metadata requires compatibility paths")
    projects = [metadata["primary"], *compatibility]
    if len({str(Path(path).resolve()).casefold() for path in projects}) != len(projects):
        raise ValueError("Proof metadata contains duplicate environments")
    metadata = resolve_metadata(metadata)
    _policy(metadata)
    if scoring_policy == "arena-v1":
        if (document.get("scoring_policy") != scoring_policy
                or metadata.get("scoring_policy") != scoring_policy
                or type(metadata.get("original_measurement_tokens")) is not int
                or metadata["original_measurement_tokens"] != metadata["original_tokens"] + 1):
            raise ValueError("Arena metadata lacks its versioned candidate token convention")
    elif "original_measurement_heartbeats" in metadata:
        measured = metadata["original_measurement_heartbeats"]
        evidence = metadata.get("original_measurement_evidence", {})
        if (type(measured) is not int or measured <= 0 or not isinstance(evidence, dict)
                or evidence.get("measured_heartbeats") != measured
                or evidence.get("historical_heartbeats") != metadata["original_heartbeats"]
                or evidence.get("scoring_denominator_changed") is not False
                or not isinstance(evidence.get("path"), str)
                or arena.sha256_file(Path(evidence["path"])) != evidence.get("sha256")):
            raise ValueError("Original control measurement lacks its frozen exact-cache evidence")
    return metadata


def _metadata_digest(label: str, metadata: dict) -> str:
    return _digest(json.dumps({"label": label, "metadata": metadata}, sort_keys=True, ensure_ascii=False))


def _policy(config: dict) -> OriginalDenominatorScorePolicy:
    return OriginalDenominatorScorePolicy(config["original_tokens"], config["original_heartbeats"],
        **({"scoring_policy": config["scoring_policy"]} if config.get("scoring_policy") == "arena-v1" else {}))


def _original_measurement_tokens(config: dict) -> int:
    if config.get("scoring_policy", "legacy-v1") == "arena-v1":
        return config["original_measurement_tokens"]
    return config["original_tokens"]


def _original_control_heartbeats(config: dict) -> int:
    if config.get("scoring_policy", "legacy-v1") == "arena-v1":
        return config["observed_original_baseline"]["heartbeats"]
    return config.get("original_measurement_heartbeats", config["original_heartbeats"])


def _incumbent_metadata(config: dict) -> dict:
    return {**{key: config[key] for key in (
        "proof_metadata_sha256", "label", "task_id", "task_sha256", "original_tokens", "original_heartbeats")},
        **({"scoring_policy": config["scoring_policy"]} if "scoring_policy" in config else {})}


def _verify_incumbent(config: dict, incumbent: dict) -> None:
    if (not incumbent.get("valid") or not incumbent.get("compatibility_complete")
            or any(incumbent.get(key) != value for key, value in _incumbent_metadata(config).items())
            or not isinstance(incumbent.get("source"), str)
            or _digest(incumbent["source"]) != incumbent.get("sha256")):
        raise ValueError("Fallback must be a verified unchanged incumbent for this proof")
    if incumbent.get("score") != _policy(config).score(
            tokens=incumbent["tokens"], heartbeats=incumbent["heartbeats"],
            compatibility_pct=incumbent["compatibility_pct"]):
        raise ValueError("Verified incumbent score does not match the frozen denominators")


def _source(path: Path) -> str:
    info = path.lstat()
    if not stat.S_ISREG(info.st_mode):
        raise ValueError("Candidate must be a regular file")
    return path.read_text(encoding="utf-8")


def _check(config: dict, candidate: Path, project: Path, *, quick: bool = False,
           timeout_seconds: float | None = None) -> dict:
    if timeout_seconds is None:
        timeout_seconds = experiment_spec(config).check_timeout_seconds
    configure_native_environment(elan_home=config.get("elan_home"))
    with scoring_policy_context(experiment_spec(config).scoring_policy):
        evaluation = arena.evaluate_candidate(Path(config["task"]), candidate, project,
            timeout_seconds=timeout_seconds, quick=quick,
            fingerprint_registry=Path(config["fingerprint_registry"]))
    return arena.evaluation_payload(evaluation)


@contextmanager
def _preparation_cache(root: Path):
    """Preparation uses its private cache; the canonical cache is never ambient."""
    with scoped_environment({"LEAN_REFACTOR_EVALUATION_CACHE": str(RuntimeContext(root).preparation_cache)}):
        yield


def _preparation_error(error: BaseException) -> dict:
    detail = {"type": type(error).__name__, "message": str(error)}
    result = getattr(error, "result", None)
    if result is not None:
        detail["lean_run"] = {name: getattr(result, name, None) for name in (
            "command", "returncode", "seconds", "timed_out", "log_path", "queue_wait_seconds")}
        detail["lean_run"]["output_tail"] = str(getattr(result, "output", ""))[-8192:]
    return detail


def prepare(root: Path, label: str, *, backend: str | None = None,
            spec: ExperimentSpec | None = None, stopping_policy: str | None = None,
            metadata: dict | None = None, baseline_snapshot: dict | None = None) -> dict:
    """Guard cached identities and verify the original without model inference."""
    from .config import resolve_backend, resolve_stopping_policy
    explicit_metadata = metadata is not None
    backend = resolve_backend(root, backend)
    spec = resolve_spec(root, spec, stopping_policy)
    if backend == "pi":
        from . import pi
        pi.validate_settings(spec.proof_settings())
    configure_native_environment()
    root = root.resolve()
    if root.is_relative_to(REPOSITORY):
        raise ValueError("Experiment capsules must live outside the repository")
    root.mkdir(parents=True, exist_ok=True)
    if (root / "config.json").exists() or (root / "run.claim").exists():
        raise FileExistsError("A fresh experiment root is required")
    preflight_path = root / "baseline-preflight.json"
    progress_path = root / "preparation" / "progress.json"
    diagnostics = {"schema_version": 1, "status": "preparing", "phase": "metadata", "label": label,
                   "started_at": arena.utc_now(), "primary": None, "compatibility": [], "phases": [],
                   "preparation_check_timeout_seconds": spec.preparation_check_timeout_seconds,
                   "model_check_timeout_seconds": spec.check_timeout_seconds,
                   "progress_path": str(progress_path), "preflight_path": str(preflight_path)}

    def save_progress():
        diagnostics["updated_at"] = arena.utc_now()
        _write(preflight_path, diagnostics)
        state = {"status": "preparation_failed" if diagnostics["status"] == "failed" else
                           "preparation_verified" if diagnostics["status"] == "passed" else "preparing",
                 "root": str(root), "label": label, "phase": diagnostics["phase"], "passes": [],
                 "phase_path": diagnostics.get("phase_path"), "preflight_path": str(preflight_path),
                 "updated_at": diagnostics["updated_at"]}
        _write(progress_path, state)
        _write(root / "state.json", state)

    save_progress()
    phase = None
    try:
        metadata = dict(metadata) if metadata is not None else _metadata(label, spec.scoring_policy)
        _policy(metadata)
        task, registry_source = Path(metadata["task"]), Path(metadata["registry_source"])
        projects = [Path(metadata["primary"]), *map(Path, metadata["compatibility"])]
        tokens, heartbeats = metadata["original_tokens"], metadata["original_heartbeats"]
        measurement_tokens = _original_measurement_tokens(metadata)
        control_heartbeats = metadata.get("original_measurement_heartbeats", heartbeats)
        policy = _policy(metadata)
        diagnostics.update(task_id=metadata["task_id"], expected_original_tokens=tokens,
                           expected_original_measurement_tokens=measurement_tokens,
                           expected_original_heartbeats=heartbeats,
                           expected_control_heartbeats=control_heartbeats if spec.scoring_policy == "legacy-v1" else None,
                           control_heartbeat_drift=control_heartbeats - heartbeats if spec.scoring_policy == "legacy-v1" else None,
                           phase="identity_and_guards")
        save_progress()
        if arena.sha256_file(task) != metadata["task_sha256"]:
            raise ValueError("Canonical original task changed")
        _, row = arena.load_task(task)
        if row["name"] != metadata["task_id"]:
            raise ValueError("Canonical task identity does not match proof metadata")
        entries = {}
        for project in projects:
            entry = arena.environment_fingerprint_registry_entry(row, project, registry_source, validate_guard=True)
            entries[arena.environment_fingerprint_registry_key(row, project)] = entry
        task_path, registry = root / "Task.json", root / "environment-fingerprints.json"
        shutil.copyfile(task, task_path)
        _write(registry, {"schema_version": arena.FINGERPRINT_REGISTRY_SCHEMA_VERSION, "entries": entries})
        config = {**metadata, "root": str(root), "canonical_task": str(task), "task": str(task_path), "label": label,
                  "proof_metadata_sha256": _metadata_digest(label, metadata),
                  "fingerprint_registry": str(registry), "fingerprint_registry_sha256": arena.sha256_file(registry),
                  "agent_backend": backend, "elan_home": os.environ["ELAN_HOME"],
                  **({"product_metadata": dict(metadata)} if explicit_metadata else {}),
                  **spec.proof_settings()}
        if backend == "pi":
            from . import pi
            config.update(pi.runtime())
        else:
            config["codex"] = str(find_codex())
        source = arena.render_candidate_scaffold(row)
        original = root / "Original.lean"
        original.write_text(source, encoding="utf-8")
        baseline_receipt = None
        if metadata.get("baseline_receipt") is not None:
            from harness.baselines import load_original_baseline
            baseline_receipt = load_original_baseline(metadata, source_snapshot=baseline_snapshot)
            diagnostics["baseline_receipt"] = {**metadata["baseline_receipt"], "status": "validated_reuse"}
        cache_root, seeds = (None, []) if baseline_receipt is not None else environment_settings()
        cache = OriginalBaselineCache(cache_root, seeds, root / "preparation" / "evaluation-cache")
        diagnostics["baseline_cache"] = {"canonical_root": str(cache_root) if cache_root else None,
                                         "explicit_seed_roots": [str(path) for path in seeds],
                                         "scope": "host preparation; unchanged canonical original entries only"}
        compatibility = diagnostics["compatibility"]
        with _preparation_cache(root):
            for index, project in enumerate(projects):
                quick = index != 0
                name = f"compatibility-{index:03d}-quick" if quick else "primary-exact"
                phase_path = root / "preparation" / "baseline-phases" / f"{name}.json"
                phase = {"phase": name, "status": "running", "environment": str(project),
                         "mode": "quick" if quick else "exact", "started_at": arena.utc_now(),
                         "timeout_seconds": spec.preparation_check_timeout_seconds, "path": str(phase_path)}
                diagnostics["phases"].append(phase)
                diagnostics.update(phase=name, phase_path=str(phase_path))
                _write(phase_path, phase)
                save_progress()
                request = cache.request(config, original, project, quick=quick) if cache_root else None
                phase["baseline_cache"] = cache.stage(request) if request else {"status": "disabled"}
                _write(phase_path, phase)
                save_progress()
                if baseline_receipt is not None:
                    from copy import deepcopy
                    result = deepcopy(baseline_receipt["evaluations"][index])
                    phase["baseline_receipt"] = {**metadata["baseline_receipt"], "status": "validated_reuse"}
                else:
                    result = _check(config, original, project, quick=quick,
                                    timeout_seconds=spec.preparation_check_timeout_seconds)
                phase["evaluation"] = result
                phase["status"] = "passed" if result.get("valid") else "failed"
                phase["finished_at"] = arena.utc_now()
                if not quick:
                    diagnostics["primary"] = primary = result
                    if spec.scoring_policy == "arena-v1":
                        observed_h = primary.get("heartbeat", {}).get("candidate")
                        entry = entries[arena.environment_fingerprint_registry_key(row, project)]
                        if (not primary.get("valid")
                                or primary.get("task_id") != metadata["task_id"]
                                or primary.get("measurement_mode") != "exact"
                                or primary.get("axiom_status") != "measured"
                                or not isinstance(primary.get("axioms"), list)
                                or any(axiom not in arena.ALLOWED_AXIOMS for axiom in primary["axioms"])
                                or primary.get("length", {}).get("original_tokens") != tokens
                                or primary.get("length", {}).get("candidate_tokens") != measurement_tokens
                                or type(observed_h) is not int or observed_h <= 0
                                or primary.get("heartbeat", {}).get("local_reference") != heartbeats
                                or primary.get("heartbeat", {}).get("environment_fingerprint") != entry["fingerprint"]):
                            raise ValueError("Arena original baseline lacks exact canonical token, heartbeat, or axiom evidence")
                        control_heartbeats = observed_h
                        config["observed_original_baseline"] = {
                            "source_sha256": _digest(source), "tokens": measurement_tokens,
                            "heartbeats": observed_h, "environment_fingerprint": entry["fingerprint"],
                            "environment_guard_sha256": entry["guard_sha256"]}
                        diagnostics["observed_original_baseline"] = config["observed_original_baseline"]
                        diagnostics["control_heartbeat_drift"] = observed_h - heartbeats
                    elif (not primary.get("valid") or primary.get("length", {}).get("candidate_tokens") != tokens
                            or primary.get("heartbeat", {}).get("candidate") != control_heartbeats
                            or primary.get("heartbeat", {}).get("local_reference") != control_heartbeats):
                        phase["status"] = "failed"
                        _write(phase_path, phase)
                        save_progress()
                        raise ValueError("Original baseline does not match the frozen control measurement; explicit calibration required")
                    compatibility.append({"environment": str(project), "passed": True})
                else:
                    compatibility.append({"environment": str(project), "passed": bool(result.get("valid")),
                                          "evaluation": result})
                _write(phase_path, phase)
                save_progress()
                if request and result.get("valid"):
                    phase["baseline_cache"]["publication"] = cache.publish(request)
                    _write(phase_path, phase)
                    save_progress()
        if not all(item["passed"] for item in compatibility):
            raise ValueError("Original failed a cached compatibility environment")
        if spec.goal_retrieval:
            from lean_tools import goal_retrieval
            phase_path = root / "preparation" / "retrieval-index.json"
            phase = {"phase": "retrieval-index", "status": "running", "path": str(phase_path),
                     "started_at": arena.utc_now(), "environment": config["primary"]}
            diagnostics["phases"].append(phase)
            diagnostics.update(phase="retrieval-index", phase_path=str(phase_path))
            _write(phase_path, phase)
            save_progress()
            config["retrieval_index"] = goal_retrieval.prepare_index(
                row, Path(config["primary"]), runtime_root() / "retrieval-index-cache",
                fingerprint_registry=Path(config["fingerprint_registry"]))
            phase.update(status="passed", artifact=config["retrieval_index"], finished_at=arena.utc_now())
            _write(phase_path, phase)
        if spec.search_extensions:
            from lean_tools import proof_example_search
            phase_path = root / "preparation" / "examples-index.json"
            phase = {"phase": "examples-index", "status": "running", "path": str(phase_path),
                     "started_at": arena.utc_now(), "environment": config["primary"]}
            diagnostics["phases"].append(phase)
            diagnostics.update(phase="examples-index", phase_path=str(phase_path))
            _write(phase_path, phase)
            save_progress()
            # Admission is exactly the frozen source prefix plus its recursive
            # imports. No run artifacts, inspiration modules or archived proofs
            # participate; canonical source identities reuse immutable indexes.
            cache_root = Path(os.environ.get(
                "E6_EXAMPLES_INDEX_CACHE", str(Path.home() / "lean-e6-example-index-cache"))).expanduser().resolve()
            config["examples_index"] = proof_example_search.prepare_index(
                row, Path(config["primary"]), cache_root,
                fingerprint_registry=Path(config["fingerprint_registry"]),
                source_roots=proof_example_search.default_source_roots(
                    Path(config["primary"]), elan_home=Path(config["elan_home"])))
            phase.update(status="passed", artifact=config["examples_index"], finished_at=arena.utc_now())
            _write(phase_path, phase)
        diagnostics.update(status="passed", phase="verified", finished_at=arena.utc_now())
        save_progress()
    except BaseException as error:
        detail = _preparation_error(error)
        if phase and phase["status"] == "running":
            phase.update(status="failed", error=detail, finished_at=arena.utc_now())
            _write(Path(phase["path"]), phase)
        diagnostics.update(status="failed", failure=str(error), error=detail, finished_at=arena.utc_now())
        save_progress()
        raise
    config["initial_best"] = {**_incumbent_metadata(config),
        "source": source, "sha256": _digest(source), "selected_path": str(original),
        "score": policy.score(tokens=measurement_tokens, heartbeats=control_heartbeats, compatibility_pct=100),
        "tokens": measurement_tokens, "heartbeats": control_heartbeats, "compatibility_pct": 100,
        "valid": True, "compatibility_complete": True, "evaluation": primary,
        "compatibility": compatibility}
    from . import prompt_bundle
    config["prompt_bundle"] = prompt_bundle.snapshot(spec.prompt_variant)
    (root / "proof-guide.md").write_text(prompt_bundle.render_guide(config), encoding="utf-8")
    _write(root / "config.json", config)
    return config


def make_capsule(root: Path, pass_number: int, best_source: str, remaining_usd: float | None = None) -> Path:
    """Build the selected first-pass view, then use verified incumbents."""
    if type(pass_number) is not int or pass_number < 1:
        raise ValueError("Pass number must be positive")
    root = root.resolve()
    config = json.loads((root / "config.json").read_text(encoding="utf-8"))
    spec = experiment_spec(config)
    stopping_policy = policy_for_config(config)
    if stopping_policy == "cost" and (remaining_usd is None or not math.isfinite(remaining_usd) or remaining_usd <= 0):
        raise ValueError("Pass number and remaining budget must be positive")
    _verify_config(config)
    capsule = root / f"pass-{pass_number:03d}"
    if capsule.exists():
        raise FileExistsError("Every pass requires a fresh capsule")
    incumbent = config["initial_best"] if pass_number == 1 else json.loads(
        (root / f"pass-{pass_number - 1:03d}" / "selection.json").read_text(encoding="utf-8"))
    if config.get("product_schema_version") and pass_number > 1:
        incumbent = json.loads((root / "best.json").read_text(encoding="utf-8"))
        incumbent["source"] = _source(Path(incumbent["selected_path"]))
    try:
        _verify_incumbent(config, incumbent)
    except (KeyError, ValueError) as error:
        raise ValueError("A fresh pass must start from the current verified incumbent for this proof") from error
    if (best_source.replace("\r\n", "\n").rstrip("\n")
            != incumbent["source"].replace("\r\n", "\n").rstrip("\n")):
        raise ValueError("A fresh pass must start from the current verified incumbent")
    mode = spec.pass_mode(pass_number)
    reprove = mode == "statement_first_reprove"
    reference_rebuild = mode == "reference_rebuild"
    task, registry, source = Path(config["task"]), Path(config["fingerprint_registry"]), incumbent["source"]
    if reprove:
        from .statement_first import prepare_view
        view = prepare_view(config)
        task, registry = Path(view["task"]), Path(view["registry"])
        _, row = arena.load_task(task)
        source = arena.render_candidate_scaffold(row)
    elif reference_rebuild:
        from .statement_first import statement_row
        _, row = arena.load_task(task)
        # Only the editable draft is unfinished. Keep the original task and
        # registry so normal source visibility and warm feedback remain legal.
        source = arena.render_candidate_scaffold(statement_row(row))
    swarm.prepare_capsule(capsule, task, root / "proof-guide.md", source,
                          fingerprint_registry=registry)
    if reference_rebuild:
        (capsule / "Original.lean").write_text(incumbent["source"], encoding="utf-8")
    _write(capsule / "pass-mode.json", {"pass_number": pass_number, "mode": mode,
                                      "original_proof_visible": not reprove,
                                      "warm_broker_available": not reprove,
                                      **({"starting_candidate_valid": False,
                                          "starting_candidate_sha256": _digest(source),
                                          "original_reference": {"path": "Original.lean",
                                              "sha256": incumbent["sha256"], "valid": True}}
                                         if reference_rebuild else {})})
    primary = Path(config["primary"])
    compatibility_roots = [Path(path) for path in config["compatibility"]]
    feedback.configure_capsule(capsule, primary, spec.check_timeout_seconds,
        **({"scoring_policy": spec.scoring_policy} if spec.scoring_policy != "legacy-v1" else {}),
        **({"response_policy": spec.response_policy} if spec.response_policy != "legacy" else {}),
        candidate_batches=spec.candidate_batches, goal_retrieval=spec.goal_retrieval,
        unfinished_cases=spec.unfinished_cases, regional_profiler=spec.regional_profiler,
        compatibility_roots=compatibility_roots, original_tokens=config["original_tokens"],
        original_heartbeats=config["original_heartbeats"], incumbent_score=incumbent["score"],
        incumbent_source_sha256=incumbent["sha256"],
        incumbent_metrics={
            "source_sha256": incumbent["sha256"],
            **({"scoring_policy": spec.scoring_policy} if spec.scoring_policy != "legacy-v1" else {}),
            **{name: incumbent[name] for name in ("tokens", "heartbeats", "compatibility_pct", "score")},
            "original_tokens": config["original_tokens"], "original_heartbeats": config["original_heartbeats"],
            "compatibility_environments": [str(primary.resolve()), *(str(path.resolve()) for path in compatibility_roots)],
            **({"environment_fingerprint": incumbent["evaluation"]["heartbeat"]["environment_fingerprint"]}
               if incumbent.get("evaluation", {}).get("heartbeat", {}).get("environment_fingerprint") else {})},
        **({"retrieval_index": Path(config["retrieval_index"]["path"]),
            "retrieval_index_sha256": config["retrieval_index"]["sha256"],
            "retrieval_pool_mode": spec.retrieval_pool_mode}
           if spec.goal_retrieval else {}),
        **({"search_extensions": True, "examples_index": Path(config["examples_index"]["path"]),
            "examples_index_sha256": config["examples_index"]["sha256"],
            "examples_index_identity": config["examples_index"]["identity"]}
           if spec.search_extensions else {}))
    from . import prompt_bundle
    prompt_bundle.write_capsule(capsule, config, incumbent, statement_first=reprove,
                                **({"reference_rebuild": True} if reference_rebuild else {}))
    return capsule


def _verify_config(config: dict) -> None:
    spec = experiment_spec(config)
    from . import prompt_bundle
    prompt_bundle.verify_snapshot(config)
    metadata = dict(config["product_metadata"]) if "product_metadata" in config else _metadata(config["label"], spec.scoring_policy)
    if config.get("source_migration"):
        # Historic selection identities bind absolute checkout paths. A
        # content-pinned receipt permits relocating tooling while retaining
        # those immutable proof identities and every prior selection file.
        from .resume import verify_source_migration
        migration = verify_source_migration(config)
        previous = Path(migration["original_source_root"])
        def original_location(value):
            if isinstance(value, dict):
                return {key: original_location(item) for key, item in value.items()}
            if isinstance(value, list):
                return [original_location(item) for item in value]
            if isinstance(value, str) and Path(value).is_absolute():
                path = Path(value)
                if path.is_relative_to(REPOSITORY):
                    return str(previous / path.relative_to(REPOSITORY))
            return value
        metadata = original_location(metadata)
    if (_metadata_digest(config["label"], metadata) != config.get("proof_metadata_sha256")
            or config.get("canonical_task") != metadata["task"]
            or any(config.get(key) != value for key, value in metadata.items() if key != "task")):
        raise ValueError("Frozen proof metadata changed or belongs to another proof")
    if metadata.get("baseline_receipt") is not None:
        from harness.baselines import load_original_baseline
        load_original_baseline(metadata, verify_sources=False)
    if arena.sha256_file(Path(config["task"])) != config["task_sha256"]:
        raise ValueError("Frozen original task changed")
    if arena.sha256_file(Path(config["fingerprint_registry"])) != config["fingerprint_registry_sha256"]:
        raise ValueError("Frozen environment registry changed")
    if spec.goal_retrieval:
        from lean_tools import goal_retrieval
        artifact = config.get("retrieval_index")
        if not isinstance(artifact, dict):
            raise ValueError("Goal retrieval requires its host-prepared index")
        _, row = arena.load_task(Path(config["task"]))
        goal_retrieval.validate_prepared_index(
            artifact, row, Path(config["primary"]),
            fingerprint_registry=Path(config["fingerprint_registry"]))

    if spec.search_extensions:
        from lean_tools import proof_example_search
        artifact = config.get("examples_index")
        if not isinstance(artifact, dict):
            raise ValueError("Search extensions require their host-prepared source example index")
        _, row = arena.load_task(Path(config["task"]))
        fingerprint = arena.measurement_environment_fingerprint(
            row, Path(config["primary"]), registry_path=Path(config["fingerprint_registry"]))
        proof_example_search.validate_prepared_index(
            artifact, row, Path(config["primary"]), environment_fingerprint=fingerprint,
            source_roots=proof_example_search.default_source_roots(
                Path(config["primary"]), elan_home=Path(config["elan_home"])) if config.get("elan_home") else None)


@contextmanager
def _host_validation_cache(config: dict):
    """Agent-written candidate verdicts are advisory and cannot bless finalists."""
    runtime = RuntimeContext.resolve(Path(config["root"]), config)
    with scoped_environment({"LEAN_REFACTOR_EVALUATION_CACHE": str(runtime.validation_cache)}):
        yield


def _native_control_evidence(config: dict, row: dict, primary: dict) -> dict:
    """Bind a missing task-local baseline to the verified preparation original."""
    error = "Candidate lacks valid exact native-control evidence"
    original = config["initial_best"]
    try:
        _verify_incumbent(config, original)
        baseline = original["evaluation"]
        arena_policy = experiment_spec(config).scoring_policy == "arena-v1"
        control = _original_control_heartbeats(config)
        reference = config["original_heartbeats"] if arena_policy else control
        if (original["sha256"] != _digest(arena.render_candidate_scaffold(row))
                or original["tokens"] != _original_measurement_tokens(config)
                or original["heartbeats"] != control
                or baseline["task_id"] != config["task_id"]
                or baseline["valid"] is not True
                or baseline["measurement_mode"] != "exact"
                or baseline["axiom_status"] != "measured"
                or not isinstance(baseline["axioms"], list)
                or any(axiom not in arena.ALLOWED_AXIOMS for axiom in baseline["axioms"])
                or baseline["length"]["candidate_tokens"] != _original_measurement_tokens(config)
                or baseline["heartbeat"]["candidate"] != control
                or baseline["heartbeat"]["local_reference"] != reference
                or primary["measurement_mode"] != "exact"
                or primary["axiom_status"] != "measured"
                or not isinstance(primary["axioms"], list)
                or any(axiom not in arena.ALLOWED_AXIOMS for axiom in primary["axioms"])):
            raise ValueError(error)
        entry = arena.environment_fingerprint_registry_entry(
            row, Path(config["primary"]), Path(config["fingerprint_registry"]), validate_guard=True)
        if (baseline["heartbeat"]["environment_fingerprint"] != entry["fingerprint"]
                or primary["heartbeat"]["environment_fingerprint"] != entry["fingerprint"]):
            raise ValueError(error)
        if arena_policy:
            observed = config.get("observed_original_baseline")
            if (type(control) is not int or control <= 0
                    or baseline["length"]["original_tokens"] != config["original_tokens"]
                    or primary["length"]["original_tokens"] != config["original_tokens"]
                    or primary["heartbeat"]["local_reference"] != reference
                    or observed != {"source_sha256": original["sha256"], "tokens": original["tokens"],
                        "heartbeats": control, "environment_fingerprint": entry["fingerprint"],
                        "environment_guard_sha256": entry["guard_sha256"]}):
                raise ValueError(error)
    except (KeyError, TypeError) as cause:
        raise ValueError(error) from cause
    return {"source": "verified_preparation_original", "task_sha256": config["task_sha256"],
            "original_sha256": original["sha256"], "heartbeats": control,
            "environment_fingerprint": entry["fingerprint"],
            "environment_guard_sha256": entry["guard_sha256"]}


def finalize(config: dict, capsule: Path, previous_best: dict | None = None) -> dict:
    with _host_validation_cache(config):
        return _finalize(config, capsule, previous_best)


class _ValidationInfrastructureError(ValueError):
    """Validation could not establish a mathematical candidate verdict."""


def _validation_exception_is_infrastructure(error: BaseException) -> bool:
    if isinstance(error, (OSError, TimeoutError, KeyError, TypeError,
                          arena.LeanTimeoutError, _ValidationInfrastructureError)):
        return True
    if isinstance(error, arena.LeanCompileError):
        result = error.result
        code = result.returncode
        return result.timed_out or (type(code) is int and (code < 0 or code in {137, 143}))
    if isinstance(error, arena.WorkflowError):
        # These native axiom-audit rejections establish a candidate verdict.
        # Failure to parse or run that audit is instead missing evidence.
        message = str(error)
        return not ("axiom audit contains sorryAx" in message or "unexpected axiom dependencies:" in message)
    return False


def _validation_infrastructure_failure(evaluation: dict) -> bool:
    """Recognize structured tooling failures without rejecting compile verdicts.

    The native evaluator raises infrastructure exceptions. These markers also
    keep adapters that return their failure diagnostics from supplying plateau
    evidence; an ordinary ``valid=False`` is a mathematical search outcome.
    """
    infrastructure_types = {"TimeoutError", "LeanTimeoutError", "OSError", "FileNotFoundError",
                            "PermissionError", "WorkflowError", "CacheLockTimeout"}
    infrastructure_statuses = {"timeout", "timed_out", "infrastructure", "infrastructure_failure",
                               "infrastructure_error", "cache_lock_timeout"}
    def failed(value):
        if isinstance(value, dict):
            code = value.get("returncode")
            if ((type(code) is int and (code < 0 or code in {137, 143}))
                    or value.get("timed_out") is True or value.get("validation_healthy") is False
                    or value.get("infrastructure_error") is True
                    or value.get("error_kind") in infrastructure_statuses
                    or value.get("status") in infrastructure_statuses
                    or value.get("error_type") in infrastructure_types
                    or value.get("type") in infrastructure_types):
                return True
            return any(failed(item) for item in value.values())
        if isinstance(value, list):
            return any(failed(item) for item in value)
        return False
    return (not isinstance(evaluation, dict)
            or type(evaluation.get("valid")) is not bool or failed(evaluation))


def _finalize(config: dict, capsule: Path, previous_best: dict | None = None) -> dict:
    """Exact-measure this pass's unique finalists and retain a verified incumbent."""
    _verify_config(config)
    spec = experiment_spec(config)
    policy = _policy(config)
    incumbent = dict(previous_best or config["initial_best"])
    _verify_incumbent(config, incumbent)
    capsule = capsule.resolve()
    validation = capsule / "final-validation"
    validation.mkdir(exist_ok=False)
    _, row = arena.load_task(Path(config["task"]))
    paths = [capsule / "Candidate.lean", *sorted((capsule / "valid-candidates").glob("*.lean"))]
    records, unique = [], {}
    previously_verified = {incumbent["sha256"]}
    for path in paths:
        try:
            source = _source(path)
            declaration, _ = arena.extract_candidate_declaration(row, source)
            # The pinned public intake compares Python string length on the
            # submitted declaration, not UTF-8 bytes or the local scaffold.
            if len(declaration) > spec.candidate_intake_characters:
                raise ValueError(f"Submitted declaration exceeds the contest's {spec.candidate_intake_characters}-character intake limit")
            key = _digest(declaration)
            if key not in unique:
                unique[key] = (source, path)
        except (OSError, ValueError, arena.WorkflowError) as error:
            records.append({"origin": str(path), "valid": False, "error": str(error),
                            "error_type": type(error).__name__,
                            "error_kind": "infrastructure" if isinstance(error, OSError) else "candidate_invalid"})

    for declaration_sha, (source, origin) in unique.items():
        record = {**_incumbent_metadata(config), "origin": str(origin),
                  "declaration_sha256": declaration_sha, "sha256": _digest(source)}
        if record["sha256"] in previously_verified:
            records.append({**record, "status": "unchanged_verified_incumbent", "valid": True})
            continue
        candidate = validation / f"{declaration_sha}.lean"
        candidate.write_text(source, encoding="utf-8")
        try:
            primary = _check(config, candidate, Path(config["primary"]), timeout_seconds=spec.check_timeout_seconds)
            record["evaluation"] = primary
            if _validation_infrastructure_failure(primary):
                raise _ValidationInfrastructureError("Exact primary validation returned an infrastructure failure")
            if not primary.get("valid"):
                raise ValueError("Candidate failed exact primary validation")
            tokens, heartbeats = primary["length"]["candidate_tokens"], primary["heartbeat"]["candidate"]
            control = _original_control_heartbeats(config)
            if type(tokens) is not int or tokens < 0:
                raise _ValidationInfrastructureError("Candidate lacks valid exact token measurement")
            if type(heartbeats) is not int or heartbeats < 0:
                raise _ValidationInfrastructureError("Candidate lacks valid exact native-control evidence")
            reference = primary["heartbeat"]["local_reference"]
            if spec.scoring_policy == "arena-v1":
                try:
                    record["native_control_evidence"] = _native_control_evidence(config, row, primary)
                except ValueError as error:
                    raise _ValidationInfrastructureError(str(error)) from error
            elif reference != control:
                if reference is not None:
                    raise _ValidationInfrastructureError("Candidate lacks valid exact native-control evidence")
                # Frozen tasks can retain baselines from another platform. The
                # unchanged native original was verified during preparation;
                # require its exact evidence and current environment guard.
                try:
                    record["native_control_evidence"] = _native_control_evidence(config, row, primary)
                except ValueError as error:
                    raise _ValidationInfrastructureError(str(error)) from error
            optimistic = policy.score(tokens=tokens, heartbeats=heartbeats, compatibility_pct=100)
            if optimistic <= incumbent["score"]:
                records.append({**record, "valid": True, "status": "cannot_improve_verified_incumbent",
                                "optimistic_score": optimistic})
                continue
            compatibility = [{"environment": config["primary"], "passed": True}]
            for project in config["compatibility"]:
                check = _check(config, candidate, Path(project), quick=True, timeout_seconds=spec.check_timeout_seconds)
                infrastructure = _validation_infrastructure_failure(check)
                compatibility.append({"environment": project,
                    "passed": not infrastructure and bool(check.get("valid")), "evaluation": check})
                record["compatibility"] = compatibility
                if infrastructure:
                    raise _ValidationInfrastructureError("Compatibility validation returned an infrastructure failure")
            compatible = 100 * sum(item["passed"] for item in compatibility) / len(compatibility)
            score = policy.score(tokens=tokens, heartbeats=heartbeats, compatibility_pct=compatible)
            record.update(valid=True, status="verified", score=score, compatibility=compatibility,
                          compatibility_pct=compatible, compatibility_complete=True,
                          tokens=tokens, heartbeats=heartbeats)
            previously_verified.add(record["sha256"])
            if score > incumbent["score"]:
                incumbent = {**record, "source": source, "selected_path": str(candidate)}
        except (OSError, ValueError, KeyError, TypeError, arena.WorkflowError, TimeoutError) as error:
            infrastructure = _validation_exception_is_infrastructure(error)
            record.update(valid=False, status="validation_failed", error=str(error),
                          error_type=type(error).__name__,
                          error_kind="infrastructure" if infrastructure else "candidate_invalid")
        records.append(record)
    selected = capsule / "Selected.lean"
    selected.write_text(incumbent["source"], encoding="utf-8")
    incumbent["selected_path"] = str(selected)
    _write(capsule / "selection.json", {**incumbent, "candidate_records": records,
        "validation_healthy": not any(record.get("error_kind") == "infrastructure" for record in records),
        "original_tokens": config["original_tokens"], "original_heartbeats": config["original_heartbeats"],
        "unique_candidate_count": len(unique)})
    return incumbent
