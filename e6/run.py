"""Independent Sol 6.1 proof cells, fresh passes and one warm broker per proof."""
from __future__ import annotations

import argparse
from decimal import Decimal
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import traceback

from lean_tools import arena_workflow as arena
from lean_tools import feedback_workflow as feedback
from lean_tools import resource_gate, process_memory
from lean_tools import capsule as swarm
from . import broker_lifecycle
from . import pass_boundary
from lean_tools import codex_preflight
from .config import (REPO_ROOT as REPO, TOOLS_ROOT as SCRIPTS, MODEL, MODEL_CATALOG,
                     source_paths, codex_home, runs_root, runtime_root, configure_native_environment,
                     resolve_backend, resolve_auth_path, resolve_stopping_policy)
from .experiment import DEFAULT_SPEC, ExperimentSpec, experiment_spec, load_spec, resolve_spec, blocking_unknown_usage
from .runtime import RuntimeContext, create_environment_directories, queue_environment_names
from .signals import defer_termination, with_termination_cleanup
from .stopping import (ConvergenceTracker, policy_for_config, SCREENING_ATTEMPTS,
                       SCREENING_ATTEMPTED_BASIS, SCREENING_HEALTHY_BASIS,
                       screening_counted_passes, screening_pass_healthy)

HERE = Path(__file__).resolve().parent
DEFAULT_ROOT = runs_root() / "proof"
DEFAULT_CODEX_HOME = codex_home()
TOKEN_ENV = "LRH_SERIAL_MODEL_TOKEN"
BROKER_STARTUP_SECONDS = DEFAULT_SPEC.broker_startup_timeout_seconds
LEAN_REQUEST_SECONDS = DEFAULT_SPEC.lean_request_timeout_seconds
PRIVATE_HOST_ENV = ("E6_BASELINE_CACHE", "E6_BASELINE_SEEDS", "E6_EXAMPLES_INDEX_CACHE")


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def write(path, value):
    arena.write_json_atomic(Path(path), value)


def low_priority(spec=DEFAULT_SPEC):
    os.nice(max(0, spec.nice_priority - os.getpriority(os.PRIO_PROCESS, 0)))


def environment(root: Path, capsule: Path | None = None, *, config=None):
    # Admission delays consume neither proof time nor model budget. Do not
    # inherit finite queue deadlines from other experiments or the host shell.
    for name in queue_environment_names(os.environ):
        os.environ.pop(name, None)
    values = RuntimeContext.resolve(root, config).environment(capsule)
    create_environment_directories(values)
    os.environ.update(values)
    return values


def writable_roots(config: dict, capsule: Path):
    return list(swarm.agent_writable_roots(Path(config["primary"]), capsule))


def host_environment(config: dict, root: Path):
    """Restore trusted host tooling roots after the model capsule is retired."""
    values = environment(root, config=config)
    cache = config.get("launch_cache_root")
    if cache:
        os.environ["LEAN_REFACTOR_LAUNCH_CACHE"] = cache
        values["LEAN_REFACTOR_LAUNCH_CACHE"] = cache
    else:
        os.environ.pop("LEAN_REFACTOR_LAUNCH_CACHE", None)
    return values


def command(config: dict, capsule: Path, url: str):
    if config.get("agent_backend", "codex") == "pi":
        from . import pi
        return pi.command(config, capsule, url)
    if config.get("agent_backend", "codex") != "codex":
        raise ValueError("Unsupported E6 agent backend")
    spec = experiment_spec(config)
    writable = writable_roots(config, capsule)
    # The relay changes only transport/accounting; the native CLI retains its
    # tools and context behavior inside the host's Linux filesystem isolation.
    settings = {
        "model_provider": "serial_budget",
        "model_providers.serial_budget.name": "Serial budget meter",
        "model_providers.serial_budget.base_url": url,
        "model_providers.serial_budget.env_key": TOKEN_ENV,
        "model_providers.serial_budget.wire_api": "responses",
        "model_providers.serial_budget.requires_openai_auth": False,
        "model_providers.serial_budget.supports_websockets": False,
        "model_providers.serial_budget.stream_idle_timeout_ms": spec.native_stream_idle_timeout_ms,
        "model_reasoning_effort": spec.reasoning_effort,
        "service_tier": spec.service_tier,
        # Hosted search charges are not included in the token-usage meter.
        "web_search": "disabled",
        # Keep benchmark instructions independent of ambient project/user state.
        "project_doc_max_bytes": 0,
        # E6 is a serial single-agent experiment, including within each pass.
        "agents.enabled": False,
        # These tools can escape the shell sandbox through host integrations.
        "features.plugins": False,
        "features.apps": False,
        "features.browser_use": False,
        "features.computer_use": False,
        "features.skip_host_skill_discovery": True,
        # The loopback relay accepts JSON over HTTP/SSE, not zstd/WebSockets.
        "features.enable_request_compression": False,
        "shell_environment_policy.set.LEAN_NUM_THREADS": str(spec.lean_threads),
        "shell_environment_policy.set.OMP_NUM_THREADS": str(spec.omp_threads),
        "shell_environment_policy.set.LEAN_REFACTOR_SCORING_POLICY": spec.scoring_policy,
        "shell_environment_policy.exclude": [TOKEN_ENV, "OPENAI_API_KEY", "OPENROUTER_API_KEY"],
        # Refactoring tools use the warm loopback service. Statement-first
        # passes use local cold tools, so their shell needs no network access.
        # This setting does not restrict the CLI's model relay transport.
        "sandbox_workspace_write.network_access": spec.rerank_config is not None or not (
            spec.first_pass_reprove and capsule.name == "pass-001"),
    }
    if config.get("model_catalog"):
        settings["model_catalog_json"] = config["model_catalog"]
    args = [str(config["codex"]), "exec", "--ephemeral", "--ignore-user-config", "--ignore-rules",
            "--skip-git-repo-check", "--json", "--color", "never",
            "-c", 'approval_policy="never"', "--sandbox", "workspace-write",
            *(argument for path in writable for argument in ("--add-dir", str(path))),
            *feedback.codex_config_args(capsule)]
    if (capsule / feedback.CONFIG_NAME).exists():
        # MCP's filtered environment does not inherit these thread settings.
        settings["mcp_servers.lean_feedback.env.LEAN_NUM_THREADS"] = str(spec.lean_threads)
        settings["mcp_servers.lean_feedback.env.OMP_NUM_THREADS"] = str(spec.omp_threads)
        settings["mcp_servers.lean_feedback.env.LEAN_REFACTOR_SCORING_POLICY"] = spec.scoring_policy
        # The documented shell wrappers remain available if this convenience
        # adapter cannot start. MCP startup must not abort the native pass.
        settings["mcp_servers.lean_feedback.required"] = False
    for key, value in settings.items():
        args.extend(["-c", f"{key}={json.dumps(value)}"])
    args.extend(["--model", spec.model, "--cd", str(capsule), "--output-last-message",
                 str(capsule / "codex-final.txt"), "-"])
    return args


def progress(root, state, **updates):
    state.update(updates, updated_at=arena.utc_now())
    write(root / "state.json", state)


def optimize_pass_result(config, root, capsule, best, selection):
    """Publish a host-only optimization without losing the raw agent selection.

    Called only after the CLI is gone, broker credentials are retired, and
    native pass validation is healthy. Subsequent capsules receive exactly
    this selected source and its matching measurements through best.json.
    """
    from . import deterministic, proof
    directory = root / "deterministic" / capsule.name
    directory.mkdir(parents=True, exist_ok=True)
    raw_selection = directory / "agent-selection.json"
    if not raw_selection.exists():
        write(raw_selection, selection)
    else:
        saved = read(raw_selection)
        if saved["sha256"] != best["sha256"]:
            raise ValueError("Deterministic boundary input differs from saved agent selection")
    before = {name: best.get(name) for name in ("sha256", "score", "tokens", "heartbeats", "compatibility_pct")}
    try:
        optimized, report = deterministic.optimize(config, capsule, best)
        proof._verify_incumbent(config, optimized)
        if optimized["score"] < best["score"]:
            raise ValueError("Deterministic optimization regressed the verified incumbent")
        best = optimized
    except Exception as error:
        report = {"status": "failed_retained_incumbent", "error": f"{type(error).__name__}: {error}",
                  "model_calls": 0}
    report = {**report, "before": before,
              "after": {name: best.get(name) for name in before},
              "agent_selection_path": str(raw_selection)}
    write(directory / "boundary.json", report)
    # The host selection and pass record must agree for exports and explicit
    # recovery. Agent candidate records and the original selection are retained.
    selected = capsule / "Selected.lean"
    selected.write_text(best["source"], encoding="utf-8")
    best = {**best, "selected_path": str(selected)}
    selection = {**selection, **best, "deterministic_refactoring": report}
    write(capsule / "selection.json", selection)
    return best, selection, report


def finish_host_stop(root, state, request, *, completed_pass, best, budget):
    record = pass_boundary.stopped_record(request, completed_pass=completed_pass,
        candidate_sha256=best["sha256"], budget=budget)
    progress(root, state, status="host_requested_stop", finished_at=arena.utc_now(),
             stop_reason=request["reason"], host_stop=record, agent_pid=None,
             stop_detail=f"Operator requested stop after finalized pass {completed_pass}")
    write(root / pass_boundary.RESULT_NAME, record)


def execute_pass(config, root, capsule, relay, state):
    """Launch one fresh solo pass through the frozen relay policy."""
    spec = experiment_spec(config)
    relay.set_pass(state["pass_number"])
    prompt = (capsule / "prompt.md").read_text(encoding="utf-8")
    pass_mode = spec.pass_mode(state["pass_number"])
    argv = command(config, capsule, relay.url)
    backend = config.get("agent_backend", "codex")
    recorded_argv = argv if backend == "pi" else argv[:-1]
    write(capsule / "invocation.json", {"command": recorded_argv + ["<prompt on stdin>"],
          "agent_backend": backend,
          "model": spec.model, "reasoning_effort": spec.reasoning_effort, "pass_mode": pass_mode,
          "pass_timeout_seconds": spec.pass_timeout_seconds,
          "native_stream_idle_timeout_ms": spec.native_stream_idle_timeout_ms,
          "pending_usage_settlement_seconds": spec.pending_usage_settlement_seconds,
          "started_at": arena.utc_now(), "deadline_epoch": None,
          "priority": spec.priority, "fresh_ephemeral": True})
    child_env = dict(os.environ)
    child_env[TOKEN_ENV] = relay.token
    if backend == "codex":
        child_env["CODEX_HOME"] = config["codex_home"]
    child_env["LEAN_REFACTOR_LAUNCH_CACHE"] = str(capsule / "launch-cache")
    for name in (*PRIVATE_HOST_ENV, "E6_CODEX_HOME", "OPENAI_API_KEY", "OPENROUTER_API_KEY"):
        child_env.pop(name, None)
    # Capabilities belong to a single fresh pass. Ambient selector settings
    # cannot enable or redirect inference in a frozen baseline experiment.
    for name in ("LEAN_REFACTOR_RERANK_URL", "LEAN_REFACTOR_RERANK_TOKEN", "LEAN_REFACTOR_RERANK_CONFIG"):
        child_env.pop(name, None)
    if pass_mode == "statement_first_reprove":
        # The host broker accepts Lean metaprograms with host filesystem IO.
        # Withhold every capability so the first pass uses only its isolated
        # local compiler, even when a normal broker is already prewarmed.
        for name in broker_lifecycle.BROKER_ENV:
            child_env.pop(name, None)
    outcome = {"status": "running", "started_at": arena.utc_now(), "pass_mode": pass_mode}
    cost_metering = policy_for_config(config) == "cost"
    request_field = "metered_responses" if cost_metering and not config.get("product_schema_version") else "dispatched_requests"
    requests_before = relay.status()[request_field]
    process = None
    decision_service = None
    with (capsule / f"{backend}-events.jsonl").open("w", encoding="utf-8") as stdout, \
            (capsule / f"{backend}-stderr.log").open("w", encoding="utf-8") as stderr:
        try:
            if spec.rerank_config is not None:
                from .decision_service import DecisionService
                decision_service = DecisionService.for_pass(config, capsule, relay, spec.rerank_config)
                decision_service.__enter__()
                child_env.update(decision_service.environment())
            from .isolation import wrap_command
            writable = writable_roots(config, capsule)
            argv, child_env = wrap_command(config, capsule, argv, writable, child_env)
            with defer_termination():
                process = subprocess.Popen(argv, cwd=capsule, stdin=subprocess.PIPE,
                    stdout=stdout, stderr=stderr, text=True, encoding="utf-8", env=child_env,
                    start_new_session=True)
                process_memory.capture_process_identity(process)
            progress(root, state, status="running", agent_pid=process.pid,
                     deadline_epoch=None, capsule=str(capsule))
            process.stdin.write(prompt)
            process.stdin.close()
            while process.poll() is None:
                budget = relay.status()
                progress(root, state, budget=budget)
                reason = relay.stop_reason
                if reason:
                    outcome["status"] = reason
                    arena.terminate_process_tree(process)
                    break
                time.sleep(1)
            process.wait(timeout=30)
            outcome["returncode"] = process.returncode
            if outcome["status"] == "running":
                outcome["status"] = "completed" if process.returncode == 0 else "failed"
                outcome["native_status"] = outcome["status"]
                if spec.pending_usage_settlement_seconds > 0:
                    progress(root, state, status="settling_pending_usage", agent_pid=None, budget=relay.status())
                    settlement = relay.drain_pending(spec.pending_usage_settlement_seconds)
                    outcome["pending_usage_settlement"] = settlement
                    budget = relay.status()
                    settled = (settlement["active_requests_before"] > 0
                               and settlement["status"] == "settled"
                               and settlement.get("newly_completed_requests", settlement.get("newly_metered_responses", 0)) > 0)
                    accounted = (not cost_metering or (settlement["newly_metered_responses"] > 0
                                 and Decimal(settlement["settled_cost_usd"]) > 0
                                 and spec.pass_exclusion(budget) is None
                                 and Decimal(budget["spent_usd"]) < spec.cumulative_budget_usd))
                    if process.returncode != 0 and settled and accounted and not relay.stop_reason:
                        # Preserve native failure evidence. The host can salvage
                        # a checkpoint for a fresh pass, but this turn is never
                        # healthy convergence evidence and is not resubmitted.
                        outcome["status"] = "accounted_disconnect"
                    elif settlement["status"] == "timed_out":
                        outcome["status"] = "failed"
                        outcome["error"] = "Pending transport requests did not settle within the frozen grace period"
            if outcome["status"] == "completed" and relay.status()[request_field] == requests_before:
                kind = "metered" if cost_metering else "dispatched"
                raise RuntimeError(f"Agent completed without a {kind} request; refusing unaccounted continuation")
        except BaseException as error:
            status = "interrupted" if isinstance(error, (KeyboardInterrupt, SystemExit)) else "failed"
            outcome.update(status=status, error=f"{type(error).__name__}: {error}")
            outcome.setdefault("native_status", status)
            raise
        finally:
            if process is not None:
                if process.poll() is None:
                    arena.terminate_process_tree(process)
                    try:
                        process.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        process.kill()
                        process.wait(timeout=10)
                outcome["returncode"] = process.returncode
            if decision_service is not None:
                decision_service.__exit__(None, None, None)
            outcome.update(finished_at=arena.utc_now(), budget=relay.status())
            write(capsule / "agent-run.json", outcome)
    return outcome


def prepare(root, label, *, backend=None, spec: ExperimentSpec | None = None, stopping_policy=None):
    from . import proof
    if (root / "config.json").exists():
        raise RuntimeError("Existing experiment: use a new --root; never reset a budget")
    backend = resolve_backend(root, backend)
    spec = resolve_spec(root, spec, stopping_policy)
    if backend == "pi":
        from . import pi
        pi.validate_settings(spec.proof_settings())
    configure_native_environment()
    low_priority(spec)
    environment(root, config=spec.proof_settings())
    config = proof.prepare(root, label, backend=backend, spec=spec)
    freeze_prepared(root, config)


def validate_codex_home(path: Path):
    """Reuse only a dedicated panel runtime; ephemeral CLI never loads its history."""
    path = path.resolve()
    if path == (Path.home() / ".codex").resolve():
        raise RuntimeError("E6_CODEX_HOME must be a dedicated panel runtime, not the user's Codex home")
    if not path.is_dir() or (path / "auth.json").exists():
        raise RuntimeError("Dedicated panel CODEX_HOME must exist without account authentication")
    for name in ("sessions", "archived_sessions"):
        if (path / name).exists() and any((path / name).iterdir()):
            raise RuntimeError("Dedicated panel CODEX_HOME contains prior session files")
    return path


def source_hashes(prompt_variant="control-efficient-v1"):
    """Pin native runtime, evaluator, transport, tasks and frozen metadata."""
    return {str(path): arena.sha256_file(path) for path in source_paths(prompt_variant)}


def tool_preflight(root, config, *, output_root=None):
    """Exercise only native CLI metadata/config and MCP initialize/tools-list."""
    spec = experiment_spec(config)
    output_root = root if output_root is None else Path(output_root)
    capsule = output_root / "preparation" / "cli-preflight"
    swarm.prepare_capsule(capsule, Path(config["task"]), root / "proof-guide.md",
                          config["initial_best"]["source"],
                          fingerprint_registry=Path(config["fingerprint_registry"]))
    feature_settings = {name: True for name in ("unfinished_cases", "regional_profiler") if getattr(spec, name)}
    if spec.candidate_batches or spec.goal_retrieval:
        feature_settings.update(candidate_batches=spec.candidate_batches, goal_retrieval=spec.goal_retrieval)
    if spec.goal_retrieval:
        feature_settings.update(retrieval_index=Path(config["retrieval_index"]["path"]),
                                retrieval_index_sha256=config["retrieval_index"]["sha256"],
                                retrieval_pool_mode=spec.retrieval_pool_mode)
    if spec.search_extensions:
        feature_settings.update(search_extensions=True,
            examples_index=Path(config["examples_index"]["path"]),
            examples_index_sha256=config["examples_index"]["sha256"],
            examples_index_identity=config["examples_index"]["identity"])
    feature_settings.update(compatibility_roots=[Path(path) for path in config["compatibility"]],
        original_tokens=config["original_tokens"], original_heartbeats=config["original_heartbeats"],
        incumbent_score=config["initial_best"]["score"])
    if spec.scoring_policy != "legacy-v1":
        feature_settings["scoring_policy"] = spec.scoring_policy
    feedback.configure_capsule(capsule, Path(config["primary"]), spec.lean_request_timeout_seconds,
                              **feature_settings)
    report = output_root / "tool-preflight.json"
    if config.get("agent_backend", "codex") == "pi":
        from . import pi
        pi.preflight(config, capsule, report)
        return report
    try:
        options = ({"provider": "openrouter", "model_catalog": Path(config["model_catalog"])}
            if config.get("product_schema_version") else {})
        codex_preflight.preflight(Path(config["codex"]), [(spec.model, spec.reasoning_effort)], capsule,
            output=report, **options)
    except codex_preflight.PreflightError as error:
        diagnostic = error.report
        if not diagnostic or diagnostic.get("failed_stage") != "stdio_schema":
            raise
        # Keep the original failed test result. Only MCP startup/schema is
        # optional; native version, model metadata, and scope checks passed.
        diagnostic.update(optional_mcp_status="failed", E6_preparation_allowed=True,
            E6_preparation_note="Optional MCP initialize/tools-list failed; documented shell feedback wrappers remain available")
        write(report, diagnostic)
    return report


def preflight_acceptable(report):
    return report.get("status") == "passed" or (
        report.get("status") == "failed"
        and report.get("failed_stage") == "stdio_schema"
        and report.get("optional_mcp_status") == "failed"
        and report.get("E6_preparation_allowed") is True
    )


def freeze_prepared(root, config):
    """Freeze runtime metadata after proof preparation and offline tool checks."""
    if (root / "run.claim").exists():
        raise RuntimeError("Cannot change a started experiment")
    spec = experiment_spec(config)
    runtime = RuntimeContext(root, spec)
    catalog = read(MODEL_CATALOG)
    model_row = next((item for item in catalog["models"] if item.get("slug") == spec.model), None)
    if model_row is None or spec.reasoning_effort not in {item["effort"] for item in model_row["supported_reasoning_levels"]}:
        raise RuntimeError(f"Frozen native model catalog has no verified {spec.model_display_name} {spec.reasoning_effort} metadata")
    # Custom providers otherwise use generic fallback instructions/tool shapes.
    # Preserve exactly the installed Codex model's native catalog entry.
    model_catalog = root / "model-catalog.json"
    write(model_catalog, {"models": [model_row]})
    backend = resolve_backend(root, config.get("agent_backend", "codex"))
    config.update(agent_backend=backend, model_catalog=str(model_catalog))
    if backend == "pi":
        from . import pi
        pi.validate_settings(config)
        pi.verify_runtime(config)
    else:
        # Reuse the already provisioned dedicated clean home as OS setup only.
        # No user's auth/settings/sessions are copied or loaded.
        home = Path(os.environ.get("E6_CODEX_HOME", str(DEFAULT_CODEX_HOME))).expanduser().resolve()
        home.mkdir(parents=True, exist_ok=True)
        home = validate_codex_home(home)
        config.update(codex_sha256=arena.sha256_file(Path(config["codex"])), codex_home=str(home),
                      codex_home_scope="dedicated clean Linux runtime home; no auth/session loads; fresh ephemeral contexts")
    preflight = tool_preflight(root, config)
    config.update(model_catalog=str(model_catalog), model_catalog_sha256=arena.sha256_file(model_catalog),
                  model_catalog_observed_at=catalog.get("fetched_at"),
                  tool_preflight=str(preflight), tool_preflight_sha256=arena.sha256_file(preflight))
    config["agent_home_scope"] = ("private empty capsule home; no host auth/settings/history; fresh in-memory Pi contexts"
                                  if backend == "pi" else config["codex_home_scope"])
    config.update(spec.proof_settings())
    from .resume import RECOVERY_POLICY
    config["native_failure_recovery"] = dict(RECOVERY_POLICY)
    config.update(agent_launch_cache_policy="private capsule/launch-cache; shared trusted host cache is never writable by a model pass",
                  host_validation_cache_root=str(runtime.validation_cache),
                  launch_cache_root=(str(Path(os.environ["LEAN_REFACTOR_LAUNCH_CACHE"]).resolve())
                    if os.environ.get("LEAN_REFACTOR_LAUNCH_CACHE") else None),
                  shared_gates=runtime.shared_gates(),
                  warm_broker_policy="one host process per proof; canonical reset and capability rotation before every fresh pass; host-owned telemetry",
                  experiment_shape=(f"up to {spec.proof_cell_capacity} independent proof cells; serial fresh solo {backend} passes of original {config['label']} proof"
                    + ("; first pass reproves from a statement-only view, subsequent passes refactor the verified incumbent" if spec.first_pass_reprove else
                       "; first pass rebuilds an unfinished candidate with the original proof as reference and resident warm feedback; subsequent passes refactor the verified incumbent" if spec.first_pass_reference_rebuild else "")),
                  started_from=("canonical theorem statement and legal context; private verified original fallback; no previous refactor"
                    if spec.first_pass_reprove else
                    "unfinished candidate with canonical original proof reference and verified original fallback; normal source visibility and resident warm feedback; no previous refactor"
                    if spec.first_pass_reference_rebuild else "canonical original contest task; no previous refactor"),
                  selection_policy=spec.selection_policy,
                  concurrent_experiment=f"up to {spec.proof_cell_capacity} independent E6 proof cells share the Lean queue")
    config["source_hashes"] = source_hashes(spec.prompt_variant)
    write(root / "config.json", config)
    write(root / "state.json", {"status": "prepared", "root": str(root), "passes": [],
                               **spec.common_settings(), "updated_at": arena.utc_now()})
    print(f"Prepared {root}", flush=True)


def run(root, auth_path, *, resume_id=None):
    from . import proof
    from .billing import BudgetRelay
    config = read(root / "config.json")
    spec = experiment_spec(config)
    stopping_policy = policy_for_config(config)
    cost_metering = stopping_policy == "cost"
    healthy_screen = stopping_policy == "screening" and spec.screening_count_basis == SCREENING_HEALTHY_BASIS
    configure_native_environment(elan_home=config.get("elan_home"))
    for path, expected in config["source_hashes"].items():
        if arena.sha256_file(Path(path)) != expected:
            raise RuntimeError(f"Prepared runner changed: {path}")
    if arena.sha256_file(Path(config["model_catalog"])) != config["model_catalog_sha256"]:
        raise RuntimeError("Prepared native model catalog changed")
    backend = resolve_backend(root)
    if backend == "pi":
        from . import pi
        pi.validate_settings(config)
        pi.verify_runtime(config)
    elif arena.sha256_file(Path(config["codex"])) != config["codex_sha256"]:
        raise RuntimeError("Prepared Codex executable changed")
    if (arena.sha256_file(Path(config["tool_preflight"])) != config["tool_preflight_sha256"]
            or not preflight_acceptable(read(config["tool_preflight"]))):
        raise RuntimeError("Prepared offline tool preflight changed or failed")
    if backend == "codex":
        validate_codex_home(Path(config["codex_home"]))
    receipt = None
    if resume_id is None:
        if read(root / "state.json")["status"] != "prepared":
            raise RuntimeError("Run already started; choose a fresh root or explicitly prepare a resume receipt")
        # Ordinary runs retain exclusive, fresh-only admission.
        with (root / "run.claim").open("x") as claim:
            claim.write(str(os.getpid()))
        state = {"status": "starting", "pid": os.getpid(), "started_at": arena.utc_now(),
                 "root": str(root), "agent_backend": backend,
                 "model": spec.model, "reasoning_effort": spec.reasoning_effort, "passes": [],
                 **spec.common_settings()}
        best = dict(config["initial_best"])
        tracker = ConvergenceTracker(best["score"], config.get("convergence")) if stopping_policy == "convergence" else None
        pass_number = 0
        billing_root = root / "billing"
        prior_budget = None
        state["telemetry_epochs"] = [{"epoch": "initial", "billing_root": str(billing_root),
                                      "counter_scope": "process"}]
    else:
        from .resume import admit
        state, best, tracker, receipt = admit(root, resume_id, config)
        pass_number = len(state["passes"])
        prior_budget = dict(state.get("budget", {}))
        billing_root = root / "resumes" / resume_id / "billing"
        state.setdefault("resume_history", []).append({"continuation_id": resume_id,
            "receipt_path": receipt["receipt_path"], "prior_status": state["status"],
            "next_pass_number": pass_number + 1, "best_sha256": best["sha256"],
            "resumed_at": arena.utc_now()})
        state.setdefault("telemetry_epochs", [{"epoch": "initial", "billing_root": str(root / "billing"),
                                              "counter_scope": "process"}]).append(
            {"epoch": resume_id, "billing_root": str(billing_root), "counter_scope": "process",
             "prior_counters": {key: prior_budget.get(key, 0) for key in (
                 "request_count", "dispatched_requests", "completed_requests", "metered_responses")}})
        for name in ("finished_at", "error", "stop_reason", "stop_detail", "broker_cleanup_error", "host_stop"):
            state.pop(name, None)
        state.update(status="starting", pid=os.getpid(), agent_pid=None,
                     resume_id=resume_id, resumed_at=arena.utc_now())
    low_priority(spec)
    state["pass_boundary_control"] = pass_boundary.runner_control(os.getpid())
    with pass_boundary.admission_lock(root):
        pass_boundary.archive_prior_request(root, state["pass_boundary_control"])
    if config.get("policy_epochs"):
        state["policy_epochs"] = config["policy_epochs"]
    if spec.max_passes is not None:
        state["max_passes"] = spec.max_passes
    progress(root, state)
    public_best = {k: v for k, v in best.items() if k != "source"}
    if receipt is None:
        shutil.copyfile(best["selected_path"], root / "Selected.lean")
        write(root / "best.json", public_best)
    progress(root, state, best=public_best, best_score=best["score"],
             official_pass=state.get("official_pass", 0),
             official_cost_usd=state.get("official_cost_usd", "0" if cost_metering else None), task_id=config.get("task_id"),
             convergence=tracker.snapshot() if tracker else None)
    broker = None
    relay = None
    try:
        # A policy amendment may confirm convergence from already verified
        # historical passes. It requires no broker, capsule, or inference.
        if tracker and tracker.snapshot()["should_stop"]:
            progress(root, state, status="diminishing_returns", finished_at=arena.utc_now(),
                     stop_detail="Verified historical passes confirm convergence under the admitted policy epoch")
            return 0
        host_environment(config, root)
        progress(root, state, status="waiting_broker_startup", agent_pid=None)
        with resource_gate.permit_from_environment(
            "broker_startup", priority=spec.lean_priority, timeout_seconds=spec.queue_timeout_seconds,
            metadata={"purpose": "e6-initial-prewarm", "root": str(root), "label": config["label"]},
        ) as lease:
            progress(root, state, status="starting_broker", broker_startup_queue_wait_seconds=lease.queue_wait_seconds)
            broker = broker_lifecycle.BrokerHost(config, root,
                startup_timeout_seconds=spec.broker_startup_timeout_seconds, request_timeout_seconds=spec.lean_request_timeout_seconds)
            broker.start()
        progress(root, state, broker=broker.status(), status="broker_ready")
        relay_options = {"backend": "pi", "pi_runtime": config} if backend == "pi" else {}
        if not cost_metering:
            relay_options["metering"] = False
        with BudgetRelay(billing_root, auth_path, cap=spec.cumulative_budget_usd,
                         spec=spec, **relay_options) as relay:
            if prior_budget is not None:
                from .resume import CumulativeTelemetryRelay
                relay = CumulativeTelemetryRelay(relay, prior_budget, resume_id)
            consecutive_recoveries = 0
            while True:
                with pass_boundary.admission_lock(root):
                    request = pass_boundary.cooperative_request(root, state, pass_number)
                    if request is not None:
                        finish_host_stop(root, state, request, completed_pass=pass_number,
                                         best=best, budget=relay.status())
                        break
                    pass_number += 1
                    capsule = root / f"pass-{pass_number:03d}"
                    before = relay.status()
                    # Publish admission under the same lock as operator request
                    # registration, before doing potentially lengthy setup.
                    progress(root, state, status="preparing_pass", pass_number=pass_number,
                             capsule=str(capsule), pass_mode=spec.pass_mode(pass_number),
                             best_score=best["score"], budget=before, agent_pid=None)
                remaining = float(before["remaining_usd"]) if cost_metering else None
                source = best["source"]
                capsule = proof.make_capsule(root, pass_number, source, remaining)
                environment(root, capsule, config=config)
                os.environ.update(broker.begin_pass(pass_number))
                progress(root, state, broker=broker.status())
                try:
                    outcome = execute_pass(config, root, capsule, relay, state)
                finally:
                    # The CLI child has terminated before credentials are revoked.
                    # Keep the resident Lean server alive through cold validation.
                    broker.end_pass()
                    for name in broker_lifecycle.BROKER_ENV:
                        os.environ.pop(name, None)
                    host_environment(config, root)
                budget = relay.status()
                if not cost_metering and relay.stop_reason and outcome["status"] == "completed":
                    outcome["status"] = relay.stop_reason
                spent = Decimal(budget["spent_usd"]) if cost_metering else None
                exclusion = spec.pass_exclusion(budget) if cost_metering else None
                eligible = exclusion is None
                validation_healthy = False
                deterministic_report = None
                if eligible:
                    progress(root, state, status="validating_pass", agent_pid=None, budget=budget)
                    # A failed native pass can still leave a verified checkpoint.
                    # Only healthy completed passes provide convergence evidence.
                    best = proof.finalize(config, capsule, best)
                    selection = read(capsule / "selection.json")
                    validation_healthy = selection.get("validation_healthy") is True
                    native_completed = (outcome["status"] == "completed"
                                        and outcome.get("native_status", outcome["status"]) == "completed")
                    if spec.deterministic_refactoring and validation_healthy and native_completed:
                        progress(root, state, status="optimizing_pass", agent_pid=None,
                                 deterministic_input_sha256=best["sha256"],
                                 deterministic_input_score=best["score"])
                        best, selection, deterministic_report = optimize_pass_result(
                            config, root, capsule, best, selection)
                    shutil.copyfile(best["selected_path"], root / "Selected.lean")
                    public_best = {k: v for k, v in best.items() if k != "source"}
                    write(root / "best.json", public_best)
                    state.update(official_pass=pass_number,
                                 official_cost_usd=budget["spent_usd"] if cost_metering else None)
                else:
                    # Keep the entire capsule as audit evidence, without promoting
                    # any candidate or checkpoint from an ineligible pass.
                    write(capsule / "exclusion.json", {
                        "pass_number": pass_number, "selection_eligible": False,
                        "exclusion_reason": exclusion, "agent_status": outcome["status"],
                        "budget": budget, "official_pass": state["official_pass"],
                        "official_candidate_sha256": best["sha256"],
                        "recorded_at": arena.utc_now()})
                convergence = tracker.observe(best["score"],
                    healthy=(outcome["status"] == "completed"
                             and outcome.get("native_status", outcome["status"]) == "completed"
                             and validation_healthy), pass_number=pass_number) if tracker else None
                recovery = None
                if (not cost_metering and validation_healthy and not relay.stop_reason
                        and (outcome["status"] == "failed"
                             or (healthy_screen and outcome["status"] == "accounted_disconnect"))
                        and type(outcome.get("returncode")) is int and outcome["returncode"] != 0):
                    from . import billing
                    from .resume import RECOVERY_POLICY
                    if config.get("native_failure_recovery") == RECOVERY_POLICY:
                        classify = getattr(billing, "classify_retryable_native_failure", None)
                        evidence = classify(capsule, billing_root, pass_number) if classify else None
                        if evidence:
                            consecutive_recoveries += 1
                            recovery = {"classification": evidence,
                                "consecutive_failed_passes": consecutive_recoveries,
                                "max_consecutive_fresh_retries": RECOVERY_POLICY["max_consecutive_fresh_retries"],
                                "decision": "retry" if consecutive_recoveries <= RECOVERY_POLICY["max_consecutive_fresh_retries"] else "exhausted"}
                elif outcome["status"] == "completed" and validation_healthy:
                    consecutive_recoveries = 0
                pass_record = {"pass_number": pass_number, "pass_mode": spec.pass_mode(pass_number), "agent_status": outcome["status"],
                                        "native_status": outcome.get("native_status", outcome["status"]),
                                        "native_returncode": outcome.get("returncode"),
                                        "pending_usage_settlement": outcome.get("pending_usage_settlement"),
                                        "best_score": best["score"], "candidate_sha256": best["sha256"],
                                        "selection_eligible": eligible, "exclusion_reason": exclusion,
                                        "validation_healthy": validation_healthy,
                                        "native_failure_recovery": recovery,
                                        "convergence": convergence,
                                        "pass_cost_usd": str(spent - Decimal(before["spent_usd"])) if cost_metering else None,
                                        "official_cost_usd": state["official_cost_usd"],
                                        "budget": budget, "finished_at": arena.utc_now()}
                if deterministic_report is not None:
                    pass_record["deterministic_refactoring"] = deterministic_report
                if spec.attempt_memory and eligible and validation_healthy:
                    from . import attempt_memory
                    from .experiment import ATTEMPT_MEMORY_V2
                    if native_completed or (spec.attempt_memory_policy == ATTEMPT_MEMORY_V2
                                             and attempt_memory.eligible_pass(pass_record, config)):
                        attempt_memory.record_pass(root, capsule, config, selection, pass_record=pass_record)
                state["passes"].append(pass_record)
                progress(root, state, best_score=best["score"], best=public_best, budget=budget,
                         broker=broker.status(), agent_pid=None, convergence=convergence)
                report = (f"Pass {pass_number}: {outcome['status']}; eligible={eligible}; "
                          f"official score {best['score']:.4f}")
                if cost_metering:
                    report += (f"; total spent ${budget['spent_usd']}; "
                               f"eligible cost ${state['official_cost_usd']}")
                elif tracker:
                    report += f"; convergence {convergence['status']}"
                else:
                    counted = screening_counted_passes(state["passes"], spec.screening_count_basis)
                    report += f"; screening {counted}/{SCREENING_ATTEMPTS} {spec.screening_count_basis}; attempts={pass_number}"
                print(report, flush=True)
                if cost_metering and (budget["unknown_requests"] or budget["active_requests"]):
                    progress(root, state, status="unknown_usage", finished_at=arena.utc_now())
                    break
                if cost_metering and spent >= spec.cumulative_budget_usd:
                    progress(root, state, status="budget_reached", finished_at=arena.utc_now(),
                             stop_detail=f"Reported usage reached the ${spec.budget_text} threshold; only settled known-usage passes within budget are eligible")
                    break
                if relay.stop_reason:
                    progress(root, state, status=relay.stop_reason, finished_at=arena.utc_now())
                    break
                with pass_boundary.admission_lock(root):
                    request = pass_boundary.cooperative_request(root, state, pass_number)
                    if request is not None and validation_healthy:
                        finish_host_stop(root, state, request, completed_pass=pass_number,
                                         best=best, budget=budget)
                        break
                if stopping_policy == "screening" and spec.screening_count_basis == SCREENING_ATTEMPTED_BASIS:
                    # Preserve frozen v1 screens, including failed attempts.
                    if pass_number >= SCREENING_ATTEMPTS:
                        progress(root, state, status="completed", finished_at=arena.utc_now(),
                                 stop_reason="screening_attempt_cap",
                                 stop_detail="Five attempted passes finalized; comparative screening requires explicit matched controls")
                        break
                    progress(root, state, status="screening_next_attempt", agent_pid=None)
                    continue
                if (recovery and recovery["decision"] == "retry"
                        and (healthy_screen or spec.max_passes is None or pass_number < spec.max_passes)):
                    progress(root, state, status="retrying_upstream_failure", agent_pid=None,
                             stop_detail="Verified transient upstream terminal failure; checkpoint retained and next fresh pass starts")
                    print(f"Pass {pass_number}: starting fresh recovery pass ({consecutive_recoveries}/"
                          f"{recovery['max_consecutive_fresh_retries']})", flush=True)
                    continue
                if outcome["status"] not in {"completed", "accounted_disconnect"}:
                    progress(root, state, status=outcome["status"], finished_at=arena.utc_now(),
                             **({"stop_detail": "Bounded fresh-pass upstream recovery exhausted"} if recovery else {}))
                    break
                if not cost_metering and not validation_healthy:
                    progress(root, state, status="failed", finished_at=arena.utc_now(),
                             stop_detail="Host candidate validation encountered an infrastructure failure")
                    break
                if healthy_screen:
                    if not screening_pass_healthy(pass_record):
                        progress(root, state, status="failed", finished_at=arena.utc_now(),
                                 stop_detail="Native pass did not complete successfully; explicit recovery is required")
                        break
                    if screening_counted_passes(state["passes"], spec.screening_count_basis) >= SCREENING_ATTEMPTS:
                        progress(root, state, status="completed", finished_at=arena.utc_now(),
                                 stop_reason="screening_healthy_pass_cap",
                                 stop_detail="Five completed healthy passes finalized; comparative screening is advisory and continuation requires a new explicit experiment")
                        break
                    progress(root, state, status="screening_next_attempt", agent_pid=None)
                    continue
                if tracker and convergence["should_stop"]:
                    progress(root, state, status="diminishing_returns", finished_at=arena.utc_now(),
                             stop_detail="Healthy fresh passes confirmed diminishing score gains")
                    break
                if spec.max_passes is not None and pass_number >= spec.max_passes:
                    progress(root, state, status="completed", finished_at=arena.utc_now(),
                             stop_reason="max_passes_reached",
                             stop_detail=f"Configured max_passes={spec.max_passes} reached after finalizing and accounting pass {pass_number}")
                    break
                # Uncapped runs continue with a fresh solo agent seeing the incumbent.
    except BaseException as error:
        progress(root, state, status="interrupted" if isinstance(error, KeyboardInterrupt) else "failed",
                 error=f"{type(error).__name__}: {error}", finished_at=arena.utc_now())
        traceback.print_exc()
        return 1
    finally:
        if broker is not None:
            try:
                broker.close()
            except BaseException as error:
                progress(root, state, status="failed", broker_cleanup_error=f"{type(error).__name__}: {error}")
        for name in broker_lifecycle.BROKER_ENV:
            os.environ.pop(name, None)
        if relay is not None:
            progress(root, state, budget=relay.status())
        write(root / "results.json", state)
    return int(state["status"] not in {"budget_reached", "completed", "diminishing_returns", "host_requested_stop"})


@with_termination_cleanup
def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("prepare", "run", "resume", "stop-after-pass"))
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    parser.add_argument("--label", help="Canonical proof label from proofs.json")
    parser.add_argument("--backend", choices=("codex", "pi"),
                        help="agent backend; new runs default to codex, pi requires explicit selection; frozen runs keep their selection")
    parser.add_argument("--stopping-policy", choices=("screening", "convergence", "cost"))
    parser.add_argument("--auth", type=Path)
    parser.add_argument("--resume-id", help="Prepared explicit continuation admission receipt")
    parser.add_argument("--reason", default="operator_requested", help="Host stop reason")
    parser.add_argument("--experiment-spec", type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    root = args.root.expanduser().resolve()
    if args.action == "stop-after-pass":
        print(json.dumps(pass_boundary.request_stop_after_pass(root, reason=args.reason), indent=2))
        return 0
    backend = resolve_backend(root, args.backend)
    stopping_policy = resolve_stopping_policy(root, args.stopping_policy)
    if args.action == "prepare":
        if not args.label:
            parser.error("prepare requires --label")
        spec = load_spec(args.experiment_spec) if args.experiment_spec else None
        prepare(root, args.label, backend=backend, spec=spec, stopping_policy=args.stopping_policy)
        return 0
    if args.action == "resume" and not args.resume_id:
        parser.error("resume requires --resume-id from prepare_continuation")
    if args.action != "resume" and args.resume_id:
        parser.error("--resume-id is only valid with resume")
    return run(root, resolve_auth_path(root, backend, args.auth),
               resume_id=args.resume_id if args.action == "resume" else None)


if __name__ == "__main__":
    raise SystemExit(main())


# The submission-facing product uses the same native command, isolation, Lean
# capsule and host finalizer. Historical research entry points above stay intact.
def prepare_product(root: Path, metadata: dict, snapshot: dict):
    from harness.config import RunConfig, CLI_VERSION, runtime_source_hashes
    from harness.openrouter import load_openrouter_settings, native_model_catalog
    from harness.runner import proof_identity, host_secret_environment_names
    for name in host_secret_environment_names():
        os.environ.pop(name, None)
    from . import proof
    public = RunConfig.from_frozen_dict(snapshot["config"])
    configure_native_environment(elan_home=str(public.elan_home))
    os.environ["E6_CODEX_EXECUTABLE"] = str(public.codex)
    spec = public.experiment_spec()
    environment(root, config=spec.proof_settings())
    if (root / "config.json").exists():
        config = read(root / "config.json")
        if (root / "billing/openrouter.sqlite").exists():
            raise RuntimeError("Started proofs cannot repeat preparation")
        if config.get("product_metadata") != metadata or experiment_spec(config) != spec:
            raise RuntimeError("Partial preparation differs from frozen input")
        proof._verify_config(config)
        proof._verify_incumbent(config, config["initial_best"])
    else:
        config = proof.prepare(root, metadata["label"], backend="codex", spec=spec,
            metadata=metadata, baseline_snapshot=snapshot)
    version = codex_preflight.executable_version(public.codex)
    if version != CLI_VERSION:
        raise RuntimeError(f"Native Codex CLI must be {CLI_VERSION}; found {version}")
    model_catalog = root / "model-catalog.json"
    native_model_catalog(load_openrouter_settings(public.openrouter), model_catalog)
    home = root / "runtime" / "codex-home"
    home.mkdir(parents=True, exist_ok=True)
    validate_codex_home(home)
    config.update(product_schema_version=1, optimizer=public.optimizer,
        openrouter=dict(public.openrouter), product_run_root=snapshot["root"],
        product_run_identity=snapshot["identity"], proof_budget_identity=proof_identity(snapshot, metadata),
        model_catalog=str(model_catalog), model_catalog_sha256=arena.sha256_file(model_catalog),
        codex_home=str(home), codex_sha256=arena.sha256_file(public.codex), codex_version=version,
        source_hashes={str(REPO / name): value for name, value in runtime_source_hashes().items()},
        host_validation_cache_root=str(RuntimeContext(root, spec).validation_cache))
    if public.recovery_policy != "none":
        config["recovery_policy"] = public.recovery_policy
    write(root / "config.json", config)
    preflight = tool_preflight(root, config)
    if not preflight_acceptable(read(preflight)):
        raise RuntimeError("Offline native tool preflight failed")
    config.update(tool_preflight=str(preflight), tool_preflight_sha256=arena.sha256_file(preflight))
    write(root / "config.json", config)
    _product_publish_best(root, config, config["initial_best"])
    write(root / "state.json", {"status": "prepared", "root": str(root), "passes": [],
        "identity": config["proof_budget_identity"], "elapsed_seconds": 0, "updated_at": arena.utc_now()})
    return config


def _product_publish_best(root, config, best):
    """Publish a content-addressed host checkpoint before mutable presentation files."""
    from . import proof
    proof._verify_incumbent(config, best)
    destination = root / "verified" / f"{best['sha256']}.lean"
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists() and proof._source(destination) != best["source"]:
        raise ValueError("Verified checkpoint content changed")
    if not destination.exists():
        temporary = destination.with_suffix(".tmp")
        temporary.write_text(best["source"], encoding="utf-8")
        temporary.replace(destination)
    best = {**best, "selected_path": str(destination)}
    write(root / "best.json", {key: value for key, value in best.items() if key != "source"})
    selected = root / "Selected.lean.tmp"
    selected.write_text(best["source"], encoding="utf-8")
    selected.replace(root / "Selected.lean")
    return best


def _product_best(root, config):
    from . import proof
    if not (root / "best.json").exists():
        return _product_publish_best(root, config, config["initial_best"])
    best = read(root / "best.json")
    path = Path(best["selected_path"]).resolve()
    if not path.is_relative_to(root / "verified"):
        raise ValueError("Best candidate must point to a private host checkpoint")
    best["source"] = proof._source(path)
    proof._verify_incumbent(config, best)
    return best


def _product_finalize_pass(config, root, capsule, best, state, budget):
    """Recover validation and optimizer promotion before admitting another turn."""
    from . import proof
    from harness.optimizer import optimize_pass_result as product_optimize
    number = int(capsule.name.removeprefix("pass-"))
    boundary = root / "host-boundaries" / f"{capsule.name}.json"
    boundary.parent.mkdir(parents=True, exist_ok=True)
    if boundary.exists():
        saved = read(boundary)
        raw_best, selection = saved["best"], saved["selection"]
        proof._verify_incumbent(config, raw_best)
    else:
        progress(root, state, status="validating_pass", agent_pid=None)
        raw_best = proof.finalize(config, capsule, best)
        selection = read(capsule / "selection.json")
        proof._verify_incumbent(config, raw_best)
        saved = {"schema_version": 1, "pass_number": number, "status": "validated",
            "best": raw_best, "selection": selection, "validated_at": arena.utc_now()}
        write(boundary, saved)
    # Checkpoint raw host selection before a potentially long optimizer turn.
    if raw_best["score"] > best["score"]:
        best = _product_publish_best(root, config, raw_best)
    report = None
    if selection.get("validation_healthy") is True and config.get("optimizer", "compact") == "compact":
        progress(root, state, status="optimizing_pass", agent_pid=None)
        optimized, selection, report = product_optimize(config, root, capsule, raw_best, selection)
        proof._verify_incumbent(config, optimized)
        if optimized["score"] > best["score"]:
            best = _product_publish_best(root, config, optimized)
    else:
        # The next fresh capsule reads this host record, even after failed native turns.
        write(capsule / "selection.json", selection)
    outcome = read(capsule / "agent-run.json") if (capsule / "agent-run.json").exists() else {"status": "interrupted", "native_status": "interrupted"}
    record = {"pass_number": number, "pass_mode": experiment_spec(config).pass_mode(number),
        "agent_status": outcome["status"], "native_status": outcome.get("native_status", outcome["status"]),
        "native_returncode": outcome.get("returncode"), "validation_healthy": selection.get("validation_healthy") is True,
        "candidate_sha256": best["sha256"], "best_score": best["score"],
        "selection_eligible": True, "budget": budget, "finished_at": arena.utc_now()}
    if report is not None:
        record["deterministic_refactoring"] = report
    state["passes"] = [row for row in state.get("passes", []) if row["pass_number"] != number] + [record]
    state["passes"].sort(key=lambda row: row["pass_number"])
    saved.update(status="committed", selected_sha256=best["sha256"], committed_at=arena.utc_now())
    write(boundary, saved)
    progress(root, state, best={key: value for key, value in best.items() if key != "source"},
        best_score=best["score"], pass_number=number, budget=budget, agent_pid=None)
    return best, record


def _product_output_limit_recovery(capsule, outcome, record, budget):
    """Match a paid output-limit terminal to native failure before a fresh pass.

    This never replays a request or makes the failed turn healthy. Missing bills,
    arbitrary native errors and host validation failures require explicit recovery.
    """
    if (outcome.get("status") != "failed" or outcome.get("native_status") != "failed"
            or type(outcome.get("returncode")) is not int or outcome["returncode"] == 0
            or record.get("validation_healthy") is not True
            or budget.get("active_requests") != 0 or blocking_unknown_usage(budget)
            or budget.get("cost_reporting_complete") is not True
            or budget.get("halted_reason") or budget.get("stop_reason")
            or budget.get("pass") != record["pass_number"]):
        return None
    receipts = budget.get("pass_receipts")
    if not isinstance(receipts, list) or not receipts:
        return None
    receipt = receipts[-1]
    metadata = receipt.get("metadata", {})
    if (receipt.get("state") != "settled" or receipt.get("pass_number") != record["pass_number"]
            or not isinstance(receipt.get("generation_id"), str) or not receipt["generation_id"]
            or metadata.get("status") != "incomplete"
            or metadata.get("incomplete_reason") != "max_output_tokens"):
        return None
    try:
        # Require spending progress so a free failure cannot loop without a cap.
        if Decimal(str(receipt.get("cost_usd"))) <= 0 or Decimal(str(budget["remaining_usd"])) <= 0:
            return None
        tail = []
        with (capsule / "codex-events.jsonl").open(encoding="utf-8") as source:
            for line in source:
                event = json.loads(line)
                if not isinstance(event, dict):
                    return None
                tail = (tail + [event])[-2:]
    except (OSError, ValueError, ArithmeticError, UnicodeError, RecursionError):
        return None
    message = "Incomplete response returned, reason: max_output_tokens"
    if (len(tail) != 2 or tail[0].get("type") != "error" or tail[0].get("message") != message
            or tail[1].get("type") != "turn.failed" or tail[1].get("error") != {"message": message}):
        return None
    return {"reason": "max_output_tokens", "continuation": "fresh_pass",
        "request_id": receipt["request_id"], "generation_id": receipt["generation_id"]}


def run_product(root: Path, *, auth_path=None, credential_provider=None, resume=False):
    """One proof, one durable OpenRouter ledger, fresh native passes until budget binds."""
    from harness.openrouter import OpenRouterRelay, load_openrouter_settings
    from harness.runner import (load_snapshot, proof_identity, host_secret_environment_names,
        validate_host_credential_path)
    for name in host_secret_environment_names():
        os.environ.pop(name, None)
    from . import proof
    root = Path(root).resolve()
    config = read(root / "config.json")
    snapshot = load_snapshot(Path(config["product_run_root"]))
    if auth_path is not None:
        auth_path = validate_host_credential_path(auth_path, snapshot)
    metadata = next(item for item in snapshot["proofs"] if item["label"] == config["label"])
    if (snapshot["identity"] != config["product_run_identity"]
            or proof_identity(snapshot, metadata) != config["proof_budget_identity"]
            or config.get("product_metadata") != metadata):
        raise RuntimeError("Proof configuration differs from its immutable run identity")
    from harness.config import RunConfig
    public = RunConfig.from_frozen_dict(snapshot["config"])
    spec = experiment_spec(config)
    if spec != public.experiment_spec() or config.get("optimizer") != public.optimizer or config.get("codex") != str(public.codex) or config.get("elan_home") != str(public.elan_home):
        raise RuntimeError("Proof runtime or method differs from frozen run")
    if config["openrouter"] != snapshot["config"]["openrouter"] or spec.cumulative_budget_usd != Decimal(str(snapshot["config"]["budget_usd"])):
        raise RuntimeError("Proof model or budget differs from frozen run")
    if config.get("recovery_policy", public.recovery_policy) != public.recovery_policy:
        raise RuntimeError("Proof recovery policy differs from frozen run")
    from harness.runtime_repair import verify_prepared_sources
    verify_prepared_sources(config, snapshot)
    for field in ("codex", "model_catalog", "tool_preflight"):
        if arena.sha256_file(Path(config[field])) != config[f"{field}_sha256"]:
            raise RuntimeError(f"Prepared {field} changed")
    if not preflight_acceptable(read(config["tool_preflight"])):
        raise RuntimeError("Frozen offline tool preflight failed")
    proof._verify_config(config)
    configure_native_environment(elan_home=config["elan_home"])
    state = read(root / "state.json")
    if not resume and state.get("status") != "prepared":
        raise RuntimeError("Proof already started; resume must reuse its ledger")
    best = _product_best(root, config)
    start, prior_elapsed = time.monotonic(), float(state.get("elapsed_seconds", 0))
    state.update(pid=os.getpid(), agent_pid=None, status="starting", resumed_at=arena.utc_now() if resume else None)
    for name in ("finished_at", "error", "stop_reason"):
        state.pop(name, None)
    broker = relay = None
    low_priority(spec)
    try:
        options = {"settings": load_openrouter_settings(config["openrouter"]),
                   "proof_id": config["proof_budget_identity"], "budget_policy": public.budget_policy,
                   "recovery_policy": public.recovery_policy}
        if credential_provider is not None:
            options["credential_provider"] = credential_provider
        else:
            options["auth_path"] = auth_path
        with OpenRouterRelay(root / "billing", **options) as relay:
            if resume:
                relay.reconcile_pending()
            budget = relay.status()
            # A crash can leave native candidates, a validated checkpoint, or a staged
            # optimizer promotion. Finish every host boundary before any new inference.
            recorded = {row["pass_number"] for row in state.get("passes", [])}
            for capsule in sorted(root.glob("pass-[0-9][0-9][0-9]")):
                number = int(capsule.name[5:])
                boundary = root / "host-boundaries" / f"{capsule.name}.json"
                if number not in recorded or (boundary.exists() and read(boundary).get("status") != "committed"):
                    best, _ = _product_finalize_pass(config, root, capsule, best, state, budget)
            while True:
                budget = relay.status()
                progress(root, state, budget=budget, elapsed_seconds=prior_elapsed + time.monotonic() - start)
                if budget.get("active_requests") or (public.recovery_policy != "none" and blocking_unknown_usage(budget)):
                    progress(root, state, status="unknown_usage", stop_reason="Unresolved provider liability must be reconciled before continuation")
                    break
                if Decimal(str(budget["remaining_usd"])) <= 0 or relay.stop_reason:
                    reason = relay.stop_reason or "budget_reached"
                    status = "budget_reached" if reason in {"budget_exhausted", "budget_reached", "insufficient_budget", "budget_limit"} else reason
                    progress(root, state, status=status)
                    break
                completed = len(state.get("passes", []))
                if spec.max_passes is not None and completed >= spec.max_passes:
                    progress(root, state, status="diagnostic_pass_cap", stop_reason=f"Diagnostic max_passes={spec.max_passes}")
                    break
                if broker is None:
                    host_environment(config, root)
                    with resource_gate.permit_from_environment("broker_startup", priority=spec.lean_priority,
                            timeout_seconds=spec.queue_timeout_seconds, metadata={"purpose": "product-prewarm", "root": str(root)}):
                        broker = broker_lifecycle.BrokerHost(config, root,
                            startup_timeout_seconds=spec.broker_startup_timeout_seconds,
                            request_timeout_seconds=spec.lean_request_timeout_seconds)
                        broker.start()
                number = max([int(path.name[5:]) for path in root.glob("pass-[0-9][0-9][0-9]")] + [0]) + 1
                progress(root, state, status="preparing_pass", pass_number=number)
                capsule = proof.make_capsule(root, number, best["source"], float(budget["remaining_usd"]))
                environment(root, capsule, config=config)
                os.environ.update(broker.begin_pass(number))
                error = None
                try:
                    outcome = execute_pass(config, root, capsule, relay, state)
                except BaseException as caught:
                    error = caught
                    outcome = read(capsule / "agent-run.json") if (capsule / "agent-run.json").exists() else {"status": "failed"}
                finally:
                    broker.end_pass()
                    for name in broker_lifecycle.BROKER_ENV:
                        os.environ.pop(name, None)
                    host_environment(config, root)
                # All terminal native paths retain the host-verified checkpoint,
                # including cap truncation, failed turns and signal interruption.
                best, record = _product_finalize_pass(config, root, capsule, best, state, relay.status())
                if error is not None:
                    raise error
                after = relay.status()
                if relay.stop_reason or Decimal(str(after["remaining_usd"])) <= 0:
                    continue
                if not record["validation_healthy"]:
                    progress(root, state, status="failed", error="Host validation infrastructure failed; verified best retained")
                    break
                if outcome["status"] != "completed":
                    recovery = _product_output_limit_recovery(capsule, outcome, record, after)
                    if recovery is not None:
                        record["native_failure_recovery"] = recovery
                        progress(root, state, status="retrying_output_limit")
                        continue
                    progress(root, state, status=outcome["status"])
                    break
    except BaseException as error:
        progress(root, state, status="interrupted" if isinstance(error, KeyboardInterrupt) else "failed",
            error=f"{type(error).__name__}: {error}")
        traceback.print_exc()
    finally:
        if broker is not None:
            try:
                broker.close()
            except BaseException as error:
                state["broker_cleanup_error"] = f"{type(error).__name__}: {error}"
        for name in broker_lifecycle.BROKER_ENV:
            os.environ.pop(name, None)
        if relay is not None:
            state["budget"] = relay.status()
        progress(root, state, finished_at=arena.utc_now(), agent_pid=None,
            elapsed_seconds=prior_elapsed + time.monotonic() - start)
        write(root / "results.json", state)
    return int(state["status"] not in {"budget_reached", "completed", "diagnostic_pass_cap", "host_requested_stop"})
