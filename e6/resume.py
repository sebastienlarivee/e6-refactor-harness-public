"""Explicit, audited continuation of interrupted unmetered proofs.

Preparation never dispatches inference. Existing pass capsules and terminal
evidence stay in place; an admission receipt authorizes one new runner epoch.
"""
from __future__ import annotations

from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

from lean_tools import arena_workflow as arena, process_memory
from .config import REPO_ROOT, source_paths
from .experiment import experiment_spec
from .stopping import (ConvergenceTracker, convergence_settings, policy_for_config, SCREENING_ATTEMPTS,
                       SCREENING_ATTEMPTED_BASIS, screening_counted_passes)

RECOVERY_POLICY = {"classification": "verified_upstream_transient_terminal_failure",
                   "max_consecutive_fresh_retries": 2}
COUNTERS = ("request_count", "dispatched_requests", "completed_requests", "metered_responses",
            "selector_requests", "selector_dispatched_requests", "selector_completed_requests")
MIGRATABLE_FIELDS = {"source_hashes", "source_migration", "tool_preflight", "tool_preflight_sha256",
                     "native_failure_recovery"}


def _read(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def _digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
                                    separators=(",", ":")).encode()).hexdigest()


def _immutable_config(config):
    return {key: value for key, value in config.items() if key not in MIGRATABLE_FIELDS}


def _policy_identity(config):
    """Everything frozen except the two explicitly amended policy aliases."""
    value = deepcopy(_immutable_config(config))
    value.pop("convergence", None)
    value.pop("policy_epochs", None)
    if isinstance(value.get("experiment_spec"), dict):
        value["experiment_spec"].pop("convergence", None)
    return value


def _amended_settings(config, settings):
    settings = convergence_settings(settings)
    if (policy_for_config(config) != "convergence"
            or settings.get("failure_policy") != "skip"
            or settings.get("confirmation_basis") != "rolling_window"):
        raise ValueError("Policy amendment requires explicit skip and rolling_window convergence")
    old = convergence_settings(config.get("convergence"))
    numerical = {"minimum_passes", "window_passes", "max_gain", "confirmation_passes"}
    if any(settings[key] != old[key] for key in numerical):
        raise ValueError("Policy amendment cannot change numerical stopping parameters")
    if settings == old:
        raise ValueError("Policy amendment must change the prior convergence settings")
    return settings


def _pinned_local(root, pointer, label):
    if not isinstance(pointer, dict):
        raise ValueError(f"{label} lacks pinned provenance")
    path = Path(pointer.get("path", ""))
    if (not path.resolve().is_relative_to(root / "resumes") or not path.is_file()
            or _pin(path) != pointer.get("sha256")):
        raise ValueError(f"{label} changed or is outside this proof")
    return _read(path)


def _policy_epochs(config):
    """Verify exact prior snapshots and the policy-only chain before replay."""
    root = Path(config["root"]).resolve()
    pointers = config.get("policy_epochs", [])
    if not isinstance(pointers, list):
        raise ValueError("Policy epochs must be an ordered pinned list")
    epochs = []
    previous_boundary = -1
    for index, pointer in enumerate(pointers):
        epoch = _pinned_local(root, pointer, "Policy epoch")
        old = _pinned_local(root, epoch.get("prior_config"), "Prior policy config")
        state = _pinned_local(root, epoch.get("prior_state"), "Prior policy state")
        kind, boundary = epoch.get("kind"), epoch.get("after_pass_number")
        if (epoch.get("schema_version") != 1 or epoch.get("root") != str(root)
                or kind not in {"queued_policy", "active_policy_epoch"}
                or type(boundary) is not int or boundary < 0 or boundary <= previous_boundary
                or old.get("policy_epochs", []) != pointers[:index]
                or _policy_identity(old) != _policy_identity(config)
                or epoch.get("old_settings") != old.get("convergence")
                or epoch.get("new_settings") != _amended_settings(old, epoch.get("new_settings"))):
            raise ValueError("Policy epoch changed proof identity, policy, or ordered provenance")
        experiment_spec(old)
        if epochs and old["convergence"] != epochs[-1]["new_settings"]:
            raise ValueError("Policy epoch settings do not follow the previous epoch")
        if kind == "queued_policy":
            if boundary != 0 or state.get("status") != "prepared" or state.get("passes", []):
                raise ValueError("Queued policy epoch requires untouched prepared evidence")
        else:
            results = _pinned_local(root, epoch.get("prior_results"), "Prior policy results")
            if (state != results or state.get("status") not in {"failed", "host_requested_stop"}
                    or not isinstance(state.get("passes"), list) or len(state["passes"]) != boundary):
                raise ValueError("Active policy epoch lacks complete terminal evidence")
            stop = epoch.get("operator_stop")
            if stop is not None and (not isinstance(stop, dict)
                    or stop.get("status") != "host_requested_stop"
                    or stop.get("completed_pass") != boundary
                    or stop.get("candidate_sha256") != state.get("best", {}).get("sha256")
                    or stop.get("boundary") != "after_validation_and_accounting"
                    or stop.get("budget") != state.get("budget")
                    or (state["status"] == "host_requested_stop" and stop != state.get("host_stop"))
                    or (state["status"] == "failed" and stop.get("results_sha256") != epoch["prior_results"]["sha256"])):
                raise ValueError("Policy epoch operator boundary differs from terminal evidence")
            if state["status"] == "host_requested_stop" and stop is None:
                raise ValueError("Policy epoch lacks its operator stop provenance")
        epochs.append({**epoch, "prior_config_value": old, "prior_state_value": state})
        previous_boundary = boundary
    if epochs and config.get("convergence") != epochs[-1]["new_settings"]:
        raise ValueError("Current convergence settings differ from the pinned policy epoch")
    return epochs


def _replay_scores(initial_score, settings, rows):
    tracker = ConvergenceTracker(initial_score, settings)
    stop_pass = None
    for row in rows:
        if stop_pass is not None:
            continue
        healthy = (row["agent_status"] == "completed" and row["native_status"] == "completed"
                   and row["validation_healthy"])
        snapshot = tracker.observe(row["best_score"], healthy=healthy, pass_number=row["pass_number"])
        if snapshot["should_stop"]:
            stop_pass = row["pass_number"]
    return tracker, stop_pass


def _replay_epoch_rows(config, state, rows):
    epochs = _policy_epochs(config)
    settings = epochs[0]["old_settings"] if epochs else config.get("convergence")
    tracker = ConvergenceTracker(config["initial_best"]["score"], settings)
    applied = 0
    for boundary in range(len(rows) + 1):
        if applied < len(epochs) and epochs[applied]["after_pass_number"] == boundary:
            epoch = epochs[applied]
            prior = epoch["prior_state_value"]
            if (prior.get("passes", []) != rows[:boundary]
                    or (boundary and prior.get("convergence") != tracker.snapshot())
                    or epoch.get("prior_convergence") != (tracker.snapshot() if boundary else None)):
                raise ValueError("Policy epoch rewrites historical convergence evidence")
            tracker, stop_pass = _replay_scores(config["initial_best"]["score"], epoch["new_settings"], rows[:boundary])
            if (epoch.get("replayed_convergence") != tracker.snapshot()
                    or epoch.get("replay_stop_pass") != stop_pass):
                raise ValueError("Policy epoch transition differs from healthy checkpoint replay")
            applied += 1
        if boundary == len(rows):
            break
        row = rows[boundary]
        healthy = (row["agent_status"] == "completed" and row["native_status"] == "completed"
                   and row["validation_healthy"])
        snapshot = tracker.observe(row["best_score"], healthy=healthy, pass_number=boundary + 1)
        if row.get("convergence") != snapshot:
            raise ValueError("Saved convergence row differs from native/host replay")
    if applied != len(epochs):
        raise ValueError("Policy epoch boundary exceeds saved pass history")
    pending = bool(epochs and state == epochs[-1]["prior_state_value"])
    if not pending and (state.get("convergence") != tracker.snapshot()
                        or (epochs and state.get("policy_epochs") != config.get("policy_epochs"))):
        raise ValueError("Root convergence/policy provenance differs from the audited replay")
    return tracker, epochs, pending


def _id(value):
    if not isinstance(value, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]{0,95}", value):
        raise ValueError("Continuation ID must be a simple unique filename")
    return value


def _pin(path):
    return arena.sha256_file(Path(path))


def _save(path, value):
    arena.write_json_atomic(Path(path), value)


def assert_processes_gone(root: Path, state: dict):
    """Read-only admission: refuse recorded PIDs and live root-bound commands."""
    if not Path("/proc").is_dir():
        raise RuntimeError("Safe resume admission requires Linux process identity checks")
    known = {state.get("pid"), state.get("agent_pid")}
    broker = state.get("broker", {})
    if isinstance(broker, dict):
        known.update(broker.get(key) for key in ("pid", "lean_pid", "parent_pid"))
    claim = root / "run.claim"
    if claim.exists():
        try:
            known.add(int(claim.read_text().strip()))
        except ValueError as error:
            raise ValueError("Malformed stale run claim") from error
    live = []
    for pid in known:
        if type(pid) is int and pid > 1 and process_memory.linux_process_identity(pid) is not None:
            live.append(pid)
    # New queue/supervisor processes can legitimately carry this proof's root
    # in their argv. Their identity-pinned ancestor chain is outside the old
    # experiment tree; recorded old PIDs above are still never exempted.
    ancestors = {}
    ancestor = os.getpid()
    while ancestor > 1 and ancestor not in ancestors:
        identity = process_memory.linux_process_identity(ancestor)
        if identity is None:
            break
        ancestors[ancestor] = identity.start_time
        ancestor = identity.parent_pid
    # Detached descendants retain their capsule/broker path in argv even after
    # the original runner exits. Match complete path arguments, not substrings.
    for process in Path("/proc").iterdir():
        if not process.name.isdecimal() or int(process.name) == os.getpid():
            continue
        pid = int(process.name)
        if pid in ancestors:
            identity = process_memory.linux_process_identity(pid)
            if identity is not None and identity.start_time == ancestors[pid]:
                continue
        try:
            argv = (process / "cmdline").read_bytes().split(b"\0")
        except OSError:
            continue
        prefix = str(root).encode()
        if any(arg == prefix or arg.startswith(prefix + b"/") for arg in argv):
            live.append(pid)
    if live:
        raise RuntimeError(f"Resume requires the old process tree to be gone; live PIDs: {sorted(set(live))}")


def _checkpoint(config, incumbent):
    """Verify saved exact and compatibility provenance without rerunning Lean."""
    from . import proof
    proof._verify_incumbent(config, incumbent)
    selected = Path(incumbent["selected_path"])
    root = Path(config["root"]).resolve()
    if not selected.resolve().is_relative_to(root) or not selected.is_file():
        raise ValueError("Checkpoint must be a regular proof-local selected source")
    if _pin(selected) != incumbent["sha256"] or proof._source(selected) != incumbent["source"]:
        raise ValueError("Checkpoint source/hash differs from its host selection")
    primary = incumbent.get("evaluation", {})
    heartbeat = primary.get("heartbeat", {})
    if (primary.get("valid") is not True or primary.get("task_id") != config["task_id"]
            or primary.get("measurement_mode") != "exact" or primary.get("axiom_status") != "measured"
            or primary.get("scoring_policy", "legacy-v1") != config.get("scoring_policy", "legacy-v1")
            or not isinstance(primary.get("axioms"), list)
            or any(axiom not in arena.ALLOWED_AXIOMS for axiom in primary["axioms"])
            or primary.get("source_sha256") != incumbent["sha256"]
            or primary.get("length", {}).get("candidate_tokens") != incumbent["tokens"]
            or heartbeat.get("candidate") != incumbent["heartbeats"]):
        raise ValueError("Checkpoint lacks matching exact primary source/measurement provenance")
    _, row = arena.load_task(Path(config["task"]))
    entry = arena.environment_fingerprint_registry_entry(
        row, Path(config["primary"]), Path(config["fingerprint_registry"]), validate_guard=True)
    if heartbeat.get("environment_fingerprint") != entry["fingerprint"]:
        raise ValueError("Checkpoint exact environment fingerprint changed")
    if config.get("scoring_policy", "legacy-v1") == "arena-v1":
        # Arena receipts expose the published scoring reference; validate the
        # separate observed original through its source/environment binding.
        expected_control = proof._native_control_evidence(config, row, primary)
        if (heartbeat.get("local_reference") != config["original_heartbeats"]
                or incumbent.get("native_control_evidence", expected_control) != expected_control):
            raise ValueError("Checkpoint lacks matching native control evidence")
    elif heartbeat.get("local_reference") != proof._original_control_heartbeats(config):
        if (heartbeat.get("local_reference") is not None
                or incumbent.get("native_control_evidence") != proof._native_control_evidence(config, row, primary)):
            raise ValueError("Checkpoint lacks matching native control evidence")
    compatibility = incumbent.get("compatibility")
    projects = [config["primary"], *config["compatibility"]]
    if (not isinstance(compatibility, list) or len(compatibility) != len(projects)
            or any(item.get("environment") != project or type(item.get("passed")) is not bool
                   for item, project in zip(compatibility, projects))
            or compatibility[0]["passed"] is not True
            or incumbent["compatibility_pct"] != 100 * sum(item["passed"] for item in compatibility) / len(projects)):
        raise ValueError("Checkpoint compatibility evidence is incomplete or belongs to different environments")
    for index, item in enumerate(compatibility[1:], 1):
        evaluation = item.get("evaluation", {})
        if not evaluation and incumbent["sha256"] == config["initial_best"]["sha256"]:
            phase = _read(root / "preparation" / "baseline-phases" / f"compatibility-{index:03d}-quick.json")
            if phase.get("status") != "passed" or phase.get("environment") != item["environment"]:
                raise ValueError("Original checkpoint compatibility preparation evidence changed")
            evaluation = phase.get("evaluation", {})
        if (type(evaluation.get("valid")) is not bool or evaluation["valid"] != item["passed"]
                or evaluation.get("task_id") != config["task_id"]
                or evaluation.get("scoring_policy", "legacy-v1") != config.get("scoring_policy", "legacy-v1")
                or evaluation.get("source_sha256") != incumbent["sha256"]
                or proof._validation_infrastructure_failure(evaluation)):
            raise ValueError("Checkpoint compatibility verdict lacks healthy host provenance")
        compatibility_entry = arena.environment_fingerprint_registry_entry(
            row, Path(item["environment"]), Path(config["fingerprint_registry"]), validate_guard=True)
        if evaluation.get("heartbeat", {}).get("environment_fingerprint") != compatibility_entry["fingerprint"]:
            raise ValueError("Checkpoint compatibility environment fingerprint changed")
    return dict(incumbent)


def reconstruct(root: Path, config: dict, state: dict, *, allow_operator_stop=False,
                allow_confirmed_transition=False, final_check=False):
    """Replay every native and host selection row, including the failed gap."""
    mode = policy_for_config(config)
    if mode == "cost":
        raise ValueError("Cost-policy resume is unsupported; a persistent settled cost ledger is required")
    spec = experiment_spec(config)
    if mode == "screening":
        if (config.get("policy_epochs") or state.get("policy_epochs")
                or state.get("stopping_policy") != mode
                or state.get("max_passes") != SCREENING_ATTEMPTS
                or state.get("screening") != spec.stopping_settings()["screening"]
                or state.get("experiment_spec", {}).get("screening_count_basis", SCREENING_ATTEMPTED_BASIS)
                != spec.screening_count_basis
                or state.get("convergence") is not None):
            raise ValueError("Screening continuation must preserve its five-pass count basis without convergence epochs")
    if not final_check and state.get("status") in {"completed", "diminishing_returns", "budget_reached"}:
        raise ValueError("Completed proof stopping evidence cannot be resumed")
    if not final_check and state.get("status") not in ({"failed", "host_requested_stop"}
                                                     if allow_operator_stop else {"failed"}):
        raise ValueError("Only a terminal failed unmetered proof can be explicitly resumed")
    passes = state.get("passes")
    if not isinstance(passes, list) or (not passes and mode != "screening"):
        raise ValueError("Resume requires complete saved pass history")
    best = _checkpoint(config, config["initial_best"])
    evidence = {}
    expected_dirs = {f"pass-{number:03d}" for number in range(1, len(passes) + 1)}
    if {path.name for path in root.glob("pass-*")} != expected_dirs:
        raise ValueError("Partial or unexpected pass capsule prevents safe continuation")
    for number, record in enumerate(passes, 1):
        if (not isinstance(record, dict) or type(record.get("pass_number")) is not int
                or record["pass_number"] != number
                or record.get("pass_mode") != spec.pass_mode(number)
                or type(record.get("validation_healthy")) is not bool
                or record.get("selection_eligible") is not True):
            raise ValueError("Saved pass order/mode/selection health is invalid")
        capsule = root / f"pass-{number:03d}"
        native = _read(capsule / "agent-run.json")
        native_status = native.get("native_status", native.get("status"))
        if (native.get("status") != record.get("agent_status")
                or native_status != record.get("native_status")
                or native.get("returncode") != record.get("native_returncode")
                or type(native.get("returncode")) is not int
                or (native_status == "completed") != (native["returncode"] == 0)):
            raise ValueError("Saved convergence history differs from native pass evidence")
        selection = _read(capsule / "selection.json")
        candidate = _checkpoint(config, selection)
        if (selection.get("validation_healthy") != record["validation_healthy"]
                or selection["score"] < best["score"]
                or selection["score"] != record.get("best_score")
                or selection["sha256"] != record.get("candidate_sha256")):
            raise ValueError("Saved pass differs from its monotone verified checkpoint")
        best = candidate
        for name in ("agent-run.json", "selection.json", "Selected.lean", "invocation.json"):
            path = capsule / name
            evidence[str(path)] = _pin(path)
    if mode == "screening":
        if any(record.get("convergence") is not None for record in passes):
            raise ValueError("Screening pass history cannot contain convergence decisions")
        tracker, epochs, pending = None, [], False
    else:
        tracker, epochs, pending = _replay_epoch_rows(config, state, passes)
    for epoch in epochs:
        hashes = {path: digest for path, digest in evidence.items()
                  if int(Path(path).parent.name.removeprefix("pass-")) <= epoch["after_pass_number"]}
        if epoch.get("pass_evidence_hashes") != hashes:
            raise ValueError("Policy epoch native/checkpoint evidence changed")
    public = {key: value for key, value in best.items() if key != "source"}
    # selection.json contains candidate audit fields not present in best.json.
    saved_best = _read(root / "best.json")
    if (any(public.get(key) != value for key, value in saved_best.items())
            or state.get("best_score") != best["score"]
            or state.get("best") != saved_best
            or _pin(root / "Selected.lean") != best["sha256"]):
        raise ValueError("Root best/convergence does not match its final verified checkpoint")
    should_stop = bool(tracker and tracker.snapshot()["should_stop"])
    if should_stop and not (final_check or allow_confirmed_transition or pending):
        raise ValueError("Confirmed convergence cannot be extended")
    counted_passes = screening_counted_passes(passes, spec.screening_count_basis) if mode == "screening" else len(passes)
    if not final_check and not should_stop and spec.max_passes is not None and counted_passes >= spec.max_passes:
        raise ValueError("Configured maximum passes already reached")
    for key in ("candidate_records", "validation_healthy", "unique_candidate_count"):
        best.pop(key, None)
    return best, tracker, evidence


def replay_policy_epochs(config: dict, result: dict) -> dict:
    """Final audit of historical policies, source checkpoints, and transition."""
    if (not config.get("policy_epochs") or policy_for_config(config) != "convergence"
            or result.get("stopping_policy") != "convergence"
            or result.get("status") != "diminishing_returns"):
        raise ValueError("Run lacks a successful policy-epoch convergence result")
    _, tracker, _ = reconstruct(Path(config["root"]).resolve(), config, result, final_check=True)
    snapshot = tracker.snapshot()
    if not snapshot["should_stop"] or result.get("convergence") != snapshot:
        raise ValueError("Final convergence decision differs from the audited policy epochs")
    return snapshot


def _frozen_revision():
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, text=True).strip()
    dirty = subprocess.check_output(["git", "status", "--porcelain", "--", "e6", "lean_tools", "transport", "data"],
                                    cwd=REPO_ROOT, text=True).strip()
    if dirty:
        raise RuntimeError("Continuation source must be frozen in a clean Git checkpoint before migration")
    return revision


def verify_source_migration(config: dict, *, source_root=None) -> dict:
    """Content-pin the permission to normalize source-relative metadata paths."""
    source = Path(source_root or REPO_ROOT).resolve()
    migration = config.get("source_migration")
    if not isinstance(migration, dict):
        raise ValueError("Source migration lacks its pinned receipt")
    path = Path(migration.get("path", ""))
    root = Path(config["root"]).resolve()
    if (not path.resolve().is_relative_to(root / "resumes") or not path.is_file()
            or _pin(path) != migration.get("sha256")):
        raise ValueError("Source migration receipt changed or is outside this proof")
    saved = _read(path)
    if (saved.get("schema_version") not in {1, 2} or saved.get("new_source_root") != str(source)
            or saved.get("immutable_config_sha256") != _digest(_immutable_config(config))
            or saved.get("new_source_hashes") != config.get("source_hashes")):
        raise ValueError("Source migration differs from the frozen proof settings")
    if saved["schema_version"] == 2:
        prior = _pinned_local(root, saved.get("prior_config"), "Prior migration config")
        if (saved.get("prior_immutable_config_sha256") != _digest(_immutable_config(prior))
                or saved.get("old_source_hashes") != prior.get("source_hashes")):
            raise ValueError("Source migration prior settings changed")
        epochs = _policy_epochs(config)
        expected = deepcopy(prior)
        if saved.get("policy_amendment") is not None:
            if not epochs or saved["policy_amendment"] != config["policy_epochs"][-1]:
                raise ValueError("Source migration lacks matching policy authorization")
            expected["convergence"] = deepcopy(epochs[-1]["new_settings"])
            if "experiment_spec" in expected:
                expected["experiment_spec"]["convergence"] = deepcopy(expected["convergence"])
            expected["policy_epochs"] = deepcopy(config["policy_epochs"])
            if prior.get("policy_epochs", []) != config["policy_epochs"][:-1]:
                raise ValueError("Source migration forged prior policy epochs")
        if _immutable_config(expected) != _immutable_config(config):
            raise ValueError("Continuation changed frozen proof, runtime or treatment settings")
    elif config.get("policy_epochs"):
        raise ValueError("Policy epochs require explicitly audited source migration")
    previous = Path(saved["previous_source_root"])
    for relative, expected in saved["data_hashes"].items():
        if _pin(source / relative) != expected or _pin(previous / relative) != expected:
            raise ValueError("Source migration changed immutable benchmark metadata")
    return saved


def prepare_continuation(root: Path, continuation_id: str, action="resume", *, previous_source_root=None,
                         queued_policy_amendment=None, policy_epoch_amendment=None):
    """Freeze a provider-free migration receipt; leave old terminal state intact."""
    from . import proof, run
    root = Path(root).resolve()
    continuation_id = _id(continuation_id)
    if action not in {"resume", "run"}:
        raise ValueError("Continuation action must be resume or run")
    config, state = _read(root / "config.json"), _read(root / "state.json")
    if (root / "resume.claim").exists():
        raise ValueError("Partial or concurrent continuation claim prevents preparation")
    if (queued_policy_amendment is not None and (action != "run" or policy_epoch_amendment is not None)
            or policy_epoch_amendment is not None and action != "resume"):
        raise ValueError("Queued policy amendments require run; active policy epochs require resume")
    amendment = queued_policy_amendment if action == "run" else policy_epoch_amendment
    new_settings = _amended_settings(config, amendment) if amendment is not None else None
    assert_processes_gone(root, state)
    revision = _frozen_revision()
    previous = Path(previous_source_root or REPO_ROOT).resolve()
    for field, hash_field in (("model_catalog", "model_catalog_sha256"),
                             ("tool_preflight", "tool_preflight_sha256")):
        if _pin(config[field]) != config[hash_field]:
            raise ValueError(f"Frozen native runtime metadata changed: {field}")
    if not run.preflight_acceptable(_read(config["tool_preflight"])):
        raise ValueError("Prior offline native preflight is not acceptable")
    if config.get("agent_backend", "codex") == "codex":
        if _pin(config["codex"]) != config["codex_sha256"]:
            raise ValueError("Frozen native executable changed")
        run.validate_codex_home(Path(config["codex_home"]))
    else:
        from . import pi
        pi.validate_settings(config)
        pi.verify_runtime(config)
    if not config.get("source_hashes"):
        raise ValueError("Continuation requires a fully pinned prior source snapshot")
    for path, expected in config["source_hashes"].items():
        if _pin(path) != expected or not Path(path).resolve().is_relative_to(previous):
            raise ValueError(f"Prior source snapshot changed or belongs to another checkout: {path}")
    prior_migration = (verify_source_migration(config, source_root=previous)
                       if config.get("source_migration") else None)
    data_hashes = {}
    for path, expected in config["source_hashes"].items():
        relative = Path(path).resolve().relative_to(previous)
        if relative.parts[0] == "data":
            if _pin(REPO_ROOT / relative) != expected:
                raise ValueError(f"Continuation cannot change benchmark metadata: {relative}")
            data_hashes[str(relative)] = expected
    if not data_hashes:
        raise ValueError("Prior snapshot lacks immutable benchmark metadata")
    operator_stop = None
    if action == "resume":
        if _read(root / "results.json") != state:
            raise ValueError("Terminal state/results differ; no complete prior result to resume")
        if new_settings is not None and state.get("budget", {}).get("active_requests", 0) != 0:
            raise ValueError("Policy amendment requires fully settled terminal requests")
        # An old runner's exclusive next-capsule guard is operator evidence,
        # never a failed proof pass. Only its authenticated empty inode moves.
        if new_settings is not None and (root / "host-pass-boundary-stop.json").exists():
            from . import pass_boundary
            if pass_boundary.classify_legacy_stop(root) is not None:
                operator_stop = pass_boundary.archive_legacy_reservation(root)
        best, tracker, evidence = reconstruct(root, config, state,
                                             allow_operator_stop=new_settings is not None)
        if state.get("status") == "host_requested_stop":
            operator_stop = state.get("host_stop")
            if (not isinstance(operator_stop, dict) or operator_stop.get("status") != "host_requested_stop"
                    or operator_stop.get("completed_pass") != len(state["passes"])
                    or operator_stop.get("candidate_sha256") != best["sha256"]
                    or operator_stop.get("boundary") != "after_validation_and_accounting"
                    or operator_stop.get("budget") != state.get("budget")
                    or state.get("budget", {}).get("active_requests", 0) != 0):
                raise ValueError("Operator terminal lacks complete host boundary evidence")
        next_pass = len(state["passes"]) + 1
    else:
        if (state.get("status") != "prepared" or state.get("passes", [])
                or (root / "run.claim").exists() or (root / "results.json").exists()
                or list(root.glob("pass-*"))):
            raise ValueError("Fresh continuation requires an untouched prepared proof")
        best, tracker, evidence, next_pass = config["initial_best"], None, {}, 1
    directory = root / "resumes" / continuation_id
    directory.mkdir(parents=True, exist_ok=False)
    prior = directory / "prior"
    prior.mkdir()
    snapshots = {}
    for name in ("config.json", "state.json", "results.json", "run.claim", "best.json", "Selected.lean"):
        path = root / name
        if path.is_file():
            target = prior / name
            shutil.copyfile(path, target)
            target.chmod(0o444)
            snapshots[name] = _pin(target)
    updated = deepcopy(config)
    variant = experiment_spec(config).prompt_variant
    paths = source_paths(variant) if variant != "baseline" else source_paths()
    updated["source_hashes"] = {str(path): _pin(path) for path in paths}
    updated["native_failure_recovery"] = dict(RECOVERY_POLICY)
    policy_pointer = None
    policy_amendment = None
    if new_settings is not None:
        prior_snapshot = tracker.snapshot() if tracker else None
        amended_tracker, stop_pass = _replay_scores(config["initial_best"]["score"], new_settings,
                                                   state.get("passes", []))
        policy_amendment = {"schema_version": 1, "root": str(root),
                            "continuation_id": continuation_id,
                            "kind": "queued_policy" if action == "run" else "active_policy_epoch",
                            "after_pass_number": next_pass - 1,
                            "old_settings": deepcopy(config["convergence"]), "new_settings": new_settings,
                            "prior_config": {"path": str(prior / "config.json"), "sha256": snapshots["config.json"]},
                            "prior_state": {"path": str(prior / "state.json"), "sha256": snapshots["state.json"]},
                            "prior_results": ({"path": str(prior / "results.json"), "sha256": snapshots["results.json"]}
                                              if "results.json" in snapshots else None),
                            "prior_convergence": prior_snapshot,
                            "replayed_convergence": amended_tracker.snapshot(), "replay_stop_pass": stop_pass,
                            "pass_evidence_hashes": evidence, "operator_stop": operator_stop,
                            "created_at": arena.utc_now()}
        policy_path = directory / "policy-epoch.json"
        _save(policy_path, policy_amendment)
        policy_path.chmod(0o444)
        policy_pointer = {"path": str(policy_path), "sha256": _pin(policy_path)}
        updated["convergence"] = deepcopy(new_settings)
        if "experiment_spec" in updated:
            updated["experiment_spec"]["convergence"] = deepcopy(new_settings)
        updated["policy_epochs"] = [*config.get("policy_epochs", []), policy_pointer]
        experiment_spec(updated)
        tracker = amended_tracker if action == "resume" else None
    original_root = prior_migration["original_source_root"] if prior_migration else str(previous)
    migration = {"schema_version": 2 if new_settings is not None or config.get("policy_epochs") else 1,
                 "continuation_id": continuation_id,
                 "previous_source_root": str(previous), "original_source_root": original_root,
                 "new_source_root": str(REPO_ROOT), "new_source_revision": revision,
                 "old_source_hashes": config["source_hashes"], "new_source_hashes": updated["source_hashes"],
                 "data_hashes": data_hashes, "immutable_config_sha256": _digest(_immutable_config(updated)),
                 "created_at": arena.utc_now()}
    if migration["schema_version"] == 2:
        migration.update(prior_config={"path": str(prior / "config.json"), "sha256": snapshots["config.json"]},
                         prior_immutable_config_sha256=_digest(_immutable_config(config)),
                         policy_amendment=policy_pointer)
    migration_path = directory / "migration.json"
    _save(migration_path, migration)
    migration_path.chmod(0o444)
    updated["source_migration"] = {"path": str(migration_path), "sha256": _pin(migration_path)}
    proof._verify_config(updated)
    report = run.tool_preflight(root, updated, output_root=directory)
    if not run.preflight_acceptable(_read(report)):
        raise ValueError("New continuation offline native preflight failed")
    updated.update(tool_preflight=str(report), tool_preflight_sha256=_pin(report))
    # Semantic digest excludes only the explicitly audited lifecycle migration.
    if _digest(_immutable_config(updated)) != migration["immutable_config_sha256"]:
        raise ValueError("Continuation changed frozen proof, runtime or treatment settings")
    _save(directory / "config.json", updated)
    receipt = {"schema_version": 1, "continuation_id": continuation_id, "action": action,
               "receipt_path": str(directory / "receipt.json"), "prior_status": state["status"],
               "previous_source_root": str(previous), "new_source_root": str(REPO_ROOT),
               "new_source_revision": revision, "next_pass_number": next_pass,
               "best_sha256": best["sha256"], "best_score": best["score"],
               "convergence": tracker.snapshot() if tracker else None,
               "prior_state_sha256": snapshots["state.json"],
               "prior_results_sha256": snapshots.get("results.json"),
               "prior_snapshots": snapshots, "pass_evidence_hashes": evidence,
               "migration_sha256": _pin(migration_path), "config_sha256": _pin(directory / "config.json"),
               "native_failure_recovery": dict(RECOVERY_POLICY), "prepared_at": arena.utc_now()}
    if policy_amendment is not None:
        receipt["policy_amendment"] = policy_amendment
    for path in (report, directory / "config.json"):
        path.chmod(0o444)
    _save(directory / "receipt.json", receipt)
    (directory / "receipt.json").chmod(0o444)
    _save(root / "config.json", updated)
    return receipt


def admit(root: Path, continuation_id: str, config: dict):
    """Consume one explicit receipt only after repeating all read-only checks."""
    root = Path(root).resolve()
    directory = root / "resumes" / _id(continuation_id)
    receipt = _read(directory / "receipt.json")
    if (receipt.get("action") != "resume" or receipt.get("continuation_id") != continuation_id
            or _pin(root / "config.json") != receipt.get("config_sha256")
            or (directory / "admitted.json").exists()):
        raise ValueError("Resume requires an unused matching explicit admission receipt")
    state = _read(root / "state.json")
    assert_processes_gone(root, state)
    for name, expected in receipt["prior_snapshots"].items():
        if _pin(directory / "prior" / name) != expected:
            raise ValueError("Immutable prior resume evidence changed")
        if name != "config.json" and _pin(root / name) != expected:
            raise ValueError("Proof changed after continuation preparation")
    verify_source_migration(config)
    from . import proof
    proof._verify_config(config)
    best, tracker, evidence = reconstruct(root, config, state,
                                         allow_operator_stop=receipt.get("policy_amendment") is not None)
    if (evidence != receipt["pass_evidence_hashes"] or best["sha256"] != receipt["best_sha256"]
            or (tracker.snapshot() if tracker else None) != receipt.get("convergence")):
        raise ValueError("Pass/checkpoint evidence changed after continuation preparation")
    # One exclusive proof-local lock protects stale-claim replacement. Never
    # remove a claim before taking the continuation admission lock.
    with (root / "resume.claim").open("x") as claim:
        claim.write(f"{os.getpid()} {continuation_id}\n")
    try:
        assert_processes_gone(root, state)
        _save(directory / "admitted.json", {"continuation_id": continuation_id, "pid": os.getpid(),
                                            "admitted_at": arena.utc_now(), "next_pass_number": receipt["next_pass_number"]})
        (directory / "admitted.json").chmod(0o444)
        replacement = directory / "new-run.claim"
        with replacement.open("x") as claim:
            claim.write(str(os.getpid()))
        os.replace(replacement, root / "run.claim")
    finally:
        (root / "resume.claim").unlink()
    return state, best, tracker, receipt


class CumulativeTelemetryRelay:
    """Retain raw per-process journals and expose additive logical-proof counts."""
    def __init__(self, relay, prior_budget: dict, epoch: str):
        self.relay, self.prior_budget, self.epoch = relay, prior_budget, epoch

    def __getattr__(self, name):
        return getattr(self.relay, name)

    def status(self):
        current = self.relay.status()
        process_counts = {key: current.get(key, 0) for key in COUNTERS}
        prior_counts = {key: self.prior_budget.get(key, 0) for key in COUNTERS}
        result = dict(current)
        for key in COUNTERS:
            result[key] = prior_counts[key] + process_counts[key]
        result.update(counter_scope="logical_proof_cumulative", relay_epoch=self.epoch,
                      process_counters=process_counts, prior_counters=prior_counts)
        return result
