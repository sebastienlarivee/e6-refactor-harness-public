"""Frozen runs and bounded proof scheduling around the preserved proof-cell engine."""
from __future__ import annotations

from contextlib import contextmanager
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from typing import Mapping

from .config import RunConfig, digest, file_hash, runtime_source_hashes, verify_source_hashes
from lean_tools import arena_workflow as arena, process_memory

COMPLETE = {"budget_reached", "completed", "diagnostic_pass_cap", "host_requested_stop"}


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def write(path, value):
    arena.write_json_atomic(Path(path), value)


@contextmanager
def run_lock(root: Path, name=".runner.lock"):
    """Kernel lease survives stale PID files and excludes concurrent subprocesses."""
    root = Path(root)
    root.mkdir(parents=True, exist_ok=True)
    with (root / name).open("a+") as stream:
        try:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError(f"A runner already holds {root}") from error
        stream.seek(0)
        stream.truncate()
        stream.write(str(os.getpid()))
        stream.flush()
        try:
            yield
        finally:
            fcntl.flock(stream, fcntl.LOCK_UN)


def load_snapshot(root: Path, *, verify=True):
    root = Path(root).resolve()
    if not (root / "resolved-config.json").is_file():
        raise ValueError(f"No frozen run snapshot in {root}; this directory cannot be resumed. "
                         "If preflight failed or was interrupted, preserve its evidence and choose a fresh --output directory.")
    snapshot = read(root / "resolved-config.json")
    payload = {key: value for key, value in snapshot.items() if key != "identity"}
    if snapshot.get("schema_version") != 1 or snapshot.get("identity") != digest(payload):
        raise RuntimeError("Frozen run configuration identity changed")
    if snapshot.get("root") != str(root):
        raise RuntimeError("Run directories cannot be relocated while active")
    if verify:
        from .runtime_repair import effective_sources
        verify_source_hashes(effective_sources(snapshot))
        for name, entry in snapshot["input_hashes"].items():
            if file_hash(Path(entry["path"])) != entry["sha256"]:
                raise RuntimeError(f"Frozen {name} changed")
        from .environments import verify_resolved_metadata
        for item in snapshot["proofs"]:
            verify_resolved_metadata(item)
            if item.get("baseline_receipt") is not None:
                from .baselines import load_original_baseline
                load_original_baseline(item, source_snapshot=snapshot)
            if file_hash(Path(item["task"])) != item["task_sha256"]:
                raise RuntimeError(f"Frozen proof row changed: {item['label']}")
    return snapshot


def prepare_run(config: RunConfig, root: Path, *, doctor=True):
    """Resolve public rows and validate prerequisites without inference."""
    from .benchmark import load_benchmark
    from .environments import load_environment_map, resolve_benchmark
    from .openrouter import load_openrouter_settings
    root = Path(root).expanduser().resolve()
    if (root / "resolved-config.json").exists():
        raise FileExistsError("Run output must be fresh; use resume to preserve its ledger")
    if root.exists() and any(root.iterdir()):
        raise FileExistsError(f"Output {root} is not empty and has no frozen run snapshot. "
                              "Preserve its preparation evidence and choose a fresh --output directory; --resume is unavailable.")
    from e6.config import REPO_ROOT
    if root.is_relative_to(REPO_ROOT):
        raise ValueError("Run output must live outside the source checkout")
    settings = load_openrouter_settings(config.openrouter)
    del settings
    root.mkdir(parents=True, exist_ok=True)
    benchmark = load_benchmark(config.input_path, config.heartbeat_path)
    env_map = load_environment_map(config.env_map)
    proofs = resolve_benchmark(benchmark, env_map, root / "benchmark",
        scoring_policy="arena-v1", selected=config.selected_proofs, elan_home=config.elan_home)
    if not proofs:
        raise ValueError("Proof selection is empty")
    if len({item["label"] for item in proofs}) != len(proofs):
        raise ValueError("Resolved proof labels are not unique")
    if doctor:
        from .doctor import check
        report = check(config, output_dir=root / "doctor", metadata=proofs, receipt_dir=root / "baselines")
        write(root / "doctor.json", report)
        if report.get("status") not in {"passed", "ready", "ok"}:
            raise RuntimeError("Doctor failed before model spending; inspect doctor.json")
        proofs = report["resolved_proofs"]
    else:
        # Internal callers may skip tooling probes, never the score baseline admission.
        from .doctor import evaluate_original
        from .baselines import freeze_original_baseline
        proofs = [freeze_original_baseline(item,
            evaluate_original(item, root / "doctor" / "proofs" / item["label"]), root / "baselines")
            for item in proofs]
    write(root / "benchmark" / "benchmark.json", {**benchmark.to_dict(), "proofs": proofs})
    payload = {"schema_version": 1, "root": str(root), "created_at": arena.utc_now(),
        "config": config.to_dict(), "source_hashes": runtime_source_hashes(),
        "input_hashes": {name: {"path": str(path), "sha256": file_hash(path)} for name, path in (
            ("input", config.input_path), ("heartbeats", config.heartbeat_path), ("env_map", config.env_map)) if path is not None},
        "benchmark_identity": benchmark.identity, "proofs": proofs,
        "model_identity": digest(config.openrouter),
        "policy_identity": digest({key: value for key, value in config.to_dict().items()
            if key not in {"input_path", "heartbeat_path", "env_map", "selected_proofs"}})}
    payload["identity"] = digest(payload)
    write(root / "resolved-config.json", payload)
    write(root / "state.json", {"schema_version": 1, "identity": payload["identity"],
        "status": "prepared", "created_at": payload["created_at"], "proofs": {}, "elapsed_seconds": 0})
    return payload


def proof_root(root: Path, item: Mapping) -> Path:
    label = item["label"]
    if not isinstance(label, str) or not label or label in {".", ".."} or any(c in label for c in "/\\"):
        raise ValueError("Unsafe proof label")
    return Path(root) / "proofs" / label


def proof_identity(snapshot: Mapping, item: Mapping) -> str:
    return digest({"run": snapshot["identity"], "proof": item["task_id"],
        "row": item["task_sha256"], "budget": snapshot["config"]["budget_usd"]})


def status(root: Path):
    root = Path(root).resolve()
    snapshot = load_snapshot(root, verify=False)
    state = read(root / "state.json") if (root / "state.json").exists() else {}
    cells = {}
    for item in snapshot["proofs"]:
        cell = proof_root(root, item)
        cell_state = read(cell / "state.json") if (cell / "state.json").exists() else {"status": "pending", "passes": []}
        best = read(cell / "best.json") if (cell / "best.json").exists() else None
        cells[item["label"]] = {"task_id": item["task_id"], "status": cell_state.get("status"),
            "passes": len(cell_state.get("passes", [])), "budget": cell_state.get("budget"),
            "best_score": best.get("score") if best else None,
            "candidate_sha256": best.get("sha256") if best else None,
            "elapsed_seconds": cell_state.get("elapsed_seconds", 0),
            **({"error": cell_state["error"]} if cell_state.get("error") else {})}
    return {"schema_version": 1, "root": str(root), "identity": snapshot["identity"],
        "status": state.get("status", "prepared"), "elapsed_seconds": state.get("elapsed_seconds", 0), "proofs": cells}



def host_secret_environment_names():
    patterns = ("API_KEY", "MANAGEMENT_KEY", "SECRET", "PASSWORD", "AUTHORIZATION", "ACCESS_TOKEN")
    return tuple(name for name in os.environ if any(pattern in name.upper() for pattern in patterns)
        or name in {"LRH_SERIAL_MODEL_TOKEN", "E6_BASELINE_CACHE", "E6_BASELINE_SEEDS", "E6_CODEX_HOME",
            "LEAN_E6_BASELINE_CACHE", "LEAN_REFACTOR_SEED_ARCHIVE"})


def worker_environment():
    excluded = set(host_secret_environment_names())
    return {name: value for name, value in os.environ.items() if name not in excluded}


def credential_forbidden_roots(snapshot: Mapping) -> tuple[Path, ...]:
    """Everything an agent can read in any selected proof, plus host run/source roots."""
    from e6.config import REPO_ROOT, runtime_root
    from e6.isolation import readonly_mount_paths, system_readable_paths
    public = snapshot['config']
    codex = Path(public['codex']).expanduser().resolve()
    # Exclude runtime containers as well as current mounts: creating a key file
    # must not turn a previously absent sidecar/package marker into a new mount.
    paths = [REPO_ROOT, Path(snapshot['root']), runtime_root(), codex.parent,
             Path(public['elan_home']), *system_readable_paths()]
    if codex.parent.name == 'bin':
        paths.append(codex.parent.parent / 'codex-package.json')
    for item in snapshot['proofs']:
        config = {**item, 'codex': public['codex'], 'agent_backend': 'codex'}
        paths.extend(readonly_mount_paths(config, elan_home=Path(public['elan_home'])))
    return tuple(dict.fromkeys(path.expanduser().resolve() for path in paths))


def validate_host_credential_path(path: Path, snapshot: Mapping) -> Path:
    """Fail before reading or creating credentials beneath an agent-visible mount."""
    resolved = Path(path).expanduser().resolve()
    if any(resolved.is_relative_to(root) for root in credential_forbidden_roots(snapshot)):
        raise ValueError('Host credential file overlaps an agent-visible filesystem mount')
    return resolved

def _bind_shared_identity(snapshot, fingerprint, *, check_proofs=True):
    """Bind the run before any worker starts; a crash cannot authorize a new key."""
    identity = {"schema_version": 1, "run_identity": snapshot["identity"],
                "budget_policy": "local-actual-cost-v1", "key_sha256": fingerprint}
    path = Path(snapshot["root"]) / "credential-identity.json"
    for item in snapshot["proofs"] if check_proofs else ():
        prior = proof_root(Path(snapshot["root"]), item) / "billing/relay-key-identity.json"
        if prior.exists() and read(prior) != {"schema_version": 1, "key_sha256": fingerprint}:
            raise ValueError(f"Proof credential identity differs: {item['label']}")
    try:
        with path.open("x", encoding="utf-8") as destination:
            json.dump(identity, destination, sort_keys=True)
            destination.write("\n")
            destination.flush()
            os.fsync(destination.fileno())
        descriptor = os.open(path.parent, os.O_DIRECTORY)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    except FileExistsError:
        if read(path) != identity:
            raise ValueError("Run credential identity and budget policy are immutable") from None


def _credential_arguments(snapshot, key_store=None, api_key_file=None):
    policy = snapshot["config"].get("budget_policy", "provider-key-v1")
    if key_store is not None and api_key_file is not None:
        raise ValueError("Choose either --api-key-file or legacy --key-store")
    if api_key_file is not None:
        if policy != "local-actual-cost-v1":
            raise ValueError("--api-key-file requires a run frozen with budget_policy=local-actual-cost-v1")
        from .openrouter import InferenceKeyFile
        path = validate_host_credential_path(api_key_file, snapshot)
        metadata = InferenceKeyFile(path).verify()
        _bind_shared_identity(snapshot, metadata["key_sha256"])
        return ["--api-key-file", str(path)]
    if not key_store:
        raise ValueError("Supply a host-only --api-key-file (or --key-store for a legacy provider-key run)")
    if policy != "provider-key-v1":
        raise ValueError("--key-store requires a run frozen with budget_policy=provider-key-v1")
    path = validate_host_credential_path(key_store, snapshot)
    if not path.is_file():
        raise FileNotFoundError(path)
    root = Path(snapshot["root"])
    from e6.config import REPO_ROOT
    if path.is_relative_to(root) or path.is_relative_to(REPO_ROOT):
        raise ValueError("Credentials must stay outside the run and source checkout")
    from .openrouter import ProofKeyStore
    store = ProofKeyStore(path, forbidden_roots=credential_forbidden_roots(snapshot))
    for item in snapshot["proofs"]:
        # Validate every selected proof before any worker can spend.
        metadata = store.metadata(proof_identity(snapshot, item))
        if metadata.get("state") != "active":
            raise ValueError(f"Proof key is unavailable: {item['label']}")
        if str(metadata.get("limit_usd")) != snapshot["config"]["budget_usd"]:
            from decimal import Decimal
            if Decimal(str(metadata.get("limit_usd"))) != Decimal(snapshot["config"]["budget_usd"]):
                raise ValueError(f"Proof key cap differs: {item['label']}")
        store.provider(proof_identity(snapshot, item))()
    return ["--key-store", str(path)]


def _metering_requeue_ready(snapshot, item):
    """Independently constrain coordinator results to settled metering failures."""
    from decimal import Decimal
    from e6.experiment import blocking_unknown_usage
    from .openrouter.ledger import read_openrouter_receipt
    cell = proof_root(Path(snapshot["root"]), item)
    state = read(cell / "state.json")
    passes = state.get("passes", [])
    latest = passes[-1] if passes else None
    if latest is not None and latest.get("validation_healthy") is not True:
        return False
    receipt = read_openrouter_receipt(cell / "billing/openrouter.sqlite")
    budget = {**receipt["budget"], "recovery_policy": snapshot["config"].get("recovery_policy", "none")}
    if (receipt["identity"]["proof_id"] != proof_identity(snapshot, item)
            or Decimal(receipt["identity"]["limit_usd"]) != Decimal(snapshot["config"]["budget_usd"])
            or budget["active_requests"] or blocking_unknown_usage(budget)
            or Decimal(budget["remaining_usd"]) <= 0):
        return False
    number = latest["pass_number"] if latest is not None else state.get("pass_number")
    same_pass = [row for row in receipt["requests"] if row["pass_number"] == number]
    if any(row["metadata"].get("protocol_conflict") is True for row in same_pass):
        return False
    status = state.get("status")
    if status in {"unknown_usage", "unreconciled_provider_cost", "upstream_http_error", "upstream_error"}:
        return True
    return (status == "failed" and latest is not None and latest["pass_number"] == state.get("pass_number")
        and bool(same_pass) and same_pass[-1]["metadata"].get("transport_failure") is True
        and same_pass[-1]["metadata"].get("transport_error_category") in {
            "timeout", "connection_lost", "incomplete_response", "invalid_response",
            "upstream_http_error", "transport_error"})


def run(root: Path, *, key_store: Path | None = None, api_key_file: Path | None = None, resume=False):
    """Run workers as isolated processes; parent owns scheduling, never model auth."""
    root = Path(root).resolve()
    with run_lock(root):
        snapshot = load_snapshot(root)
        credential_args = _credential_arguments(snapshot, key_store, api_key_file)
        prior = read(root / "state.json")
        if not resume and prior.get("status") != "prepared":
            raise RuntimeError("Run already started; use harness resume")
        state = {**prior, "status": "running", "pid": os.getpid(), "updated_at": arena.utc_now()}
        state.pop("finished_at", None)
        state.pop("recovery_error", None)
        start, elapsed = time.monotonic(), float(prior.get("elapsed_seconds", 0))
        pending = []
        for item in snapshot["proofs"]:
            cell = proof_root(root, item)
            cell_state = read(cell / "state.json") if (cell / "state.json").exists() else {}
            if resume and cell_state.get("status") in COMPLETE:
                continue
            pending.append(item)
        active = {}
        code = 0
        recovery = None
        automatic_requeues = set()
        try:
            if snapshot["config"].get("recovery_policy", "none") != "none" and api_key_file is not None:
                try:
                    from .recovery import RecoveryCoordinator
                    recovery = RecoveryCoordinator(root, snapshot, api_key_file=api_key_file)
                    recovery.initialize()
                except (RuntimeError, ValueError, OSError) as error:
                    state["recovery_error"] = {"type": type(error).__name__,
                        "message": "Automatic recovery initialization failed; inspect host recovery evidence"}
                    state.update(status="needs_attention", finished_at=arena.utc_now())
                    return 1
            while True:
                while pending and len(active) < snapshot["config"]["concurrency"]:
                    item = pending.pop(0)
                    cell = proof_root(root, item)
                    cell.mkdir(parents=True, exist_ok=True)
                    log = (cell / "worker.log").open("a", encoding="utf-8")
                    argv = [sys.executable, "-m", "harness", "_proof", str(root), item["label"], *credential_args]
                    if resume or item["label"] in automatic_requeues:
                        argv.append("--resume")
                    from e6.config import REPO_ROOT
                    process = subprocess.Popen(argv, cwd=REPO_ROOT, stdout=log, stderr=subprocess.STDOUT,
                        start_new_session=True, env=worker_environment())
                    process_memory.capture_process_identity(process)
                    active[process.pid] = (process, item, log)
                for pid, (process, item, log) in list(active.items()):
                    result = process.poll()
                    if result is not None:
                        process.wait()
                        log.close()
                        active.pop(pid)
                        code = max(code, int(result != 0))
                        state.setdefault("worker_returncodes", {})[item["label"]] = result
                if not pending and not active:
                    labels = []
                    if recovery is not None:
                        try:
                            labels = recovery.recover()
                            by_label = {item["label"]: item for item in snapshot["proofs"]}
                            if (not isinstance(labels, list) or any(not isinstance(label, str) for label in labels)
                                    or len(labels) != len(set(labels))
                                    or any(label not in by_label
                                        or label in automatic_requeues for label in labels)
                                    or any(not _metering_requeue_ready(snapshot, by_label[label]) for label in labels)):
                                raise RuntimeError("Recovery returned an ineligible or already retried proof")
                        except (RuntimeError, ValueError, OSError) as error:
                            state["recovery_error"] = {"type": type(error).__name__,
                                "message": "Automatic metering recovery stopped; inspect host recovery evidence"}
                            code = 1
                            break
                    if not labels:
                        break
                    automatic_requeues.update(labels)
                    state["automatic_requeues"] = sorted(automatic_requeues)
                    pending.extend(by_label[label] for label in labels)
                state.update(elapsed_seconds=elapsed + time.monotonic() - start, updated_at=arena.utc_now())
                write(root / "state.json", state)
                if pending or active:
                    time.sleep(0.2)
            if recovery is not None:
                # Reconciliation can either revoke a provisional completion or
                # exhaust a failed worker's remaining allowance without another
                # worker. Keep its return code as history; use current terminal
                # proof/accounting states for this recovery-enabled invocation.
                code = int(bool(state.get("recovery_error")) or any(
                    not (proof_root(root, item) / "state.json").is_file()
                    or read(proof_root(root, item) / "state.json").get("status") not in COMPLETE
                    for item in snapshot["proofs"]))
            state.update(status="completed" if code == 0 else "needs_attention", finished_at=arena.utc_now())
            return code
        except BaseException:
            state.update(status="interrupted", finished_at=arena.utc_now())
            raise
        finally:
            # Give native workers SIGTERM so their own cleanup preserves candidates and accounting.
            for process, item, log in active.values():
                process.terminate()
            for process, item, log in active.values():
                try:
                    process.wait(timeout=45)
                except subprocess.TimeoutExpired:
                    arena.terminate_process_tree(process)
                log.close()
            state.update(elapsed_seconds=elapsed + time.monotonic() - start, updated_at=arena.utc_now())
            write(root / "state.json", state)
            write(root / "results.json", status(root))


def run_proof(root: Path, label: str, *, credentials=None, key_store=None, api_key_file=None, resume=False):
    snapshot = load_snapshot(root)
    item = next((item for item in snapshot["proofs"] if item["label"] == label), None)
    if item is None:
        raise ValueError("Proof is absent from frozen selection")
    if sum(value is not None for value in (credentials, key_store, api_key_file)) > 1:
        raise ValueError("Choose one host credential source")
    if key_store is not None:
        key_store = validate_host_credential_path(key_store, snapshot)
    if credentials is not None:
        credentials = validate_host_credential_path(credentials, snapshot)
    provider = None
    if api_key_file is not None:
        from .openrouter import InferenceKeyFile
        import hashlib
        if snapshot["config"].get("budget_policy", "provider-key-v1") != "local-actual-cost-v1":
            raise ValueError("Shared keys require the frozen local budget policy")
        path = validate_host_credential_path(api_key_file, snapshot)
        key_file = InferenceKeyFile(path)
        fingerprint = hashlib.sha256(key_file.credential().encode()).hexdigest()
        # Normally the scheduler verified and bound this key before dispatch.
        # Direct private worker entry still requires read-only verification once.
        if not (Path(snapshot["root"]) / "credential-identity.json").exists():
            fingerprint = key_file.verify()["key_sha256"]
        _bind_shared_identity(snapshot, fingerprint, check_proofs=False)
        provider = key_file.provider(fingerprint)
    if key_store is not None and snapshot["config"].get("budget_policy", "provider-key-v1") != "provider-key-v1":
        raise ValueError("Legacy proof keys require the frozen provider-key budget policy")
    cell = proof_root(Path(root), item)
    with run_lock(cell):
        from e6.run import prepare_product, run_product
        if (not (cell / "config.json").exists() or not read(cell / "config.json").get("product_schema_version")
                or not read(cell / "config.json").get("tool_preflight_sha256")):
            prepare_product(cell, item, snapshot)
        if key_store:
            from .openrouter import ProofKeyStore
            store = ProofKeyStore(Path(key_store), forbidden_roots=credential_forbidden_roots(snapshot))
            provider = store.provider(proof_identity(snapshot, item))
        return run_product(cell, auth_path=Path(credentials) if credentials else None,
            credential_provider=provider, resume=resume)
