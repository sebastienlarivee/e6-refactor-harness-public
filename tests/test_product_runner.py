"""Offline product integration: durable real SQLite billing, scripted native/Lean edges."""
from contextlib import nullcontext
from copy import deepcopy
import json
import os
from pathlib import Path
import subprocess
import sys
from types import SimpleNamespace

import pytest

from e6 import proof, run as core
from harness import runner
from harness.config import RunConfig, file_hash
from harness.openrouter import OpenRouterLedger


@pytest.fixture
def cell(tmp_path, monkeypatch):
    root = tmp_path / "run"
    cell = root / "proofs" / "tiny"
    cell.mkdir(parents=True)
    codex = tmp_path / "tooling/bin/codex"; codex.parent.mkdir(parents=True); codex.write_text("scripted")
    elan = tmp_path / "elan"; elan.mkdir()
    public = RunConfig.from_dict({"input": "input.jsonl", "heartbeats": "h.json", "env_map": "env.toml",
        "budget_policy": "provider-key-v1",
        "recovery_policy": "none",
        "optimizer": "off", "runtime": {"codex": str(codex), "elan_home": str(elan)},
        "openrouter": {"model_id": "test/model", "provider": "Test", "input_price_per_million": "1",
            "output_price_per_million": "1", "context_length": 10000, "max_output_tokens": 1000,
            "supported_reasoning_efforts": ["high"], "default_reasoning_effort": "high"}}, base=tmp_path)
    task = cell / "Task.json"; task.write_text('{"name":"tiny"}')
    metadata = {"label": "tiny", "task_id": "Tiny", "task": str(task), "task_sha256": file_hash(task),
        "original_tokens": 100, "original_heartbeats": 100, "primary": str(tmp_path / "primary"),
        "compatibility": [], "registry_source": str(cell / "registry.json")}
    snapshot = {"root": str(root), "identity": "fixed-run", "proofs": [metadata], "config": public.to_dict()}
    config = {**metadata, "root": str(cell), "proof_metadata_sha256": "fixed-proof",
        "product_metadata": metadata, "product_run_root": str(root), "product_run_identity": snapshot["identity"],
        "proof_budget_identity": runner.proof_identity(snapshot, metadata), "optimizer": "off", "product_schema_version": 1,
        "elan_home": str(elan), "codex": str(codex), "codex_sha256": file_hash(codex),
        "openrouter": public.openrouter, "source_hashes": {}, **public.experiment_spec().proof_settings()}
    for name in ("model_catalog", "tool_preflight"):
        path = cell / f"{name}.json"; path.write_text('{"status":"passed"}')
        config[name], config[f"{name}_sha256"] = str(path), file_hash(path)
    def candidate(source, tokens=100, heartbeats=100):
        return {**proof._incumbent_metadata(config), "source": source, "sha256": proof._digest(source),
            "tokens": tokens, "heartbeats": heartbeats, "compatibility_pct": 100,
            "score": proof._policy(config).score(tokens=tokens, heartbeats=heartbeats, compatibility_pct=100),
            "valid": True, "compatibility_complete": True, "selected_path": str(cell / "Original.lean")}
    initial = candidate("original proof")
    improved = candidate("improved proof", 20, 10)
    config["initial_best"] = initial
    runner.write(cell / "config.json", config)
    runner.write(cell / "state.json", {"status": "prepared", "passes": [], "elapsed_seconds": 0})
    monkeypatch.setattr(runner, "load_snapshot", lambda *a, **k: deepcopy(snapshot))
    monkeypatch.setattr(core, "configure_native_environment", lambda **k: {})
    monkeypatch.setattr(core, "environment", lambda *a, **k: {})
    monkeypatch.setattr(core, "host_environment", lambda *a, **k: {})
    monkeypatch.setattr(core, "low_priority", lambda *a: None)
    monkeypatch.setattr(proof, "_verify_config", lambda *a: None)
    monkeypatch.setattr(core.resource_gate, "permit_from_environment", lambda *a, **k: nullcontext())
    class Broker:
        def __init__(self, *a, **k): pass
        def start(self): pass
        def begin_pass(self, number): return {}
        def end_pass(self): pass
        def close(self): pass
    monkeypatch.setattr(core.broker_lifecycle, "BrokerHost", Broker)
    checks = []
    def finalize(config, capsule, best):
        checks.append(capsule.name)
        selected = {**improved, "selected_path": str(capsule / "Selected.lean")}
        (capsule / "Selected.lean").write_text(selected["source"])
        runner.write(capsule / "selection.json", {**selected, "validation_healthy": True})
        return selected
    monkeypatch.setattr(proof, "finalize", finalize)
    def capsule(root, number, source, remaining):
        path = root / f"pass-{number:03d}"; path.mkdir()
        (path / "Candidate.lean").write_text(source)
        return path
    monkeypatch.setattr(proof, "make_capsule", capsule)
    auth = tmp_path / "host-key"; auth.write_text("synthetic-never-dispatched")
    return SimpleNamespace(root=root, cell=cell, config=config, snapshot=snapshot, public=public,
        initial=initial, improved=improved, auth=auth, checks=checks, candidate=candidate)


def charge(relay, number, amount="3"):
    relay.set_pass(number)
    identity = relay.ledger.reserve(amount, pass_number=number)
    relay.ledger.mark_dispatched(identity)
    relay.ledger.settle(identity, cost_usd=amount, generation_id=f"fake-generation-{number}")


def output_limit(relay, number, capsule, amount="1"):
    """Model-independent native Responses terminal with a durable provider bill."""
    relay.set_pass(number)
    identity = relay.ledger.reserve(relay.status()["remaining_usd"], pass_number=number)
    relay.ledger.mark_dispatched(identity)
    relay.ledger.settle(identity, cost_usd=amount, generation_id=f"limited-generation-{number}",
        metadata={"status": "incomplete", "incomplete_reason": "max_output_tokens"})
    message = "Incomplete response returned, reason: max_output_tokens"
    (capsule / "codex-events.jsonl").write_text("\n".join(json.dumps(event) for event in [
        {"type": "error", "message": message},
        {"type": "turn.failed", "error": {"message": message}}]) + "\n")
    outcome = {"status": "failed", "native_status": "failed", "returncode": 1}
    runner.write(capsule / "agent-run.json", outcome)
    return outcome


def test_output_limit_starts_fresh_capsule_from_verified_checkpoint_using_same_ledger(cell, monkeypatch):
    calls = []
    ledgers = []
    def execute(config, root, capsule, relay, state):
        number = state["pass_number"]
        calls.append(capsule.name)
        ledgers.append(relay.ledger)
        if number == 1:
            return output_limit(relay, number, capsule)
        assert number == 2 and relay.status()["spent_usd"] == "1"
        assert (capsule / "Candidate.lean").read_text() == cell.improved["source"]
        charge(relay, number, "2")
        outcome = {"status": "completed", "native_status": "completed", "returncode": 0}
        runner.write(capsule / "agent-run.json", outcome)
        return outcome
    monkeypatch.setattr(core, "execute_pass", execute)
    assert core.run_product(cell.cell, auth_path=cell.auth) == 0
    state = runner.read(cell.cell / "results.json")
    assert calls == ["pass-001", "pass-002"] and ledgers[0] is ledgers[1]
    assert state["status"] == "budget_reached" and state["budget"]["spent_usd"] == "3"
    failed = state["passes"][0]
    assert failed["agent_status"] == failed["native_status"] == "failed"
    assert failed["native_returncode"] == 1
    assert failed["native_failure_recovery"]["reason"] == "max_output_tokens"
    assert len(ledgers[0].requests()) == 2
    assert len({row["generation_id"] for row in ledgers[0].requests()}) == 2
    assert not (cell.cell / "resumes").exists()


@pytest.mark.parametrize("failure", ["native_message", "provider_reason", "provider_status", "missing_reason",
    "unknown", "active", "halted", "billing_incomplete", "validation", "wrong_pass", "free", "missing_events",
    "unsettled", "missing_receipt", "missing_generation", "budget", "native_status", "returncode"])
def test_output_limit_recovery_requires_matching_terminal_and_healthy_settled_boundary(cell, failure):
    from decimal import Decimal
    ledger = OpenRouterLedger(cell.cell / "billing/openrouter.sqlite", proof_id=cell.config["proof_budget_identity"],
        model="test/model", limit_usd="3")
    class Relay:
        def set_pass(self, number): pass
        def status(self): return {"remaining_usd": "3"}
    relay = Relay(); relay.ledger = ledger
    capsule = cell.cell / "pass-001"; capsule.mkdir()
    outcome = output_limit(relay, 1, capsule)
    budget = {"active_requests": 0, "unknown_requests": 0, "cost_reporting_complete": True,
        "halted_reason": None, "stop_reason": None, "pass": 1, "remaining_usd": "2",
        "pass_receipts": ledger.requests()}
    record = {"pass_number": 1, "validation_healthy": True}
    assert core._product_output_limit_recovery(capsule, outcome, record, budget)
    last = budget["pass_receipts"][-1]
    if failure == "native_message":
        path = capsule / "codex-events.jsonl"
        path.write_text(path.read_text().replace("max_output_tokens", "content_filter"))
    elif failure == "provider_reason": last["metadata"]["incomplete_reason"] = "content_filter"
    elif failure == "provider_status": last["metadata"]["status"] = "completed"
    elif failure == "missing_reason": last["metadata"].pop("incomplete_reason")
    elif failure == "unknown": budget["unknown_requests"] = 1
    elif failure == "active": budget["active_requests"] = 1
    elif failure == "halted": budget["halted_reason"] = "accounting_error"
    elif failure == "billing_incomplete": budget["cost_reporting_complete"] = False
    elif failure == "validation": record["validation_healthy"] = False
    elif failure == "wrong_pass": last["pass_number"] = 2
    elif failure == "free": last["cost_usd"] = Decimal(0)
    elif failure == "missing_events": (capsule / "codex-events.jsonl").unlink()
    elif failure == "unsettled": last["state"] = "unknown"
    elif failure == "missing_receipt": budget["pass_receipts"] = []
    elif failure == "missing_generation": last["generation_id"] = None
    elif failure == "budget": budget["remaining_usd"] = "0"
    elif failure == "native_status": outcome["native_status"] = "interrupted"
    elif failure == "returncode": outcome["returncode"] = 0
    assert core._product_output_limit_recovery(capsule, outcome, record, budget) is None


def test_output_limit_recovery_obeys_diagnostic_pass_cap(cell, monkeypatch):
    from dataclasses import replace
    public = replace(cell.public, diagnostic_max_passes=1)
    cell.snapshot["config"] = public.to_dict()
    cell.config.update(**public.experiment_spec().proof_settings())
    cell.config["proof_budget_identity"] = runner.proof_identity(cell.snapshot, cell.snapshot["proofs"][0])
    runner.write(cell.cell / "config.json", cell.config)
    calls = []
    def execute(config, root, capsule, relay, state):
        calls.append(state["pass_number"])
        return output_limit(relay, state["pass_number"], capsule)
    monkeypatch.setattr(core, "execute_pass", execute)
    assert core.run_product(cell.cell, auth_path=cell.auth) == 0
    state = runner.read(cell.cell / "results.json")
    assert calls == [1] and state["status"] == "diagnostic_pass_cap"
    assert state["budget"]["spent_usd"] == "1" and state["budget"]["remaining_usd"] == "2"


def test_budget_terminal_failed_native_pass_preserves_verified_candidate_and_real_ledger(cell, monkeypatch):
    def execute(config, root, capsule, relay, state):
        charge(relay, state["pass_number"])
        outcome = {"status": "failed", "returncode": 9, "native_status": "failed"}
        runner.write(capsule / "agent-run.json", outcome)
        return outcome
    monkeypatch.setattr(core, "execute_pass", execute)
    assert core.run_product(cell.cell, auth_path=cell.auth) == 0
    best = runner.read(cell.cell / "best.json")
    assert best["sha256"] == cell.improved["sha256"]
    assert Path(best["selected_path"]).is_relative_to(cell.cell / "verified")
    assert runner.read(cell.cell / "results.json")["status"] == "budget_reached"
    ledger = OpenRouterLedger(cell.cell / "billing/openrouter.sqlite", proof_id=cell.config["proof_budget_identity"], model="test/model", limit_usd="3")
    assert str(ledger.snapshot()["spent_usd"]) == "3"
    assert core.run_product(cell.cell, auth_path=cell.auth, resume=True) == 0
    assert len(ledger.requests()) == 1 and cell.checks == ["pass-001"]


def test_interrupted_native_turn_finalizes_checkpoint_and_resume_keeps_accounting(cell, monkeypatch):
    def interrupted(config, root, capsule, relay, state):
        charge(relay, state["pass_number"], "1")
        runner.write(capsule / "agent-run.json", {"status": "interrupted", "returncode": -15})
        raise KeyboardInterrupt("scripted signal")
    monkeypatch.setattr(core, "execute_pass", interrupted)
    assert core.run_product(cell.cell, auth_path=cell.auth) == 1
    assert runner.read(cell.cell / "best.json")["sha256"] == cell.improved["sha256"]
    def complete(config, root, capsule, relay, state):
        assert relay.status()["spent_usd"] == "1"
        assert state["pass_number"] == 2
        charge(relay, 2, "2")
        outcome = {"status": "completed", "native_status": "completed", "returncode": 0}
        runner.write(capsule / "agent-run.json", outcome)
        return outcome
    monkeypatch.setattr(core, "execute_pass", complete)
    assert core.run_product(cell.cell, auth_path=cell.auth, resume=True) == 0
    state = runner.read(cell.cell / "results.json")
    assert state["budget"]["spent_usd"] == "3" and len(state["passes"]) == 2
    assert not (cell.cell / "resumes").exists()


def test_provider_final_charge_overrun_finishes_as_budget_stop_and_resume_is_free(cell, monkeypatch):
    calls = []
    def execute(config, root, capsule, relay, state):
        calls.append(state["pass_number"])
        relay.set_pass(1)
        identity = relay.ledger.reserve("3", pass_number=1)
        relay.ledger.mark_dispatched(identity)
        relay.ledger.settle(identity, cost_usd="3.001")
        result = {"status": "budget_reached", "native_status": "failed", "returncode": -15}
        runner.write(capsule / "agent-run.json", result)
        return result
    monkeypatch.setattr(core, "execute_pass", execute)
    assert core.run_product(cell.cell, auth_path=cell.auth) == 0
    state = runner.read(cell.cell / "results.json")
    assert state["status"] == "budget_reached" and state["budget"]["over_budget_usd"] == "0.001"
    assert runner.read(cell.cell / "best.json")["sha256"] == cell.improved["sha256"]
    assert core.run_product(cell.cell, auth_path=cell.auth, resume=True) == 0
    assert calls == [1]


def test_resume_finishes_unrecorded_validation_before_new_inference(cell, monkeypatch):
    capsule = cell.cell / "pass-001"; capsule.mkdir()
    (capsule / "Candidate.lean").write_text("partial native result")
    runner.write(capsule / "agent-run.json", {"status": "failed", "returncode": 1})
    ledger = OpenRouterLedger(cell.cell / "billing/openrouter.sqlite", proof_id=cell.config["proof_budget_identity"], model="test/model", limit_usd="3")
    identity = ledger.reserve("3", pass_number=1); ledger.mark_dispatched(identity)
    ledger.settle(identity, cost_usd="3", generation_id="saved-generation")
    monkeypatch.setattr(core, "execute_pass", lambda *a: pytest.fail("must not start another paid turn"))
    assert core.run_product(cell.cell, auth_path=cell.auth, resume=True) == 0
    assert cell.checks == ["pass-001"]
    assert runner.read(cell.cell / "best.json")["sha256"] == cell.improved["sha256"]


def test_missing_receipt_does_not_block_completed_native_pass_or_erase_proof(cell, monkeypatch):
    calls = []
    def execute(config, root, capsule, relay, state):
        number = state["pass_number"]
        calls.append(number)
        if number == 1:
            relay.set_pass(1)
            identity = relay.ledger.reserve("3", pass_number=1)
            relay.ledger.mark_dispatched(identity)
            relay.ledger.mark_unknown(identity, "synthetic missing receipt", blocks_spending=False)
        else:
            assert number == 2
            assert relay.status()["unknown_requests"] == 1
            assert relay.status()["active_requests"] == 0
            charge(relay, 2, "0.5")
            relay._stop("budget_reached", "Synthetic provider key limit")
        result = {"status": "completed", "native_status": "completed", "returncode": 0}
        runner.write(capsule / "agent-run.json", result)
        return result
    monkeypatch.setattr(core, "execute_pass", execute)
    assert core.run_product(cell.cell, auth_path=cell.auth) == 0
    assert calls == [1, 2]
    assert runner.read(cell.cell / "best.json")["sha256"] == cell.improved["sha256"]
    budget = runner.read(cell.cell / "state.json")["budget"]
    assert budget["unknown_requests"] == 1 and budget["active_requests"] == 0
    assert budget["spent_usd"] == "0.5" and budget["cost_reporting_complete"] is False
    # The actual provider stop remains durable; missing receipts remain unknown.
    assert core.run_product(cell.cell, auth_path=cell.auth, resume=True) == 0
    assert calls == [1, 2]


def test_lock_excludes_real_second_process_and_recovers_stale_pid(tmp_path):
    script = "from harness.runner import run_lock; from pathlib import Path; import sys;\nwith run_lock(Path(sys.argv[1])): print('admitted')"
    with runner.run_lock(tmp_path):
        child = subprocess.run([sys.executable, "-c", script, str(tmp_path)], capture_output=True, text=True)
        assert child.returncode != 0 and "already holds" in child.stderr
    child = subprocess.run([sys.executable, "-c", script, str(tmp_path)], capture_output=True, text=True)
    assert child.returncode == 0 and "admitted" in child.stdout


def test_private_checkpoint_is_preserved_if_presentation_file_corrupts(cell):
    best = core._product_publish_best(cell.cell, cell.config, cell.improved)
    (cell.cell / "Selected.lean").write_text("unfinished user-visible copy")
    restored = core._product_best(cell.cell, cell.config)
    assert restored["source"] == cell.improved["source"]
    assert restored["selected_path"] == best["selected_path"]


def test_unfinished_optimizer_boundary_recovers_before_budget_exit_or_new_native_pass(cell, monkeypatch):
    from dataclasses import replace
    from harness import optimizer
    public = replace(cell.public, optimizer="compact")
    cell.snapshot["config"] = public.to_dict()
    cell.config.update(optimizer="compact", **public.experiment_spec().proof_settings())
    runner.write(cell.cell / "config.json", cell.config)
    calls = []
    def optimize(config, root, capsule, best, selection):
        calls.append(capsule.name)
        transaction = root / "optimizer-boundaries" / capsule.name / "transaction.json"
        transaction.parent.mkdir(parents=True, exist_ok=True)
        if not transaction.exists():
            runner.write(transaction, {"status": "verified"})
            raise KeyboardInterrupt("crash after optimizer staged output")
        runner.write(transaction, {"status": "committed"})
        return best, selection, {"status": "recovered", "model_calls": 0}
    monkeypatch.setattr(optimizer, "optimize_pass_result", optimize)
    def execute(config, root, capsule, relay, state):
        charge(relay, 1)
        result = {"status": "completed", "native_status": "completed", "returncode": 0}
        runner.write(capsule / "agent-run.json", result)
        return result
    monkeypatch.setattr(core, "execute_pass", execute)
    assert core.run_product(cell.cell, auth_path=cell.auth) == 1
    assert runner.read(cell.cell / "best.json")["sha256"] == cell.improved["sha256"]
    assert runner.read(cell.cell / "host-boundaries/pass-001.json")["status"] == "validated"
    monkeypatch.setattr(core, "execute_pass", lambda *a: pytest.fail("resume must recover optimizer before any new inference"))
    assert core.run_product(cell.cell, auth_path=cell.auth, resume=True) == 0
    assert calls == ["pass-001", "pass-001"] and cell.checks == ["pass-001"]
    assert runner.read(cell.cell / "host-boundaries/pass-001.json")["status"] == "committed"
    assert runner.read(cell.cell / "state.json")["budget"]["spent_usd"] == "3"


@pytest.mark.parametrize("concurrency", [1, 2])
def test_scheduler_runs_real_subprocesses_at_selected_concurrency_and_retains_failure_results(tmp_path, monkeypatch, concurrency):
    root = tmp_path / "run"; root.mkdir()
    rows = [{"label": f"proof-{n}", "task_id": f"Task{n}", "task_sha256": str(n)} for n in range(4)]
    snapshot = {"root": str(root), "identity": "frozen", "proofs": rows, "config": {"concurrency": concurrency}}
    runner.write(root / "state.json", {"status": "prepared", "elapsed_seconds": 0})
    monkeypatch.setattr(runner, "load_snapshot", lambda *a, **k: snapshot)
    monkeypatch.setattr(runner, "_credential_arguments", lambda *a: [])
    real_popen = subprocess.Popen
    script = """import json,sys,time
from pathlib import Path
root,label=Path(sys.argv[1]),sys.argv[2]
with (root/'events.jsonl').open('a') as log: log.write(json.dumps({'kind':'start','proof':label,'time':time.monotonic()})+'\\n')
time.sleep(0.25)
cell=root/'proofs'/label
(cell/'state.json').write_text(json.dumps({'status':'failed' if label=='proof-1' else 'budget_reached','passes':[],'budget':{'spent_usd':'1.5'}}))
(cell/'best.json').write_text(json.dumps({'sha256':label,'score':42}))
with (root/'events.jsonl').open('a') as log: log.write(json.dumps({'kind':'end','proof':label,'time':time.monotonic()})+'\\n')
sys.exit(1 if label=='proof-1' else 0)
"""
    def launch(argv, **kwargs):
        return real_popen([sys.executable, "-c", script, argv[4], argv[5]], **kwargs)
    monkeypatch.setattr(runner.subprocess, "Popen", launch)
    assert runner.run(root, key_store=tmp_path / "ignored") == 1
    events = [json.loads(line) for line in (root / "events.jsonl").read_text().splitlines()]
    active = peak = 0
    for event in sorted(events, key=lambda row: row["time"]):
        active += 1 if event["kind"] == "start" else -1
        peak = max(peak, active)
    assert peak == concurrency and active == 0
    result = runner.read(root / "results.json")
    assert result["status"] == "needs_attention"
    assert all(item["best_score"] == 42 for item in result["proofs"].values())
    assert result["proofs"]["proof-1"]["status"] == "failed"
    assert not (root / "resolved-config.json").exists()  # Scheduler never rewrites immutable configuration.


def test_worker_environment_excludes_ambient_credentials_and_archives(monkeypatch):
    monkeypatch.setenv("OPENROUTER_MANAGEMENT_KEY", "management-secret")
    monkeypatch.setenv("OPENROUTER_API_KEY", "inference-secret")
    monkeypatch.setenv("OPENAI_API_KEY", "account-secret")
    monkeypatch.setenv("E6_BASELINE_SEEDS", "/old/archive")
    monkeypatch.setenv("HARNESS_PUBLIC_SETTING", "safe")
    environment = runner.worker_environment()
    assert "OPENROUTER_MANAGEMENT_KEY" not in environment
    assert "OPENROUTER_API_KEY" not in environment and "OPENAI_API_KEY" not in environment
    assert "E6_BASELINE_SEEDS" not in environment and environment["HARNESS_PUBLIC_SETTING"] == "safe"


@pytest.mark.parametrize("native_status", ["failed", "accounted_disconnect"])
@pytest.mark.parametrize("stop", [None, "budget_reached"])
def test_paid_failed_attempt_never_churns_fresh_contexts(cell, monkeypatch, stop, native_status):
    expected = stop or native_status
    calls = []
    def execute(config, root, capsule, relay, state):
        calls.append(state["pass_number"])
        charge(relay, state["pass_number"], "0.1")
        if stop:
            relay._stop(stop, "Scripted provider key rejection")
        result = {"status": native_status, "returncode": 1, "native_status": "failed"}
        runner.write(capsule / "agent-run.json", result)
        return result
    monkeypatch.setattr(core, "execute_pass", execute)
    code = core.run_product(cell.cell, auth_path=cell.auth)
    state = runner.read(cell.cell / "state.json")
    assert state["status"] == expected and code == int(expected != "budget_reached")
    assert state["budget"]["spent_usd"] == "0.1"
    assert state["best_score"] == cell.improved["score"]
    assert calls == [1]
    assert len(state["passes"]) == 1
    if stop:
        monkeypatch.setattr(core, "execute_pass", lambda *a: pytest.fail("a capped key must not restart"))
        assert core.run_product(cell.cell, auth_path=cell.auth, resume=True) == 0


def test_product_tool_preflight_uses_frozen_external_catalog(cell, monkeypatch):
    calls = []
    registry = cell.cell / "registry.json"; registry.write_text("{}")
    config = {**cell.config, "fingerprint_registry": str(registry)}
    def prepare(capsule, *args, **kwargs):
        capsule.mkdir(parents=True, exist_ok=True)
    monkeypatch.setattr(core.swarm, "prepare_capsule", prepare)
    monkeypatch.setattr(core.feedback, "configure_capsule", lambda *a, **k: None)
    def preflight(codex, models, capsule, *, output, **options):
        calls.append(options)
        runner.write(output, {"status": "passed", "model_calls": 0})
    monkeypatch.setattr(core.codex_preflight, "preflight", preflight)
    output = core.tool_preflight(cell.cell, config)
    assert runner.read(output)["status"] == "passed"
    assert calls == [{"provider": "openrouter", "model_catalog": Path(config["model_catalog"])}]
    config.pop("product_schema_version")
    core.tool_preflight(cell.cell, config)
    assert calls[-1] == {}


def test_missing_later_proof_key_blocks_all_workers_before_first_dispatch(tmp_path, monkeypatch):
    import harness.openrouter as provider
    root = tmp_path / "run"; root.mkdir()
    key_store = tmp_path / "keys.json"; key_store.write_text("{}")
    rows = [{"label": f"proof-{n}", "task_id": f"Task{n}", "task_sha256": str(n)} for n in range(2)]
    snapshot = {"root": str(root), "identity": "frozen", "proofs": rows, "config": {"budget_usd": "3", "concurrency": 2,
        "codex": sys.executable, "elan_home": str(tmp_path / "elan")}}
    runner.write(root / "state.json", {"status": "prepared"})
    monkeypatch.setattr(runner, "load_snapshot", lambda *a, **k: snapshot)
    identities = [runner.proof_identity(snapshot, item) for item in rows]
    class Keys:
        def __init__(self, *a, **k): pass
        def metadata(self, identity):
            if identity == identities[1]: raise ValueError("Second proof key unavailable")
            return {"state": "active", "limit_usd": "3"}
        def provider(self, identity): return lambda: "synthetic-key"
    monkeypatch.setattr(provider, "ProofKeyStore", Keys)
    monkeypatch.setattr(runner.subprocess, "Popen", lambda *a, **k: pytest.fail("no proof may dispatch"))
    with pytest.raises(ValueError, match="Second proof key"):
        runner.run(root, key_store=key_store)
    assert runner.read(root / "state.json")["status"] == "prepared"


def test_frozen_config_input_and_environment_checks_fail_closed(tmp_path, monkeypatch):
    from harness.config import digest
    import harness.environments as environments
    root = tmp_path / "run"; root.mkdir()
    source = tmp_path / "original.jsonl"; source.write_text("original contest row")
    task = root / "Task.json"; task.write_text("frozen row")
    metadata = {"label": "tiny", "task": str(task), "task_sha256": file_hash(task)}
    payload = {"schema_version": 1, "root": str(root), "source_hashes": {"harness/runner.py": "source"},
        "input_hashes": {"input": {"path": str(source), "sha256": file_hash(source)}}, "proofs": [metadata], "config": {"budget_usd": "3"}}
    payload["identity"] = digest(payload)
    runner.write(root / "resolved-config.json", payload)
    seen = []
    monkeypatch.setattr(runner, "verify_source_hashes", lambda hashes: seen.append(hashes))
    monkeypatch.setattr(environments, "verify_resolved_metadata", lambda item: seen.append(item))
    assert runner.load_snapshot(root)["identity"] == payload["identity"]
    assert len(seen) == 2
    source.write_text("changed contest row")
    with pytest.raises(RuntimeError, match="Frozen input changed"):
        runner.load_snapshot(root)
    source.write_text("original contest row")
    payload["config"]["budget_usd"] = "1.5"
    runner.write(root / "resolved-config.json", payload)
    with pytest.raises(RuntimeError, match="identity changed"):
        runner.load_snapshot(root)


def test_private_raw_relay_entry_rejects_agent_readable_auth_before_ledger_creation(cell):
    primary = Path(cell.config["primary"]); primary.mkdir()
    exposed = primary / "synthetic-key.txt"; exposed.write_text("SYNTHETIC_KEY_ONLY")
    with pytest.raises(ValueError, match="agent-visible"):
        core.run_product(cell.cell, auth_path=exposed)
    assert not (cell.cell / "billing/openrouter.sqlite").exists()


@pytest.mark.parametrize("cap_text", ["0.50", "1.50", "3.00"])
def test_equivalent_decimal_cap_formats_execute_with_same_frozen_amount(cell, monkeypatch, cap_text):
    from dataclasses import replace
    from decimal import Decimal
    public = replace(cell.public, budget_usd=Decimal(cap_text),
        openrouter={**cell.public.openrouter, "budget_usd": cap_text})
    cell.snapshot["config"] = public.to_dict()
    cell.config.update(openrouter=public.openrouter, **public.experiment_spec().proof_settings())
    cell.config["proof_budget_identity"] = runner.proof_identity(cell.snapshot, cell.snapshot["proofs"][0])
    runner.write(cell.cell / "config.json", cell.config)
    # ExperimentSpec snapshots normalize decimal text; public run snapshots
    # deliberately preserve the user's decimal formatting and budget identity.
    assert cell.config["experiment_spec"]["cumulative_budget_usd"] != cap_text
    def execute(config, root, capsule, relay, state):
        assert relay.settings.budget_usd == Decimal(cap_text)
        charge(relay, state["pass_number"], cap_text)
        outcome = {"status": "completed", "native_status": "completed", "returncode": 0}
        runner.write(capsule / "agent-run.json", outcome)
        return outcome
    monkeypatch.setattr(core, "execute_pass", execute)
    assert core.run_product(cell.cell, auth_path=cell.auth) == 0
    state = runner.read(cell.cell / "results.json")
    assert state["status"] == "budget_reached"
    assert Decimal(state["budget"]["spent_usd"]) == Decimal(cap_text)


@pytest.mark.parametrize("run_cap,proof_cap", [("0.50", "0.51"), ("1.50", "1.49"), ("3.00", "2.99")])
def test_genuinely_unequal_frozen_caps_rejected_before_ledger_or_native_dispatch(cell, monkeypatch, run_cap, proof_cap):
    from dataclasses import replace
    from decimal import Decimal
    public = replace(cell.public, budget_usd=Decimal(run_cap),
        openrouter={**cell.public.openrouter, "budget_usd": run_cap})
    unequal = replace(public, budget_usd=Decimal(proof_cap),
        openrouter={**public.openrouter, "budget_usd": proof_cap})
    cell.snapshot["config"] = public.to_dict()
    cell.config.update(openrouter=public.openrouter, **unequal.experiment_spec().proof_settings())
    cell.config["proof_budget_identity"] = runner.proof_identity(cell.snapshot, cell.snapshot["proofs"][0])
    runner.write(cell.cell / "config.json", cell.config)
    monkeypatch.setattr(core, "execute_pass", lambda *a: pytest.fail("unequal proof cap must not dispatch"))
    with pytest.raises(RuntimeError, match="differs from frozen run"):
        core.run_product(cell.cell, auth_path=cell.auth)
    assert not (cell.cell / "billing/openrouter.sqlite").exists()


@pytest.mark.parametrize("policy", [None, "legacy-v1"])
def test_historical_workflow_resume_fails_before_dispatch(cell, monkeypatch, policy):
    cell.snapshot["config"].pop("workflow_policy")
    if policy is not None:
        cell.snapshot["config"]["workflow_policy"] = policy
    monkeypatch.setattr(core, "execute_pass", lambda *a: pytest.fail("historical workflow must not dispatch"))
    with pytest.raises(ValueError, match="original frozen release"):
        core.run_product(cell.cell, auth_path=cell.auth, resume=True)
    assert not (cell.cell / "billing/openrouter.sqlite").exists()



def test_product_preparation_pins_complete_product_source_revision(cell, monkeypatch):
    from dataclasses import replace
    from harness.config import runtime_source_hashes
    public = cell.public
    cell.snapshot["config"] = public.to_dict()
    cell.config.pop("response_policy", None)
    cell.config.update(**public.experiment_spec().proof_settings())
    runner.write(cell.cell / "config.json", cell.config)
    monkeypatch.setattr(core.codex_preflight, "executable_version", lambda path: "0.164.0")
    monkeypatch.setattr(core, "tool_preflight", lambda root, config: Path(cell.config["tool_preflight"]))
    result = core.prepare_product(cell.cell, cell.config["product_metadata"], cell.snapshot)
    relative = {str(Path(path).relative_to(core.REPO)): value for path, value in result["source_hashes"].items()}
    assert relative == runtime_source_hashes()
    assert result["experiment_spec"]["prompt_variant"] == public.experiment_spec().prompt_variant
    assert "prompts/runtime/control-efficient-v1/start-prompt.md" in relative
    assert not any("control-feedback-v2" in path or "control-approved-v1" in path for path in relative)


def test_shared_unknown_liability_preserves_verified_proof_and_blocks_native_resume(cell, monkeypatch):
    from dataclasses import replace
    cell.snapshot["config"] = replace(cell.public, budget_policy="local-actual-cost-v1").to_dict()
    calls = []
    def execute(config, root, capsule, relay, state):
        assert relay.budget_policy == "local-actual-cost-v1"
        calls.append(state["pass_number"])
        relay.set_pass(state["pass_number"])
        request_id = relay.ledger.reserve("3", pass_number=state["pass_number"])
        relay.ledger.mark_dispatched(request_id)
        relay.ledger.mark_unknown(request_id, "synthetic missing final receipt")
        result = {"status": "completed", "native_status": "completed", "returncode": 0}
        runner.write(capsule / "agent-run.json", result)
        return result
    monkeypatch.setattr(core, "execute_pass", execute)
    assert core.run_product(cell.cell, auth_path=cell.auth) == 1
    state = runner.read(cell.cell / "state.json")
    assert state["status"] == "unknown_usage" and state["budget"]["active_requests"] == 1
    assert runner.read(cell.cell / "best.json")["sha256"] == cell.improved["sha256"]
    assert core.run_product(cell.cell, auth_path=cell.auth, resume=True) == 1
    assert calls == [1] and len(cell.checks) == 1
