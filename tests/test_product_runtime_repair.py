"""A reviewed runtime fix may not replace a proof budget or weaken later guards."""
from types import SimpleNamespace
import json
from pathlib import Path

import pytest

from harness import runner, runtime_repair as repair
from harness.config import digest, file_hash
from harness.openrouter.ledger import OpenRouterLedger, read_openrouter_receipt


@pytest.fixture
def run(tmp_path, monkeypatch):
    import harness.environments as environments
    import e6.config as e6_config
    repo = tmp_path / "source"; repo.mkdir()
    code = repo / "relay.py"; code.write_text("original runtime")
    root = tmp_path / "run"; root.mkdir()
    cell = root / "proofs/tiny"; cell.mkdir(parents=True)
    task = root / "Task.json"; task.write_text('{"name":"Tiny"}')
    original = tmp_path / "original.jsonl"; original.write_text("original row")
    sources = lambda: {"relay.py": file_hash(code)}
    monkeypatch.setattr(repair, "runtime_source_hashes", sources)
    def verify(expected):
        if expected != sources():
            raise RuntimeError("Frozen harness source changed")
    monkeypatch.setattr(runner, "verify_source_hashes", verify)
    monkeypatch.setattr(repair, "verify_source_hashes", verify)
    monkeypatch.setattr(environments, "verify_resolved_metadata", lambda item: None)
    monkeypatch.setattr(e6_config, "REPO_ROOT", repo)
    item = {"label": "tiny", "task_id": "Tiny", "task": str(task), "task_sha256": file_hash(task)}
    snapshot = {"schema_version": 1, "root": str(root), "source_hashes": sources(),
        "input_hashes": {"input": {"path": str(original), "sha256": file_hash(original)}},
        "proofs": [item], "config": {"budget_usd": "3.00"}}
    snapshot["identity"] = digest(snapshot)
    runner.write(root / "resolved-config.json", snapshot)
    runner.write(cell / "state.json", {"status": "account_error", "pass_number": 4})
    prepared = {"source_hashes": {str(code): file_hash(code)}}
    runner.write(cell / "config.json", prepared)
    identity = runner.proof_identity(snapshot, item)
    ledger = OpenRouterLedger(cell / "billing/openrouter.sqlite", proof_id=identity, model="test/model", limit_usd="3")
    request_id = ledger.reserve("3", pass_number=1)
    ledger.mark_dispatched(request_id)
    ledger.settle(request_id, cost_usd="2.59")
    return SimpleNamespace(root=root, cell=cell, snapshot=snapshot, prepared=prepared,
        code=code, original=original, ledger=ledger, identity=identity)


def test_explicit_repair_preserves_snapshot_prepared_config_and_spend(run):
    frozen = (run.root / "resolved-config.json").read_bytes()
    prepared = (run.cell / "config.json").read_bytes()
    before = read_openrouter_receipt(run.ledger.path)
    run.code.write_text("reviewed retry fix")
    with pytest.raises(RuntimeError, match="source changed"):
        runner.load_snapshot(run.root)
    result = repair.authorize(run.root, reason="Recognize structured key-limit rejection")
    loaded = runner.load_snapshot(run.root)
    repair.verify_prepared_sources(run.prepared, loaded)
    assert loaded == run.snapshot
    assert (run.root / "resolved-config.json").read_bytes() == frozen
    assert (run.cell / "config.json").read_bytes() == prepared
    assert read_openrouter_receipt(run.ledger.path) == before
    assert runner.proof_identity(loaded, loaded["proofs"][0]) == run.identity
    assert result["repairs"][0]["proof_states"]["tiny"]["pass_number"] == 4
    assert result["repairs"][0]["changed_paths"] == ["relay.py"]
    with pytest.raises(RuntimeError, match="No runtime change"):
        repair.authorize(run.root, reason="duplicate")
    run.code.write_text("unreviewed later edit")
    with pytest.raises(RuntimeError, match="source changed"):
        runner.load_snapshot(run.root)


@pytest.mark.parametrize("scope", ["root", "cell"])
def test_active_runner_or_proof_prevents_runtime_repair(run, scope):
    run.code.write_text("reviewed fix")
    with runner.run_lock(getattr(run, scope)):
        with pytest.raises(RuntimeError, match="runner already holds"):
            repair.authorize(run.root, reason="must wait for active workers")
    assert not (run.root / "runtime-repairs").exists()


def test_frozen_inputs_cannot_be_changed_by_runtime_authorization(run):
    run.code.write_text("reviewed fix")
    run.original.write_text("different contest row")
    with pytest.raises(RuntimeError, match="Frozen input changed"):
        repair.authorize(run.root, reason="runtime only")
    assert not (run.root / "runtime-repairs").exists()


@pytest.mark.parametrize("corruption", ["receipt", "run_binding", "prepared_source"])
def test_repair_rejects_tampered_receipts_foreign_runs_and_unrecorded_sources(run, corruption):
    run.code.write_text("reviewed fix")
    repair.authorize(run.root, reason="reviewed")
    if corruption == "prepared_source":
        with pytest.raises(RuntimeError, match="not a recorded"):
            repair.verify_prepared_sources({"source_hashes": {str(run.code): "foreign"}}, run.snapshot)
        return
    path = run.root / "runtime-repairs/001.json"
    receipt = json.loads(path.read_text())
    if corruption == "receipt":
        receipt["reason"] = "tampered"
    else:
        receipt["run_identity"] = "another run"
        receipt["receipt_sha256"] = digest({k: v for k, v in receipt.items() if k != "receipt_sha256"})
    runner.write(path, receipt)
    with pytest.raises(RuntimeError, match="receipt or binding"):
        runner.load_snapshot(run.root)


def test_second_repair_chains_from_first_without_resetting_original_identity(run):
    run.code.write_text("first fix")
    repair.authorize(run.root, reason="first reviewed fix")
    run.code.write_text("second fix")
    repair.authorize(run.root, reason="second reviewed fix")
    assert len(repair.history(run.snapshot)[0]) == 3
    assert runner.load_snapshot(run.root)["identity"] == run.snapshot["identity"]
    repair.verify_prepared_sources(run.prepared, run.snapshot)
