from pathlib import Path
import json
import pytest

from harness.export import _validate_run_proofs, _cost, export_run


def snapshot():
    return {"identity": "run", "policy_identity": "policy", "model_identity": "model",
        "source_hashes": {"a": "hash"}, "config": {"budget_usd": "3", "openrouter": {"model_id": "a/b"}},
        "proofs": [{"task_id": "a", "task_sha256": "row"}]}








def test_missing_ledger_cost_is_unknown_not_zero(tmp_path):
    result = _cost(snapshot(), snapshot()["proofs"][0], tmp_path)
    assert result["status"] == "not_started"
    assert result["actual_cost_usd"] is None


def test_export_cannot_skip_independent_validation(tmp_path):
    with pytest.raises(ValueError, match="independent host"):
        export_run(tmp_path, tmp_path / "submission.jsonl", verify=False)


def test_nonblocking_missing_receipt_keeps_export_total_unknown(tmp_path):
    from harness.openrouter.ledger import OpenRouterLedger
    from harness.runner import proof_identity
    saved = snapshot()
    item = saved["proofs"][0]
    ledger = OpenRouterLedger(tmp_path / "billing/openrouter.sqlite",
        proof_id=proof_identity(saved, item), model="a/b", limit_usd="3")
    missing = ledger.reserve("3", pass_number=1)
    ledger.mark_dispatched(missing)
    ledger.mark_unknown(missing, "No itemized cost", blocks_spending=False)
    known = ledger.reserve("3", pass_number=1)
    ledger.mark_dispatched(known)
    ledger.settle(known, cost_usd="0.2")
    result = _cost(saved, item, tmp_path)
    assert result["status"] == "unresolved" and result["actual_cost_usd"] is None
    assert result["reported_settled_cost_usd"] == "0.2"
    assert result["budget"]["active_requests"] == 0


def test_fully_priced_overrun_is_known_cost_with_an_explicit_breach(tmp_path):
    from harness.openrouter.ledger import OpenRouterLedger
    from harness.runner import proof_identity
    saved = snapshot()
    item = saved["proofs"][0]
    ledger = OpenRouterLedger(tmp_path / "billing/openrouter.sqlite",
        proof_id=proof_identity(saved, item), model="a/b", limit_usd="3")
    identity = ledger.reserve("3", pass_number=1)
    ledger.mark_dispatched(identity)
    ledger.settle(identity, cost_usd="3.001")
    result = _cost(saved, item, tmp_path)
    assert result["status"] == "budget_breach"
    assert result["actual_cost_usd"] == "3.001" and result["cost_reporting_complete"] is True
    assert result["over_budget_usd"] == "0.001"


def test_cost_ledger_identity_is_checked(tmp_path, monkeypatch):
    (tmp_path / "billing").mkdir(); (tmp_path / "billing/openrouter.sqlite").touch()
    monkeypatch.setattr("harness.openrouter.ledger.read_openrouter_receipt", lambda p: {
        "identity": {"proof_id": "other-run", "model": "a/b", "limit_usd": "3"}, "budget": {}})
    with pytest.raises(ValueError, match="different run"):
        _cost(snapshot(), snapshot()["proofs"][0], tmp_path)


def export_fixture(tmp_path, monkeypatch):
    from harness.benchmark import file_hash
    from lean_tools import arena_workflow as arena
    root = tmp_path / "run"; root.mkdir()
    task = root / "Task.json"
    row = {"name": "test_export", "signature": "theorem test_export : True",
        "src": "theorem test_export : True := by trivial", "header": "", "contexts": []}
    task.write_text(json.dumps({"schema_version": 1, "row": row}))
    item = {"label": "test", "task_id": row["name"], "task": str(task), "task_sha256": file_hash(task),
        "original_tokens": 5, "original_heartbeats": 10, "scoring_policy": "arena-v1",
        "primary": "/prebuilt", "compatibility": [], "registry_source": "/registry", "elan_home": "/elan"}
    saved = snapshot(); saved["root"] = str(root); saved["proofs"] = [item]
    monkeypatch.setattr("harness.runner.load_snapshot", lambda path: saved)
    valid = {"tokens": 6, "heartbeats": 10, "compatibility_pct": 100, "score": 33, "environments": []}
    monkeypatch.setattr("harness.export._evaluate_source", lambda *a: dict(valid))
    return root, item, row, arena.render_candidate_scaffold(row), valid


def test_export_original_fallback_is_full_declaration(tmp_path, monkeypatch):
    root, item, row, source, valid = export_fixture(tmp_path, monkeypatch)
    output = tmp_path / "submission.jsonl"
    result = export_run(root, output)
    exported = json.loads(output.read_text())
    assert set(exported) == {"name", "proof"}
    assert exported["proof"] == row["src"]
    assert result["proofs"][0]["selection"] == "original_fallback"
    assert result["proofs"][0]["cost"]["actual_cost_usd"] is None


def test_forged_or_stale_best_falls_back_after_independent_measurement(tmp_path, monkeypatch):
    root, item, row, source, valid = export_fixture(tmp_path, monkeypatch)
    cell = root / "proofs/test"; cell.mkdir(parents=True); (cell / "best.json").write_text("{}")
    monkeypatch.setattr("harness.export._cost", lambda *a: {"status": "settled", "ledger_present": True})
    monkeypatch.setattr("harness.export._best", lambda *a: (source, {**valid, "tokens": 1}))
    output = tmp_path / "submission.jsonl"
    result = export_run(root, output)
    assert json.loads(output.read_text())["proof"] == row["src"]
    assert result["status"] == "exported_with_failures"
    assert "disagrees with independent" in result["proofs"][0]["fallback_reason"]


def test_failed_original_never_produces_submission(tmp_path, monkeypatch):
    root, item, row, source, valid = export_fixture(tmp_path, monkeypatch)
    def fail(*args):
        raise ValueError("compiler failed")
    monkeypatch.setattr("harness.export._evaluate_source", fail)
    output = tmp_path / "submission.jsonl"
    with pytest.raises(ValueError, match="No validated original fallback"):
        export_run(root, output)
    assert not output.exists()
    assert json.loads(output.with_name(output.name + ".report.json").read_text())["status"] == "failed"


def test_unknown_cost_does_not_erase_verified_incumbent_or_become_zero(tmp_path, monkeypatch):
    root, item, row, source, valid = export_fixture(tmp_path, monkeypatch)
    cell = root / "proofs/test"; cell.mkdir(parents=True); (cell / "best.json").write_text("{}")
    monkeypatch.setattr("harness.export._cost", lambda *a: {"status": "unresolved", "ledger_present": True, "actual_cost_usd": None})
    monkeypatch.setattr("harness.export._best", lambda *a: (source, valid))
    output = tmp_path / "submission.jsonl"
    result = export_run(root, output)
    assert result["proofs"][0]["selection"] == "verified_incumbent"
    assert result["cost_status"] == "unresolved"


def test_known_overrun_export_is_not_mislabeled_as_unknown_cost(tmp_path, monkeypatch):
    root, item, row, source, valid = export_fixture(tmp_path, monkeypatch)
    cell = root / "proofs/test"; cell.mkdir(parents=True); (cell / "best.json").write_text("{}")
    monkeypatch.setattr("harness.export._cost", lambda *a: {"status": "budget_breach", "ledger_present": True, "actual_cost_usd": "3.001"})
    monkeypatch.setattr("harness.export._best", lambda *a: (source, valid))
    result = export_run(root, tmp_path / "submission.jsonl")
    assert result["proofs"][0]["selection"] == "verified_incumbent"
    assert result["cost_status"] == "budget_breach"








def test_duplicate_proof_in_one_run_is_rejected():
    saved = snapshot()
    saved["proofs"] *= 2
    with pytest.raises(ValueError, match="Repeated proof"):
        _validate_run_proofs(saved)


def test_one_run_rejects_conflicting_snapshot_bindings():
    saved = snapshot()
    environment = {"snapshot_id": "same", "path": "/prebuilt", "repository": "repo", "revision": "rev", "snapshot_requirement_sha256": "original"}
    saved["proofs"][0]["environments"] = [environment, {**environment, "revision": "changed"}]
    with pytest.raises(ValueError, match="changed snapshot"):
        _validate_run_proofs(saved)


def test_export_requires_one_run_directory(tmp_path):
    with pytest.raises(ValueError, match="one frozen run"):
        export_run([tmp_path / "a", tmp_path / "b"], tmp_path / "submission.jsonl")
