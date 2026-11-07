"""Explicit evaluator repairs retain original evidence and the existing ledger."""
from copy import deepcopy
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from e6 import proof
from e6.experiment import DEFAULT_RUN_SPEC
from harness import baselines, runner, runtime_repair as repair
from harness.config import digest, file_hash
from harness.openrouter.ledger import OpenRouterLedger, read_openrouter_receipt
from tests.test_product_baselines import prepare_fixture


@pytest.fixture
def baseline_run(tmp_path, monkeypatch):
    import e6.config as e6_config
    import harness.environments as environments
    repo = tmp_path / "source"
    evaluator = repo / "lean_tools/arena_workflow.py"
    transport = repo / "harness/openrouter/relay.py"
    for path in (evaluator, transport):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("original")
    def sources():
        return {str(path.relative_to(repo)): file_hash(path) for path in (evaluator, transport)}
    def verify(expected):
        if expected != sources():
            raise RuntimeError("Frozen harness source changed")
    monkeypatch.setattr(repair, "runtime_source_hashes", sources)
    monkeypatch.setattr(baselines, "runtime_source_hashes", sources)
    monkeypatch.setattr(repair, "verify_source_hashes", verify)
    monkeypatch.setattr(runner, "verify_source_hashes", verify)
    monkeypatch.setattr(e6_config, "REPO_ROOT", repo)
    metadata, evidence, calls = prepare_fixture(tmp_path, monkeypatch,
        supplied_heartbeat=False, compatibility=True)
    item = baselines.freeze_original_baseline(metadata, evidence, tmp_path / "baselines")
    monkeypatch.setattr(environments, "verify_resolved_metadata", lambda _: None)
    root = tmp_path / "run"
    cell = root / "proofs" / item["label"]
    cell.mkdir(parents=True)
    original = tmp_path / "frozen-input.jsonl"
    original.write_text("unchanged original rows")
    snapshot = {"schema_version": 1, "root": str(root), "source_hashes": sources(),
        "input_hashes": {"input": {"path": str(original), "sha256": file_hash(original)}},
        "proofs": [item], "config": {"budget_usd": "2.90"}}
    snapshot["identity"] = digest(snapshot)
    runner.write(root / "resolved-config.json", snapshot)
    runner.write(cell / "state.json", {"status": "failed", "pass_number": 2,
        "passes": [{"pass_number": 2, "validation_healthy": False}]})
    runner.write(cell / "config.json", {"source_hashes": {str(repo / k): v for k, v in sources().items()}})
    ledger = OpenRouterLedger(cell / "billing/openrouter.sqlite",
        proof_id=runner.proof_identity(snapshot, item), model="test/model", limit_usd="2.90")
    request = ledger.reserve("2.90", pass_number=1)
    ledger.mark_dispatched(request)
    ledger.settle(request, cost_usd="1.8336975")
    return SimpleNamespace(root=root, cell=cell, snapshot=snapshot, item=item,
        evaluator=evaluator, transport=transport, ledger=ledger, evidence=evidence, calls=calls)


def authorize(run):
    run.evaluator.write_text("reviewed axiom fallback repair")
    return repair.authorize(run.root, reason="Preserve original measurements after reviewed axiom resolver fix",
        preserve_original_baselines=True)


def test_measurement_change_requires_explicit_preservation_before_receipt(baseline_run):
    run = baseline_run
    run.evaluator.write_text("reviewed fix")
    with pytest.raises(ValueError, match="preserve_original_baselines=True"):
        repair.authorize(run.root, reason="Missing explicit preservation review")
    assert not (run.root / "runtime-repairs").exists()


def test_preservation_keeps_all_original_evidence_failure_history_and_spend(baseline_run):
    run = baseline_run
    paths = [run.root / "resolved-config.json", run.cell / "config.json", run.cell / "state.json",
        Path(run.item["task"]), Path(run.item["baseline_receipt"]["path"]),
        Path(run.evidence["original_path"]), Path(run.evidence["task_path"])]
    before = {path: path.read_bytes() for path in paths}
    cost = read_openrouter_receipt(run.ledger.path)
    result = authorize(run)
    assert runner.load_snapshot(run.root) == run.snapshot
    assert baselines.load_original_baseline(run.item, source_snapshot=run.snapshot)
    assert result["repairs"][0]["preserved_original_baseline_count"] == 1
    assert all(path.read_bytes() == value for path, value in before.items())
    assert read_openrouter_receipt(run.ledger.path) == cost
    assert cost["budget"]["spent_usd"] == "1.8336975"
    assert len(run.calls) == 2  # Original preflight only; repair runs no compiler.
    with pytest.raises(ValueError, match="measurement source"):
        baselines.load_original_baseline(run.item)


def test_future_proof_preparation_uses_exact_run_authority_without_remeasurement(baseline_run, tmp_path, monkeypatch):
    import e6.config as e6_config
    run = baseline_run
    authorize(run)
    monkeypatch.setattr(e6_config, "REPO_ROOT", Path(__file__).resolve().parents[1])
    monkeypatch.setenv("ELAN_HOME", run.item["elan_home"])
    monkeypatch.setattr(proof, "configure_native_environment", lambda **_: None)
    monkeypatch.setattr(proof, "find_codex", lambda: Path("fake-native-codex"))
    monkeypatch.setattr(proof.arena, "environment_fingerprint_registry_entry", lambda *_a, **_k:
        {"fingerprint": run.item["environments"][0]["fingerprint"], "guard_sha256": "f" * 64})
    monkeypatch.setattr(proof, "_check", lambda *_a, **_k: pytest.fail("Repair must not compile the original again"))
    spec = replace(DEFAULT_RUN_SPEC, deterministic_refactoring=False, goal_retrieval=False)
    config = proof.prepare(tmp_path / "future-cell", run.item["label"], metadata=run.item,
        baseline_snapshot=runner.load_snapshot(run.root), spec=spec)
    assert config["initial_best"]["heartbeats"] == run.item["original_heartbeats"]
    assert config["product_metadata"] == run.item
    assert len(run.calls) == 2


@pytest.mark.parametrize("target", ["receipt", "native_evidence", "original_source"])
def test_preservation_never_waives_native_evidence_integrity(baseline_run, target):
    run = baseline_run
    authorize(run)
    path = (Path(run.item["baseline_receipt"]["path"]) if target == "receipt" else
        Path(run.evidence["environments"][0]["evidence_path"]) if target == "native_evidence" else
        Path(run.evidence["original_path"]))
    path.write_text("tampered")
    with pytest.raises(ValueError):
        runner.load_snapshot(run.root)


def test_preservation_cannot_be_borrowed_for_foreign_metadata_or_snapshot(baseline_run):
    run = baseline_run
    authorize(run)
    metadata = deepcopy(run.item)
    metadata["unrelated"] = "another proof"
    with pytest.raises(ValueError, match="proof metadata|authority"):
        baselines.load_original_baseline(metadata, source_snapshot=run.snapshot)
    foreign = deepcopy(run.snapshot)
    foreign["config"]["budget_usd"] = "3"
    foreign["identity"] = digest({k: v for k, v in foreign.items() if k != "identity"})
    with pytest.raises(ValueError, match="authority"):
        baselines.load_original_baseline(run.item, source_snapshot=foreign)


def test_later_measurement_repair_needs_a_new_review_but_transport_change_does_not(baseline_run):
    run = baseline_run
    authorize(run)
    run.transport.write_text("reviewed transport-only repair")
    repair.authorize(run.root, reason="Transport only")
    assert runner.load_snapshot(run.root) == run.snapshot
    run.evaluator.write_text("another measurement change")
    with pytest.raises(ValueError, match="preserve_original_baselines=True"):
        repair.authorize(run.root, reason="Missing new preservation review")
    repair.authorize(run.root, reason="Second explicit measurement review", preserve_original_baselines=True)
    assert runner.load_snapshot(run.root) == run.snapshot


def test_preservation_binding_is_checked_even_if_outer_receipt_digest_is_recomputed(baseline_run):
    run = baseline_run
    authorize(run)
    path = run.root / "runtime-repairs/001.json"
    receipt = runner.read(path)
    receipt["preserved_original_baselines"]["proofs"][run.item["label"]]["metadata_sha256"] = "foreign"
    receipt["receipt_sha256"] = digest({k: v for k, v in receipt.items() if k != "receipt_sha256"})
    runner.write(path, receipt)
    with pytest.raises(RuntimeError, match="preservation binding"):
        runner.load_snapshot(run.root)
