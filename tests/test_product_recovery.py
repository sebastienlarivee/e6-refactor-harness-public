"""Offline recovery scenarios with real ledgers and no inference or Lean builds."""
from datetime import datetime, timezone
from decimal import Decimal
import hashlib
import json
import os
from pathlib import Path
from types import SimpleNamespace

import pytest

from harness import recovery
from harness.openrouter.ledger import OpenRouterLedger, read_openrouter_receipt
from harness.runner import proof_identity


KEY = "offline-recovery-test-key"
FINGERPRINT = hashlib.sha256(KEY.encode()).hexdigest()


class KeyClient:
    def __init__(self):
        self.transport = self
        self.usage, self.byok = Decimal("100"), Decimal("10")
        self.calls = []
        self.on_call = None

    def credential(self):
        return KEY

    def call(self, method, path, key):
        assert (method, path, key) == ("GET", "/key", KEY)
        self.calls.append((method, path))
        if self.on_call:
            self.on_call()
        return {"data": {"usage": self.usage, "byok_usage": self.byok,
                         "is_management_key": False, "is_provisioning_key": False}}


@pytest.fixture
def scenario(tmp_path):
    root = tmp_path / "run"
    root.mkdir()
    snapshot = {"identity": "run-identity", "root": str(root), "config": {
        "recovery_policy": "exclusive-key-v1", "budget_policy": "local-actual-cost-v1",
        "budget_usd": "2.90", "openrouter": {"model_id": "model"}},
        "proofs": [{"label": "p", "task_id": "Task.p", "task_sha256": "hash-p"},
                   {"label": "q", "task_id": "Task.q", "task_sha256": "hash-q"}]}
    recovery._write(root / "credential-identity.json", {"run_identity": snapshot["identity"], "key_sha256": FINGERPRINT})
    key = KeyClient()
    ticks = [1800000000.0]
    sleeps = []
    callbacks = {}

    def sleep(seconds):
        sleeps.append(seconds)
        ticks[0] += seconds

    def relay(cell, item):
        return SimpleNamespace(reconcile_pending=lambda: callbacks.get(item["label"], lambda: None)(), close=lambda: None)

    def coordinator():
        return recovery.RecoveryCoordinator(root, snapshot, api_key_file=tmp_path / "unused-key-path",
            key_client=key, relay_factory=relay, sleep=sleep, clock=lambda: ticks[0])

    def ledger(label="p"):
        item = next(x for x in snapshot["proofs"] if x["label"] == label)
        return OpenRouterLedger(root / "proofs" / label / "billing/openrouter.sqlite",
            proof_id=proof_identity(snapshot, item), model="model", limit_usd="2.90")

    def state(label="p", **fields):
        recovery._write(root / "proofs" / label / "state.json", {"status": "unknown_usage", **fields})

    def paid(label="p", amount="0.10", byok=None):
        book = ledger(label)
        request = book.reserve(book.snapshot()["remaining_usd"], pass_number=1)
        book.mark_dispatched(request)
        usage = {"cost": amount}
        total = Decimal(amount)
        if byok is not None:
            usage.update(is_byok=True, upstream_inference_cost=byok)
            total += Decimal(byok)
        book.settle(request, cost_usd=total, usage=usage, generation_id="gen-" + request)
        key.usage += Decimal(amount)
        key.byok += Decimal(byok or 0)
        return request

    def unknown(label="p", generation=None, output=False, finished_age=1000, **extra):
        book = ledger(label)
        request = book.reserve(book.snapshot()["remaining_usd"], pass_number=2,
            metadata={"output_observed": output, "response_headers_received": generation is not None,
                "transport_failure": True,
                "transport_finished_at": datetime.fromtimestamp(ticks[0] - finished_age, timezone.utc).isoformat(), **extra})
        book.mark_dispatched(request)
        if generation:
            book.attach_generation(request, generation)
        book.mark_unknown(request, "Offline simulated transport failure")
        state(label)
        return request

    return SimpleNamespace(root=root, snapshot=snapshot, key=key, sleeps=sleeps, ticks=ticks,
        callbacks=callbacks, coordinator=coordinator, ledger=ledger, state=state, paid=paid, unknown=unknown)


def test_exclusive_zero_audit_resumes_once_without_inventing_bill(scenario):
    s = scenario
    c = s.coordinator(); c.initialize()
    s.paid(); request = s.unknown()
    assert c.recover() == ["p"]
    receipt = s.ledger().request(request)
    assert receipt["state"] == "unknown" and receipt["cost_usd"] is None
    budget = read_openrouter_receipt(s.ledger().path)["budget"]
    assert budget["spent_usd"] == "0.10" and budget["active_requests"] == 0
    assert budget["unknown_requests"] == budget["provisional_unknown_requests"] == 1
    assert c.recover() == []
    restarted = s.coordinator(); restarted.initialize()
    assert restarted.recover() == []
    assert all(method == "GET" for method, _ in s.key.calls)


def test_confirmed_generation_bill_recovery_without_key_audit(scenario):
    s = scenario; s.snapshot["config"]["recovery_policy"] = "generation-v1"
    c = s.coordinator(); c.initialize()
    s.paid(); request = s.unknown(generation="gen-lost-stream")
    s.callbacks["p"] = lambda: s.ledger().settle(request, cost_usd="0.20", usage={"cost": "0.20"})
    assert c.recover() == ["p"]
    assert s.ledger().snapshot()["spent_usd"] == Decimal("0.30")
    assert s.key.calls == []


def test_default_recovery_does_not_assume_zero(scenario):
    s = scenario; s.snapshot["config"]["recovery_policy"] = "generation-v1"
    c = s.coordinator(); c.initialize(); s.unknown()
    assert c.recover() == []
    assert len(s.ledger().snapshot()["active_requests"]) == 1
    assert s.key.calls == []


@pytest.mark.parametrize("case", ["positive", "negative", "byok", "two_unknown", "output", "protocol"])
def test_ambiguous_or_mismatched_evidence_never_releases_cost(scenario, case):
    s = scenario; c = s.coordinator(); c.initialize(); s.paid()
    s.unknown(output=case == "output", protocol_conflict=case == "protocol")
    if case == "positive": s.key.usage += Decimal("0.01")
    if case == "negative": s.key.usage -= Decimal("0.01")
    if case == "byok": s.key.byok += Decimal("0.01")
    if case == "two_unknown": s.unknown("q")
    assert c.recover() == []
    assert len(s.ledger().snapshot()["active_requests"]) == 1
    assert c.state["presumption"] is None


def test_three_matching_readings_and_cooldown_required(scenario):
    s = scenario; c = s.coordinator(); c.initialize(); s.paid(); s.unknown(finished_age=10)
    assert c.recover() == ["p"]
    assert s.sleeps == [290, 30, 30]
    assert len(s.key.calls) == 4  # baseline plus three quiet samples


def test_a_single_lagging_counter_sample_prevents_zero_inference(scenario):
    s = scenario; c = s.coordinator(); c.initialize(); s.paid(); s.unknown()
    values = iter([Decimal("100.10"), Decimal("100.09"), Decimal("100.10")])
    s.key.on_call = lambda: setattr(s.key, "usage", next(values))
    assert c.recover() == []
    assert len(s.ledger().snapshot()["active_requests"]) == 1


def test_late_authoritative_bill_is_counted_after_presumed_zero(scenario):
    s = scenario; c = s.coordinator(); c.initialize(); s.paid(); request = s.unknown()
    assert c.recover() == ["p"]
    s.ledger().attach_generation(request, "gen-late")
    s.ledger().settle(request, cost_usd="0.20", usage={"cost": "0.20"})
    assert c.recover() == []
    assert s.ledger().snapshot()["spent_usd"] == Decimal("0.30")
    assert c.state["presumption"]["provider_settled"] is True


def test_later_unexplained_charge_revokes_recovery_without_erasing_spend(scenario):
    s = scenario; c = s.coordinator(); c.initialize(); s.paid(); request = s.unknown()
    assert c.recover() == ["p"]
    s.paid(amount="0.50")
    s.key.usage += Decimal("0.20")
    assert c.recover() == []
    receipt = read_openrouter_receipt(s.ledger().path)
    assert Decimal(receipt["budget"]["spent_usd"]) == Decimal("0.60")
    assert receipt["budget"]["halted_reason"]
    assert s.ledger().request(request)["cost_usd"] is None
    assert c.state["presumption"]["revoked"] is True
    state = recovery._read(s.root / "proofs/p/state.json")
    assert state["status"] == "unknown_usage"
    assert Decimal(state["budget"]["spent_usd"]) == Decimal("0.60")
    assert state["budget"]["halted_reason"]


def test_restart_cannot_create_baseline_over_existing_charges(scenario):
    s = scenario; s.paid(); s.unknown()
    c = s.coordinator(); c.initialize()
    assert c.state["baseline_unavailable"] is True
    assert c.recover() == []
    assert s.key.calls == []


def test_foreign_key_binding_is_rejected_before_provider_calls(scenario):
    s = scenario
    recovery._write(s.root / "credential-identity.json", {"run_identity": "different", "key_sha256": FINGERPRINT})
    with pytest.raises(RuntimeError, match="binding"):
        s.coordinator().initialize()
    assert s.key.calls == []


def test_live_cell_prevents_idle_recovery(scenario):
    s = scenario; c = s.coordinator(); c.initialize(); s.unknown(); s.state(pid=os.getpid())
    with pytest.raises(RuntimeError, match="live PIDs"):
        c.recover()
    assert len(s.key.calls) == 1


def test_second_ambiguous_failure_cannot_gain_another_zero_retry(scenario):
    s = scenario; c = s.coordinator(); c.initialize(); first = s.unknown()
    assert c.recover() == ["p"]
    s.unknown("q")
    assert c.recover() == []
    assert len(s.ledger("q").snapshot()["active_requests"]) == 1
    assert c.state["presumption"]["request_id"] == first


def test_generic_failed_worker_is_not_retried(scenario):
    s = scenario; c = s.coordinator(); c.initialize(); s.paid()
    s.state(status="failed", passes=[{"pass_number": 1, "validation_healthy": True}])
    assert c.recover() == []


def test_healthy_transport_failure_requeues_only_matching_pass(scenario):
    s = scenario; s.snapshot["config"]["recovery_policy"] = "generation-v1"
    c = s.coordinator(); c.initialize(); request = s.unknown(generation="gen-recovered")
    s.ledger().settle(request, cost_usd="0.10", usage={"cost": "0.10"})
    s.state(status="failed", passes=[{"pass_number": 2, "validation_healthy": True}])
    assert c.recover() == ["p"]


def test_stale_transport_marker_does_not_hide_new_failure(scenario):
    s = scenario; s.snapshot["config"]["recovery_policy"] = "generation-v1"
    c = s.coordinator(); c.initialize(); request = s.unknown(generation="gen-previous")
    s.ledger().settle(request, cost_usd="0.10", usage={"cost": "0.10"})
    s.state(status="failed", passes=[{"pass_number": 3, "validation_healthy": True}])
    assert c.recover() == []


@pytest.mark.parametrize("after_release", [False, True])
def test_restart_completes_a_crash_interrupted_presumption(scenario, monkeypatch, after_release):
    s = scenario; c = s.coordinator(); c.initialize(); s.paid(); request = s.unknown()
    original = OpenRouterLedger.presume_zero

    def interrupted(book, *args, **kwargs):
        if after_release:
            original(book, *args, **kwargs)
        raise RuntimeError("synthetic crash at durable recovery boundary")

    monkeypatch.setattr(OpenRouterLedger, "presume_zero", interrupted)
    with pytest.raises(RuntimeError, match="synthetic crash"):
        c.recover()
    assert c.state["presumption"]["phase"] == "prepared"
    monkeypatch.setattr(OpenRouterLedger, "presume_zero", original)
    restarted = s.coordinator(); restarted.initialize()
    assert restarted.state["presumption"]["phase"] == "applied"
    assert restarted.recover() == ["p"]
    assert s.ledger().request(request)["cost_usd"] is None
    assert restarted.recover() == []


def test_counter_reconciliation_preserves_small_exact_charges(scenario):
    s = scenario; c = s.coordinator(); c.initialize()
    s.paid(amount="0.00000000000000000000000000001")
    s.key.usage = Decimal("100.00000000000000000000000000001")
    s.unknown()
    assert c.recover() == ["p"]


def test_recovered_transport_error_does_not_mask_later_native_failure(scenario):
    s = scenario; s.snapshot["config"]["recovery_policy"] = "generation-v1"
    c = s.coordinator(); c.initialize(); request = s.unknown(generation="gen-earlier")
    book = s.ledger(); book.settle(request, cost_usd="0.10", usage={"cost": "0.10"})
    later = book.reserve(book.snapshot()["remaining_usd"], pass_number=2)
    book.mark_dispatched(later); book.settle(later, cost_usd="0.10", usage={"cost": "0.10"})
    s.state(status="failed", passes=[{"pass_number": 2, "validation_healthy": True}])
    assert c.recover() == []


@pytest.mark.parametrize("value", [None, True, "invalid", "NaN", "Infinity", "-1"])
def test_invalid_key_counter_is_a_controlled_error(scenario, value):
    s = scenario; s.key.usage = value
    with pytest.raises(ValueError, match="usage counter"):
        s.coordinator().initialize()
    assert not (s.root / "proofs").exists()


def test_bill_exhausting_cap_finishes_without_a_new_worker(scenario):
    s = scenario; s.snapshot["config"]["recovery_policy"] = "generation-v1"
    c = s.coordinator(); c.initialize(); s.paid(); request = s.unknown(generation="gen-final-bill")
    s.callbacks["p"] = lambda: s.ledger().settle(request, cost_usd="2.80", usage={"cost": "2.80"})
    assert c.recover() == []
    assert recovery._read(s.root / "proofs/p/state.json")["status"] == "budget_reached"
    assert c.state["requeued"] == {}


def test_restart_republishes_revocation_after_status_write_crash(scenario, monkeypatch):
    s = scenario; c = s.coordinator(); c.initialize(); s.paid(); s.unknown()
    assert c.recover() == ["p"]
    s.state(status="budget_reached")
    s.key.usage += Decimal("0.20")
    original = c._publish_budget
    monkeypatch.setattr(c, "_publish_budget", lambda *a, **kw: (_ for _ in ()).throw(RuntimeError("publication crash")))
    with pytest.raises(RuntimeError, match="publication crash"):
        c.recover()
    assert c.state["presumption"]["revoked"] is True
    assert recovery._read(s.root / "proofs/p/state.json")["status"] == "budget_reached"
    restarted = s.coordinator(); restarted.initialize()
    assert recovery._read(s.root / "proofs/p/state.json")["status"] == "unknown_usage"
    assert restarted.recover() == []
