"""Durable recovery facts release a hold without inventing a provider bill."""
import json
import sqlite3
from decimal import Decimal

import pytest

from harness.openrouter.ledger import (
    BudgetExhausted, LedgerError, OpenRouterLedger, UnsettledRequest,
    read_openrouter_receipt, receipt_identity,
)


@pytest.fixture
def ledger(tmp_path):
    return OpenRouterLedger(tmp_path / "account.sqlite", proof_id="run/proof", model="openai/model", limit_usd="3")


def unknown(ledger, **changes):
    request = ledger.reserve("3", pass_number=1)
    ledger.mark_dispatched(request)
    tags = {"response_headers_received": False, "output_observed": False,
        "request_bytes_sent": None, "transport_phase": "failed", "protocol_conflict": False,
        "transport_error_category": "timeout", "transport_finished_at": "2026-11-02T23:00:00+00:00"}
    tags.update(changes)
    ledger.annotate(request, metadata=tags)
    ledger.mark_unknown(request, "Closed attempt has no itemized receipt")
    return request


def presume(ledger, request, **changes):
    options = {"evidence_sha256": "a" * 64, "key_sha256": "b" * 64,
        "baseline_sha256": "c" * 64, "expected_receipt_sha256": receipt_identity(ledger.request(request)),
        "exclusive_key": True}
    options.update(changes)
    return ledger.presume_zero(request, **options)


def test_provisional_release_is_unknown_not_a_zero_bill_and_survives_reopen(ledger):
    request = unknown(ledger)
    original = ledger.request(request)
    pins = {"evidence_sha256": "a" * 64, "key_sha256": "b" * 64,
        "baseline_sha256": "c" * 64, "expected_receipt_sha256": receipt_identity(original), "exclusive_key": True}
    value = ledger.presume_zero(request, **pins)
    assert value["state"] == "unknown" and value["cost_usd"] is None and value["settled_at"] is None
    assert value["usage"] == {} and value["generation_id"] is None
    assert value["unknown_reason"] == original["unknown_reason"]
    assert ledger.presume_zero(request, **pins) == value
    snapshot = ledger.snapshot()
    assert snapshot["remaining_usd"] == 3 and snapshot["spent_usd"] == snapshot["reserved_usd"] == 0
    assert len(snapshot["unknown_requests"]) == len(snapshot["provisional_unknown_requests"]) == 1
    assert snapshot["blocking_unknown_requests"] == snapshot["active_requests"] == []
    reopened = OpenRouterLedger(ledger.path, proof_id=ledger.proof_id, model=ledger.model, limit_usd="3")
    assert reopened.presumed_zero_valid(request)
    exported = read_openrouter_receipt(ledger.path)
    assert exported["budget"]["unknown_requests"] == exported["budget"]["provisional_unknown_requests"] == 1
    assert exported["budget"]["blocking_unknown_requests"] == exported["budget"]["active_requests"] == 0
    assert exported["requests"][0]["cost_usd"] is None
    assert exported["budget"]["metered_responses"] == 0


@pytest.mark.parametrize("changes", [
    {"exclusive_key": False}, {"exclusive_key": 1}, {"evidence_sha256": "bad"},
    {"key_sha256": "B" * 64}, {"baseline_sha256": None}, {"expected_receipt_sha256": "d" * 64},
])
def test_invalid_audit_pins_never_release_hold(ledger, changes):
    request = unknown(ledger)
    before = ledger.request(request)
    with pytest.raises(LedgerError):
        presume(ledger, request, **changes)
    assert ledger.request(request) == before
    assert ledger.snapshot()["remaining_usd"] == 0


@pytest.mark.parametrize("changes", [
    {"output_observed": True},
    {"protocol_conflict": True}, {"byok_liability_unresolved": True}, {"transport_error_category": "protocol_error"},
    {"transport_finished_at": "not finished"},
])
def test_transport_evidence_must_admit_a_closed_no_output_attempt(ledger, changes):
    request = unknown(ledger, **changes)
    with pytest.raises(LedgerError):
        presume(ledger, request)
    assert ledger.snapshot()["remaining_usd"] == 0


def test_response_headers_without_id_are_not_mistaken_for_observed_output(ledger):
    request = unknown(ledger, response_headers_received=True)
    presume(ledger, request)
    assert ledger.presumed_zero_valid(request)


def test_id_or_partial_usage_cannot_receive_a_presumption(ledger):
    request = unknown(ledger)
    ledger.attach_generation(request, "gen-known")
    with pytest.raises(LedgerError):
        presume(ledger, request)


def test_usage_and_second_active_request_prevent_release(ledger):
    request = unknown(ledger)
    ledger.mark_unknown(request, "Missing BYOK cost", usage={"is_byok": True})
    with pytest.raises(LedgerError):
        presume(ledger, request)


def test_once_ever_survives_actual_settlement(ledger):
    first = unknown(ledger)
    presume(ledger, first)
    ledger.settle(first, cost_usd="0.1", usage={"cost": "0.1"})
    settled = ledger.request(first)
    assert settled["metadata"]["presumed_zero_recovery"]["retry_used"] is True
    assert settled["metadata"]["presumed_zero_recovery"]["status"] == "settled"
    assert not ledger.presumed_zero_valid(first)
    request = ledger.reserve("2.9", pass_number=2)
    ledger.mark_dispatched(request)
    ledger.annotate(request, metadata={"output_observed": False, "response_headers_received": False,
        "transport_finished_at": "2026-11-03T00:00:00+00:00"})
    ledger.mark_unknown(request, "Another attempt missing its bill")
    with pytest.raises(LedgerError, match="only one"):
        presume(ledger, request)


def test_late_bill_after_other_spend_is_counted_and_halts_without_losing_receipts(ledger):
    first = unknown(ledger)
    presume(ledger, first)
    second = ledger.reserve("3", pass_number=2)
    ledger.mark_dispatched(second)
    ledger.settle(second, cost_usd="2.8", usage={"cost": "2.8"}, generation_id="gen-new")
    ledger.settle(first, cost_usd="0.4", usage={"cost": "0.4"}, generation_id="gen-old")
    snapshot = ledger.snapshot()
    assert snapshot["spent_usd"] == Decimal("3.2")
    assert snapshot["provisional_unknown_requests"] == snapshot["unknown_requests"] == []
    assert snapshot["halted_reason"] == "actual_cost_exceeded_budget"
    receipt = read_openrouter_receipt(ledger.path)
    assert receipt["budget"]["spent_usd"] == "3.2" and len(receipt["requests"]) == 2
    with pytest.raises(BudgetExhausted):
        ledger.reserve("0", pass_number=3)
    with pytest.raises(LedgerError, match="immutable"):
        ledger.settle(first, cost_usd="0")


def test_revocation_restores_original_hold_even_when_it_exceeds_remaining(ledger):
    first = unknown(ledger)
    presume(ledger, first)
    second = ledger.reserve("3", pass_number=2)
    ledger.mark_dispatched(second)
    ledger.settle(second, cost_usd="2", usage={"cost": "2"})
    ledger.revoke_presumed_zero(first, evidence_sha256="e" * 64)
    snapshot = ledger.snapshot()
    assert snapshot["remaining_usd"] == 0 and snapshot["reserved_usd"] == 3 and snapshot["spent_usd"] == 2
    assert snapshot["halted_reason"] == "presumed_zero_recovery_revoked"
    receipt = read_openrouter_receipt(ledger.path)
    assert receipt["budget"]["blocking_unknown_requests"] == 1
    assert receipt["budget"]["provisional_unknown_requests"] == 0
    with pytest.raises((UnsettledRequest, BudgetExhausted)):
        ledger.reserve("0", pass_number=3)
    ledger.settle(first, cost_usd="0.5", usage={"cost": "0.5"})
    assert read_openrouter_receipt(ledger.path)["budget"]["spent_usd"] == "2.5"
    assert ledger.request(first)["metadata"]["presumed_zero_recovery"]["retry_used"] is True


def test_late_generation_or_positive_transport_facts_revoke_release(ledger):
    first = unknown(ledger)
    presume(ledger, first)
    ledger.annotate(first, generation_id="gen-late", metadata={"response_headers_received": True})
    assert not ledger.presumed_zero_valid(first)
    assert ledger.snapshot()["halted_reason"] == "presumed_zero_recovery_revoked"
    assert read_openrouter_receipt(ledger.path)["budget"]["blocking_unknown_requests"] == 1


@pytest.mark.parametrize("method", ["reserve", "annotate", "unknown", "settle"])
@pytest.mark.parametrize("tags", [
    {"presumed_zero_recovery": {"status": "provisional"}},
    {"unreported_cost_nonblocking": True},
])
def test_generic_metadata_cannot_inject_a_nonblocking_certificate(ledger, method, tags):
    request = ledger.reserve("3", pass_number=1)
    ledger.mark_dispatched(request)
    with pytest.raises(LedgerError, match="dedicated"):
        if method == "reserve":
            ledger.reserve("0", pass_number=2, metadata=tags)
        elif method == "annotate":
            ledger.annotate(request, metadata=tags)
        elif method == "unknown":
            ledger.mark_unknown(request, "missing", metadata=tags)
        else:
            ledger.settle(request, cost_usd="0", metadata=tags)


def test_annotation_cannot_release_unknown_hold_with_legacy_nonblocking_flag(ledger):
    request = unknown(ledger)
    before = ledger.snapshot()
    with pytest.raises(LedgerError, match="dedicated"):
        ledger.annotate(request, metadata={"unreported_cost_nonblocking": True})
    assert ledger.snapshot() == before
    assert [row["request_id"] for row in ledger.snapshot()["blocking_unknown_requests"]] == [request]
    assert ledger.snapshot()["reserved_usd"] == Decimal("3")


def test_annotation_persists_header_id_and_refuses_conflicting_or_weakened_facts(ledger):
    request = ledger.reserve("3", pass_number=1)
    ledger.mark_dispatched(request)
    ledger.annotate(request, generation_id="gen-header", metadata={"response_headers_received": True})
    assert ledger.request(request)["generation_id"] == "gen-header"
    with pytest.raises(LedgerError, match="immutable"):
        ledger.annotate(request, generation_id="gen-other")
    with pytest.raises(LedgerError, match="weakened"):
        ledger.annotate(request, metadata={"response_headers_received": False})
    assert ledger.request(request)["cost_usd"] is None


def test_proven_pre_send_failure_is_cancelled_not_falsely_settled(ledger):
    request = ledger.reserve("3", pass_number=1)
    ledger.mark_dispatched(request)
    with pytest.raises(LedgerError):
        ledger.cancel_pre_send_failure(request, category="timeout")
    ledger.annotate(request, metadata={"transport_phase": "pre_send", "request_bytes_sent": False,
        "response_headers_received": False, "output_observed": False})
    result = ledger.cancel_pre_send_failure(request, category="dns_failure")
    assert result["state"] == "cancelled" and result["cost_usd"] is None
    assert result["dispatched_at"] and result["cancelled_at"]
    assert ledger.snapshot()["remaining_usd"] == 3
    receipt = read_openrouter_receipt(ledger.path)
    assert receipt["budget"]["metered_responses"] == 0
    assert receipt["requests"][0]["metadata"]["pre_send_failure"]["category"] == "dns_failure"


def test_tampered_provisional_binding_fails_closed_in_read_only_export(ledger):
    request = unknown(ledger)
    presume(ledger, request)
    with sqlite3.connect(ledger.path) as connection:
        row = connection.execute("SELECT metadata_json FROM openrouter_requests WHERE request_id=?", (request,)).fetchone()
        tags = json.loads(row[0]);tags["presumed_zero_recovery"]["proof_id"] = "foreign"
        connection.execute("UPDATE openrouter_requests SET metadata_json=? WHERE request_id=?", (json.dumps(tags), request))
    with pytest.raises(LedgerError, match="binding"):
        read_openrouter_receipt(ledger.path)


def test_invalid_transport_annotation_never_records_ambiguous_boolean(ledger):
    request = ledger.reserve("3", pass_number=1)
    ledger.mark_dispatched(request)
    with pytest.raises(LedgerError, match="booleans"):
        ledger.annotate(request, metadata={"response_headers_received": None})
    assert ledger.request(request)["metadata"] == {}


def test_late_bill_with_another_dispatch_keeps_readable_receipts_and_halts_admission(ledger):
    first = unknown(ledger)
    presume(ledger, first)
    second = ledger.reserve("3", pass_number=2)
    ledger.mark_dispatched(second)
    ledger.settle(first, cost_usd="0.4", usage={"cost": "0.4"})
    receipt = read_openrouter_receipt(ledger.path)
    assert receipt["budget"]["spent_usd"] == "0.4" and receipt["budget"]["active_requests"] == 1
    assert receipt["budget"]["halted_reason"] == "late_cost_exceeded_reserved_allowance"
    ledger.settle(second, cost_usd="0.1", usage={"cost": "0.1"})
    assert ledger.snapshot()["spent_usd"] == Decimal("0.5")
    with pytest.raises(BudgetExhausted):
        ledger.reserve("0.1", pass_number=3)


def test_revocation_while_second_dispatch_is_active_is_honestly_exportable(ledger):
    first = unknown(ledger)
    presume(ledger, first)
    second = ledger.reserve("3", pass_number=2)
    ledger.mark_dispatched(second)
    ledger.revoke_presumed_zero(first, evidence_sha256="e" * 64)
    exported = read_openrouter_receipt(ledger.path)
    assert exported["budget"]["active_requests"] == 2
    assert exported["budget"]["halted_reason"] == "presumed_zero_recovery_revoked"
    ledger.settle(first, cost_usd="0.3", usage={"cost": "0.3"})
    ledger.settle(second, cost_usd="0.2", usage={"cost": "0.2"})
    assert read_openrouter_receipt(ledger.path)["budget"]["spent_usd"] == "0.5"


def test_recovery_marker_and_history_cannot_be_overwritten_during_annotations(ledger):
    request = unknown(ledger)
    presume(ledger, request)
    before = ledger.request(request)
    with pytest.raises(LedgerError, match="dedicated"):
        ledger.annotate(request, metadata={"presumed_zero_recovery": {}})
    with pytest.raises(LedgerError, match="timestamp"):
        ledger.mark_unknown(request, "still missing", blocks_spending=False,
            metadata={"transport_finished_at": "invalid"})
    assert ledger.request(request) == before


def test_unknown_reopened_with_default_blocking_revokes_release_and_keeps_once_history(ledger):
    request = unknown(ledger)
    presume(ledger, request)
    ledger.mark_unknown(request, "Policy no longer authorizes provisional release")
    assert not ledger.presumed_zero_valid(request)
    assert read_openrouter_receipt(ledger.path)["budget"]["blocking_unknown_requests"] == 1
    with pytest.raises(LedgerError, match="only one"):
        presume(ledger, request)
