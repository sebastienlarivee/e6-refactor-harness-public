"""Offline accounting contract; no provider access or token-price estimates."""

from concurrent.futures import ThreadPoolExecutor
from decimal import Decimal, localcontext
import multiprocessing
import json
import sqlite3
import threading

import pytest

from harness.openrouter.ledger import (
    BudgetExhausted,
    LedgerError,
    OpenRouterLedger,
    UnsettledRequest,
    read_openrouter_receipt,
)


def ledger(tmp_path, **options):
    return OpenRouterLedger(tmp_path / "actual-usd.sqlite3", proof_id="proof-a",
                            model="openai/test-model", **options)


def dispatched(account, amount="1", *, pass_number=1, purpose="inference"):
    request_id = account.reserve(amount, pass_number=pass_number, purpose=purpose)
    account.mark_dispatched(request_id)
    return request_id


def test_default_cap_and_exact_cross_pass_retry_compaction_accounting(tmp_path):
    account = ledger(tmp_path)
    assert account.limit_usd == Decimal("3")
    first = dispatched(account, "1", pass_number=1)
    account.settle(first, cost_usd="0.11", usage={"cost": "0.11", "prompt_tokens": 99999999},
                   generation_id="gen-first")
    retry = dispatched(account, "0.3", pass_number=1, purpose="retry")
    account.settle(retry, cost_usd="0.02", metadata={"http_status": 503})
    compact = dispatched(account, "0.5", pass_number=2, purpose="compaction")
    account.settle(compact, cost_usd="0.07", usage={"cost": "0.07"})
    state = account.snapshot()
    assert state["spent_usd"] == Decimal("0.20")
    assert state["reserved_usd"] == 0
    assert state["remaining_usd"] == Decimal("2.80")
    assert state["halted_reason"] is None
    assert len(account.pass_receipts(pass_number=1)) == 2
    assert account.requests(pass_number=2)[0]["purpose"] == "compaction"
    with pytest.raises(BudgetExhausted):
        account.reserve("2.800000000000000001", pass_number=3)
    assert len(account.requests()) == 3


def test_known_zero_cost_is_settled_but_missing_is_never_zero(tmp_path):
    account = ledger(tmp_path)
    request_id = dispatched(account)
    with pytest.raises(LedgerError):
        account.settle(request_id, cost_usd=None)
    assert account.request(request_id)["cost_usd"] is None
    assert account.snapshot()["reserved_usd"] == 1
    account.settle(request_id, cost_usd=0, usage={"cost": 0}, generation_id="gen-free")
    assert account.request(request_id)["state"] == "settled"
    assert account.snapshot()["spent_usd"] == 0
    assert account.snapshot()["reserved_usd"] == 0


def test_nonblocking_missing_receipt_remains_unknown_and_can_be_reconciled_later(tmp_path):
    account = ledger(tmp_path)
    first = dispatched(account, "3")
    account.attach_generation(first, "gen-late")
    account.mark_unknown(first, "HTTP attempt closed without receipt", blocks_spending=False)
    restarted = ledger(tmp_path)
    state = restarted.snapshot()
    assert len(state["unknown_requests"]) == 1
    assert state["active_requests"] == []
    assert state["reserved_usd"] == 0 and state["halted_reason"] is None
    assert restarted.request(first)["cost_usd"] is None
    second = dispatched(restarted, "3")
    restarted.settle(second, cost_usd="0.2", generation_id="gen-next")
    report = read_openrouter_receipt(restarted.path)
    assert report["budget"]["unknown_requests"] == 1
    assert report["budget"]["active_requests"] == 0
    restarted.settle(first, cost_usd="0.1", generation_id="gen-late")
    assert restarted.snapshot()["spent_usd"] == Decimal("0.3")
    assert restarted.snapshot()["unknown_requests"] == []


@pytest.mark.parametrize("bad", [None, True, False, -1, "-0.001", float("nan"),
                                float("inf"), Decimal("NaN"), Decimal("Infinity"),
                                "", "one", "1_000", {}, [], "0x10"])
def test_invalid_money_is_rejected_at_every_boundary(tmp_path, bad):
    with pytest.raises(LedgerError):
        ledger(tmp_path, limit_usd=bad)
    account = ledger(tmp_path)
    with pytest.raises(LedgerError):
        account.reserve(bad, pass_number=1)
    request_id = dispatched(account)
    with pytest.raises(LedgerError):
        account.settle(request_id, cost_usd=bad)
    assert account.snapshot()["reserved_usd"] == 1
    assert account.snapshot()["spent_usd"] == 0


@pytest.mark.parametrize("pass_number", [0, -1, True, 1.0, "1", None])
def test_invalid_pass_number_is_rejected(tmp_path, pass_number):
    account = ledger(tmp_path)
    with pytest.raises(LedgerError):
        account.reserve("1", pass_number=pass_number)
    if pass_number is not None:
        with pytest.raises(LedgerError):
            account.requests(pass_number=pass_number)


def test_only_undispatched_request_can_release_reservation(tmp_path):
    account = ledger(tmp_path)
    reserved = account.reserve("2", pass_number=1)
    assert account.snapshot()["remaining_usd"] == 1
    with pytest.raises(UnsettledRequest):
        account.reserve("0.01", pass_number=1)
    account.cancel_before_dispatch(reserved)
    account.cancel_before_dispatch(reserved)
    assert account.snapshot()["remaining_usd"] == 3
    request_id = dispatched(account, "2")
    account.mark_dispatched(request_id)
    with pytest.raises(LedgerError):
        account.cancel_before_dispatch(request_id)
    account.mark_unknown(request_id, "read_timeout")
    with pytest.raises(LedgerError):
        account.cancel_before_dispatch(request_id)
    assert account.snapshot()["reserved_usd"] == 2
    with pytest.raises(LedgerError):
        account.settle(reserved, cost_usd="0.1")
    with pytest.raises(LedgerError):
        account.mark_dispatched(reserved)


@pytest.mark.parametrize("phase", ["reserved", "dispatched", "unknown"])
def test_restart_never_frees_an_unsettled_reservation(tmp_path, phase):
    account = ledger(tmp_path)
    request_id = account.reserve("1.25", pass_number=1)
    if phase != "reserved":
        account.mark_dispatched(request_id)
    if phase == "unknown":
        account.attach_generation(request_id, "gen-lost")
        account.mark_unknown(request_id, "provider_cost_missing")
    restarted = ledger(tmp_path)
    state = restarted.snapshot()
    assert state["spent_usd"] == 0
    assert state["reserved_usd"] == Decimal("1.25")
    assert state["remaining_usd"] == Decimal("1.75")
    assert state["active_requests"][0]["request_id"] == request_id
    with pytest.raises(UnsettledRequest):
        restarted.reserve("0.1", pass_number=2)
    if phase == "unknown":
        assert state["halted_reason"] == "unreconciled_provider_cost"
        assert state["unknown_requests"][0]["generation_id"] == "gen-lost"
    restarted.settle(request_id, cost_usd="0.35", generation_id="gen-lost",
                     metadata={"source": "generation_lookup"})
    assert restarted.snapshot()["spent_usd"] == Decimal("0.35")
    assert restarted.snapshot()["reserved_usd"] == 0
    restarted.reserve("1", pass_number=2)


def test_receipt_deduplication_and_immutable_generation_and_cost(tmp_path):
    account = ledger(tmp_path)
    first = dispatched(account)
    account.attach_generation(first, "gen-one")
    account.attach_generation(first, "gen-one")
    account.settle(first, cost_usd="0.2", generation_id="gen-one")
    settled_at = account.request(first)["settled_at"]
    account.settle(first, cost_usd=Decimal("0.2000"), generation_id="gen-one")
    account.mark_unknown(first, "late_disconnect")
    assert account.request(first)["settled_at"] == settled_at
    assert account.request(first)["state"] == "settled"
    with pytest.raises(LedgerError):
        account.settle(first, cost_usd="0.21")
    with pytest.raises(LedgerError):
        account.attach_generation(first, "gen-changed")
    second = dispatched(account)
    with pytest.raises(LedgerError):
        account.settle(second, cost_usd="0.2", generation_id="gen-one")
    assert account.snapshot()["spent_usd"] == Decimal("0.2")
    assert account.snapshot()["reserved_usd"] == 1
    assert account.request(second)["state"] == "dispatched"
    account.mark_unknown(second, "duplicate_generation_id")
    with pytest.raises(UnsettledRequest):
        account.reserve("0.1", pass_number=2)


def test_provider_charge_on_failure_counts_toward_cap(tmp_path):
    account = ledger(tmp_path, limit_usd="0.5")
    failed = dispatched(account, "0.3")
    receipt = account.settle(failed, cost_usd="0.3", usage={"cost": "0.3"},
                            metadata={"http_status": 500, "error_type": "provider_error"})
    assert receipt["metadata"]["http_status"] == 500
    assert account.snapshot()["remaining_usd"] == Decimal("0.2")
    with pytest.raises(BudgetExhausted):
        account.reserve("0.21", pass_number=1, purpose="retry")
    retry = dispatched(account, "0.2", purpose="retry")
    account.settle(retry, cost_usd="0.2")
    assert account.snapshot()["halted_reason"] == "budget_exhausted"
    with pytest.raises(BudgetExhausted):
        account.reserve("0.0001", pass_number=2)


@pytest.mark.parametrize("limit,ceiling,actual", [("3", "0.1", "0.2"), ("0.1", "0.1", "0.2")])
def test_actual_cost_above_reservation_is_retained_and_permanently_halts(tmp_path, limit, ceiling, actual):
    account = ledger(tmp_path, limit_usd=limit)
    request_id = dispatched(account, ceiling)
    account.settle(request_id, cost_usd=actual, generation_id="gen-breach")
    state = account.snapshot()
    assert state["spent_usd"] == Decimal(actual)
    assert state["reserved_usd"] == 0
    assert state["remaining_usd"] == max(Decimal("0"), Decimal(limit) - Decimal(actual))
    assert state["halted_reason"] == "actual_cost_exceeded_reservation"
    restarted = ledger(tmp_path, limit_usd=limit)
    restarted.settle(request_id, cost_usd=actual)
    with pytest.raises(BudgetExhausted, match="permanently halted"):
        restarted.reserve("0", pass_number=2)


def test_database_identity_cannot_be_changed_on_restart(tmp_path):
    account = ledger(tmp_path, limit_usd="1.20")
    assert ledger(tmp_path, limit_usd="1.2").limit_usd == Decimal("1.2")
    for changes in [{"proof_id": "other"}, {"model": "other"}, {"limit_usd": "2"}]:
        arguments = {"proof_id": "proof-a", "model": "openai/test-model", "limit_usd": "1.2"}
        arguments.update(changes)
        with pytest.raises(LedgerError, match="immutable"):
            OpenRouterLedger(account.path, **arguments)
    for field, value in [("proof_id", "other"), ("model", "other"), ("limit_usd", Decimal("4"))]:
        with pytest.raises(AttributeError):
            setattr(account, field, value)


def test_decimal_arithmetic_ignores_low_precision_callers(tmp_path):
    account = ledger(tmp_path, limit_usd="1.00000000000000000000000000000000000001")
    with localcontext() as context:
        context.prec = 3
        request_id = dispatched(account, "0.99999999999999999999999999999999999999")
        account.settle(request_id, cost_usd="0.99999999999999999999999999999999999999")
        assert account.snapshot()["remaining_usd"] == Decimal("0.00000000000000000000000000000000000002")
        with pytest.raises(BudgetExhausted):
            account.reserve("0.00000000000000000000000000000000000003", pass_number=2)


def test_reserve_is_atomic_across_concurrent_connections(tmp_path):
    account = ledger(tmp_path)
    count = 12
    barrier = threading.Barrier(count)

    def reserve_one(_):
        other = ledger(tmp_path)
        barrier.wait(timeout=10)
        try:
            return other.reserve("2", pass_number=1)
        except UnsettledRequest:
            return None

    with ThreadPoolExecutor(max_workers=count) as executor:
        results = list(executor.map(reserve_one, range(count)))
    assert len([result for result in results if result is not None]) == 1
    assert len(account.requests()) == 1
    assert account.snapshot()["reserved_usd"] == 2


def _reserve_process(path, start, results):
    account = OpenRouterLedger(path, proof_id="proof-a", model="openai/test-model")
    start.wait(timeout=10)
    try:
        account.reserve("2", pass_number=1)
        results.put("reserved")
    except UnsettledRequest:
        results.put("unsettled")


def test_reserve_is_atomic_across_processes(tmp_path):
    account = ledger(tmp_path)
    context = multiprocessing.get_context("spawn")
    start, results = context.Event(), context.Queue()
    processes = [context.Process(target=_reserve_process, args=(account.path, start, results)) for _ in range(4)]
    try:
        for process in processes:
            process.start()
        start.set()
        outcome = [results.get(timeout=20) for _ in processes]
        for process in processes:
            process.join(timeout=10)
            assert process.exitcode == 0
        assert outcome.count("reserved") == 1
        assert outcome.count("unsettled") == 3
        assert account.snapshot()["reserved_usd"] == 2
    finally:
        for process in processes:
            if process.is_alive():
                process.terminate()
                process.join(timeout=5)
        results.close()


def test_duplicate_settlement_concurrency_counts_receipt_once(tmp_path):
    account = ledger(tmp_path)
    request_id = dispatched(account)

    def settle_one(_):
        return ledger(tmp_path).settle(request_id, cost_usd="0.125", generation_id="gen-once")

    with ThreadPoolExecutor(max_workers=8) as executor:
        receipts = list(executor.map(settle_one, range(16)))
    assert {receipt["cost_usd"] for receipt in receipts} == {Decimal("0.125")}
    assert account.snapshot()["spent_usd"] == Decimal("0.125")
    assert len(account.requests()) == 1


def test_snapshot_is_read_only_and_does_not_reclassify_active_work(tmp_path):
    account = ledger(tmp_path)
    request_id = dispatched(account)
    before = account.path.read_bytes()
    receipt = account.request(request_id)
    for _ in range(3):
        assert account.snapshot()["active_requests"][0] == receipt
        assert account.requests() == [receipt]
    assert account.path.read_bytes() == before


def test_only_accounting_data_reaches_database(tmp_path):
    account = ledger(tmp_path)
    for metadata in [{"prompt": "private prompt"}, {"nested": {"api_key": "private-key"}},
                     {"messages": []}, {"headers": {}}, {"request_body": "private"},
                     {"source": "Bearer private-key"}]:
        with pytest.raises(LedgerError):
            account.reserve("1", pass_number=1, metadata=metadata)
    request_id = dispatched(account)
    account.settle(request_id, cost_usd="0.1", usage={
        "cost": "0.1", "prompt_tokens": 12,
        "prompt_tokens_details": {"cached_tokens": 3, "content": "private prompt"},
        "messages": [{"content": "private prompt"}], "api_key": "private-key",
    }, metadata={"http_status": 200, "source": "terminal_usage"})
    receipt = account.request(request_id)
    assert receipt["usage"] == {"cost": "0.1", "prompt_tokens": "12",
                                "prompt_tokens_details": {"cached_tokens": "3"}}
    assert b"private prompt" not in account.path.read_bytes()
    assert b"private-key" not in account.path.read_bytes()


def test_conflicting_provider_usage_does_not_settle_or_free_reservation(tmp_path):
    account = ledger(tmp_path)
    request_id = dispatched(account)
    with pytest.raises(LedgerError, match="conflicts"):
        account.settle(request_id, cost_usd="0.1", usage={"cost": "0.2"})
    assert account.snapshot()["reserved_usd"] == 1
    assert account.request(request_id)["cost_usd"] is None


def test_unrecognized_request_ids_and_generation_transitions_fail(tmp_path):
    account = ledger(tmp_path)
    with pytest.raises(LedgerError):
        account.request("missing")
    request_id = account.reserve("1", pass_number=1)
    with pytest.raises(LedgerError):
        account.attach_generation(request_id, "gen-before-dispatch")
    account.mark_dispatched(request_id)
    for value in [None, "", True]:
        with pytest.raises(LedgerError):
            account.attach_generation(request_id, value)


def test_read_only_receipt_helper_is_json_safe_stable_and_includes_passes(tmp_path):
    account = ledger(tmp_path)
    request_id = dispatched(account, pass_number=2)
    account.settle(request_id, cost_usd="0.15", usage={"cost": "0.15"}, generation_id="gen-export")
    before = account.path.read_bytes()
    exported = read_openrouter_receipt(account.path)
    assert exported == read_openrouter_receipt(account.path)
    assert exported["identity"]["proof_id"] == "proof-a"
    assert exported["budget"]["spent_usd"] == "0.15"
    assert exported["budget"]["metering_enabled"] is True
    assert exported["budget"]["active_requests"] == 0
    assert exported["budget"]["unknown_requests"] == 0
    assert exported["budget"]["completed_requests"] == 1
    assert exported["requests"][0]["pass_number"] == 2
    assert len(exported["sha256"]) == 64
    json.dumps(exported, allow_nan=False)
    assert account.path.read_bytes() == before
    second = dispatched(account, pass_number=3)
    assert exported["sha256"] != read_openrouter_receipt(account.path)["sha256"]
    assert read_openrouter_receipt(account.path)["budget"]["reserved_usd"] == "1"
    assert read_openrouter_receipt(account.path)["budget"]["active_request_ids"] == [second]


def test_receipt_helper_does_not_create_missing_database(tmp_path):
    path = tmp_path / "missing.sqlite3"
    with pytest.raises(LedgerError):
        read_openrouter_receipt(path)
    assert not path.exists()


def test_receipt_helper_rejects_corrupted_money_and_conflicting_provider_cost(tmp_path):
    account = ledger(tmp_path)
    request_id = dispatched(account)
    account.settle(request_id, cost_usd="0.1", usage={"cost": "0.1"})
    with sqlite3.connect(account.path) as connection:
        connection.execute("UPDATE openrouter_requests SET usage_json = ? WHERE request_id = ?",
                           ('{"cost":"0.2"}', request_id))
    with pytest.raises(LedgerError, match="conflicts"):
        read_openrouter_receipt(account.path)
    with sqlite3.connect(account.path) as connection:
        connection.execute("UPDATE openrouter_requests SET cost_usd = 'NaN' WHERE request_id = ?", (request_id,))
    with pytest.raises(LedgerError):
        read_openrouter_receipt(account.path)


def test_byok_combined_liability_survives_resume_and_export(tmp_path):
    account = ledger(tmp_path, limit_usd="0.1")
    request_id = dispatched(account, "0.1")
    usage = {"cost": "0.0001", "is_byok": True, "cost_details": {
        "upstream_inference_cost": "0.000096",
        "upstream_inference_input_cost": "0.000026",
        "upstream_inference_output_cost": "0.000070"}}
    with localcontext() as context:
        context.prec = 2
        account.settle(request_id, cost_usd="0.000196", usage=usage, generation_id="gen-byok")
    resumed = ledger(tmp_path, limit_usd="0.1")
    resumed.settle(request_id, cost_usd="0.000196", usage=usage, generation_id="gen-byok")
    state = resumed.snapshot()
    assert state["spent_usd"] == Decimal("0.000196")
    assert state["openrouter_cost_usd"] == Decimal("0.0001")
    assert state["byok_upstream_cost_usd"] == Decimal("0.000096")
    assert state["remaining_usd"] == Decimal("0.099804")
    exported = read_openrouter_receipt(account.path)
    assert exported["requests"][0]["usage"] == usage
    assert exported["budget"]["spent_usd"] == "0.000196"
    assert exported["budget"]["byok_upstream_cost_usd"] == "0.000096"
    with pytest.raises(LedgerError, match="conflicting"):
        resumed.settle(request_id, cost_usd="0.000196", usage={"cost": "0.000096", "is_byok": True,
                       "cost_details": {"upstream_inference_cost": "0.0001"}})


@pytest.mark.parametrize("usage", [
    {"cost": "0", "is_byok": True},
    {"cost": "0", "is_byok": True, "cost_details": {"upstream_inference_cost": "NaN"}},
    {"cost": "0", "is_byok": True, "upstream_inference_cost": "0.01",
     "cost_details": {"upstream_inference_cost": "0.02"}},
    {"cost": "0", "is_byok": True, "cost_details": {"upstream_inference_cost": "0.01",
     "upstream_inference_input_cost": "0.01", "upstream_inference_output_cost": "0.01"}},
])
def test_byok_missing_or_inconsistent_liability_cannot_settle_at_zero(tmp_path, usage):
    account = ledger(tmp_path)
    request_id = dispatched(account)
    with pytest.raises(LedgerError):
        account.settle(request_id, cost_usd="0", usage=usage)
    assert account.request(request_id)["state"] == "dispatched"
    assert account.snapshot()["reserved_usd"] == 1


def test_ordinary_upstream_cost_detail_is_not_added_twice(tmp_path):
    account = ledger(tmp_path)
    request_id = dispatched(account)
    account.settle(request_id, cost_usd="0.2", usage={"cost": "0.2", "is_byok": False,
                   "cost_details": {"upstream_inference_cost": "0.2"}})
    assert account.snapshot()["spent_usd"] == Decimal("0.2")
    assert account.snapshot()["byok_upstream_cost_usd"] == 0


def test_byok_export_rejects_old_fee_only_settlement(tmp_path):
    account = ledger(tmp_path)
    request_id = dispatched(account)
    account.settle(request_id, cost_usd="0", usage={"cost": "0"})
    with sqlite3.connect(account.path) as connection:
        connection.execute("UPDATE openrouter_requests SET usage_json = ? WHERE request_id = ?",
                           (json.dumps({"cost": "0", "is_byok": True,
                                        "cost_details": {"upstream_inference_cost": "0.1"}}), request_id))
    with pytest.raises(LedgerError, match="conflicts"):
        read_openrouter_receipt(account.path)


@pytest.mark.parametrize("details", [
    {"upstream_inference_cost": "0.01", "upstream_inference_input_cost": "0.02"},
    {"upstream_inference_cost": "0.01", "upstream_inference_input_cost": "0.004",
     "upstream_inference_prompt_cost": "0.006"},
])
def test_byok_partial_components_and_aliases_cannot_contradict_aggregate(tmp_path, details):
    account = ledger(tmp_path)
    request_id = dispatched(account)
    with pytest.raises(LedgerError, match="conflict"):
        account.settle(request_id, cost_usd="0.01", usage={"cost": "0", "is_byok": True,
                       "cost_details": details})
    assert account.snapshot()["reserved_usd"] == 1
