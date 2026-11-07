"""Local relay + real SQLite only; all provider POST/GET operations are scripted."""
from contextlib import contextmanager
from decimal import Decimal
from email.message import Message
import http.client
import hashlib
import json
import socket
import threading
from urllib.error import URLError

import pytest

from harness.openrouter import OpenRouterRelay
from harness.openrouter import relay as module
from harness.openrouter.ledger import receipt_identity
from tests.test_product_openrouter_relay import KEY, SETTINGS, Response, body, call, event
from tests.test_product_ledger_recovery import unknown, presume


class ScriptedTransport:
    def __init__(self, outcomes, generations=()):
        self.outcomes = iter(outcomes)
        self.generations = iter(generations)
        self.calls, self.lookups = [], []
        self.before_lookup = None

    @contextmanager
    def open_response(self, payload, *, api_key, timeout):
        assert api_key == KEY
        self.calls.append(payload)
        value = next(self.outcomes)
        if isinstance(value, BaseException):
            raise value
        yield value

    def get_generation(self, generation_id, *, api_key, timeout):
        assert api_key == KEY
        self.lookups.append(generation_id)
        if self.before_lookup:
            self.before_lookup()
        value = next(self.generations, {})
        if isinstance(value, BaseException):
            raise value
        return value


@contextmanager
def relay_at(root, transport, *, policy="generation-v1", sleep=None, backoff=(0, 0, 0)):
    with OpenRouterRelay(root, settings=SETTINGS, proof_id="frozen-run/proof", transport=transport,
            credential_provider=lambda: KEY, budget_policy="local-actual-cost-v1", recovery_policy=policy,
            recovery_backoff=backoff, recovery_sleep=sleep or (lambda _: None)) as relay:
        relay.set_pass(1)
        yield relay


def final(generation="gen-header", cost="0.0123"):
    return {"data": {"id": generation, "status": "completed", "total_cost": cost}}


@pytest.mark.parametrize("failure", [None, TimeoutError(KEY)])
def test_header_id_is_durable_before_first_read_and_delayed_final_cost_settles(tmp_path, failure):
    class CheckedResponse(Response):
        def read(self, size=-1):
            receipt = relay.ledger.requests()[0]
            assert receipt["generation_id"] == "gen-header"
            assert receipt["metadata"]["response_headers_received"] is True
            assert receipt["metadata"]["output_observed"] is False
            if failure:
                raise failure
            return b""
    response = CheckedResponse(raw=b"", headers={"x-generation-id": "gen-header"})
    transport = ScriptedTransport([response], [{}, {"data": {"id": "gen-header", "status": "in_progress", "total_cost": "0"}}, final()])
    sleeps = []
    with relay_at(tmp_path, transport, backoff=(0, 2, 10), sleep=sleeps.append) as relay:
        def before_lookup():
            assert relay.ledger.requests()[0]["metadata"]["transport_finished_at"].endswith("+00:00")
        transport.before_lookup = before_lookup
        status, raw, _ = call(relay)
        assert status == 200 and raw == b""
        receipt, = relay.ledger.requests()
        assert receipt["state"] == "settled" and receipt["cost_usd"] == Decimal("0.0123")
        assert receipt["metadata"]["transport_failure"] is True
        assert receipt["metadata"]["transport_error_category"] == ("timeout" if failure else "incomplete_response")
        assert receipt["metadata"]["transport_finished_at"].endswith("+00:00")
        assert receipt["metadata"]["reconciled"] is True
        assert relay.gate_request()
        assert transport.lookups == ["gen-header"] * 3 and len(transport.calls) == 1
        assert sleeps == [2, 10]
        assert KEY not in json.dumps(relay.status())


def test_policy_none_keeps_header_id_but_does_not_automatically_poll(tmp_path):
    transport = ScriptedTransport([Response(raw=b"", headers={"X-Generation-Id": "gen-header"})], [final()])
    with relay_at(tmp_path, transport, policy="none") as relay:
        assert call(relay)[0] == 200
        receipt, = relay.ledger.requests()
        assert receipt["generation_id"] == "gen-header" and receipt["state"] == "unknown"
        assert receipt["cost_usd"] is None and relay.status()["blocking_unknown_requests"] == 1
        assert not relay.gate_request() and transport.lookups == []


def test_non_success_status_header_id_is_captured_and_polled_without_post_retry(tmp_path):
    transport = ScriptedTransport([Response(raw=b"", status=503, headers={"X-Generation-Id": "gen-header"})], [final()])
    with relay_at(tmp_path, transport) as relay:
        assert call(relay)[0] == 503
        receipt, = relay.ledger.requests()
        assert receipt["generation_id"] == "gen-header" and receipt["state"] == "settled"
        assert receipt["metadata"]["transport_error_category"] == "upstream_http_error"
        assert len(transport.calls) == len(transport.lookups) == 1
        assert relay.gate_request()


@pytest.mark.parametrize("stream", [False, True])
def test_header_and_body_generation_conflict_stops_without_reconciliation_or_retry(tmp_path, stream):
    raw = event(generation="gen-other") if stream else json.dumps({"id": "gen-other", "usage": {"cost": "0.01"}}).encode()
    transport = ScriptedTransport([Response(raw, headers={"X-Generation-Id": "gen-header"})], [final()])
    with relay_at(tmp_path, transport) as relay:
        call(relay, body(stream=stream))
        receipt, = relay.ledger.requests()
        assert receipt["generation_id"] == "gen-header" and receipt["cost_usd"] is None
        assert receipt["metadata"]["protocol_conflict"] is True
        assert receipt["metadata"]["output_observed"] is True
        assert relay.stop_reason == "accounting_error"
        assert transport.lookups == [] and len(transport.calls) == 1


def test_conflicting_duplicate_header_ids_are_rejected_before_any_body_read(tmp_path):
    headers = Message()
    headers.add_header("X-Generation-Id", "gen-header")
    headers.add_header("X-Generation-Id", "gen-other")
    class Unreadable(Response):
        def read(self, _size=-1):
            pytest.fail("conflicting headers must stop before body admission")
    transport = ScriptedTransport([Unreadable(headers=headers)], [final()])
    with relay_at(tmp_path, transport) as relay:
        assert call(relay)[0] == 502
        receipt, = relay.ledger.requests()
        assert receipt["generation_id"] == "gen-header"
        assert receipt["metadata"]["response_headers_received"] is True
        assert receipt["metadata"]["protocol_conflict"] is True
        assert transport.lookups == []


@pytest.mark.parametrize("error,category", [(socket.gaierror(-2, KEY), "dns_failure"),
    (ConnectionRefusedError(KEY), "connection_refused")])
def test_proven_pre_send_category_only_originates_in_connector_before_send(monkeypatch, error, category):
    def fail(_connection):
        raise error
    monkeypatch.setattr(http.client.HTTPSConnection, "connect", fail)
    connection = module._PreSendHTTPSConnection("unused.invalid")
    with pytest.raises(module.PreSendTransportError) as caught:
        connection.connect()
    assert caught.value.category == category and KEY not in str(caught.value)


def test_proven_pre_send_retry_is_bounded_and_never_invents_zero_receipts(tmp_path):
    transport = ScriptedTransport([module.PreSendTransportError("dns_failure"),
        module.PreSendTransportError("connection_refused"), Response(event(generation="gen-success"))])
    with relay_at(tmp_path, transport) as relay:
        assert call(relay)[0] == 200
        receipts = relay.ledger.requests()
        assert [row["state"] for row in receipts] == ["cancelled", "cancelled", "settled"]
        assert [row["cost_usd"] for row in receipts[:2]] == [None, None]
        assert all(row["metadata"]["request_bytes_sent"] is False for row in receipts[:2])
        assert all(row["metadata"]["transport_phase"] == "pre_send" for row in receipts[:2])
        assert relay.status()["spent_usd"] == "0.01" and relay.status()["unknown_requests"] == 0
        assert len(transport.calls) == 3 and all(payload == transport.calls[0] for payload in transport.calls)


def test_exhausted_proven_pre_send_retries_release_only_proven_holds(tmp_path):
    transport = ScriptedTransport([module.PreSendTransportError("dns_failure")] * 3)
    with relay_at(tmp_path, transport) as relay:
        assert call(relay)[0] == 503
        receipts = relay.ledger.requests()
        assert len(receipts) == len(transport.calls) == 3
        assert all(row["state"] == "cancelled" and row["cost_usd"] is None for row in receipts)
        assert receipts[-1]["metadata"]["retry_exhausted"] is True
        assert relay.gate_request() and relay.status()["spent_usd"] == "0"


@pytest.mark.parametrize("error", [TimeoutError(KEY), URLError(socket.gaierror(-2, KEY)), OSError(KEY)])
def test_ambiguous_no_header_failures_never_release_or_automatically_retry(tmp_path, error):
    transport = ScriptedTransport([error])
    with relay_at(tmp_path, transport) as relay:
        assert call(relay)[0] == 502
        receipt, = relay.ledger.requests()
        assert receipt["state"] == "unknown" and receipt["cost_usd"] is None
        assert receipt["metadata"]["response_headers_received"] is False
        assert receipt["metadata"]["output_observed"] is False
        assert receipt["metadata"]["request_bytes_sent"] is None
        assert receipt["metadata"]["transport_finished_at"]
        assert len(transport.calls) == 1 and not transport.lookups and not relay.gate_request()
        assert KEY not in json.dumps(relay.status())
        assert all(KEY.encode() not in path.read_bytes() for path in tmp_path.rglob("*") if path.is_file())


def test_partial_stream_and_close_settle_authoritative_bill_without_paid_retry(tmp_path):
    started, release = threading.Event(), threading.Event()
    partial = b'data: {"type":"response.created","response":{"id":"gen-header"}}\n\n'
    class Interrupted(Response):
        reads = 0
        def read(self, _size=-1):
            self.reads += 1
            if self.reads == 1:
                return partial
            started.set()
            assert release.wait(3)
            raise TimeoutError(KEY)
    transport = ScriptedTransport([Interrupted(headers={"X-Generation-Id": "gen-header"})], [final()])
    with relay_at(tmp_path, transport) as relay:
        results = []
        thread = threading.Thread(target=lambda: results.append(call(relay)))
        thread.start()
        assert started.wait(3)
        relay.close()
        release.set()
        thread.join(4)
        assert not thread.is_alive()
        receipt, = relay.ledger.requests()
        assert receipt["state"] == "settled" and receipt["metadata"]["output_observed"] is True
        assert receipt["metadata"]["transport_failure"] is True
        assert len(transport.calls) == 1 and len(transport.lookups) == 1
        assert not relay.gate_request()


@pytest.mark.parametrize("policy,allowed", [("none", False), ("exclusive-key-v1", True)])
def test_only_frozen_exclusive_policy_preserves_ledger_validated_provisional_marker(tmp_path, policy, allowed):
    transport = ScriptedTransport([])
    with relay_at(tmp_path, transport, policy=policy) as relay:
        relay._credential()  # A real dispatch always freezes its host key identity first.
        request = unknown(relay.ledger)
        presume(relay.ledger, request, key_sha256=hashlib.sha256(KEY.encode()).hexdigest())
    with relay_at(tmp_path, transport, policy=policy) as relay:
        status = relay.reconcile_pending()
        assert status["recovery_policy"] == policy
        assert status["cost_reporting_complete"] is False
        assert status["unknown_requests"] == 1
        assert status["provisional_unknown_requests"] == int(allowed)
        assert status["blocking_unknown_requests"] == int(not allowed)
        assert relay.gate_request() is allowed
        assert relay.ledger.request(request)["cost_usd"] is None
        assert not transport.calls and not transport.lookups


def test_recovery_policy_cannot_change_across_restart(tmp_path):
    with relay_at(tmp_path, ScriptedTransport([]), policy="none"):
        pass
    with pytest.raises(ValueError, match="immutable"):
        with relay_at(tmp_path, ScriptedTransport([]), policy="generation-v1"):
            pass


def test_policy_none_does_not_release_or_retry_even_proven_pre_send_failure(tmp_path):
    transport = ScriptedTransport([module.PreSendTransportError("dns_failure")])
    with relay_at(tmp_path, transport, policy="none") as relay:
        assert call(relay)[0] == 502
        receipt, = relay.ledger.requests()
        assert receipt["state"] == "unknown" and receipt["cost_usd"] is None
        assert receipt["metadata"]["request_bytes_sent"] is False
        assert len(transport.calls) == 1 and not relay.gate_request()


@pytest.mark.parametrize("data", [
    {"id": "gen-other", "status": "completed", "total_cost": "0"},
    {"id": "gen-header", "status": "completed", "usage": {"cost": "0.1"}, "total_cost": "0.2"},
])
def test_generation_identity_or_cost_conflict_is_durably_blocking_not_swallowed(tmp_path, data):
    transport = ScriptedTransport([Response(raw=b"", headers={"X-Generation-Id": "gen-header"})],
        [{"data": data}, final()])
    with relay_at(tmp_path, transport) as relay:
        call(relay)
        receipt, = relay.ledger.requests()
        assert receipt["state"] == "unknown" and receipt["cost_usd"] is None
        assert receipt["metadata"]["protocol_conflict"] is True
        assert receipt["metadata"]["transport_error_category"] == "protocol_error"
        assert relay.stop_reason == "accounting_error" and not relay.gate_request()
        assert len(transport.lookups) == 1 and len(transport.calls) == 1


def test_exclusive_policy_reblocks_marker_for_a_different_host_key(tmp_path):
    transport = ScriptedTransport([])
    with relay_at(tmp_path, transport, policy="exclusive-key-v1") as relay:
        relay._credential()
        request = unknown(relay.ledger)
        presume(relay.ledger, request)  # This helper's synthetic key pin intentionally differs.
    with relay_at(tmp_path, transport, policy="exclusive-key-v1") as relay:
        assert not relay.gate_request()
        assert relay.status()["blocking_unknown_requests"] == 1
        assert relay.status()["provisional_unknown_requests"] == 0


def test_transport_annotation_rejects_raw_exception_or_arbitrary_metadata(tmp_path):
    with relay_at(tmp_path, ScriptedTransport([])) as relay:
        request = relay.ledger.reserve("3", pass_number=1)
        relay.ledger.mark_dispatched(request)
        for tags in ({"transport_error_category": KEY}, {"transport_phase": KEY},
                     {"response_headers_received": "false"}, {"exception_message": KEY}):
            with pytest.raises(ValueError):
                relay._annotate_transport(request, **tags)
        assert KEY not in json.dumps(relay.ledger.request(request)["metadata"])
