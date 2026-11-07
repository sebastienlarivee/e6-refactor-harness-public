"""Synthetic Responses streams only: no live inference or key API calls."""
from contextlib import contextmanager
from dataclasses import replace
from decimal import Decimal, localcontext
from http.client import HTTPConnection
import io
import json
from pathlib import Path
import threading
from urllib.parse import urlparse
import pytest
from harness.openrouter import OpenRouterRelay, OpenRouterSettings, UnsettledRequest

KEY = "synthetic-only-host-credential"
SETTINGS = OpenRouterSettings("test/model", "pinned", Decimal("2.5"), Decimal("10"), 1050000,
                              128000, supported_reasoning_efforts=("high",), default_reasoning_effort="high")

def event(kind="response.completed", cost="0.01", generation="gen-one", **fields):
    usage = {"input_tokens": 10, "output_tokens": 1, "output_tokens_details": {"reasoning_tokens": 1}}
    if cost is not None:
        usage["cost"] = cost
    return ("event: " + kind + "\r\ndata: " + json.dumps({"type": kind, "response": {
        "id": generation, "model": "test/model", "status": kind.split(".")[-1], "usage": usage, **fields}}) + "\r\n\r\n").encode()

class Response:
    def __init__(self, raw=None, *, chunks=None, status=200, headers=None):
        self.source = io.BytesIO(event() if raw is None else raw)
        self.chunks = iter(chunks) if chunks is not None else None
        self.status = status
        self.headers = headers or {}
    def read(self, size=-1):
        if self.chunks is not None:
            chunk = next(self.chunks, b"")
            if isinstance(chunk, BaseException):
                raise chunk
            return chunk
        return self.source.read(size)

class Transport:
    def __init__(self, response=None, generation=None):
        self.response = response or Response()
        self.generation = generation
        self.calls = []
        self.lookups = []
    @contextmanager
    def open_response(self, payload, *, api_key, timeout):
        assert api_key == KEY
        self.calls.append(payload)
        yield self.response
    def get_generation(self, generation_id, *, api_key, timeout):
        self.lookups.append(generation_id)
        assert api_key == KEY
        return self.generation

def body(**fields):
    return {"model": "test/model", "input": [{"role": "user", "content": "refactor"}], "stream": True, **fields}

def call(relay, payload=None):
    url = urlparse(relay.url)
    connection = HTTPConnection(url.hostname, url.port, timeout=5)
    connection.request("POST", "/responses", json.dumps(payload or body()),
                       {"Authorization": "Bearer " + relay.token, "Content-Type": "application/json"})
    response = connection.getresponse()
    status, raw, headers = response.status, response.read(), response.headers
    connection.close()
    assert relay.wait_for_idle(3)
    return status, raw, headers

@contextmanager
def relay_at(root, *, settings=SETTINGS, transport=None, budget_policy="provider-key-v1", proof_id="frozen-run/proof"):
    with OpenRouterRelay(root, settings=settings, proof_id=proof_id, transport=transport or Transport(),
                         credential_provider=lambda: KEY, budget_policy=budget_policy) as relay:
        relay.set_pass(1)
        yield relay

@pytest.mark.parametrize("cap", [None, 8192, 128000])
def test_native_payload_preserved_without_local_context_or_output_budgeting(tmp_path, cap):
    wire = event()
    transport = Transport(Response(chunks=[wire[:17], wire[17:43], wire[43:]]))
    # This history exceeded both the former byte-based input budget and its
    # guessed context capacity. The provider, not the relay, decides admission.
    payload = body(input=[{"role": "user", "content": "Lean history " * 100000}],
        instructions="preserve instructions", reasoning={"effort": "xhigh"},
        tools=[{"type": "function", "name": "check", "parameters": {"type": "object"}}],
        include=["reasoning.encrypted_content"], truncation="disabled")
    if cap is not None:
        payload["max_output_tokens"] = cap
    with relay_at(tmp_path, settings=replace(SETTINGS, budget_usd=Decimal("0.03")), transport=transport) as relay:
        assert call(relay, payload)[0:2] == (200, wire)
        sent = transport.calls[0]
        for field, value in payload.items():
            assert sent[field] == value
        assert ("max_output_tokens" in sent) == (cap is not None)
        assert sent["provider"]["only"] == ["pinned"]
        assert sent["provider"]["allow_fallbacks"] is False
        assert sent["provider"]["require_parameters"] is True
        receipt = relay.ledger.requests()[0]
        assert receipt["reserved_usd"] == Decimal("0.03")
        assert receipt["cost_usd"] == Decimal("0.01")
        assert relay.status()["strict_dollar_cap_claimed"] is False
        assert relay.status()["context_admission_enabled"] is False
        assert relay.status()["output_cap_tokens"] is None


def test_actual_cached_charges_release_allowance_without_changing_output_or_context(tmp_path):
    transport = Transport(Response(event(cost="0.01")))
    payload = body(input=["full unchanged history"] * 100, max_output_tokens=128000)
    with relay_at(tmp_path, settings=replace(SETTINGS, budget_usd=Decimal("0.03")), transport=transport) as relay:
        assert call(relay, payload)[0] == 200
        assert relay.gate_request()
        relay.transport = Transport(Response(event(cost="0.02", generation="gen-two")))
        assert call(relay, payload)[0] == 200
        assert relay.transport.calls[0] == transport.calls[0]
        assert relay.ledger.requests()[1]["reserved_usd"] == Decimal("0.02")
        assert relay.status()["spent_usd"] == "0.03"
        assert call(relay)[0] == 402
        assert len(relay.transport.calls) == 1
        assert relay.stop_reason == "budget_reached"


def test_parallel_tool_permission_uses_frozen_provider_capability(tmp_path):
    with relay_at(tmp_path) as relay:
        assert call(relay, body(parallel_tool_calls=True))[0] == 200
        assert "parallel_tool_calls" not in relay.transport.calls[0]


@pytest.mark.parametrize("kind", ["response.completed", "response.failed", "response.incomplete"])
def test_terminal_status_including_charged_failures_settles_actual(tmp_path, kind):
    with relay_at(tmp_path, transport=Transport(Response(event(kind, cost="0.023")))) as relay:
        assert call(relay)[0] == 200
        assert relay.status()["spent_usd"] == "0.023"
        assert relay.status()["unknown_requests"] == 0


@pytest.mark.parametrize("reason", ["max_output_tokens", "content_filter", "provider prose", {"bad": "shape"}, None])
def test_incomplete_reason_is_sanitized_without_changing_wire_or_replaying(tmp_path, reason):
    wire = event("response.incomplete", incomplete_details={"reason": reason, "message": KEY})
    transport = Transport(Response(wire))
    with relay_at(tmp_path, transport=transport) as relay:
        status, raw, _ = call(relay)
        assert status == 200 and raw == wire.replace(KEY.encode(), b"[REDACTED]")
        metadata = relay.ledger.requests()[0]["metadata"]
        if reason in ("max_output_tokens", "content_filter"):
            assert metadata["incomplete_reason"] == reason
        else:
            assert "incomplete_reason" not in metadata
        assert len(transport.calls) == 1 and relay.status()["spent_usd"] == "0.01"
        assert KEY not in json.dumps(metadata)

@pytest.mark.parametrize("cost", [None, "NaN", "-1", True])
def test_unreported_cost_is_visible_without_blocking_native_retry_or_resume(tmp_path, cost):
    with relay_at(tmp_path, transport=Transport(Response(event(cost=cost)))) as relay:
        assert call(relay)[0] == 200
        assert relay.status()["unknown_requests"] == 1
        assert Decimal(relay.status()["reserved_usd"]) == 0
        assert relay.status()["active_requests"] == 0
        assert relay.status()["cost_reporting_complete"] is False
        assert relay.gate_request()
        relay.transport = Transport(Response(event(cost="0.02", generation="gen-next")))
        assert call(relay)[0] == 200
        assert relay.status()["unknown_requests"] == 1
        assert relay.status()["spent_usd"] == "0.02"
    with relay_at(tmp_path) as resumed:
        assert resumed.stop_reason is None
        assert resumed.gate_request()
        assert resumed.status()["dispatched_requests"] == 2

def test_interruption_then_final_generation_receipt_reconciles_same_identity(tmp_path):
    wire = event(cost=None)
    with relay_at(tmp_path, transport=Transport(Response(chunks=[wire, OSError("disconnect")]))) as relay:
        assert call(relay)[0] == 200
        assert relay.status()["unknown_requests"] == 1
    transport = Transport(generation={"data": {"id": "gen-one", "status": "completed", "total_cost": "0.001234"}})
    with relay_at(tmp_path, transport=transport) as resumed:
        status = resumed.reconcile_pending()
        assert status["spent_usd"] == "0.001234"
        assert status["unknown_requests"] == 0
        assert status["stop_reason"] is None
        assert resumed.gate_request()
        assert transport.calls == []

def test_provisional_generation_cost_does_not_release_unknown(tmp_path):
    transport = Transport(Response(event(cost=None)), generation={"data": {"id": "gen-one", "total_cost": "0"}})
    with relay_at(tmp_path, transport=transport) as relay:
        call(relay)
        assert relay.status()["unknown_requests"] == 1
        assert relay.gate_request()
        assert relay.status()["cost_reporting_complete"] is False

def test_duplicate_terminal_receipt_does_not_double_charge(tmp_path):
    wire = event()
    with relay_at(tmp_path, transport=Transport(Response(wire + wire))) as relay:
        assert call(relay)[0] == 200
        assert relay.status()["spent_usd"] == "0.01"
        assert relay.status()["metered_responses"] == 1
        assert relay.stop_reason is None

def test_changed_profile_and_proof_identity_rejected_on_resume(tmp_path):
    with relay_at(tmp_path) as relay:
        call(relay)
    with pytest.raises(ValueError, match="immutable"):
        OpenRouterRelay(tmp_path, settings=replace(SETTINGS, budget_usd=Decimal("1.5")))
    from harness.openrouter import LedgerError
    with pytest.raises(LedgerError, match="immutable"):
        OpenRouterRelay(tmp_path, settings=SETTINGS, proof_id="another/proof")

def test_compaction_passes_and_restart_share_decimal_actual_total(tmp_path):
    costs = ["0.010000000000000000000000000001", "0.02"]
    with relay_at(tmp_path) as relay:
        for number, cost in enumerate(costs, 1):
            relay.set_pass(number)
            relay.transport = Transport(Response(event(cost=cost, generation=f"gen-{number}")))
            call(relay, body(instructions="compact previous history" if number == 2 else "refactor"))
    with relay_at(tmp_path) as relay:
        assert relay.status()["spent_usd"] == "0.030000000000000000000000000001"
        assert relay.status()["dispatched_requests"] == 2

@pytest.mark.parametrize("field,value", [("previous_response_id", "hidden"), ("background", True),
    ("tools", [{"type": "web_search"}]), ("input", [{"type": "input_image", "image_url": "secret"}]), ("model", "fallback/model")])
def test_unbounded_or_fallback_request_rejected_before_payment(tmp_path, field, value):
    with relay_at(tmp_path) as relay:
        assert call(relay, body(**{field:value}))[0] == 400
        assert not relay.transport.calls

def test_http_status_and_retry_headers_passthrough_after_authoritative_settlement(tmp_path):
    raw = json.dumps({"error": {"message": "rate limited"}, "usage": {"cost": "0"}, "id": "gen-http"}).encode()
    transport = Transport(Response(raw, status=429, headers={"Retry-After": "7"}))
    with relay_at(tmp_path, transport=transport) as relay:
        status, wire, headers = call(relay)
        assert status == 429 and wire == raw and headers["Retry-After"] == "7"
        assert relay.status()["spent_usd"] == "0"
        assert relay.stop_reason is None
        assert relay.gate_request()

def test_upstream_key_echo_split_across_chunks_redacted(tmp_path):
    wire = event(extra=KEY)
    index = wire.index(KEY.encode()) + 8
    with relay_at(tmp_path, transport=Transport(Response(chunks=[wire[:index], wire[index:]]))) as relay:
        status, raw, _ = call(relay)
        assert status == 200 and KEY.encode() not in raw and b"[REDACTED]" in raw
        assert KEY not in json.dumps(relay.status())
        for path in Path(tmp_path).rglob("*"):
            if path.is_file():
                assert KEY.encode() not in path.read_bytes()

def test_one_paid_request_in_flight_per_proof(tmp_path):
    started, release = threading.Event(), threading.Event()
    class BlockingTransport(Transport):
        @contextmanager
        def open_response(self, payload, *, api_key, timeout):
            self.calls.append(payload)
            started.set()
            assert release.wait(4)
            yield Response()
    with relay_at(tmp_path, transport=BlockingTransport()) as relay:
        result = []
        worker = threading.Thread(target=lambda: result.append(call(relay)))
        worker.start()
        assert started.wait(3)
        url = urlparse(relay.url)
        conn = HTTPConnection(url.hostname, url.port, timeout=3)
        conn.request("POST", "/responses", json.dumps(body()), {"Authorization": "Bearer " + relay.token})
        response = conn.getresponse()
        assert response.status == 409
        response.read()
        conn.close()
        assert len(relay.transport.calls) == 1
        release.set()
        worker.join(4)
        assert result[0][0] == 200


def test_key_replacement_on_resume_fails_before_dispatch(tmp_path):
    with relay_at(tmp_path) as relay:
        call(relay)
    with OpenRouterRelay(tmp_path, settings=SETTINGS, proof_id="frozen-run/proof", transport=Transport(),
                         credential_provider=lambda: "different-synthetic-key") as resumed:
        resumed.set_pass(2)
        assert call(resumed)[0] == 503
        assert resumed.transport.calls == []
        assert resumed.status()["dispatched_requests"] == 1


def test_final_charge_overrun_is_reported_and_permanently_stops_at_budget(tmp_path):
    settings = replace(SETTINGS, budget_usd=Decimal("0.01"))
    with relay_at(tmp_path, settings=settings, transport=Transport(Response(event(cost="0.02")))) as relay:
        assert call(relay)[0] == 200
        assert relay.status()["spent_usd"] == "0.02"
        assert relay.stop_reason == "budget_reached"
        assert relay.status()["halted_reason"] == "actual_cost_exceeded_reservation"
        assert relay.status()["over_budget_usd"] == "0.01"
        assert relay.status()["cost_reporting_complete"] is True
        assert not relay.gate_request()
    with relay_at(tmp_path, settings=settings) as relay:
        assert relay.stop_reason == "budget_reached"
        assert not relay.gate_request()


def test_anthropic_automatic_cache_control_preserves_the_native_payload(tmp_path):
    settings = replace(SETTINGS, model_id="anthropic/claude-haiku-5.5", automatic_prompt_cache=True)
    payload = body(model=settings.model_id, instructions="keep this guide", input=["native conversation"],
        reasoning={"effort": "xhigh"})
    with relay_at(tmp_path, settings=settings) as relay:
        assert call(relay, payload)[0] == 200
        sent = relay.transport.calls[0]
        for name, value in payload.items():
            assert sent[name] == value
        assert sent["cache_control"] == {"type": "ephemeral"}
        assert "max_output_tokens" not in sent
        assert relay.status()["prompt_cache_policy"] == "anthropic_ephemeral"
    with pytest.raises(ValueError, match="Anthropic"):
        replace(SETTINGS, automatic_prompt_cache=True)


def test_compaction_preserves_native_output_setting_and_history(tmp_path):
    payload = body(instructions="compact history", input=["history"], max_output_tokens=16000)
    with relay_at(tmp_path) as relay:
        prepared, reserved = relay._prepare(payload)
        assert prepared["max_output_tokens"] == 16000
        assert prepared["input"] == payload["input"]
        assert prepared["instructions"] == payload["instructions"]
        assert reserved == SETTINGS.budget_usd
        assert relay.status()["reservation_policy"] == "hold_remaining_allowance_during_http_attempt"


@pytest.mark.parametrize("http_status,source,expected_stop", [
    (402, "openrouter_key_limit", "budget_reached"),
    (403, "openrouter_key_limit", "budget_reached"),
    (402, "openrouter_credits", "account_error"),
    (403, "openrouter_guardrail_budget", "account_error"),
    (403, "openrouter_workspace_budget", "account_error"),
    (402, "openrouter_in_flight_budget", None),
])
def test_documented_pre_provider_credit_rejection_settles_zero_without_fresh_pass(
        tmp_path, http_status, source, expected_stop):
    raw = json.dumps({"error": {"code": http_status, "message": "limited",
        "metadata": {"limit_source": source}}}).encode()
    transport = Transport(Response(raw, status=http_status, headers={"Retry-After": "7"}))
    with relay_at(tmp_path, transport=transport) as relay:
        status, wire, headers = call(relay)
        assert (status, wire, headers["Retry-After"]) == (http_status, raw, "7")
        assert relay.stop_reason == expected_stop
        assert relay.status()["unknown_requests"] == 0
        assert relay.status()["spent_usd"] == "0"
        assert relay.status()["metered_responses"] == 0
        assert relay.status()["credit_rejected_requests"] == 1
        row = relay.ledger.requests()[0]
        assert row["metadata"]["billing_basis"] == "openrouter_credit_rejection"
        assert (tmp_path / row["metadata"]["credit_rejection_evidence_file"]).read_bytes() == raw
        if expected_stop:
            relay.set_pass(2)
            assert call(relay)[0] == 402
            assert len(transport.calls) == 1
        else:
            relay.transport = Transport(Response(event()))
            assert call(relay)[0] == 200
            assert relay.ledger.requests()[1]["pass_number"] == 1
    if expected_stop:
        with relay_at(tmp_path) as resumed:
            assert resumed.stop_reason == expected_stop
            assert not resumed.gate_request()


@pytest.mark.parametrize("extra,metadata", [
    ({}, {}),
    ({}, {"limit_source": "provider_limit"}),
    ({"id": "gen-maybe-paid"}, {"limit_source": "openrouter_key_limit"}),
    ({}, {"limit_source": "openrouter_key_limit", "provider_name": "upstream"}),
])
def test_generic_or_provider_credit_error_is_not_assumed_free(tmp_path, extra, metadata):
    raw = json.dumps({**extra, "error": {"code": 402, "message": "limited", "metadata": metadata}}).encode()
    with relay_at(tmp_path, transport=Transport(Response(raw, status=402))) as relay:
        assert call(relay)[0] == 402
        assert relay.status()["unknown_requests"] == 1
        assert not relay.gate_request()


def credit_error(requested=65536, affordable=63129, structured=False):
    metadata = {"provider_name": None}
    if structured:
        metadata.update(limit_source="openrouter_key_limit", remedy_hint="Raise or remove this API key's usage limit.")
    return json.dumps({"error": {"code": 402, "metadata": metadata,
        "message": "This request requires more credits, or fewer max_tokens. "
        f"You requested up to {requested} tokens, but can only afford {affordable}. "
        "To increase, visit https://openrouter.ai/workspaces/default/keys/abc123 "
        "and adjust the key's total limit"}}).encode()


class SequenceTransport(Transport):
    def __init__(self, responses):
        super().__init__()
        self.responses = iter(responses)

    @contextmanager
    def open_response(self, payload, *, api_key, timeout):
        assert api_key == KEY
        self.calls.append(payload)
        yield next(self.responses)


@pytest.mark.parametrize("structured", [False, True])
def test_provider_affordable_hint_retries_same_native_context_without_cost_estimation(tmp_path, structured):
    transport = SequenceTransport([Response(credit_error(structured=structured), status=402), Response(event(cost="0.017"))])
    payload = body(input=["full native history"], reasoning={"effort": "xhigh"}, instructions="continue")
    with relay_at(tmp_path, transport=transport) as relay:
        assert call(relay, payload)[0] == 200
        first, second = transport.calls
        assert "max_output_tokens" not in first
        assert second == {**first, "max_output_tokens": 63129}
        receipts = relay.ledger.requests()
        assert len(receipts) == 2
        assert receipts[0]["cost_usd"] == 0
        assert receipts[1]["cost_usd"] == Decimal("0.017")
        assert receipts[1]["metadata"]["provider_advertised_output_cap"] is True
        assert relay.status()["unknown_requests"] == 0
        assert relay.status()["active_requests"] == 0
        assert relay.stop_reason is None
        assert relay.gate_request()


def test_credit_hint_adjustments_are_bounded_and_never_increase_a_native_cap(tmp_path):
    transport = SequenceTransport([Response(credit_error(a, b), status=402)
        for a, b in [(65536, 60000), (60000, 50000), (50000, 40000)]])
    with relay_at(tmp_path, transport=transport) as relay:
        assert call(relay)[0] == 402
        assert len(transport.calls) == 3
        assert relay.stop_reason == "budget_reached"
        assert relay.status()["unknown_requests"] == 0
        assert relay.status()["spent_usd"] == "0"
    with relay_at(tmp_path / "native-cap", transport=Transport(Response(credit_error(), status=402))) as relay:
        assert call(relay, body(max_output_tokens=8000))[0] == 402
        assert len(relay.transport.calls) == 1
        assert relay.transport.calls[0]["max_output_tokens"] == 8000


def test_closing_between_credit_rejection_and_retry_prevents_new_dispatch(tmp_path):
    class ClosingTransport(Transport):
        @contextmanager
        def open_response(self, payload, **kwargs):
            self.calls.append(payload)
            yield Response(credit_error(), status=402)
            relay.close()
    transport = ClosingTransport()
    with relay_at(tmp_path, transport=transport) as relay:
        assert call(relay)[0] == 503
        assert len(transport.calls) == 1
        assert relay.status()["spent_usd"] == "0"
        assert relay.status()["unknown_requests"] == 0


def test_zero_provider_allowance_stops_without_retry_or_unknown_usage(tmp_path):
    with relay_at(tmp_path, transport=Transport(Response(credit_error(65536, 0), status=402))) as relay:
        assert call(relay)[0] == 402
        assert len(relay.transport.calls) == 1
        assert relay.stop_reason == "budget_reached"
        assert relay.status()["unknown_requests"] == 0


def test_transient_http_failure_without_usage_allows_native_retry(tmp_path):
    transport = SequenceTransport([Response(b'{"error":{"code":503,"message":"busy"}}', status=503), Response(event())])
    with relay_at(tmp_path, transport=transport) as relay:
        assert call(relay)[0] == 503
        assert relay.status()["unknown_requests"] == 1
        assert relay.stop_reason is None
        assert call(relay)[0] == 200
        assert relay.status()["spent_usd"] == "0.01"


BYOK_USAGE = {"cost": "0", "is_byok": True, "input_tokens": 13, "output_tokens": 7,
              "cost_details": {"upstream_inference_cost": "0.000096",
                               "upstream_inference_input_cost": "0.000026",
                               "upstream_inference_output_cost": "0.000070"}}


@pytest.mark.parametrize("usage,stop_reason", [
    pytest.param(BYOK_USAGE, None, id="complete"),
    pytest.param({"cost": "0", "is_byok": True}, "unreconciled_provider_cost", id="missing-cost"),
    pytest.param({"cost": "0", "is_byok": True,
                  "cost_details": {"upstream_inference_cost": "bad"}}, "accounting_error", id="malformed-cost"),
    pytest.param({"cost": "0", "is_byok": "true"}, "accounting_error", id="malformed-indicator"),
])
def test_byok_unknown_during_http_settlement_defers_stop_until_handler_finishes(tmp_path, monkeypatch,
                                                                            usage, stop_reason):
    paused, release = threading.Event(), threading.Event()
    with relay_at(tmp_path, transport=Transport(Response(event(usage=usage)))) as relay:
        original = relay.ledger.mark_unknown

        def pause_after_commit(*args, **kwargs):
            receipt = original(*args, **kwargs)
            if not paused.is_set():
                paused.set()
                assert release.wait(5), "BYOK settlement barrier was not released"
            return receipt

        monkeypatch.setattr(relay.ledger, "mark_unknown", pause_after_commit)
        results, errors = [], []

        def request():
            try:
                results.append(call(relay))
            except BaseException as error:
                errors.append(error)

        worker = threading.Thread(target=request)
        worker.start()
        try:
            assert paused.wait(3), "BYOK receipt did not reach the settlement barrier"
            state = relay.status()
            # The real first unknown commit is durable and still holds the full
            # allowance; only its premature native-agent stop is deferred.
            assert state["halted_reason"] == "unreconciled_provider_cost"
            assert state["unknown_requests"] == state["active_requests"] == 1
            assert state["cost_reporting_complete"] is False
            assert Decimal(state["reserved_usd"]) == SETTINGS.budget_usd
            assert Decimal(state["remaining_usd"]) == 0
            assert state["stop_reason"] is None
            assert relay.stop_reason is None
            assert not relay.gate_request()
            with pytest.raises(UnsettledRequest):
                relay.ledger.reserve("0.01", pass_number=1)

            url = urlparse(relay.url)
            connection = HTTPConnection(url.hostname, url.port, timeout=3)
            try:
                connection.request("POST", "/responses", json.dumps(body()),
                                   {"Authorization": "Bearer " + relay.token})
                response = connection.getresponse()
                assert response.status == 409
                response.read()
            finally:
                connection.close()
            assert len(relay.transport.calls) == 1
        finally:
            release.set()
            worker.join(5)
        assert not worker.is_alive()
        assert not errors
        assert results[0][0] == 200
        assert relay.wait_for_idle(0)
        state = relay.status()
        assert state["stop_reason"] == stop_reason
        if stop_reason is None:
            assert state["unknown_requests"] == state["active_requests"] == 0
            assert state["spent_usd"] == "0.000096"
            assert Decimal(state["reserved_usd"]) == 0
            assert relay.gate_request()
        else:
            assert state["unknown_requests"] == state["active_requests"] == 1
            assert state["pass_receipts"][0]["cost_usd"] is None
            assert Decimal(state["reserved_usd"]) == SETTINGS.budget_usd
            assert not relay.gate_request()
            assert call(relay)[0] == 402
            assert len(relay.transport.calls) == 1


def test_byok_stop_deferral_requires_same_request_owner_and_preserves_durable_errors(tmp_path):
    with relay_at(tmp_path) as relay:
        request_id = relay.ledger.reserve(SETTINGS.budget_usd, pass_number=1)
        relay.ledger.mark_dispatched(request_id)
        relay.ledger.mark_unknown(request_id, "Awaiting complete BYOK provider liability", usage={"is_byok": True})
        assert relay.stop_reason == "unreconciled_provider_cost"
        with relay._state:
            relay._active.add("unrelated-request")
        try:
            assert relay.stop_reason == "unreconciled_provider_cost"
            with relay._state:
                relay._active.add(request_id)
            assert relay.stop_reason is None
            relay._stop("accounting_error", "Conflicting or invalid provider accounting evidence")
            assert relay.stop_reason == "accounting_error"
        finally:
            with relay._state:
                relay._active.clear()
        assert relay.stop_reason == "accounting_error"


def test_byok_zero_fee_stream_counts_upstream_once_without_changing_payload(tmp_path):
    wire = event(usage=BYOK_USAGE)
    transport = Transport(Response(wire + wire))
    with relay_at(tmp_path, transport=transport) as relay:
        assert call(relay)[0:2] == (200, wire + wire)
        state = relay.status()
        assert state["spent_usd"] == "0.000096"
        assert state["openrouter_cost_usd"] == "0"
        assert state["byok_upstream_cost_usd"] == "0.000096"
        assert Decimal(state["remaining_usd"]) == SETTINGS.budget_usd - Decimal("0.000096")
        assert state["pass_receipts"][0]["usage"] == {**BYOK_USAGE, "input_tokens": "13", "output_tokens": "7"}
        assert state["billing_basis"] == "openrouter_byok_fee_plus_upstream"
        assert transport.calls[0]["input"] == body()["input"]


@pytest.mark.parametrize("usage", [
    {"cost": "0", "is_byok": True},
    {"cost": "0", "is_byok": True, "cost_details": {"upstream_inference_cost": "bad"}},
    {"cost": "0", "is_byok": True, "upstream_inference_cost": "0.01",
     "cost_details": {"upstream_inference_cost": "0.02"}},
])
def test_byok_missing_or_inconsistent_liability_blocks_spending_across_resume(tmp_path, usage):
    with relay_at(tmp_path, transport=Transport(Response(event(usage=usage)))) as relay:
        call(relay)
        state = relay.status()
        assert state["spent_usd"] == "0"
        assert state["unknown_requests"] == 1
        assert state["active_requests"] == 1
        assert state["pass_receipts"][0]["cost_usd"] is None
        assert state["pass_receipts"][0]["usage"]["is_byok"] is True
        assert not relay.gate_request()
    with relay_at(tmp_path) as resumed:
        resumed.reconcile_pending()
        assert resumed.status()["unknown_requests"] == 1
        assert resumed.status()["active_requests"] == 1
        assert not resumed.gate_request()


def test_byok_final_generation_shape_reconciles_missing_receipt_after_restart(tmp_path):
    with relay_at(tmp_path, transport=Transport(Response(event(usage={"cost": "0", "is_byok": True})))) as relay:
        call(relay)
        assert relay.status()["unknown_requests"] == 1
    generation = {"data": {"id": "gen-one", "total_cost": "0", "usage": 0, "is_byok": True,
                  "upstream_inference_cost": "0.000096", "native_finish_reason": "completed", "finish_reason": "stop"}}
    with relay_at(tmp_path, transport=Transport(generation=generation)) as resumed:
        state = resumed.reconcile_pending()
        assert state["unknown_requests"] == 0
        assert state["spent_usd"] == "0.000096"
        assert state["byok_upstream_cost_usd"] == "0.000096"
        assert state["pass_receipts"][0]["metadata"]["generation_total_cost"] == "0"
        assert resumed.gate_request()
        resumed.reconcile_pending()
        assert resumed.status()["spent_usd"] == "0.000096"


def test_byok_nonstream_charged_failure_counts_fee_and_upstream(tmp_path):
    usage = {**BYOK_USAGE, "cost": "0.000004"}
    raw = json.dumps({"id": "gen-failed", "status": "failed", "usage": usage}).encode()
    with relay_at(tmp_path, transport=Transport(Response(raw, status=500))) as relay:
        assert call(relay, body(stream=False))[0:2] == (500, raw)
        state = relay.status()
        assert state["spent_usd"] == "0.000100"
        assert state["openrouter_cost_usd"] == "0.000004"
        assert state["byok_upstream_cost_usd"] == "0.000096"
        assert state["completed_requests"] == 1


def test_nonbyok_stream_does_not_add_upstream_details_again(tmp_path):
    usage = {**BYOK_USAGE, "cost": "0.000096", "is_byok": False}
    with relay_at(tmp_path, transport=Transport(Response(event(usage=usage)))) as relay:
        call(relay)
        assert relay.status()["spent_usd"] == "0.000096"
        assert relay.status()["byok_upstream_cost_usd"] == "0"


def test_byok_missing_final_generation_upstream_amount_keeps_unknown_blocking(tmp_path):
    with relay_at(tmp_path, transport=Transport(Response(event(cost=None)))) as relay:
        call(relay)
        assert relay.status()["active_requests"] == 0
    generation = {"data": {"id": "gen-one", "total_cost": "0", "usage": 0,
                           "is_byok": True, "finish_reason": "stop"}}
    with relay_at(tmp_path, transport=Transport(generation=generation)) as resumed:
        state = resumed.reconcile_pending()
        assert state["unknown_requests"] == state["active_requests"] == 1
        assert state["pass_receipts"][0]["usage"]["is_byok"] is True
        assert state["pass_receipts"][0]["cost_usd"] is None
        assert not resumed.gate_request()


@pytest.mark.parametrize("indicator", ["true", "false", 0, 1, None])
def test_malformed_byok_indicator_remains_blocking_unknown_on_resume(tmp_path, indicator):
    with relay_at(tmp_path, transport=Transport(Response(event(usage={"cost": "0", "is_byok": indicator})))) as relay:
        call(relay)
        assert relay.status()["unknown_requests"] == relay.status()["active_requests"] == 1
        assert relay.status()["pass_receipts"][0]["cost_usd"] is None
    with relay_at(tmp_path) as resumed:
        resumed.reconcile_pending()
        assert resumed.status()["unknown_requests"] == resumed.status()["active_requests"] == 1
        assert not resumed.gate_request()


def test_prior_byok_receipt_cannot_be_downgraded_by_generation_false(tmp_path):
    with relay_at(tmp_path, transport=Transport(Response(event(usage={"cost": "0", "is_byok": True})))) as relay:
        call(relay)
    generation = {"data": {"id": "gen-one", "total_cost": "0", "is_byok": False, "finish_reason": "stop"}}
    with relay_at(tmp_path, transport=Transport(generation=generation)) as resumed:
        state = resumed.reconcile_pending()
        assert state["unknown_requests"] == state["active_requests"] == 1
        assert state["pass_receipts"][0]["usage"]["is_byok"] is True
        assert not resumed.gate_request()


def test_byok_generation_equivalent_numeric_encodings_reconcile(tmp_path):
    with relay_at(tmp_path, transport=Transport(Response(event(usage={"cost": "0", "is_byok": True})))) as relay:
        call(relay)
    generation = {"data": {"id": "gen-one", "total_cost": Decimal("0"), "is_byok": True,
                           "upstream_inference_cost": Decimal("0.01"), "finish_reason": "stop",
                           "usage": {"cost": "0.000", "is_byok": True,
                                     "upstream_inference_cost": "0.010"}}}
    with relay_at(tmp_path, transport=Transport(generation=generation)) as resumed:
        state = resumed.reconcile_pending()
        assert state["unknown_requests"] == 0
        assert state["spent_usd"] == "0.01"


# Real local HTTP and SQLite boundaries; every upstream below is synthetic.
LOCAL = "local-actual-cost-v1"


@pytest.mark.parametrize("requested,expected", [(None, 128000), (8192, 8192), (200000, 128000)])
def test_shared_explicit_endpoint_output_ceiling_preserves_history(tmp_path, requested, expected):
    payload = body(reasoning={"effort": "high"}, instructions="unchanged", input=["native history"])
    if requested is not None:
        payload["max_output_tokens"] = requested
    with relay_at(tmp_path, budget_policy=LOCAL) as relay:
        assert call(relay, payload)[0] == 200
        sent = relay.transport.calls[0]
        assert sent["max_output_tokens"] == expected
        assert all(sent[field] == payload[field] for field in ("input", "instructions", "reasoning"))
        assert relay.status()["provider_budget_is_per_proof"] is False
        assert relay.status()["strict_dollar_cap_claimed"] is False


@pytest.mark.parametrize("cost", [None, "NaN", "-1", True])
def test_shared_missing_or_invalid_cost_blocks_retry_and_resume(tmp_path, cost):
    with relay_at(tmp_path, transport=Transport(Response(event(cost=cost))), budget_policy=LOCAL) as relay:
        assert call(relay)[0] == 200
        state = relay.status()
        assert state["unknown_requests"] == state["active_requests"] == 1
        assert Decimal(state["reserved_usd"]) == 3 and Decimal(state["spent_usd"]) == 0
        assert not relay.gate_request() and call(relay)[0] == 402
        assert len(relay.transport.calls) == 1
    with relay_at(tmp_path, budget_policy=LOCAL) as resumed:
        state = resumed.reconcile_pending()
        assert state["unknown_requests"] == state["active_requests"] == 1
        assert not resumed.gate_request() and resumed.transport.calls == []


@pytest.mark.parametrize("generation,settled", [
    ({"id": "gen-one", "total_cost": "0"}, False),
    ({"id": "wrong-generation", "status": "completed", "total_cost": "0"}, False),
    ({"id": "gen-one", "status": "completed", "total_cost": "0.125"}, True),
])
def test_shared_recovery_requires_exact_final_generation(tmp_path, generation, settled):
    with relay_at(tmp_path, transport=Transport(Response(event(cost=None))), budget_policy=LOCAL) as relay:
        call(relay)
    transport = Transport(generation={"data": generation})
    with relay_at(tmp_path, transport=transport, budget_policy=LOCAL) as resumed:
        state = resumed.reconcile_pending()
        assert state["active_requests"] == int(not settled)
        assert resumed.gate_request() is settled
        assert Decimal(state["spent_usd"]) == (Decimal("0.125") if settled else 0)
        assert transport.calls == [] and transport.lookups == ["gen-one"]


@pytest.mark.parametrize("failure", ["http_error", "truncated_stream", "no_generation", "transport_error"])
def test_shared_failed_dispatch_preserves_unknown_allowance(tmp_path, failure):
    if failure == "http_error":
        transport = Transport(Response(b'{"error":{"code":503}}', status=503))
    elif failure == "truncated_stream":
        transport = Transport(Response(chunks=[event(cost=None), OSError("synthetic disconnect")]))
    elif failure == "no_generation":
        transport = Transport(Response(event(cost=None, generation=None)))
    else:
        class FailedTransport(Transport):
            @contextmanager
            def open_response(self, payload, **kwargs):
                self.calls.append(payload)
                raise OSError("synthetic dispatch ambiguity")
                yield
        transport = FailedTransport()
    with relay_at(tmp_path, transport=transport, budget_policy=LOCAL) as relay:
        call(relay)
        assert not relay.gate_request() and relay.status()["active_requests"] == 1
    with relay_at(tmp_path, budget_policy=LOCAL) as resumed:
        state = resumed.reconcile_pending()
        assert state["unknown_requests"] == state["active_requests"] == 1
        assert Decimal(state["reserved_usd"]) == 3 and resumed.transport.calls == []


@pytest.mark.parametrize("first_cost", ["1.5", None])
def test_concurrent_shared_key_proofs_never_cross_attribute_cost_or_unknowns(tmp_path, first_cost):
    from concurrent.futures import ThreadPoolExecutor
    barrier = threading.Barrier(2)
    class ConcurrentTransport(Transport):
        @contextmanager
        def open_response(self, payload, *, api_key, timeout):
            assert api_key == KEY
            self.calls.append(payload)
            barrier.wait(timeout=3)
            yield self.response
    a = ConcurrentTransport(Response(event(cost=first_cost, generation="gen-a")))
    b = ConcurrentTransport(Response(event(cost="2", generation="gen-b")))
    with relay_at(tmp_path / "a", proof_id="run/a", transport=a, budget_policy=LOCAL) as left, \
         relay_at(tmp_path / "b", proof_id="run/b", transport=b, budget_policy=LOCAL) as right:
        with ThreadPoolExecutor(max_workers=2) as pool:
            results = [pool.submit(call, relay) for relay in (left, right)]
            assert [result.result()[0] for result in results] == [200, 200]
        ls, rs = left.status(), right.status()
        assert Decimal(ls["spent_usd"]) == (Decimal(first_cost) if first_cost else 0)
        assert Decimal(rs["spent_usd"]) == 2 and Decimal(rs["remaining_usd"]) == 1
        assert ls["active_requests"] == int(first_cost is None) and rs["active_requests"] == 0
        assert left.gate_request() is (first_cost is not None)
        assert right.gate_request()
        right.transport = Transport(Response(event(cost="1", generation="gen-b-next")))
        assert call(right)[0] == 200 and not right.gate_request()
        assert len(left.ledger.requests()) == 1 and len(right.ledger.requests()) == 2
        assert KEY not in json.dumps([left.status(), right.status()])


def test_shared_native_disconnect_still_drains_provider_bill(tmp_path):
    reading, release = threading.Event(), threading.Event()
    class DelayedResponse(Response):
        def __init__(self):
            self.reads = 0
        def read(self, size=-1):
            self.reads += 1
            if self.reads == 1:
                return b": upstream activity\n\n"
            if self.reads == 2:
                reading.set()
                assert release.wait(3)
                return event(cost="0.75")
            return b""
    with relay_at(tmp_path, transport=Transport(DelayedResponse()), budget_policy=LOCAL) as relay:
        url = urlparse(relay.url)
        connection = HTTPConnection(url.hostname, url.port, timeout=5)
        connection.request("POST", "/responses", json.dumps(body()), {"Authorization": "Bearer " + relay.token})
        response = connection.getresponse()
        assert reading.wait(3)
        response.close()
        connection.close()
        release.set()
        assert relay.wait_for_idle(3)
        assert relay.status()["unknown_requests"] == 0
        assert Decimal(relay.status()["spent_usd"]) == Decimal("0.75")


def test_shared_process_loss_preserves_dispatched_hold(tmp_path):
    with relay_at(tmp_path, budget_policy=LOCAL) as relay:
        request_id = relay.ledger.reserve("3", pass_number=1)
        relay.ledger.mark_dispatched(request_id)
    with relay_at(tmp_path, budget_policy=LOCAL) as resumed:
        state = resumed.reconcile_pending()
        assert state["active_request_ids"] == state["unknown_request_ids"] == [request_id]
        assert Decimal(state["remaining_usd"]) == 0 and resumed.transport.calls == []


def test_shared_policy_cannot_switch_or_adopt_historical_ledger(tmp_path):
    with relay_at(tmp_path / "shared", budget_policy=LOCAL):
        pass
    with pytest.raises(ValueError, match="policy is immutable"):
        OpenRouterRelay(tmp_path / "shared", settings=SETTINGS)
    from harness.openrouter import OpenRouterLedger
    OpenRouterLedger(tmp_path / "historical/openrouter.sqlite", proof_id="run/proof", model="test/model")
    with pytest.raises(ValueError, match="no frozen local budget policy"):
        OpenRouterRelay(tmp_path / "historical", settings=SETTINGS, budget_policy=LOCAL)


def test_shared_known_final_overrun_is_recorded_and_resume_cannot_spend(tmp_path):
    transport = SequenceTransport([Response(event(cost="2.99")), Response(event(cost="0.02", generation="gen-last"))])
    with relay_at(tmp_path, transport=transport, budget_policy=LOCAL) as relay:
        assert call(relay)[0] == call(relay)[0] == 200
        state = relay.status()
        assert Decimal(state["spent_usd"]) == Decimal("3.01")
        assert Decimal(state["over_budget_usd"]) == Decimal("0.01")
        assert state["strict_dollar_cap_claimed"] is False and relay.stop_reason == "budget_reached"
    with relay_at(tmp_path, budget_policy=LOCAL) as resumed:
        resumed.reconcile_pending()
        assert call(resumed)[0] == 402 and resumed.transport.calls == []


def test_shared_provider_key_limit_is_account_stop_not_proof_charge(tmp_path):
    raw = json.dumps({"error": {"code": 402, "metadata": {"limit_source": "openrouter_key_limit"}}}).encode()
    with relay_at(tmp_path, transport=Transport(Response(raw, status=402)), budget_policy=LOCAL) as relay:
        assert call(relay)[0] == 402 and relay.stop_reason == "account_error"
        assert Decimal(relay.status()["spent_usd"]) == 0 and relay.status()["unknown_requests"] == 0


def test_shared_byok_settles_fee_plus_upstream_once(tmp_path):
    usage = {"cost": "0.001", "is_byok": True, "cost_details": {"upstream_inference_cost": "0.02"}}
    wire = b"data: " + json.dumps({"type": "response.completed", "response": {
        "id": "gen-byok", "status": "completed", "usage": usage}}).encode() + b"\n\n"
    with relay_at(tmp_path, transport=Transport(Response(wire)), budget_policy=LOCAL) as relay:
        assert call(relay)[0] == 200
        state = relay.status()
        assert Decimal(state["spent_usd"]) == Decimal("0.021")
        assert Decimal(state["openrouter_cost_usd"]) == Decimal("0.001")
        assert Decimal(state["byok_upstream_cost_usd"]) == Decimal("0.02")


def test_shared_credential_rotation_is_rejected_before_another_dispatch(tmp_path):
    with relay_at(tmp_path, budget_policy=LOCAL) as relay:
        assert call(relay)[0] == 200
        relay.credential_provider = lambda: "different-synthetic-credential"
        assert call(relay)[0] == 503
        assert len(relay.transport.calls) == 1 and relay.status()["unknown_requests"] == 0
