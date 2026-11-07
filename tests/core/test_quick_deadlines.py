"""Fast deadline/ownership regression tests; all Lean processes are fake."""
from __future__ import annotations

from contextlib import contextmanager
import json
import socket
import threading
from types import SimpleNamespace

import pytest

from lean_tools import arena_workflow as arena, broker_client, check_budget
from lean_tools import feedback_workflow as feedback, persistent_quick_workflow as persistent


@pytest.fixture
def service(tmp_path):
    row = {"name": "demo", "header": "import Mathlib\n\n", "contexts": [],
           "signature": "theorem demo : True", "src": "theorem demo : True := by trivial", "proof_length": 2}
    task = tmp_path / "Task.json"
    task.write_text(json.dumps({"schema_version": 1, "row": row}))
    candidate = tmp_path / "Candidate.lean"
    candidate.write_text(arena.render_candidate_scaffold(row))
    return feedback.Feedback({"task": str(task), "candidate": str(candidate), "project_root": str(tmp_path)})


@pytest.mark.parametrize("code", ["operation_timeout", "queue_timeout", "transport_timeout", "transport_failed", "source_mismatch"])
def test_warm_failure_does_not_replay_uncertain_work(service, monkeypatch, code):
    monkeypatch.setattr(arena, "persistent_quick_matches_project", lambda _: True)
    evidence = {"ok": False, "valid": None, "failure_kind": code,
                "failure_phase": "change_document", "cleanup_complete": True}
    failure = arena.PersistentQuickFailure(broker_client.BrokerClientError(code, "bounded failure", result=evidence))
    monkeypatch.setattr(arena, "persistent_quick_request", lambda *_: (_ for _ in ()).throw(failure))
    monkeypatch.setattr(arena, "run_lean", lambda *_a, **_k: pytest.fail("uncertain warm work replayed cold"))
    monkeypatch.setattr(arena, "measurement_environment_fingerprint", lambda *_a, **_k: "a" * 64)
    result = service.call("edit_check", {})
    assert result["status"] == ("timeout" if code.endswith("timeout") else "check_failed")
    assert result["valid"] is None and not result.get("checkpoint")
    assert result["failure_kind"] == code
    assert not list((service.root / "valid-candidates").glob("*.lean"))


def test_predispatch_fallback_spends_only_remaining_quick_allowance(service, monkeypatch):
    now = [100.0]
    monkeypatch.setattr(check_budget.time, "monotonic", lambda: now[0])
    monkeypatch.setattr(arena, "persistent_quick_matches_project", lambda _: True)
    observed = []

    def unavailable(_source, timeout):
        assert timeout <= 60
        now[0] += 12
        raise arena.PersistentQuickFailure(broker_client.BrokerClientError("transport_failed", "not connected", retryable=True))

    def cold(_source, _project, _timeout, **_kwargs):
        observed.append(check_budget.remaining(_timeout))
        return arena.LeanRun(["fake-lean"], 0, 0.1, "")

    monkeypatch.setattr(arena, "persistent_quick_request", unavailable)
    monkeypatch.setattr(arena, "run_lean", cold)
    arena.evaluate_candidate_fresh(service.task, service.candidate, service.project, quick=True,
                                   environment_fingerprint="a" * 64)
    assert observed == [48]
    assert check_budget.current() is None


def test_cache_lock_and_cold_work_share_one_deadline(service, monkeypatch):
    now = [100.0]
    monkeypatch.setattr(check_budget.time, "monotonic", lambda: now[0])
    monkeypatch.setattr(arena, "measurement_environment_fingerprint", lambda *_a, **_k: "a" * 64)
    monkeypatch.setattr(arena, "evaluation_cache_root", lambda: service.root / "cache")
    monkeypatch.setattr(arena, "persistent_quick_matches_project", lambda _: False)

    @contextmanager
    def lock(*_args, **_kwargs):
        now[0] += 50
        yield 50

    def cold(*_args, **_kwargs):
        assert check_budget.remaining() == 10
        now[0] += 11
        check_budget.remaining()

    monkeypatch.setattr(arena, "exclusive_file_lock", lock)
    monkeypatch.setattr(arena, "run_lean", cold)
    monkeypatch.setattr(arena, "store_cached_evaluation", lambda *_a, **_k: pytest.fail("timeout entered success cache"))
    with pytest.raises(check_budget.DeadlineExpired):
        arena.evaluate_candidate(service.task, service.candidate, service.project, quick=True)
    assert check_budget.current() is None


def test_queued_expired_request_never_edits_source_and_has_durable_stage(service, monkeypatch):
    now = [100.0]
    monkeypatch.setattr(check_budget.time, "monotonic", lambda: now[0])
    before = service.candidate.read_bytes()
    arguments = {"body": "by constructor", "timeout_seconds": 1}
    admission = service.request_journal.admit("edit_check", arguments, identity="slow-queue", budget_seconds=1)
    now[0] += 2
    with service.request_journal.rpc_request("slow-queue", admission=admission):
        result = service.call("edit_check", arguments)
    assert result["status"] == "timeout" and result["valid"] is None
    assert service.candidate.read_bytes() == before
    receipt = json.loads((service.request_journal.directory / (admission.request_id + ".json")).read_text())
    assert receipt["stage"] == "source_lock" and receipt["remaining_seconds_at_stage_start"] == 0
    assert receipt["timeout_scope"] == "quick_request" and receipt["deadline_unix"]
    assert receipt["phase"] == "completed"


def test_explicit_quick_escalation_does_not_leak_to_exact_or_next_call(service, monkeypatch):
    observed = []

    def check(request):
        budget = check_budget.current()
        observed.append(None if budget is None else budget.seconds)
        return {"status": "probe", "valid": None}

    monkeypatch.setattr(service, "_check", check)
    service.check({})
    service.check({"timeout_seconds": 600})
    service.check({"mode": "exact"})
    service.check({})
    assert observed == [60, 600, None, 60]
    assert check_budget.current() is None
    with pytest.raises(arena.WorkflowError):
        service.check({"timeout_seconds": 601})
    with pytest.raises(arena.WorkflowError):
        service.check({"timeout_seconds": 1800})  # trusted host allowance is not agent-facing
    with pytest.raises(arena.WorkflowError):
        service.check({"mode": "exact", "timeout_seconds": 60})


def test_broker_failure_metadata_survives_both_facades(monkeypatch):
    request = broker_client.SourceRequest("theorem demo : True := by trivial", 1)
    reply = {"ok": False, "valid": None, "source_sha256": request.source_sha256,
             "failure_kind": "operation_timeout", "failure_phase": "change_document", "cleanup_complete": True}
    with pytest.raises(broker_client.BrokerClientError) as caught:
        broker_client.validate_response(reply, request)
    monkeypatch.setattr(broker_client, "request_to", lambda *_a, **_k: (_ for _ in ()).throw(caught.value))
    with pytest.raises(arena.PersistentQuickFailure) as arena_error:
        arena.persistent_quick_request_to("127.0.0.1:1", "fake", request.source, 1)
    assert arena_error.value.code == "operation_timeout" and arena_error.value.result == reply
    monkeypatch.setenv(broker_client.ENDPOINT_ENV, "127.0.0.1:1")
    monkeypatch.setenv(broker_client.TOKEN_ENV, "fake")
    with pytest.raises(persistent.PersistentQuickError) as persistent_error:
        persistent.feedback_request(request.source, 1)
    assert persistent_error.value.code == "operation_timeout" and persistent_error.value.result == reply


def test_wire_request_deadline_overrides_compile_scope_broker_queue(service, monkeypatch):
    monkeypatch.setenv("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE", "compile")
    broker = persistent.PersistentQuickBroker(service.project, service.root / "broker", "original", timeout_seconds=600)
    broker.session_lock.acquire()
    broker.start()
    try:
        with check_budget.scope(0.04):
            with pytest.raises(broker_client.BrokerClientError) as caught:
                broker_client.request_to(broker.environment()[broker_client.ENDPOINT_ENV], broker.token,
                                        broker_client.SourceRequest("frozen source", 600), timeout_scope="compile")
        assert caught.value.code == "queue_timeout"
        assert caught.value.result["failure_phase"] == "document_lock"
        assert broker.session is None
    finally:
        broker.session_lock.release()
        broker.close()


def test_operation_timeout_retires_owned_session_before_failure_ack(service, monkeypatch):
    events = []

    class Session:
        def __init__(self, *_args, **_kwargs):
            self.version = 0
            self.process = None
        def start(self):
            events.append("start")
        def open_document(self, _source):
            events.append("operation_timeout")
            raise persistent.PersistentQuickError("expired", code="operation_timeout")
        def tree_working_set_bytes(self):
            return None
        def close(self):
            events.append("retired")

    monkeypatch.setattr(persistent, "LeanLspSession", Session)
    broker = persistent.PersistentQuickBroker(service.project, service.root / "broker", "original", timeout_seconds=600)
    with pytest.raises(persistent.PersistentQuickError) as caught:
        broker._validate("frozen source", timeout_seconds=1, request_scope=True)
    events.append("failure_ack")
    assert events == ["start", "operation_timeout", "retired", "failure_ack"]
    assert caught.value.code == "operation_timeout" and caught.value.result["cleanup_complete"] is True
    assert broker.session is None


@pytest.mark.parametrize("scope", ["request", "compile"])
def test_blocked_lsp_input_has_watchdog_in_both_scopes(service, monkeypatch, scope):
    monkeypatch.setenv("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE", scope)
    stopped = threading.Event()
    class Input:
        def write(self, _data):
            assert stopped.wait(1), "watchdog did not terminate owned process"
            raise BrokenPipeError()
    process = SimpleNamespace(stdin=Input())
    monkeypatch.setattr(arena, "terminate_process_tree", lambda owned: stopped.set() if owned is process else pytest.fail("wrong process"))
    session = persistent.LeanLspSession(service.project, service.root / "doc.lean", service.root / "stderr", 0.02)
    session.process = process
    with pytest.raises(persistent.PersistentQuickError) as caught:
        session._send({"method": "probe"})
    assert caught.value.code == "operation_timeout" and stopped.is_set()


def test_after_send_transport_timeout_is_typed_and_never_retryable(monkeypatch):
    class Connection:
        def __enter__(self): return self
        def __exit__(self, *_args): pass
        def settimeout(self, _value): pass
        def sendall(self, _value): pass
        def recv(self, _size): raise socket.timeout("reply deadline")
    monkeypatch.setattr(broker_client.socket, "create_connection", lambda *_a, **_k: Connection())
    with check_budget.scope(1), pytest.raises(broker_client.BrokerClientError) as caught:
        broker_client.request_to("127.0.0.1:1", "fake", broker_client.SourceRequest("source", 1), timeout_scope="compile")
    assert caught.value.code == "transport_timeout" and caught.value.retryable is False
