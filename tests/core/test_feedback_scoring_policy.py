from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
import json
from pathlib import Path
import threading
import tomllib

import pytest

from lean_tools import arena_workflow as arena, broker_client, candidate_batches, capsule
from lean_tools import feedback_workflow as feedback, goal_retrieval
from lean_tools import persistent_quick_workflow as persistent
from lean_tools.measurement_policy import (
    ARENA_POLICY, LEGACY_POLICY, SCORING_POLICY_ENV,
    resolve_scoring_policy, scoring_policy_context,
)
from lean_tools.scoring import (
    IncumbentMetricsError, OriginalDenominatorScorePolicy,
    incumbent_score_delta, validate_incumbent_metrics,
)


def make_service(root, policy=None, **options):
    root.mkdir(parents=True, exist_ok=True)
    row = {"name": "demo", "header": "", "contexts": [],
           "signature": "theorem demo : True",
           "src": "theorem demo : True := by exact True.intro", "proof_length": 40}
    task = root / "Task.json"
    task.write_text(json.dumps({"schema_version": 1, "row": row}))
    candidate = root / "Candidate.lean"
    candidate.write_text(arena.render_candidate_scaffold(row))
    settings = {"task": str(task), "candidate": str(candidate),
                "project_root": str(root), **options}
    if policy is not None:
        settings["scoring_policy"] = policy
    return feedback.Feedback(settings), settings


def measured(task, candidate, project, **kwargs):
    policy = resolve_scoring_policy()
    tokens = arena.candidate_token_count(task, candidate)
    exact = not kwargs.get("quick", False)
    return arena.Evaluation(
        task_id="demo", candidate_path=str(candidate), valid=True,
        compile_seconds=0.01, axiom_audit_seconds=0.01 if exact else None,
        axioms=[] if exact else None, original_local_tokens=40,
        candidate_local_tokens=tokens, local_token_reduction_pct=0,
        official_original_tokens=40, published_reference_heartbeat=100,
        local_reference_heartbeat=None, environment_fingerprint="same-environment",
        heartbeat=5 if exact else None, heartbeat_reduction_pct=95 if exact else None,
        scoring_policy=policy, candidate_token_offset=int(policy == ARENA_POLICY),
    )


def test_missing_feedback_config_is_frozen_legacy_even_in_arena_process(tmp_path, monkeypatch):
    monkeypatch.setenv(SCORING_POLICY_ENV, ARENA_POLICY)
    service, source_settings = make_service(tmp_path)
    source_settings["scoring_policy"] = ARENA_POLICY
    assert service.scoring_policy == LEGACY_POLICY
    assert service.settings["scoring_policy"] == LEGACY_POLICY
    with pytest.raises(AttributeError):
        service.scoring_policy = ARENA_POLICY
    config = feedback.configure_capsule(tmp_path, tmp_path)
    assert "scoring_policy" not in json.loads(config.read_text())
    config = feedback.configure_capsule(tmp_path, tmp_path, scoring_policy=ARENA_POLICY)
    assert json.loads(config.read_text())["scoring_policy"] == ARENA_POLICY


@pytest.mark.parametrize("policy", [None, "", "arena-v0", False])
def test_feedback_rejects_invalid_explicit_config_policy(tmp_path, policy):
    service, settings = make_service(tmp_path)
    with pytest.raises((ValueError, arena.WorkflowError)):
        feedback.Feedback({**settings, "scoring_policy": policy})
    with pytest.raises((ValueError, arena.WorkflowError)):
        feedback.configure_capsule(tmp_path, tmp_path, scoring_policy=policy)


@pytest.mark.parametrize("policy", [LEGACY_POLICY, ARENA_POLICY])
def test_native_and_shell_commands_use_frozen_policy_over_ambient(tmp_path, monkeypatch, policy):
    monkeypatch.setenv(SCORING_POLICY_ENV, ARENA_POLICY if policy == LEGACY_POLICY else LEGACY_POLICY)
    feedback.configure_capsule(tmp_path, tmp_path, scoring_policy=policy)
    parsed = tomllib.loads("\n".join(feedback.codex_config_args(tmp_path)[1::2]))
    assert parsed["shell_environment_policy"]["set"][SCORING_POLICY_ENV] == policy
    server = parsed["mcp_servers"]["lean_feedback"]
    assert server["env"][SCORING_POLICY_ENV] == policy
    assert SCORING_POLICY_ENV not in server["env_vars"]
    quick, exact = capsule.evaluator_commands(tmp_path, Path(arena.__file__), tmp_path)
    assert quick.startswith(f"{SCORING_POLICY_ENV}={policy} ")
    assert exact.startswith(f"{SCORING_POLICY_ENV}={policy} ")


def test_two_feedback_instances_keep_threaded_counts_and_nested_calls_isolated(tmp_path, monkeypatch):
    services = [make_service(tmp_path / name, policy)[0]
                for name, policy in (("legacy", LEGACY_POLICY), ("arena", ARENA_POLICY))]
    barrier = threading.Barrier(2)

    def evaluate(*args, **kwargs):
        before = resolve_scoring_policy()
        barrier.wait(timeout=5)
        result = measured(*args, **kwargs)
        assert resolve_scoring_policy() == before
        return result

    monkeypatch.setattr(arena, "evaluate_candidate", evaluate)
    monkeypatch.setattr(arena, "evaluation_cache_root", lambda: None)
    monkeypatch.setattr(arena, "record_event", lambda *_args, **_kwargs: None)
    monkeypatch.setattr(candidate_batches, "_run_candidates",
                        lambda *_args, **_kwargs: {"policy": resolve_scoring_policy()})

    def run(service):
        outer = ARENA_POLICY if service.scoring_policy == LEGACY_POLICY else LEGACY_POLICY
        with scoring_policy_context(outer):
            report = service.check({})
            assert resolve_scoring_policy() == outer
            assert candidate_batches.compare_candidates(service, {}) == {"policy": service.scoring_policy}
            assert resolve_scoring_policy() == outer
            with pytest.raises(arena.WorkflowError):
                service.check({"mode": "unknown"})
            assert resolve_scoring_policy() == outer
            return report

    with ThreadPoolExecutor(max_workers=2) as executor:
        reports = list(executor.map(run, services))
    assert all(report["valid"] is True for report in reports)
    assert reports[1]["tokens"] == reports[0]["tokens"] + 1
    for service, report in zip(services, reports, strict=True):
        saved = json.loads(Path(report["details_path"]).read_text())
        assert saved["evaluation"]["scoring_policy"] == service.scoring_policy


def test_direct_snapshot_cache_lookup_is_bound_and_policy_separated(tmp_path, monkeypatch):
    services = [make_service(tmp_path / policy, policy)[0] for policy in (LEGACY_POLICY, ARENA_POLICY)]
    lookups = []
    monkeypatch.setattr(arena, "evaluate_candidate", measured)
    monkeypatch.setattr(arena, "evaluation_cache_root", lambda: tmp_path / "cache")
    monkeypatch.setattr(arena, "cached_evaluation",
                        lambda path, *_args, **_kwargs: lookups.append((path, resolve_scoring_policy())))
    for service in services:
        snapshot = service.prepare_snapshot({})
        with scoring_policy_context(ARENA_POLICY if service.scoring_policy == LEGACY_POLICY else LEGACY_POLICY):
            service.evaluate_snapshot(snapshot, "quick", {}, {})
    assert [policy for _path, policy in lookups] == [LEGACY_POLICY, ARENA_POLICY]
    assert lookups[0][0] != lookups[1][0]


def test_checkpoint_restore_rejects_other_policy_even_for_same_source(tmp_path, monkeypatch):
    legacy, _settings = make_service(tmp_path, LEGACY_POLICY)
    other = feedback.Feedback({**legacy.settings, "scoring_policy": ARENA_POLICY})
    monkeypatch.setattr(arena, "evaluate_candidate", measured)
    monkeypatch.setattr(arena, "evaluation_cache_root", lambda: None)
    monkeypatch.setattr(arena, "record_event", lambda *_args, **_kwargs: None)
    checked = legacy.check({})
    legacy.resolve_checkpoint(checked["checkpoint_id"])
    with pytest.raises(arena.WorkflowError, match="scoring policy"):
        other.resolve_checkpoint(checked["checkpoint_id"])


def test_direct_score_and_comparison_use_same_policy_for_pruning_and_scoring(tmp_path, monkeypatch):
    service, _settings = make_service(tmp_path, ARENA_POLICY, candidate_batches=True,
        original_tokens=100, original_heartbeats=100, compatibility_roots=[], incumbent_score=99)
    seen = []

    def evaluate(*args, **kwargs):
        seen.append(resolve_scoring_policy())
        return measured(*args, **kwargs)

    monkeypatch.setattr(arena, "evaluate_candidate", evaluate)
    monkeypatch.setattr(arena, "record_event", lambda *_args, **_kwargs: None)
    request = {"expected_sha256": arena.sha256_file(service.candidate)}
    with scoring_policy_context(LEGACY_POLICY):
        scored = candidate_batches.score_candidate(service, request)
        compared = candidate_batches.compare_candidates(service, {
            **request, "alternatives": [{"label": "one", "body": "by exact True.intro"},
                                        {"label": "two", "body": "by trivial"}]})
        assert resolve_scoring_policy() == LEGACY_POLICY
    policy = OriginalDenominatorScorePolicy(100, 100, ARENA_POLICY)
    assert scored["score"] == policy.score(tokens=scored["tokens"], heartbeats=5, compatibility_pct=100)
    assert all(item["status"] == "valid_pruned" for item in compared["alternatives"])
    assert seen and set(seen) == {ARENA_POLICY}


def test_broker_payload_freezes_context_and_checks_response_policy():
    with scoring_policy_context(ARENA_POLICY):
        request = broker_client.SourceRequest("source", 5)
    with scoring_policy_context(LEGACY_POLICY):
        assert request.payload("token", "compile")["scoring_policy"] == ARENA_POLICY
    response = {"ok": True, "valid": True, "diagnostics": [],
                "source_sha256": request.source_sha256, "document_version": 1}
    with pytest.raises(broker_client.BrokerClientError) as error:
        broker_client.validate_response(response, request)
    assert error.value.code == "scoring_policy_mismatch"
    broker_client.validate_response({**response, "scoring_policy": ARENA_POLICY}, request)
    assert "scoring_policy" not in broker_client.SourceRequest(
        "source", 5, scoring_policy=LEGACY_POLICY).payload("token", "compile")


def test_shared_warm_broker_binds_each_feedback_request_and_restores_failures(tmp_path, monkeypatch):
    monkeypatch.setenv(SCORING_POLICY_ENV, LEGACY_POLICY)
    broker = persistent.PersistentQuickBroker(tmp_path, tmp_path / "broker", "original", timeout_seconds=5)
    seen = []

    def validate(source, **_kwargs):
        seen.append(resolve_scoring_policy())
        if source == "failure":
            raise persistent.PersistentQuickError("synthetic failure")
        return {"ok": True, "valid": True, "diagnostics": [], "document_version": 1,
                "source_sha256": arena.sha256_bytes(source.encode())}

    monkeypatch.setattr(broker, "_validate", validate)
    monkeypatch.setattr(goal_retrieval, "retrieve_lemmas",
        lambda _owner, request: persistent.feedback_request(request.get("source", "shared source"), 5))
    broker.start()
    try:
        env = broker.environment()
        assert env[SCORING_POLICY_ENV] == LEGACY_POLICY
        for key, value in env.items():
            monkeypatch.setenv(key, value)
        monkeypatch.setenv(SCORING_POLICY_ENV, ARENA_POLICY)
        services = [make_service(tmp_path / policy, policy, goal_retrieval=True)[0]
                    for policy in (ARENA_POLICY, LEGACY_POLICY)]
        for service in services:
            result = service.call("retrieve_lemmas", {})
            assert result.get("scoring_policy", LEGACY_POLICY) == service.scoring_policy
        with pytest.raises(persistent.PersistentQuickError, match="synthetic failure"):
            services[0].call("retrieve_lemmas", {"source": "failure"})
        services[1].call("retrieve_lemmas", {})
        assert resolve_scoring_policy() == ARENA_POLICY
    finally:
        broker.close()
    assert seen == [ARENA_POLICY, LEGACY_POLICY, ARENA_POLICY, LEGACY_POLICY]


def test_incumbent_receipts_cannot_cross_policy_with_identical_denominators():
    legacy = OriginalDenominatorScorePolicy(100, 100)
    arena_policy = replace(legacy, scoring_policy=ARENA_POLICY)
    receipt = {"source_sha256": "a" * 64, "tokens": 10, "heartbeats": 10,
               "compatibility_pct": 100, "score": 93.3333,
               "original_tokens": 100, "original_heartbeats": 100}
    validate_incumbent_metrics(legacy, receipt, incumbent_source_sha256="a" * 64)
    with pytest.raises(IncumbentMetricsError) as error:
        validate_incumbent_metrics(arena_policy, receipt, incumbent_source_sha256="a" * 64)
    assert error.value.reason == "scoring_policy_mismatch"
    assert incumbent_score_delta(arena_policy, tokens=10, heartbeats=10, compatibility_pct=100,
        incumbent_score=receipt["score"], incumbent_metrics=receipt, incumbent_source_sha256="a" * 64) == {
            "status": "unavailable", "reason": "scoring_policy_mismatch", "score": None}
    validate_incumbent_metrics(arena_policy, {**receipt, "scoring_policy": ARENA_POLICY},
                               incumbent_source_sha256="a" * 64)
