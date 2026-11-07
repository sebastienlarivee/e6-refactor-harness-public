from __future__ import annotations

import pytest

from lean_tools.scoring import (
    IncumbentMetricsError,
    OriginalDenominatorScorePolicy,
    contest_score_components,
    incumbent_score_delta,
    score_breakdown,
    validate_incumbent_metrics,
)


SOURCE = "a" * 64
POLICY = OriginalDenominatorScorePolicy(100, 100)


def receipt(*, tokens=20, heartbeats=10, compatibility_pct=100.0):
    return {"source_sha256": SOURCE, "tokens": tokens, "heartbeats": heartbeats,
            "compatibility_pct": compatibility_pct,
            "score": POLICY.score(tokens=tokens, heartbeats=heartbeats, compatibility_pct=compatibility_pct),
            "original_tokens": 100, "original_heartbeats": 100}


def delta(*, tokens=10, heartbeats=20, compatibility_pct=100.0, metrics=None, **kwargs):
    return incumbent_score_delta(POLICY, tokens=tokens, heartbeats=heartbeats,
        compatibility_pct=compatibility_pct, incumbent_metrics=receipt() if metrics is None else metrics,
        incumbent_source_sha256=SOURCE, **kwargs)


def reconciles(breakdown):
    assert round(sum(breakdown["score_points"].values()) + breakdown["rounding_adjustment"], 4) == breakdown["score"]


def test_breakdown_reuses_component_and_scalar_rounding():
    policy = OriginalDenominatorScorePolicy(37, 91)
    measured = contest_score_components(37, 91, 5, 27, 100 / 3)
    breakdown = score_breakdown(policy, tokens=5, heartbeats=27, compatibility_pct=100 / 3)
    for key in ("length_reduction_pct", "heartbeat_reduction_pct", "compatibility_pct"):
        assert breakdown[key] == measured[key]
    assert breakdown["score"] == measured["official_score"] == policy.score(
        tokens=5, heartbeats=27, compatibility_pct=100 / 3)
    reconciles(breakdown)


def test_rounding_residual_is_explicit_for_score_and_delta():
    breakdown = score_breakdown(POLICY, tokens=0, heartbeats=0, compatibility_pct=100)
    assert breakdown["score"] == 100
    assert breakdown["score_points"] == {"length": 33.3333, "heartbeats": 33.3333, "compatibility": 33.3333}
    assert breakdown["rounding_adjustment"] == 0.0001
    change = delta(tokens=0, heartbeats=0, metrics=receipt(tokens=100, heartbeats=100, compatibility_pct=0))
    assert change["score"] == 100 and change["rounding_adjustment"] == 0.0001
    reconciles(breakdown)
    reconciles(change)


def test_shortening_can_have_a_negative_total_delta():
    change = delta(tokens=10, heartbeats=80)
    assert change["status"] == "complete"
    assert change["incumbent_source_sha256"] == SOURCE
    assert change["tokens"] == -10 and change["heartbeats"] == 70
    assert change["length_reduction_pct"] == 10 and change["heartbeat_reduction_pct"] == -70
    assert change["score_points"] == {"length": 3.3333, "heartbeats": -23.3333, "compatibility": 0.0}
    assert change["score"] == -20
    reconciles(change)


def test_compatibility_loss_can_outweigh_both_local_improvements():
    change = delta(tokens=10, heartbeats=10, compatibility_pct=50,
                   metrics=receipt(tokens=20, heartbeats=20))
    assert change["tokens"] == change["heartbeats"] == -10
    assert change["compatibility_pct"] == -50
    assert change["score_points"]["compatibility"] == -16.6667
    assert change["score"] == -10
    reconciles(change)


@pytest.mark.parametrize("metrics, reason", [
    (None, "missing_metrics"), ({}, "missing_metrics"),
    ({**receipt(), "source_sha256": "b" * 64}, "source_mismatch"),
    ({**receipt(), "original_tokens": 101}, "denominator_mismatch"),
    ({**receipt(), "original_heartbeats": True}, "denominator_mismatch"),
    ({**receipt(), "heartbeats": None}, "invalid_metrics"),
    ({**receipt(), "tokens": -1}, "invalid_metrics"),
    ({**receipt(), "score": float("nan")}, "score_mismatch"),
    ({**receipt(), "score": 91}, "score_mismatch"),
])
def test_missing_or_rejected_receipt_exposes_only_the_separate_scalar(metrics, reason):
    change = incumbent_score_delta(POLICY, tokens=10, heartbeats=20, compatibility_pct=100,
        incumbent_score=91, incumbent_metrics=metrics, incumbent_source_sha256=SOURCE)
    assert change == {"status": "scalar_only", "reason": reason, "score": -1.0}


def test_missing_scalar_and_metrics_are_unavailable_instead_of_zero():
    assert incumbent_score_delta(POLICY, tokens=10, heartbeats=20, compatibility_pct=100) == {
        "status": "unavailable", "reason": "missing_metrics", "score": None}


def test_receipt_requires_an_independent_source_binding():
    with pytest.raises(IncumbentMetricsError, match="independent incumbent") as error:
        validate_incumbent_metrics(POLICY, receipt())
    assert error.value.reason == "missing_binding"


@pytest.mark.parametrize("extra, context, reason", [
    ({"environment_fingerprint": "old"}, {"environment_fingerprint": "current"}, "environment_mismatch"),
    ({"compatibility_environments": ["primary", "old"]},
     {"compatibility_environments": ["primary", "current"]}, "compatibility_mismatch"),
    ({"compatibility_environments": ["primary", "primary"]}, {}, "invalid_metrics"),
])
def test_environment_or_panel_mismatch_has_an_explicit_fallback_reason(extra, context, reason):
    assert delta(metrics={**receipt(), **extra}, incumbent_score=90, **context) == {
        "status": "scalar_only", "reason": reason, "score": 0.0}


def test_frozen_panel_order_is_irrelevant_and_matching_context_keeps_components():
    metrics = {**receipt(), "environment_fingerprint": "exact", "compatibility_environments": ["a", "b"]}
    change = delta(metrics=metrics, environment_fingerprint="exact", compatibility_environments=["b", "a"])
    assert change["status"] == "complete"


def test_separate_scalar_must_agree_with_complete_receipt():
    assert delta(incumbent_score=95) == {"status": "scalar_only", "reason": "score_mismatch", "score": -5.0}


@pytest.mark.parametrize("replacement", [
    {"tokens": -1}, {"tokens": True}, {"tokens": 1.5}, {"tokens": float("inf")},
    {"heartbeats": -1}, {"heartbeats": None}, {"heartbeats": float("nan")},
    {"compatibility_pct": None}, {"compatibility_pct": True},
    {"compatibility_pct": -0.01}, {"compatibility_pct": 100.01},
    {"compatibility_pct": float("nan")}, {"compatibility_pct": float("inf")},
    {"tokens": 10 ** 307}, {"tokens": 10 ** 1000},
])
def test_unknown_nonfinite_or_negative_candidate_metrics_cannot_be_explained(replacement):
    values = {"tokens": 10, "heartbeats": 20, "compatibility_pct": 100, **replacement}
    with pytest.raises(ValueError):
        score_breakdown(POLICY, **values)


def test_regressions_below_zero_are_real_scores_and_deltas():
    change = delta(tokens=400, heartbeats=400, compatibility_pct=0)
    assert change["score"] == -290
    reconciles(change)
