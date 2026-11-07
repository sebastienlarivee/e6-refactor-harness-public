"""Pure scoring with original denominators and the contest's stable rounding."""
from __future__ import annotations

import math
import re
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any, Protocol

from lean_tools.workflow_errors import WorkflowError
from lean_tools.measurement_policy import ARENA_POLICY, LEGACY_POLICY


class LocalScoreMetrics(Protocol):
    local_token_reduction_pct: float
    heartbeat_reduction_pct: float | None


def local_selection_score(evaluation: LocalScoreMetrics) -> float:
    if evaluation.heartbeat_reduction_pct is None:
        raise WorkflowError(
            "cannot select a finalist without a local heartbeat reduction"
        )
    return round(
        (evaluation.local_token_reduction_pct + evaluation.heartbeat_reduction_pct) / 2,
        4,
    )


def contest_score_components(
    original_tokens: int,
    original_heartbeats: int,
    candidate_tokens: int,
    candidate_heartbeats: int,
    compatibility_pct: float,
) -> dict[str, float | int]:
    """Reconstruct the local three-axis contest score with stable rounding."""

    if original_tokens <= 0 or original_heartbeats <= 0:
        raise WorkflowError("contest score baselines must be positive")
    if candidate_tokens < 0 or candidate_heartbeats < 0:
        raise WorkflowError("contest candidate metrics cannot be negative")
    length_reduction = round(
        100.0 * (original_tokens - candidate_tokens) / original_tokens, 2
    )
    heartbeat_reduction = round(
        100.0
        * (original_heartbeats - candidate_heartbeats)
        / original_heartbeats,
        2,
    )
    score = round(
        (length_reduction + heartbeat_reduction + compatibility_pct) / 3, 4
    )
    return {
        "tokens": candidate_tokens,
        "heartbeats": candidate_heartbeats,
        "compatibility_pct": compatibility_pct,
        "length_reduction_pct": length_reduction,
        "heartbeat_reduction_pct": heartbeat_reduction,
        "official_score": score,
    }


@dataclass(frozen=True)
class OriginalDenominatorScorePolicy:
    original_tokens: int
    original_heartbeats: int
    scoring_policy: str = LEGACY_POLICY

    def __post_init__(self) -> None:
        if not isinstance(self.scoring_policy, str) or self.scoring_policy not in {LEGACY_POLICY, ARENA_POLICY}:
            raise ValueError("scoring_policy must be legacy-v1 or arena-v1")
        for name in ("original_tokens", "original_heartbeats"):
            value = getattr(self, name)
            if type(value) is not int or value <= 0:
                raise ValueError(f"{name} must be a positive integer")

    def components(self, *, tokens: int, heartbeats: int, compatibility_pct: float) -> dict[str, float | int]:
        for name, value in (("tokens", tokens), ("heartbeats", heartbeats)):
            if type(value) is not int or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")
        if not _finite_number(compatibility_pct) or not 0 <= compatibility_pct <= 100:
            raise ValueError("compatibility_pct must be finite and between 0 and 100")
        try:
            components = contest_score_components(
                self.original_tokens, self.original_heartbeats,
                tokens, heartbeats, compatibility_pct,
            )
        except OverflowError as error:
            raise ValueError("scoring metrics exceed the finite numeric range") from error
        if not all(math.isfinite(components[name]) for name in (
                "length_reduction_pct", "heartbeat_reduction_pct", "official_score")):
            raise ValueError("scoring metrics exceed the finite numeric range")
        return components

    def score(self, *, tokens: int, heartbeats: int, compatibility_pct: float) -> float:
        return self.components(tokens=tokens, heartbeats=heartbeats,
                               compatibility_pct=compatibility_pct)["official_score"]

    def optimistic_score(self, *, tokens: int) -> float:
        """Maximum score if the proof has zero heartbeats and full compatibility."""
        return self.score(tokens=tokens, heartbeats=0, compatibility_pct=100.0)

    def cannot_beat_validated_incumbent(
        self, *, tokens: int, validated_incumbent_score: float
    ) -> bool:
        """Prune only strict scalar losers; equality may win a later tie-break.

        The incumbent must be computed by `score` after authoritative validity and
        compatibility checks. Calling this method is not a substitute for those
        checks. It says nothing about preserving the full three-axis Pareto set.
        """
        if not math.isfinite(validated_incumbent_score) or validated_incumbent_score > 100:
            raise ValueError("validated_incumbent_score must be finite and at most 100")
        return self.optimistic_score(tokens=tokens) < validated_incumbent_score


def _finite_number(value: Any) -> bool:
    try:
        return type(value) in (int, float) and math.isfinite(value)
    except OverflowError:
        return False


def _point_contributions(length: float, heartbeats: float, compatibility: float,
                         score: float) -> dict[str, Any]:
    """Expose rounded thirds and the residual needed to recover the scalar score."""
    points = {"length": round(length / 3, 4), "heartbeats": round(heartbeats / 3, 4),
              "compatibility": round(compatibility / 3, 4)}
    return {"score_points": points,
            "rounding_adjustment": round(score - sum(points.values()), 4), "score": score}


def score_breakdown(policy: OriginalDenominatorScorePolicy, *, tokens: int,
                    heartbeats: int, compatibility_pct: float) -> dict[str, Any]:
    """Explain a complete measured score without changing its rounding policy.

    Reductions use the contest's two decimal places. Contributions and the final
    scalar use four; rounding_adjustment makes the displayed terms reconcile.
    Call only after exact metrics and the full compatibility panel are complete.
    """
    measured = policy.components(tokens=tokens, heartbeats=heartbeats,
                                 compatibility_pct=compatibility_pct)
    length, heartbeat = measured["length_reduction_pct"], measured["heartbeat_reduction_pct"]
    return {"length_reduction_pct": length, "heartbeat_reduction_pct": heartbeat,
            "compatibility_pct": compatibility_pct,
            **_point_contributions(length, heartbeat, compatibility_pct, measured["official_score"])}


class IncumbentMetricsError(ValueError):
    """A frozen incumbent receipt cannot support component comparisons."""

    def __init__(self, reason: str, message: str):
        super().__init__(message)
        self.reason = reason


def validate_incumbent_metrics(
    policy: OriginalDenominatorScorePolicy, metrics: Any, *,
    incumbent_source_sha256: str | None = None,
    environment_fingerprint: str | None = None,
    compatibility_environments: Sequence[str] | None = None,
) -> dict[str, Any]:
    """Validate host-frozen metrics against an independently frozen incumbent.

    The binding is the host's verified pass-start incumbent, which can differ
    from the editable scaffold in a statement-first pass. Never derive it from
    a request's expected_sha256 or from the draft after edits have begun.
    """
    required = {"source_sha256", "tokens", "heartbeats", "compatibility_pct", "score",
                "original_tokens", "original_heartbeats"}
    if not isinstance(metrics, Mapping) or not required.issubset(metrics):
        raise IncumbentMetricsError("missing_metrics", "complete incumbent metrics are unavailable")
    if metrics.get("scoring_policy", LEGACY_POLICY) != policy.scoring_policy:
        raise IncumbentMetricsError("scoring_policy_mismatch", "incumbent metrics use a different scoring policy")
    source = metrics["source_sha256"]
    if not isinstance(source, str) or re.fullmatch(r"[0-9a-f]{64}", source) is None:
        raise IncumbentMetricsError("invalid_metrics", "incumbent source_sha256 must be a SHA256 digest")
    if (not isinstance(incumbent_source_sha256, str)
            or re.fullmatch(r"[0-9a-f]{64}", incumbent_source_sha256) is None):
        raise IncumbentMetricsError("missing_binding", "independent incumbent source binding is unavailable")
    if source != incumbent_source_sha256:
        raise IncumbentMetricsError("source_mismatch", "incumbent metrics do not match the frozen incumbent source")
    if any(type(metrics[name]) is not int or metrics[name] != getattr(policy, name)
           for name in ("original_tokens", "original_heartbeats")):
        raise IncumbentMetricsError("denominator_mismatch", "incumbent metrics use different original denominators")
    try:
        measured = policy.components(tokens=metrics["tokens"], heartbeats=metrics["heartbeats"],
                                     compatibility_pct=metrics["compatibility_pct"])
    except (ValueError, TypeError, OverflowError) as error:
        raise IncumbentMetricsError("invalid_metrics", "incumbent metrics must contain finite measured values") from error
    if not _finite_number(metrics["score"]) or metrics["score"] != measured["official_score"]:
        raise IncumbentMetricsError("score_mismatch", "incumbent score does not match its frozen metrics")
    fingerprint = metrics.get("environment_fingerprint")
    if fingerprint is not None:
        if not isinstance(fingerprint, str) or not fingerprint:
            raise IncumbentMetricsError("invalid_metrics", "incumbent environment fingerprint must be nonempty")
        if environment_fingerprint is not None and fingerprint != environment_fingerprint:
            raise IncumbentMetricsError("environment_mismatch", "incumbent metrics use a different primary environment")
    environments = metrics.get("compatibility_environments")
    if environments is not None:
        if (not isinstance(environments, list) or not environments
                or any(not isinstance(item, str) or not item for item in environments)
                or len(set(environments)) != len(environments)):
            raise IncumbentMetricsError("invalid_metrics", "incumbent compatibility environments must be unique nonempty paths")
        if compatibility_environments is not None and set(environments) != set(compatibility_environments):
            raise IncumbentMetricsError("compatibility_mismatch", "incumbent metrics use a different compatibility panel")
    return dict(metrics)


def incumbent_score_delta(
    policy: OriginalDenominatorScorePolicy, *, tokens: int, heartbeats: int,
    compatibility_pct: float, incumbent_score: float | None = None,
    incumbent_metrics: Any = None, incumbent_source_sha256: str | None = None,
    environment_fingerprint: str | None = None,
    compatibility_environments: Sequence[str] | None = None,
) -> dict[str, Any]:
    """Explain improvement over the fixed pass-start incumbent, never a batch floor.

    Positive reduction/score deltas mean improvement; raw token/heartbeat deltas
    are candidate minus incumbent. Missing or rejected metrics expose no made-up
    components. A separately frozen scalar score can still support total delta.
    """
    candidate = score_breakdown(policy, tokens=tokens, heartbeats=heartbeats,
                                compatibility_pct=compatibility_pct)
    try:
        receipt = validate_incumbent_metrics(policy, incumbent_metrics,
            incumbent_source_sha256=incumbent_source_sha256,
            environment_fingerprint=environment_fingerprint,
            compatibility_environments=compatibility_environments)
        if incumbent_score is not None and (not _finite_number(incumbent_score)
                                            or incumbent_score != receipt["score"]):
            raise IncumbentMetricsError("score_mismatch", "incumbent scalar and metrics receipt disagree")
    except IncumbentMetricsError as error:
        if error.reason == "scoring_policy_mismatch":
            return {"status": "unavailable", "reason": error.reason, "score": None}
        if _finite_number(incumbent_score) and incumbent_score <= 100:
            return {"status": "scalar_only", "reason": error.reason,
                    "score": round(candidate["score"] - incumbent_score, 4)}
        return {"status": "unavailable", "reason": error.reason, "score": None}
    incumbent = score_breakdown(policy, tokens=receipt["tokens"], heartbeats=receipt["heartbeats"],
                               compatibility_pct=receipt["compatibility_pct"])
    length = round(candidate["length_reduction_pct"] - incumbent["length_reduction_pct"], 2)
    heartbeat = round(candidate["heartbeat_reduction_pct"] - incumbent["heartbeat_reduction_pct"], 2)
    compatibility = compatibility_pct - receipt["compatibility_pct"]
    delta = round(candidate["score"] - receipt["score"], 4)
    return {"status": "complete", "incumbent_source_sha256": receipt["source_sha256"],
            "tokens": tokens - receipt["tokens"], "heartbeats": heartbeats - receipt["heartbeats"],
            "length_reduction_pct": length, "heartbeat_reduction_pct": heartbeat,
            "compatibility_pct": compatibility,
            **_point_contributions(length, heartbeat, compatibility, delta)}
