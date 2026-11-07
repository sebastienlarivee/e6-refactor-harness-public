"""Frozen stopping policies and host-only diminishing-returns decisions."""
from __future__ import annotations

from decimal import Decimal
import math
from typing import Any


POLICIES = ("screening", "convergence", "cost")
DEFAULT_POLICY = "convergence"
LEGACY_POLICY = "cost"
CONVERGENCE_DEFAULTS = {
    "minimum_passes": 5,
    "window_passes": 3,
    "max_gain": 0.5,
    "confirmation_passes": 1,
    "failure_policy": "skip",
    "confirmation_basis": "rolling_window",
}
SCREENING_ATTEMPTS = 5
SCREENING_ATTEMPTED_BASIS = "attempted_passes"
SCREENING_HEALTHY_BASIS = "completed_healthy_passes"
SCREENING_LEGACY_DEFAULTS = {
    "attempts": SCREENING_ATTEMPTS,
    "margin": 0.5,
    "required_healthy_comparisons": 3,
    "comparison_basis": "matched_attempt_budget",
    "control_reducer": "maximum",
    "unhealthy_policy": "skip_confirmation_reset_on_observed_gap_at_or_below_margin",
    "current_comparison_must_be_healthy": True,
}
SCREENING_DEFAULTS = {**SCREENING_LEGACY_DEFAULTS,
    "count_basis": SCREENING_HEALTHY_BASIS,
    "comparison_basis": "matched_completed_healthy_pass_budget",
    "unhealthy_policy": "exclude_failed_attempts"}


def screening_settings(settings: dict | None = None) -> dict:
    """New screens count healthy completions; omitted frozen bases stay legacy."""
    values = dict(SCREENING_DEFAULTS if settings is None else settings)
    if set(values) not in (set(SCREENING_DEFAULTS), set(SCREENING_DEFAULTS) - {"count_basis"}):
        raise ValueError("Screening settings must declare every screening parameter")
    basis = values.get("count_basis", SCREENING_ATTEMPTED_BASIS)
    if not isinstance(basis, str) or basis not in {
            SCREENING_ATTEMPTED_BASIS, SCREENING_HEALTHY_BASIS}:
        raise ValueError("Unsupported screening count_basis")
    expected = SCREENING_DEFAULTS if basis == SCREENING_HEALTHY_BASIS else SCREENING_LEGACY_DEFAULTS
    if any(values[key] != default for key, default in expected.items()):
        raise ValueError("Screening requires the frozen five-pass comparison settings")
    return values


def screening_pass_healthy(record: dict | None) -> bool:
    """Count native completion and host health, independent of score improvement."""
    return bool(isinstance(record, dict)
        and record.get("agent_status") == "completed"
        and record.get("native_status") == "completed"
        and type(record.get("native_returncode")) is int
        and record["native_returncode"] == 0
        and record.get("validation_healthy") is True
        and record.get("selection_eligible") is True)


def screening_counted_passes(passes: list[dict], count_basis: str) -> int:
    if count_basis == SCREENING_HEALTHY_BASIS:
        return sum(screening_pass_healthy(record) for record in passes)
    if count_basis == SCREENING_ATTEMPTED_BASIS:
        return len(passes)
    raise ValueError("Unsupported screening count_basis")


def policy_for_config(config: dict) -> str:
    """Older frozen roots retain the policy under which they were prepared."""
    policy = config.get("stopping_policy", LEGACY_POLICY)
    if policy not in POLICIES:
        raise ValueError("Unsupported E6 stopping policy")
    return policy


def convergence_settings(settings: dict | None = None) -> dict:
    """Preserve frozen settings; absent policy fields retain their old semantics."""
    values = dict(CONVERGENCE_DEFAULTS if settings is None else settings)
    keys = set(CONVERGENCE_DEFAULTS)
    if set(values) not in (keys, keys - {"confirmation_basis"},
                           keys - {"failure_policy", "confirmation_basis"}):
        raise ValueError("Convergence settings must declare every stopping parameter")
    if values.get("failure_policy", "reset") not in ("skip", "reset"):
        raise ValueError("Convergence failure_policy must be skip or reset")
    if values.get("confirmation_basis", "original_anchor") not in ("rolling_window", "original_anchor"):
        raise ValueError("Convergence confirmation_basis must be rolling_window or original_anchor")
    for name in ("minimum_passes", "window_passes", "confirmation_passes"):
        if type(values[name]) is not int or values[name] < 1:
            raise ValueError(f"Convergence {name} must be a positive integer")
    if values["minimum_passes"] < values["window_passes"]:
        raise ValueError("Minimum passes cannot be shorter than the gain window")
    if values["confirmation_passes"] != 1:
        raise ValueError("Convergence requires exactly one confirmation pass")
    gain = values["max_gain"]
    if isinstance(gain, bool) or not isinstance(gain, (int, float)) or not math.isfinite(gain) or gain < 0:
        raise ValueError("Convergence max_gain must be finite and nonnegative")
    values["max_gain"] = float(gain)
    return values


def policy_fields(policy: str) -> dict:
    policy_for_config({"stopping_policy": policy})
    metered = policy == LEGACY_POLICY
    return {
        "stopping_policy": policy,
        "convergence": convergence_settings() if policy == "convergence" else None,
        "cost_metering": metered,
        "cumulative_budget_usd": "3" if metered else None,
        "total_budget_usd": 3 if metered else None,
        "cost_basis": "reported usage at fixed API-equivalent rates; not an invoice" if metered else "unmetered research",
        "budget_policy": "reported_usage_serial_threshold" if metered else "disabled",
        "selection_policy": (
            "host-validated candidates from settled known-usage passes within $3; exclude the entire overshooting pass"
            if metered else "host-validated candidates independent of spending; stop after five completed healthy passes"
            if policy == "screening" else "host-validated candidates independent of spending; stop on confirmed diminishing returns"
        ),
        **({"screening": dict(SCREENING_DEFAULTS), "max_passes": SCREENING_ATTEMPTS}
           if policy == "screening" else {}),
    }


def verify_final_screening(config: dict, result: dict) -> dict:
    """Certify the frozen pass budget, independently of the advisory comparison."""
    from .experiment import experiment_spec
    spec = experiment_spec(config)
    basis = spec.screening_count_basis
    reason = "screening_healthy_pass_cap" if basis == SCREENING_HEALTHY_BASIS else "screening_attempt_cap"
    if (spec.stopping_policy != "screening" or result.get("stopping_policy") != "screening"
            or result.get("status") != "completed"
            or result.get("stop_reason") != reason
            or result.get("convergence") is not None):
        raise ValueError("Run lacks a completed five-pass screening result")
    if (result.get("screening", None if basis == SCREENING_HEALTHY_BASIS else spec.stopping_settings()["screening"])
            != spec.stopping_settings()["screening"]
            or result.get("experiment_spec", {}).get("screening_count_basis", SCREENING_ATTEMPTED_BASIS) != basis
            or result.get("max_passes", SCREENING_ATTEMPTS) != SCREENING_ATTEMPTS):
        raise ValueError("Screening result differs from its frozen count basis or budget")
    passes = result.get("passes")
    if not isinstance(passes, list) or screening_counted_passes(passes, basis) != SCREENING_ATTEMPTS:
        raise ValueError("Screening requires exactly five counted passes")
    if screening_counted_passes(passes[:-1], basis) >= SCREENING_ATTEMPTS:
        raise ValueError("Screening continued beyond its five counted passes")
    previous = ConvergenceTracker._score(config.get("initial_best", {}).get("score"))
    healthy = 0
    for number, record in enumerate(passes, 1):
        if (not isinstance(record, dict) or type(record.get("pass_number")) is not int
                or record["pass_number"] != number
                or type(record.get("validation_healthy")) is not bool
                or record.get("selection_eligible") is not True
                or record.get("convergence") is not None):
            raise ValueError("Screening pass order or host selection evidence is invalid")
        current = ConvergenceTracker._score(record.get("best_score"))
        if current < previous:
            raise ValueError("Screening verified incumbent score cannot decrease")
        previous = current
        healthy += screening_pass_healthy(record)
    if result.get("best_score") != float(previous):
        raise ValueError("Screening final score differs from its pass evidence")
    return {"attempted_passes": len(passes), "healthy_passes": healthy,
            "counted_passes": screening_counted_passes(passes, basis), "count_basis": basis,
            "pass_cap": SCREENING_ATTEMPTS,
            "attempt_cap": SCREENING_ATTEMPTS if basis == SCREENING_ATTEMPTED_BASIS else None,
            "screening_complete": True}


def verify_screening_capsules(root, result: dict | None = None) -> None:
    """A completion cannot hide any unrecorded additional admitted capsule."""
    attempts = SCREENING_ATTEMPTS if result is None else len(result["passes"])
    expected = {f"pass-{number:03d}" for number in range(1, attempts + 1)}
    paths = list(root.glob("pass-*"))
    if {path.name for path in paths} != expected or any(not path.is_dir() for path in paths):
        raise ValueError("Completed screening requires exactly its recorded attempted-pass capsules")


class ConvergenceTracker:
    """Observe monotone incumbents with a frozen policy for failed passes.

    New runs detect and confirm plateaus with the same rolling healthy-pass
    window, skipping explicit failures. Frozen older settings retain original
    anchor confirmation and their declared failure policy. No future score is used.
    """

    def __init__(self, initial_score: float, settings: dict | None = None):
        self.settings = convergence_settings(settings)
        self._history = [(0, self._score(initial_score))]
        self._last_score = self._history[0][1]
        self._last_pass = 0
        self._healthy_passes = 0
        self._consecutive_healthy_passes = 0
        self._pending: tuple[int, Decimal] | None = None
        self._status = "tracking"
        self._recent_gain: Decimal | None = None
        self._confirmed_gain: Decimal | None = None

    @staticmethod
    def _score(value: Any) -> Decimal:
        if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value) or not 0 <= value <= 100:
            raise ValueError("Verified incumbent score must be finite and between 0 and 100")
        return Decimal(str(value))

    def snapshot(self) -> dict:
        anchor = self._pending
        return {
            "settings": dict(self.settings),
            "status": self._status,
            "healthy_passes": self._healthy_passes,
            "consecutive_healthy_passes": self._consecutive_healthy_passes,
            "recent_gain": None if self._recent_gain is None else float(self._recent_gain),
            "anchor_pass": None if anchor is None else anchor[0],
            "anchor_score": None if anchor is None else float(anchor[1]),
            "confirmed_gain": None if self._confirmed_gain is None else float(self._confirmed_gain),
            "should_stop": self._status == "diminishing_returns",
        }

    def observe(self, score: float, *, healthy: bool = True, pass_number: int | None = None) -> dict:
        if self._status == "diminishing_returns":
            raise ValueError("Cannot extend a confirmed stopping trajectory")
        number = self._last_pass + 1 if pass_number is None else pass_number
        if type(number) is not int or number <= self._last_pass:
            raise ValueError("Observed pass numbers must strictly increase")
        if type(healthy) is not bool:
            raise ValueError("Pass health must be explicit")
        current = self._score(score)
        if current < self._last_score:
            raise ValueError("Verified incumbent score cannot decrease")
        failure_policy = self.settings.get("failure_policy", "reset")
        # An absent row has unknown health; only explicit failures can be skipped.
        if number != self._last_pass + 1:
            if failure_policy == "skip":
                raise ValueError("Convergence requires evidence for every observed pass")
            self._history = [(self._last_pass, self._last_score)]
            self._pending = None
            self._consecutive_healthy_passes = 0
        self._last_pass = number
        self._last_score = current
        if not healthy:
            self._consecutive_healthy_passes = 0
            if failure_policy == "skip":
                return self.snapshot()
            self._confirmed_gain = None
            self._history = [(number, current)]
            self._pending = None
            self._recent_gain = None
            self._status = "tracking"
            return self.snapshot()
        self._confirmed_gain = None
        self._healthy_passes += 1
        self._consecutive_healthy_passes += 1
        self._history.append((number, current))
        window = self.settings["window_passes"]
        self._recent_gain = current - self._history[-window - 1][1] if len(self._history) > window else None
        limit = Decimal(str(self.settings["max_gain"]))
        if self._pending is not None:
            if self.settings.get("confirmation_basis", "original_anchor") == "rolling_window":
                self._pending = self._history[-window - 1]
            self._confirmed_gain = current - self._pending[1]
            if self._confirmed_gain <= limit:
                self._status = "diminishing_returns"
                return self.snapshot()
            self._pending = None
            self._status = "tracking"
            # Review a later window after a rejected confirmation, never
            # immediately reuse the confirmation as another tentative stop.
            return self.snapshot()
        if (self._healthy_passes >= self.settings["minimum_passes"]
                and self._recent_gain is not None and self._recent_gain <= limit):
            self._pending = self._history[-window - 1]
            self._status = "confirmation"
        else:
            self._status = "tracking"
        return self.snapshot()


def verify_final_convergence(config: dict, result: dict) -> dict:
    """Replay saved pass evidence before retaining or exporting a research run."""
    if config.get("policy_epochs"):
        from .resume import replay_policy_epochs
        return replay_policy_epochs(config, result)
    if (policy_for_config(config) != "convergence"
            or result.get("stopping_policy") != "convergence"
            or result.get("status") != "diminishing_returns"):
        raise ValueError("Run lacks a successful convergence stopping result")
    settings = convergence_settings(config.get("convergence"))
    initial = config.get("initial_best", {})
    if not isinstance(initial, dict) or "score" not in initial:
        raise ValueError("Convergence evidence lacks a verified initial score")
    tracker = ConvergenceTracker(initial["score"], settings)
    passes = result.get("passes")
    if not isinstance(passes, list) or not passes:
        raise ValueError("Convergence pass evidence is missing")
    for number, record in enumerate(passes, 1):
        if (not isinstance(record, dict) or type(record.get("pass_number")) is not int
                or record["pass_number"] != number
                or type(record.get("validation_healthy")) is not bool):
            raise ValueError("Convergence pass order or validation health is invalid")
        healthy = (record.get("agent_status") == "completed"
                   and record.get("native_status", record.get("agent_status")) == "completed"
                   and record["validation_healthy"])
        if healthy and record.get("selection_eligible") is not True:
            raise ValueError("Healthy convergence pass lacks host selection")
        snapshot = tracker.observe(record.get("best_score"), healthy=healthy, pass_number=number)
        if "convergence" in record and record["convergence"] != snapshot:
            raise ValueError("Saved pass convergence decision differs from its verified scores")
    snapshot = tracker.snapshot()
    if not snapshot["should_stop"] or result.get("convergence") != snapshot:
        raise ValueError("Final convergence decision differs from the pass evidence")
    return snapshot
