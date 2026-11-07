"""Validated, immutable settings for the E6 experiment.

The snapshot travels with each proof and panel. Public configuration fields
are derived from the single production prompt and its tool contract.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass, field, fields, replace
from decimal import Decimal, InvalidOperation
import math
from typing import Mapping

from .stopping import (convergence_settings, policy_fields, SCREENING_ATTEMPTS,
                       SCREENING_ATTEMPTED_BASIS, SCREENING_HEALTHY_BASIS, SCREENING_LEGACY_DEFAULTS)
from .deterministic_support.search_policy import POLICIES as DETERMINISTIC_POLICIES

ATTEMPT_MEMORY_V1 = "bounded_same_run_negative_observations"
ATTEMPT_MEMORY_V2 = "bounded_same_run_decisive_observations_v2"
EFFICIENT_CONTROL_PROMPT = "control-efficient-v1"


def blocking_unknown_usage(budget: Mapping) -> bool:
    """Only ledger-validated provisional unknowns may be nonblocking.

    Historical/malformed counters never relax the existing unknown-usage gate.
    A provisional receipt retains its null actual cost and future liability.
    """
    unknown = budget.get("unknown_requests", 0)
    if not unknown:
        return False
    active = budget.get("active_requests")
    provisional = budget.get("provisional_unknown_requests")
    blocking = budget.get("blocking_unknown_requests")
    return not (budget.get("recovery_policy") == "exclusive-key-v1"
        and type(unknown) is int and type(provisional) is int and unknown > 0
        and provisional == unknown and type(active) is int and active == 0
        and type(blocking) is int and blocking == 0)


def _decimal_text(value: Decimal) -> str:
    text = format(value, "f")
    return text.rstrip("0").rstrip(".") if "." in text else text


@dataclass(frozen=True)
class RerankSettings:
    """Optional selector policy frozen with a new experiment."""
    ranker: str = "jev"
    model: str | None = None
    candidate_limit: int = 30
    questions_per_call: int = 30
    state_pool_scope: str = "batch"
    max_request_bytes: int = 2 * 1024 * 1024
    max_total_questions: int | None = None
    max_total_request_bytes: int | None = None
    max_calls: int | None = None
    one_call: bool = False
    timeout_seconds: float = 60

    def __post_init__(self) -> None:
        if not isinstance(self.ranker, str) or self.ranker not in {"baseline", "lexical", "jev", "openai", "model"}:
            raise ValueError("Unsupported declaration ranker")
        if self.model is not None and (not isinstance(self.model, str) or not self.model):
            raise ValueError("Selector model must be a nonempty string")
        if type(self.candidate_limit) is not int or not 1 <= self.candidate_limit <= 5000:
            raise ValueError("candidate_limit must be in 1..5000")
        from lean_tools.decision_rerank import MODELS
        model = self.model or MODELS.get(self.ranker, MODELS["jev"])
        if self.ranker == "model" and self.model is None:
            raise ValueError("ranker=model requires an explicit model identifier")
        object.__setattr__(self, "model", model)
        try:
            self.core_config().validate()
        except RuntimeError as error:
            raise ValueError(str(error)) from error

    def to_dict(self) -> dict:
        return asdict(self)

    def core_config(self):
        from lean_tools.decision_rerank import RerankConfig
        values = self.to_dict()
        values.pop("candidate_limit")
        ranker = values.pop("ranker")
        values["mode"] = ranker if ranker in {"baseline", "lexical"} else "decisions"
        return RerankConfig(**values)


@dataclass(frozen=True)
class ConvergenceSettings:
    """Immutable host stopping rule; exported as a plain configuration mapping."""
    minimum_passes: int = 5
    window_passes: int = 3
    max_gain: float = 0.5
    confirmation_passes: int = 1
    failure_policy: str | None = "skip"
    confirmation_basis: str | None = "rolling_window"

    def __post_init__(self) -> None:
        values = convergence_settings(self.to_dict())
        object.__setattr__(self, "max_gain", values["max_gain"])

    def to_dict(self) -> dict:
        values = asdict(self)
        # Original snapshots used four keys and reset after a failed pass.
        # Preserve their exact shape so historical results remain replayable.
        if self.failure_policy is None:
            values.pop("failure_policy")
        if self.confirmation_basis is None:
            values.pop("confirmation_basis")
        return values

    @classmethod
    def from_dict(cls, value: Mapping) -> ConvergenceSettings:
        values = convergence_settings(dict(value))
        values.setdefault("failure_policy", None)
        values.setdefault("confirmation_basis", None)
        return cls(**values)


@dataclass(frozen=True)
class ExperimentSpec:
    model: str = "gpt-6.1-sol"
    reasoning_effort: str = "xhigh"
    model_display_name: str = "Sol 6.1"
    cumulative_budget_usd: Decimal = Decimal("3")
    accounting_rates: tuple[tuple[str, str], ...] = (
        ("input", "2.5"), ("cache_read", "0.1"),
        ("cache_write", "2.5"), ("output", "10"))
    lean_capacity: int = 2
    proof_cell_capacity: int = 2
    broker_startup_capacity: int = 1
    lean_threads: int = 1
    omp_threads: int = 1
    nice_priority: int = 10
    lean_priority: int = 100
    check_timeout_seconds: float = 600
    preparation_check_timeout_seconds: float = 1800
    broker_startup_timeout_seconds: float = 1800
    lean_request_timeout_seconds: float = 600
    pass_timeout_seconds: None = None
    max_passes: int | None = None
    queue_timeout_seconds: None = None
    cold_lean_capacity: None = None
    model_capacity: None = None
    lean_timeout_scope: str = "compile"
    service_tier: str = "default"
    stopping_policy: str = "convergence"
    scoring_policy: str = "legacy-v1"
    screening_count_basis: str = SCREENING_HEALTHY_BASIS
    convergence: ConvergenceSettings = ConvergenceSettings()
    budget_policy: str = field(init=False)
    context_policy: str = "native_cli_context_and_compaction"
    pass_policy: str = "fresh_ephemeral_incumbent_only"
    selection_mode: str = field(init=False)
    validation_policy: str = "exact_primary_quick_compatibility_host_private_cache"
    candidate_intake_characters: int = 262144
    incumbent_briefing: bool = True
    local_attempts_guidance: bool = False
    candidate_batches: bool = True
    goal_retrieval: bool = False
    retrieval_pool_mode: str = "overlap"
    attempt_memory: bool = False
    attempt_memory_policy: str = ATTEMPT_MEMORY_V2
    rerank_config: RerankSettings | None = RerankSettings(ranker="baseline", candidate_limit=30, one_call=True)
    first_pass_reprove: bool = False
    first_pass_reference_rebuild: bool = True
    prompt_variant: str = EFFICIENT_CONTROL_PROMPT
    early_search_pass1: bool = False
    search_extensions: bool = False
    unfinished_cases: bool = True
    regional_profiler: bool = True
    response_policy: str = "compact-v1"
    deterministic_refactoring: bool = False
    deterministic_budget_seconds: int = 1800
    deterministic_max_candidates: int = 256
    deterministic_rounds: int = 4
    deterministic_policy: str = "legacy"
    deterministic_cache: bool = False
    deterministic_regenerate: bool = False
    deterministic_late_budget_seconds: int | None = None
    deterministic_beam_width: int = 1
    deterministic_beam_score_drop: float = 0.1
    native_stream_idle_timeout_ms: int = 900000
    pending_usage_settlement_seconds: float = 120

    def __post_init__(self) -> None:
        if not isinstance(self.scoring_policy, str) or self.scoring_policy not in {"legacy-v1", "arena-v1"}:
            raise ValueError("Unsupported E6 scoring policy")
        if self.prompt_variant != EFFICIENT_CONTROL_PROMPT:
            raise ValueError("Unsupported prompt_variant; historical prompts must use their original frozen release")
        if self.response_policy != "compact-v1":
            raise ValueError("Unsupported response_policy; historical policies must use their original frozen release")
        if not isinstance(self.stopping_policy, str) or self.stopping_policy not in {"screening", "convergence", "cost"}:
            raise ValueError("Unsupported E6 stopping policy")
        if not isinstance(self.screening_count_basis, str) or self.screening_count_basis not in {SCREENING_ATTEMPTED_BASIS, SCREENING_HEALTHY_BASIS}:
            raise ValueError("Unsupported screening count_basis")
        if self.stopping_policy != "screening":
            object.__setattr__(self, "screening_count_basis", SCREENING_HEALTHY_BASIS)
        if self.stopping_policy == "screening":
            if self.max_passes is None:
                object.__setattr__(self, "max_passes", SCREENING_ATTEMPTS)
            elif type(self.max_passes) is not int or self.max_passes != SCREENING_ATTEMPTS:
                raise ValueError("Screening requires max_passes=5 counted passes")
        if self.convergence is None:
            object.__setattr__(self, "convergence", ConvergenceSettings())
        elif isinstance(self.convergence, Mapping):
            try:
                values = convergence_settings(dict(self.convergence))
                values.setdefault("failure_policy", "skip")
                values.setdefault("confirmation_basis", "rolling_window")
                object.__setattr__(self, "convergence", ConvergenceSettings(**values))
            except TypeError as error:
                raise ValueError("convergence contains unsupported settings") from error
        elif not isinstance(self.convergence, ConvergenceSettings):
            raise ValueError("convergence must be frozen ConvergenceSettings")
        if self.stopping_policy != "convergence" and self.convergence != ConvergenceSettings():
            raise ValueError("Cost or screening stopping cannot declare custom convergence settings")
        object.__setattr__(self, "budget_policy", "reported_usage_serial_threshold" if self.cost_metering else "disabled")
        object.__setattr__(self, "selection_mode", "settled_known_usage_within_threshold_exclude_entire_overshoot"
                           if self.cost_metering else "host_validated_independent_of_spending")
        if isinstance(self.rerank_config, Mapping):
            try:
                object.__setattr__(self, "rerank_config", RerankSettings(**dict(self.rerank_config)))
            except TypeError as error:
                raise ValueError("rerank_config contains unsupported settings") from error
        elif self.rerank_config is not None and not isinstance(self.rerank_config, RerankSettings):
            raise ValueError("rerank_config must be optional frozen RerankSettings")
        for name in ("incumbent_briefing", "local_attempts_guidance", "candidate_batches", "goal_retrieval", "first_pass_reprove", "first_pass_reference_rebuild", "attempt_memory", "early_search_pass1", "search_extensions", "unfinished_cases", "regional_profiler", "deterministic_refactoring", "deterministic_cache", "deterministic_regenerate"):
            if type(getattr(self, name)) is not bool:
                raise ValueError(f"{name} must be a boolean")
        if self.first_pass_reprove and self.first_pass_reference_rebuild:
            raise ValueError("first_pass_reprove and first_pass_reference_rebuild are mutually exclusive")
        for name, upper in (("deterministic_budget_seconds", 86400),
                            ("deterministic_max_candidates", 4096), ("deterministic_rounds", 64)):
            value = getattr(self, name)
            if type(value) is not int or not 1 <= value <= upper:
                raise ValueError(f"{name} must be an integer in 1..{upper}")
            if not self.deterministic_refactoring and value != type(self).__dataclass_fields__[name].default:
                raise ValueError(f"{name} requires deterministic_refactoring")
        if not isinstance(self.deterministic_policy, str) or self.deterministic_policy not in DETERMINISTIC_POLICIES:
            raise ValueError("deterministic_policy must be legacy, prioritized, regional, deep or compact")
        if type(self.deterministic_beam_width) is not int or not 1 <= self.deterministic_beam_width <= 3:
            raise ValueError("deterministic_beam_width must be an integer in 1..3")
        if (type(self.deterministic_beam_score_drop) not in {int, float}
                or not math.isfinite(self.deterministic_beam_score_drop)
                or not 0 <= self.deterministic_beam_score_drop <= 1):
            raise ValueError("deterministic_beam_score_drop must be finite and in 0..1")
        for name in ("deterministic_beam_width", "deterministic_beam_score_drop"):
            if (getattr(self, name) != type(self).__dataclass_fields__[name].default
                    and self.deterministic_policy != "deep"):
                raise ValueError(f"{name} requires deterministic_policy=deep")
        late_budget = self.deterministic_late_budget_seconds
        if late_budget is not None and (type(late_budget) is not int or not 1 <= late_budget <= 86400):
            raise ValueError("deterministic_late_budget_seconds must be an integer in 1..86400 or None")
        for name in ("deterministic_policy", "deterministic_cache", "deterministic_regenerate", "deterministic_late_budget_seconds",
                     "deterministic_beam_width", "deterministic_beam_score_drop"):
            if not self.deterministic_refactoring and getattr(self, name) != type(self).__dataclass_fields__[name].default:
                raise ValueError(f"{name} requires deterministic_refactoring")
        if self.early_search_pass1 and not self.goal_retrieval:
            raise ValueError("early_search_pass1 requires goal_retrieval")
        if not isinstance(self.attempt_memory_policy, str) or self.attempt_memory_policy not in {ATTEMPT_MEMORY_V1, ATTEMPT_MEMORY_V2}:
            raise ValueError("Unsupported attempt-memory policy")
        if not isinstance(self.retrieval_pool_mode, str) or self.retrieval_pool_mode not in {"overlap", "diverse", "hybrid"}:
            raise ValueError("retrieval_pool_mode must be overlap, diverse or hybrid")
        for name in ("model", "model_display_name"):
            if not isinstance(getattr(self, name), str) or not getattr(self, name).strip():
                raise ValueError(f"{name} must be a nonempty string")
        if (not isinstance(self.reasoning_effort, str)
                or self.reasoning_effort not in {"none", "minimal", "low", "medium", "high", "xhigh"}):
            raise ValueError("Unsupported reasoning effort")
        try:
            amount = Decimal(str(self.cumulative_budget_usd))
        except InvalidOperation as error:
            raise ValueError("Cumulative budget must be positive and finite") from error
        if isinstance(self.cumulative_budget_usd, bool) or not amount.is_finite() or amount <= 0:
            raise ValueError("Cumulative budget must be positive and finite")
        maximum = type(self).__dataclass_fields__["cumulative_budget_usd"].default
        if amount > maximum:
            raise ValueError(f"The E6 cumulative budget must be at most {_decimal_text(maximum)}")
        object.__setattr__(self, "cumulative_budget_usd", amount)
        try:
            rates = tuple(tuple(item) for item in self.accounting_rates)
        except TypeError as error:
            raise ValueError("Accounting rates require all four token partitions exactly once") from error
        if (any(len(item) != 2 for item in rates)
                or len(rates) != 4 or {item[0] for item in rates} != {"input", "cache_read", "cache_write", "output"}):
            raise ValueError("Accounting rates require all four token partitions exactly once")
        normalized = []
        for name, raw in rates:
            try:
                rate = Decimal(str(raw))
            except InvalidOperation as error:
                raise ValueError("Accounting rates must be finite and nonnegative") from error
            if isinstance(raw, bool) or not rate.is_finite() or rate < 0:
                raise ValueError("Accounting rates must be finite and nonnegative")
            normalized.append((name, _decimal_text(rate)))
        order = [name for name, _ in type(self).__dataclass_fields__["accounting_rates"].default]
        normalized.sort(key=lambda item: order.index(item[0]))
        object.__setattr__(self, "accounting_rates", tuple(normalized))
        for name in ("lean_capacity", "proof_cell_capacity", "broker_startup_capacity", "lean_threads",
                     "omp_threads", "candidate_intake_characters", "native_stream_idle_timeout_ms"):
            if type(getattr(self, name)) is not int or getattr(self, name) <= 0:
                raise ValueError(f"{name} must be a positive integer")
        if self.max_passes is not None and (type(self.max_passes) is not int or self.max_passes <= 0):
            raise ValueError("max_passes must be a positive integer or None")
        if type(self.nice_priority) is not int or not 0 <= self.nice_priority <= 19:
            raise ValueError("nice_priority must be between 0 and 19")
        if type(self.lean_priority) is not int:
            raise ValueError("lean_priority must be an integer")
        for name in ("check_timeout_seconds", "preparation_check_timeout_seconds",
                     "broker_startup_timeout_seconds", "lean_request_timeout_seconds"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value) or value <= 0:
                raise ValueError(f"{name} must be positive and finite")
        grace = self.pending_usage_settlement_seconds
        if isinstance(grace, bool) or not isinstance(grace, (int, float)) or not math.isfinite(grace) or grace < 0:
            raise ValueError("pending_usage_settlement_seconds must be nonnegative and finite")
        fixed = {"pass_timeout_seconds", "queue_timeout_seconds", "cold_lean_capacity", "model_capacity",
                 "lean_timeout_scope", "service_tier", "context_policy", "pass_policy", "validation_policy", "candidate_intake_characters"}
        for field in fields(self):
            if field.name in fixed and getattr(self, field.name) != field.default:
                raise ValueError(f"E6 requires {field.name}={field.default!r}")
        if (not self.incumbent_briefing
                or self.rerank_config is None or self.rerank_config.ranker != "baseline"
                or self.rerank_config.candidate_limit != 30 or self.retrieval_pool_mode != "overlap"
                or any((self.local_attempts_guidance, self.attempt_memory,
                        self.early_search_pass1, self.search_extensions))
                or self.check_timeout_seconds != 600):
            raise ValueError("Efficient CONTROL prompt requires its frozen feature and tool contract")
        if not (self.unfinished_cases and self.regional_profiler and self.candidate_batches):
            raise ValueError("Efficient CONTROL prompt requires unfinished_cases, regional_profiler and candidate_batches")

    @property
    def cost_metering(self) -> bool:
        return self.stopping_policy == "cost"

    def stopping_settings(self) -> dict:
        values = policy_fields(self.stopping_policy)
        if self.stopping_policy == "screening" and self.screening_count_basis == SCREENING_ATTEMPTED_BASIS:
            # Omission identifies frozen v1 screens without changing their JSON.
            values["screening"] = dict(SCREENING_LEGACY_DEFAULTS)
        values.update(convergence=self.convergence.to_dict() if self.stopping_policy == "convergence" else None,
                      cumulative_budget_usd=self.budget_text if self.cost_metering else None,
                      total_budget_usd=float(self.cumulative_budget_usd) if self.cost_metering else None,
                      selection_policy=self.selection_policy)
        return values

    @property
    def budget_text(self) -> str:
        return _decimal_text(self.cumulative_budget_usd)

    @property
    def priority(self) -> str:
        return f"nice_{self.nice_priority}"

    def rates(self) -> dict[str, str]:
        return dict(self.accounting_rates)

    def to_dict(self) -> dict:
        result = asdict(self)
        if self.scoring_policy == "legacy-v1":
            result.pop("scoring_policy")
        result["cumulative_budget_usd"] = self.budget_text
        result["accounting_rates"] = self.rates()
        result["convergence"] = self.convergence.to_dict() if self.stopping_policy == "convergence" else None
        if self.stopping_policy != "screening" or self.screening_count_basis == SCREENING_ATTEMPTED_BASIS:
            result.pop("screening_count_basis")
        # Disabled additions do not rewrite historical policy snapshots.
        if not self.deterministic_refactoring:
            for name in ("deterministic_refactoring", "deterministic_budget_seconds",
                         "deterministic_max_candidates", "deterministic_rounds"):
                result.pop(name)
        # Omitted policy additions preserve the exact historical optimizer
        # snapshot and request binding; each ablation is independently opt-in.
        for name in ("deterministic_policy", "deterministic_cache", "deterministic_regenerate", "deterministic_late_budget_seconds",
                     "deterministic_beam_width", "deterministic_beam_score_drop"):
            if getattr(self, name) == type(self).__dataclass_fields__[name].default:
                result.pop(name)
        if not self.attempt_memory:
            result.pop("attempt_memory")
            result.pop("attempt_memory_policy")
        elif self.attempt_memory_policy == ATTEMPT_MEMORY_V1:
            # Omission is the frozen v1 contract; retain exact historical snapshots.
            result.pop("attempt_memory_policy")
        if not self.early_search_pass1:
            result.pop("early_search_pass1")
        for name in ("search_extensions", "unfinished_cases", "regional_profiler", "first_pass_reference_rebuild"):
            if not getattr(self, name):
                result.pop(name)
        if self.retrieval_pool_mode == "overlap":
            result.pop("retrieval_pool_mode")
        if self.max_passes is None:
            result.pop("max_passes")
        return result

    @classmethod
    def from_dict(cls, value: Mapping) -> ExperimentSpec:
        if not isinstance(value, Mapping):
            raise ValueError("experiment_spec must be a mapping")
        names = {item.name for item in fields(cls)}
        optional = {"incumbent_briefing", "local_attempts_guidance", "candidate_batches", "goal_retrieval", "first_pass_reprove", "first_pass_reference_rebuild",
                    "deterministic_refactoring", "deterministic_budget_seconds", "deterministic_max_candidates", "deterministic_rounds",
                    "deterministic_policy", "deterministic_cache", "deterministic_regenerate", "deterministic_late_budget_seconds",
                    "deterministic_beam_width", "deterministic_beam_score_drop",
                    "native_stream_idle_timeout_ms", "pending_usage_settlement_seconds", "rerank_config",
                    "attempt_memory", "attempt_memory_policy", "retrieval_pool_mode", "max_passes", "early_search_pass1", "search_extensions", "unfinished_cases", "regional_profiler", "stopping_policy", "convergence", "screening_count_basis", "prompt_variant", "scoring_policy", "response_policy"}
        if not names - optional <= set(value) <= names:
            raise ValueError("experiment_spec must contain exactly the supported settings")
        values = dict(value)
        # Optional omissions preserve supported frozen settings.
        for name in optional - {"deterministic_budget_seconds", "deterministic_max_candidates", "deterministic_rounds", "deterministic_policy", "deterministic_late_budget_seconds", "deterministic_beam_width", "deterministic_beam_score_drop", "attempt_memory_policy", "native_stream_idle_timeout_ms", "pending_usage_settlement_seconds", "rerank_config", "retrieval_pool_mode", "max_passes", "stopping_policy", "convergence", "screening_count_basis", "prompt_variant", "scoring_policy", "response_policy"}:
            values.setdefault(name, False)
        values.setdefault("attempt_memory_policy", ATTEMPT_MEMORY_V1 if values["attempt_memory"] else ATTEMPT_MEMORY_V2)
        values.setdefault("native_stream_idle_timeout_ms", 300000)
        values.setdefault("pending_usage_settlement_seconds", 0)
        values.setdefault("rerank_config", None)
        values.setdefault("retrieval_pool_mode", "overlap")
        if "prompt_variant" not in values:
            raise ValueError("Frozen experiment lacks prompt_variant; must use its original frozen release")
        values.setdefault("scoring_policy", "legacy-v1")
        if "response_policy" not in values:
            raise ValueError("Frozen experiment lacks response_policy; must use its original frozen release")
        values.setdefault("max_passes", None)
        values.setdefault("stopping_policy", "cost")
        values.setdefault("convergence", None)
        values.setdefault("screening_count_basis", SCREENING_ATTEMPTED_BASIS
                          if values["stopping_policy"] == "screening" else SCREENING_HEALTHY_BASIS)
        if isinstance(values["convergence"], Mapping):
            values["convergence"] = ConvergenceSettings.from_dict(values["convergence"])
        computed = {name: values.pop(name) for name in ("budget_policy", "selection_mode")}
        rates = values["accounting_rates"]
        if not isinstance(rates, Mapping):
            raise ValueError("accounting_rates must be a mapping")
        values["accounting_rates"] = tuple(rates.items())
        spec = cls(**values)
        for name, saved in computed.items():
            if saved != getattr(spec, name):
                raise ValueError(f"Frozen experiment setting {name} differs from stopping policy")
        return spec

    def common_settings(self) -> dict:
        return {"experiment_spec": self.to_dict(), **self.stopping_settings(), "model": self.model,
                **({"scoring_policy": self.scoring_policy} if self.scoring_policy != "legacy-v1" else {}),
                "reasoning_effort": self.reasoning_effort,
                "pass_timeout_seconds": self.pass_timeout_seconds,
                "lean_capacity": self.lean_capacity, "cold_lean_capacity": self.cold_lean_capacity,
                "lean_timeout_scope": self.lean_timeout_scope, "queue_timeout_seconds": self.queue_timeout_seconds,
                "model_capacity": self.model_capacity, "proof_cell_capacity": self.proof_cell_capacity,
                "native_stream_idle_timeout_ms": self.native_stream_idle_timeout_ms,
                "pending_usage_settlement_seconds": self.pending_usage_settlement_seconds,
                "priority": self.priority,
                **({"max_passes": self.max_passes} if self.max_passes is not None else {}),
                **self.deterministic_settings(),
                **{name: True for name in ("search_extensions", "unfinished_cases", "regional_profiler") if getattr(self, name)},
                "prompt_variant": self.prompt_variant,
                "response_policy": self.response_policy,
                **({"effective_context_policy": self.effective_context_policy} if self.attempt_memory else {})}

    @property
    def effective_context_policy(self) -> str:
        if not self.attempt_memory:
            return self.pass_policy
        suffix = "_v2_decisive_diagnostics" if self.attempt_memory_policy == ATTEMPT_MEMORY_V2 else ""
        return "fresh_ephemeral_incumbent_with_bounded_same_proof_attempt_memory" + suffix

    def proof_settings(self) -> dict:
        return {**self.common_settings(),
                "check_timeout_seconds": self.check_timeout_seconds,
                "preparation_check_timeout_seconds": self.preparation_check_timeout_seconds,
                "broker_startup_capacity": self.broker_startup_capacity,
                "broker_startup_timeout_seconds": self.broker_startup_timeout_seconds,
                "lean_request_timeout_seconds": self.lean_request_timeout_seconds}

    @property
    def selection_policy(self) -> str:
        if self.stopping_policy == "screening":
            basis = "completed healthy" if self.screening_count_basis == SCREENING_HEALTHY_BASIS else "attempted"
            return f"host-validated candidates independent of spending; stop after five {basis} passes"
        if not self.cost_metering:
            return "host-validated candidates independent of spending; stop on confirmed diminishing returns"
        return ("host-validated candidates from settled known-usage passes within "
                f"${self.budget_text}; exclude the entire overshooting pass")

    def panel_settings(self) -> dict:
        return {**self.common_settings(),
                "cumulative_budget_usd_per_proof": self.budget_text if self.cost_metering else None,
                "startup_capacity": self.broker_startup_capacity}

    def pass_exclusion(self, budget: Mapping) -> str | None:
        if not self.cost_metering:
            return None
        if blocking_unknown_usage(budget):
            return "unknown_usage"
        if budget["active_requests"]:
            return "unsettled_requests"
        if Decimal(str(budget["spent_usd"])) > self.cumulative_budget_usd:
            return "budget_overshoot"
        return None

    def pass_mode(self, pass_number: int) -> str:
        if type(pass_number) is not int or pass_number < 1:
            raise ValueError("Pass number must be a positive integer")
        if pass_number == 1:
            if self.first_pass_reprove:
                return "statement_first_reprove"
            if self.first_pass_reference_rebuild:
                return "reference_rebuild"
        return "refactor"

    def deterministic_settings(self) -> dict:
        """Export enabled optimizer settings without changing legacy snapshots."""
        if not self.deterministic_refactoring:
            return {}
        names = ("deterministic_refactoring", "deterministic_budget_seconds",
                 "deterministic_max_candidates", "deterministic_rounds")
        result = {name: getattr(self, name) for name in names}
        for name in ("deterministic_policy", "deterministic_cache", "deterministic_regenerate", "deterministic_late_budget_seconds",
                     "deterministic_beam_width", "deterministic_beam_score_drop"):
            if getattr(self, name) != type(self).__dataclass_fields__[name].default:
                result[name] = getattr(self, name)
        return result

    def deterministic_budget_for_pass(self, pass_number: int) -> int:
        """Optional late budget starts after the first two completed model passes."""
        if type(pass_number) is not int or pass_number < 1:
            raise ValueError("Pass number must be a positive integer")
        if pass_number > 2 and self.deterministic_late_budget_seconds is not None:
            return self.deterministic_late_budget_seconds
        return self.deterministic_budget_seconds


# All new API, public-run and panel settings share the one production prompt.
DEFAULT_SPEC = ExperimentSpec()
DEFAULT_RUN_SPEC = ExperimentSpec(scoring_policy="arena-v1")
DEFAULT_PANEL_SPEC = replace(DEFAULT_RUN_SPEC, stopping_policy="screening")


def experiment_spec(config: Mapping | None = None) -> ExperimentSpec:
    """Read the frozen production settings, or return the current API defaults."""
    if config is None:
        return DEFAULT_SPEC
    if not isinstance(config, Mapping):
        raise ValueError("Experiment configuration must be a mapping")
    if "experiment_spec" in config:
        spec = ExperimentSpec.from_dict(config["experiment_spec"])
    else:
        raise ValueError("Frozen experiment lacks experiment_spec; must use its original frozen release")
    aliases = {**spec.proof_settings(), **spec.panel_settings()}
    aliases["max_passes"] = spec.max_passes
    for name in ("deterministic_refactoring", "deterministic_budget_seconds",
                 "deterministic_max_candidates", "deterministic_rounds", "deterministic_policy",
                 "deterministic_cache", "deterministic_regenerate", "deterministic_late_budget_seconds",
                     "deterministic_beam_width", "deterministic_beam_score_drop"):
        aliases[name] = getattr(spec, name)
    for name in ("search_extensions", "unfinished_cases", "regional_profiler"):
        aliases[name] = getattr(spec, name)
    aliases["prompt_variant"] = spec.prompt_variant
    aliases["scoring_policy"] = spec.scoring_policy
    aliases["response_policy"] = spec.response_policy
    aliases["effective_context_policy"] = spec.effective_context_policy
    # Historical cost summaries used different prose for the same selection rule.
    if spec.cost_metering:
        aliases.pop("selection_policy")
    for key, expected in aliases.items():
        if key != "experiment_spec" and key in config and config[key] != expected:
            # Preparation's older policy name describes the same threshold.
            if (spec.cost_metering and key == "budget_policy"
                    and config[key] == "cumulative_reported_cost_discard_crossing_pass"):
                continue
            raise ValueError(f"Frozen experiment setting {key} differs from experiment_spec")
    return spec


def resolve_spec(root, spec: ExperimentSpec | None = None, stopping_policy: str | None = None) -> ExperimentSpec:
    """Resolve new or saved settings before a preparation/activation mutates state."""
    from .config import resolve_stopping_policy
    saved = []
    for filename in ("panel-config.json", "config.json"):
        path = root / filename
        if path.is_file():
            import json
            saved.append(experiment_spec(json.loads(path.read_text(encoding="utf-8-sig"))))
    if saved and any(value != saved[0] for value in saved[1:]):
        raise ValueError("Frozen E6 configurations have conflicting experiment specs")
    if spec is not None and not isinstance(spec, ExperimentSpec):
        raise ValueError("spec must be an ExperimentSpec")
    policy = resolve_stopping_policy(root, stopping_policy if stopping_policy is not None else (spec.stopping_policy if spec is not None else None))
    if saved:
        if spec is not None and spec != saved[0]:
            raise ValueError("Requested experiment spec differs from the frozen E6 configuration")
        return saved[0]
    if spec is not None:
        if spec.stopping_policy != policy:
            raise ValueError("Requested stopping policy differs from experiment spec")
        return spec
    return replace(DEFAULT_RUN_SPEC, stopping_policy=policy)


def load_spec(path) -> ExperimentSpec:
    """Read a raw snapshot or a frozen proof/panel configuration without setup."""
    import json
    value = json.loads(path.read_text(encoding="utf-8-sig"))
    if not isinstance(value, Mapping):
        raise ValueError("Experiment snapshot must be a mapping")
    return ExperimentSpec.from_dict(value) if "model_display_name" in value else experiment_spec(value)


def resolve_panel_spec(root, spec: ExperimentSpec | None = None, stopping_policy: str | None = None) -> ExperimentSpec:
    """New panels count five healthy passes; frozen panels retain their policy."""
    if (spec is None and stopping_policy is None
            and not any((root / name).is_file() for name in ("panel-config.json", "config.json"))):
        spec = DEFAULT_PANEL_SPEC
    return resolve_spec(root, spec, stopping_policy)
