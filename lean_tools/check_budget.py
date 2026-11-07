"""Context-local wall budget for quick feedback; exact scoring keeps its contract."""
from __future__ import annotations

from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass
from functools import wraps
import inspect
import math
import time
from typing import Callable

DEFAULT_QUICK_SECONDS = 60.0
MAX_QUICK_SECONDS = 600.0
CLEANUP_GRACE_SECONDS = 5.0


class DeadlineExpired(TimeoutError):
    def __init__(self, stage: str) -> None:
        super().__init__(f"quick request deadline expired during {stage}")
        self.code = "queue_timeout" if any(word in stage for word in ("queue", "lock", "admission")) else "operation_timeout"
        self.stage = stage


@dataclass
class Budget:
    deadline: float
    seconds: float
    stage: str = "setup"
    observe: Callable | None = None


_current: ContextVar[Budget | None] = ContextVar("lean_quick_budget", default=None)


def current() -> Budget | None:
    return _current.get()


def validate_seconds(value: float, *, maximum: float | None = MAX_QUICK_SECONDS) -> float:
    if (isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value)
            or value <= 0 or (maximum is not None and value > maximum)):
        limit = f", and at most {maximum:g}" if maximum is not None else ""
        raise ValueError(f"quick timeout_seconds must be finite and positive{limit}")
    return float(value)


def remaining(default: float | None = None) -> float | None:
    budget = current()
    if budget is None:
        return default
    value = budget.deadline - time.monotonic()
    if value <= 0:
        raise DeadlineExpired(budget.stage)
    return min(default, value) if default is not None else value


def stage(name: str, **details) -> None:
    budget = current()
    if budget is not None:
        budget.stage = name
        if budget.observe is not None:
            budget.observe(name, budget, details)
        remaining()


@contextmanager
def scope(seconds: float, *, started: float | None = None, observe: Callable | None = None):
    # The agent-facing edit_check validates its own <=600-second cap. Trusted
    # preparation/compatibility callers have separate explicit allowances (for
    # example 1800 seconds) and must not inherit that tool-intake restriction.
    seconds = validate_seconds(seconds, maximum=None)
    parent = current()
    deadline = (time.monotonic() if started is None else started) + seconds
    if parent is not None:
        deadline = min(deadline, parent.deadline)
        observe = observe or parent.observe
    budget = Budget(deadline, seconds, observe=observe)
    token = _current.set(budget)
    try:
        yield budget
    finally:
        _current.reset(token)


def quick_evaluation(operation):
    """Share an enclosing request, or honor a trusted caller's explicit budget."""
    signature = inspect.signature(operation)

    @wraps(operation)
    def bounded(*args, **kwargs):
        arguments = signature.bind(*args, **kwargs).arguments
        if not arguments.get("quick", False) or current() is not None:
            return operation(*args, **kwargs)
        seconds = arguments.get("timeout_seconds", DEFAULT_QUICK_SECONDS)
        with scope(seconds):
            return operation(*args, **kwargs)
    return bounded
