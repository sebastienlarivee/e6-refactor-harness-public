"""Versioned scoring policy selection for candidate measurement.

An absent policy keeps historical configurations on their original semantics.
Fresh Arena experiments select arena-v1 explicitly in their frozen settings.
"""
from __future__ import annotations

from contextlib import contextmanager
from contextvars import ContextVar
import os
from typing import Iterator

from lean_tools.workflow_errors import WorkflowError

LEGACY_POLICY = LEGACY = "legacy-v1"
ARENA_POLICY = ARENA = "arena-v1"
SCORING_POLICY_ENV = "LEAN_REFACTOR_SCORING_POLICY"
_SUPPORTED_POLICIES = {LEGACY_POLICY, ARENA_POLICY}
_SCORING_POLICY: ContextVar[str | None] = ContextVar("lean_refactor_scoring_policy", default=None)


def resolve_scoring_policy(value: str | None = None) -> str:
    """Resolve an explicit policy, scoped policy, environment, then legacy."""
    policy = value if value is not None else _SCORING_POLICY.get()
    if policy is None:
        policy = os.environ.get(SCORING_POLICY_ENV, LEGACY_POLICY)
    if not isinstance(policy, str) or policy not in _SUPPORTED_POLICIES:
        raise WorkflowError(f"unsupported scoring policy: {policy!r}")
    return policy


@contextmanager
def scoring_policy_context(policy: str) -> Iterator[str]:
    """Select one policy for nested calls without mutating process environment."""
    resolved = resolve_scoring_policy(policy)
    token = _SCORING_POLICY.set(resolved)
    try:
        yield resolved
    finally:
        _SCORING_POLICY.reset(token)


def candidate_token_offset(policy: str | None = None) -> int:
    """The Arena candidate metric includes one presumed assignment token."""
    return 1 if resolve_scoring_policy(policy) == ARENA_POLICY else 0
