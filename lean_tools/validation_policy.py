"""Compatibility import for the explicit winner-only scalar selection policy.

Equality stays eligible for a later tie-break; this bound does not preserve the
full Pareto set or replace authoritative validity and compatibility checks.
"""
from lean_tools.scoring import OriginalDenominatorScorePolicy

__all__ = ["OriginalDenominatorScorePolicy"]
