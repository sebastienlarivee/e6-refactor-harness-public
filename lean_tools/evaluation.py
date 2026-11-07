"""Public fresh evaluation boundary for trusted finalization and replay.

Fresh evaluation validates one candidate and launches the existing evaluator
without reading or writing the evaluation-result cache. Environment and helper
caches remain available to avoid rebuilding expensive Lean setup.
"""
from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import time
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from lean_tools.arena_workflow import Evaluation


def evaluate_candidate_fresh(
    task_path: Path,
    candidate_path: Path,
    project_root: Path,
    timeout_seconds: int = 600,
    quick: bool = False,
    environment_fingerprint: str | None = None,
    *,
    scoring_policy: str | None = None,
) -> Evaluation:
    from lean_tools.arena_workflow import evaluate_candidate_fresh as evaluate

    started = time.perf_counter()
    result = evaluate(
        task_path,
        candidate_path,
        project_root,
        timeout_seconds=timeout_seconds,
        quick=quick,
        environment_fingerprint=environment_fingerprint,
        scoring_policy=scoring_policy,
    )
    return replace(
        result,
        cache_status="disabled",
        cache_source_mode=None,
        request_wall_seconds=time.perf_counter() - started,
    )
