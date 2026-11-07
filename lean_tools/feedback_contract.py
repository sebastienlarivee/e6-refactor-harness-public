"""Capsule-scoped tool contracts, selected by frozen experiment settings."""

from __future__ import annotations

from collections.abc import Mapping
import math
from typing import Any

TOOL_NAME = "edit_check"

TOOL = {
    "name": TOOL_NAME,
    "description": "Edit literal Lean source and get feedback in one call. Quick checks default to a 60-second whole-request allowance, including queue, locks and diagnostics, plus bounded cleanup; timeout_seconds explicitly increases it up to the capsule maximum (at most 600). A timeout is inconclusive and never automatically replayed cold. Exact mode retains its per-process scoring/audit allowance. Quick success saves an immutable checkpoint; exact also audits axioms and measures heartbeats. Advisory counts are scheduling hints only. source_text is literal Lean text; legacy source is an alias. checkpoint_id loads a verified capsule checkpoint before optional edits. Copy-only clone (to a separate candidate), promote (to the main candidate), and restore operations do not evaluate; existing destinations require expected_sha256. Returned validity/measurements bind to source_sha256. Failed edits return a zero-based failed_edit_index, match_count and bounded source excerpt. Goal line/column are one-based. Full logs stay on disk.",
    "inputSchema": {
        "type": "object",
        "properties": {
            "candidate": {"type": "string"},
            "body": {"type": "string"},
            "source_text": {"type": "string", "description": "Literal complete Lean source, never a filename or checkpoint path."},
            "source": {"type": "string", "description": "Legacy alias for source_text; use only one source field."},
            "checkpoint_id": {"type": "string", "description": "Returned checkpoint basename in this capsule, with a matching validation receipt."},
            "operation": {"type": "string", "enum": ["check", "clone", "promote", "restore"]},
            "expected_sha256": {"type": "string", "pattern": "^[0-9a-f]{64}$"},
            "mode": {"type": "string", "enum": ["quick", "advisory", "exact"]},
            "timeout_seconds": {"type": "number", "exclusiveMinimum": 0, "maximum": 600, "default": 60,
                                "description": "Quick mode only: whole-request wall allowance; default min(60, capsule timeout), explicit escalation up to min(600, capsule timeout). Timeout leaves validity unknown; exact scoring keeps its configured per-process allowance."},
            "edits": {
                "type": "array",
                "items": {
                    "type": "object",
                    "properties": {
                        "old": {"type": "string"},
                        "new": {"type": "string"},
                    },
                    "required": ["old", "new"],
                    "additionalProperties": False,
                },
            },
            "goal": {
                "type": "object",
                "properties": {
                    "line": {"type": "integer", "minimum": 1},
                    "column": {"type": "integer", "minimum": 1},
                },
                "required": ["line"],
                "additionalProperties": False,
            },
        },
        "additionalProperties": False,
    },
}


FEATURE_TOOLS = {"candidate_batches": "compare_candidates", "goal_retrieval": "retrieve_lemmas",
                 "search_extensions": "suggest_proof", "unfinished_cases": "unfinished_cases",
                 "regional_profiler": "profile_proof"}


def score_capability(settings: Mapping[str, Any] | None = None) -> bool:
    """Complete frozen host metadata enables scoring without the batch treatment."""
    if settings is not None and not isinstance(settings, Mapping):
        raise ValueError("feedback settings must be a mapping")
    supplied = settings or {}
    required = {"original_tokens", "original_heartbeats", "compatibility_roots"}
    present = required.intersection(supplied)
    if not present:
        return False
    if present != required:
        raise ValueError("complete scoring metadata requires original_tokens, original_heartbeats and compatibility_roots")
    from lean_tools.scoring import OriginalDenominatorScorePolicy
    OriginalDenominatorScorePolicy(supplied["original_tokens"], supplied["original_heartbeats"])
    roots = supplied["compatibility_roots"]
    if not isinstance(roots, list) or not all(isinstance(root, str) and root.strip() for root in roots):
        raise ValueError("compatibility_roots must be an array of nonempty paths")
    floor = supplied.get("incumbent_score")
    try:
        if not all(math.isfinite(supplied[name]) for name in ("original_tokens", "original_heartbeats")):
            raise ValueError("original scoring metrics must be finite positive integers")
        if floor is not None and (isinstance(floor, bool) or not isinstance(floor, (int, float))
                or not math.isfinite(floor) or floor > 100):
            raise ValueError("incumbent_score must be finite and at most 100")
    except OverflowError as error:
        raise ValueError("scoring metadata must be finite") from error
    return True


def feature_flags(settings: Mapping[str, Any] | None = None) -> dict[str, bool]:
    """Absent legacy settings disable features; coercion would change the arm."""
    if settings is not None and not isinstance(settings, Mapping):
        raise ValueError("feedback settings must be a mapping")
    flags = {name: (settings or {}).get(name, False) for name in FEATURE_TOOLS}
    for name, value in flags.items():
        if type(value) is not bool:
            raise ValueError(f"{name} must be a boolean")
    return flags


def enabled_tools(settings: Mapping[str, Any] | None = None) -> list[str]:
    """Return a fresh allowlist for the same settings used by the server."""
    flags = feature_flags(settings)
    return [TOOL_NAME, *(["compare_candidates"] if flags["candidate_batches"] else []),
            *(["score_candidate"] if score_capability(settings) else []),
            *(["retrieve_lemmas"] if flags["goal_retrieval"] else []),
            *(["suggest_proof", "search_examples", "example_neighbours"] if flags["search_extensions"] else []),
            *(["unfinished_cases"] if flags["unfinished_cases"] else []),
            *(["profile_proof"] if flags["regional_profiler"] else [])]


def tool_catalog(settings: Mapping[str, Any] | None = None) -> list[dict[str, Any]]:
    """Load optional contracts only in arms that expose their tools."""
    flags = feature_flags(settings)
    from copy import deepcopy
    quick_tool = deepcopy(TOOL)
    maximum = min(600, (settings or {}).get("timeout_seconds", 600))
    quick_tool["inputSchema"]["properties"]["timeout_seconds"].update(maximum=maximum, default=min(60, maximum))
    catalog = [quick_tool]
    if flags["candidate_batches"]:
        from lean_tools import candidate_batches
        catalog.append(candidate_batches.TOOL)
    if score_capability(settings):
        from lean_tools import candidate_batches
        catalog.append(candidate_batches.SCORE_TOOL)
    if flags["goal_retrieval"]:
        from lean_tools import goal_retrieval
        from lean_tools import rerank_service_client as reranking
        options, automatic = reranking.resolve_options()
        tool = goal_retrieval.TOOL
        if automatic:
            from copy import deepcopy
            tool = deepcopy(tool)
            limits = reranking.search_limit_contract(options, automatic, result_max=goal_retrieval.MAX_LIMIT, default_limit=8)
            properties = tool["inputSchema"]["properties"]
            pool_mode = (settings or {}).get("retrieval_pool_mode", "overlap")
            ranker = options["ranker"]
            properties["pool_mode"]["description"] = f"Frozen to {pool_mode} for this pass; omit this field or supply {pool_mode}."
            properties["name_query"]["description"] = (
                "Declaration words used by diverse or hybrid pool construction; ignored by the overlap pool frozen for this pass."
                if pool_mode == "overlap" else
                f"Declaration words used by the {pool_mode} pool frozen for this pass."
            )
            rerank_context = (
                "Baseline ordering ignores this field." if ranker == "baseline" else
                "JEV may use this field to order the same candidate pool." if ranker == "jev" else
                f"The frozen {ranker} reranker may use this field to order the same candidate pool."
            )
            properties["same_run_context"]["description"] = (
                "Context supplied to the frozen reranker; does not expand the candidate pool. " + rerank_context
            )
            properties["search_intent"]["description"] = (
                f"Mathematical operation used by {pool_mode} pool construction and supplied to the frozen reranker. "
                if pool_mode != "overlap" else
                "Context supplied to the frozen reranker; does not expand the candidate pool. "
            ) + (
                "Baseline reranking preserves the pool order constructed using this field."
                if ranker == "baseline" and pool_mode != "overlap" else rerank_context
            )
            tool["description"] += f" Frozen host pool: {pool_mode}; ranker: {ranker}."
            properties["limit"].update(maximum=limits["result_limit"]["maximum"], default=limits["result_limit"]["default"])
            properties["candidate_limit"].update(maximum=limits["candidate_limit"]["maximum"], default=limits["candidate_limit"]["default"],
                description="Number of candidates before ranking; must be at least limit and cannot exceed the frozen maximum.")
            tool["description"] += f" Frozen host limits: results 1..{limits['result_limit']['maximum']}, candidates limit..{limits['candidate_limit']['maximum']}."
        catalog.append(tool)
    if flags["search_extensions"]:
        from lean_tools import search_extensions
        catalog.extend(search_extensions.TOOLS)
    if flags["unfinished_cases"]:
        from lean_tools import unfinished_cases
        tool = unfinished_cases.TOOL
        if flags["goal_retrieval"]:
            tool = {**tool, "description": tool["description"]
                    + " Returned source-bound handles also work in retrieve_lemmas."}
        catalog.append(tool)
    if flags["regional_profiler"]:
        from lean_tools import regional_profiler
        from copy import deepcopy
        tool = deepcopy(regional_profiler.TOOL)
        capability = (settings or {}).get("profiler_capability")
        if isinstance(capability, dict):
            if capability.get("available") is True:
                tool["description"] += (
                    f" Capsule source form: {capability.get('source_form')}; supported modes: "
                    + ", ".join(capability.get("supported_modes", []))
                    + f". Default/maximum timeout per Lean process: {capability.get('default_timeout_seconds')}/{capability.get('max_timeout_seconds')} seconds. "
                    "Validation and profiling have separate process allowances; admission shares a separate "
                    f"{capability.get('shared_queue_wait_seconds', 10)}-second budget. No automatic retries.")
            else:
                tool["description"] += (
                    f" Unavailable for this capsule ({capability.get('outcome')}); "
                    "use ordinary quick checks and complete scoring instead of retrying profiling.")
        catalog.append(tool)
    if [tool["name"] for tool in catalog] != enabled_tools(settings):
        raise ValueError("configured tool contracts do not match the capsule allowlist")
    return catalog
