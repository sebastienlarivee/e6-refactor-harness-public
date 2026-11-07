"""Generic, source-independent scheduling for deterministic proposal inventories.

The legacy policy preserves its caller's inventory exactly. The opt-in policies
prioritize normalization and cleanup while retaining a small, bounded sample of
broad native exploration. No proof text, task identity or past results are read.
"""
from __future__ import annotations

from collections import defaultdict, deque
from typing import Iterable


POLICIES = ("legacy", "prioritized", "regional", "deep", "compact")
# Eight priority proposals per cycle leave room for other generic families.
PRIORITY_BATCH = 8
MAX_TERM_EXPLORATION = 16
MAX_WINDOW_EXPLORATION = 8

PRIORITY_FAMILIES = (
    "normalization_fusion", "normalization_delay", "rw_simp_conversion",
    "simp_list_delete", "solver_list_delete", "simp_list_normalize",
    "simp_list_chunk_delete", "solver_list_chunk_delete", "native-rule-subset",
    "native-delete-wrapper",
)
COMPACT_PRIORITY_FAMILIES = ("semantic_search_solver_term", *PRIORITY_FAMILIES)
REGIONAL_PRIORITY_FAMILIES = (
    "native-regional-normalization-delay", "native-regional-opaque-normalization-delay",
    "native-regional-prune", "native-regional-unused-local",
    "native-regional-repair", "native-regional-opaque-repair",
)
# Deep search gives a scoped elaborator option an early turn, alongside ordinary
# cleanup. Keep the older schedules byte-for-byte equivalent for clean ablations.
DEEP_PRIORITY_FAMILIES = (
    "native-delete-wrapper", "elaborator_option", "compiler_simp_specialization", "normalization_fusion",
    "rw_simp_conversion", "simp_list_delete", "solver_list_delete",
    "simp_list_normalize", "simp_list_chunk_delete", "solver_list_chunk_delete",
    "native-rule-subset", "same_edit_batch", "compatible_edit_pack", "regional_option_wrapper", "normalization_delay",
    *REGIONAL_PRIORITY_FAMILIES,
)
TERM_FAMILIES = frozenset({
    "native-normal", "native-explicit", "inferred-type", "normalized-type",
    "named-instance", "named-implicit", "normalized-type-argument",
    "selective-instance", "selective-implicit",
})
WINDOW_FAMILIES = frozenset({"native-delete-window", "native-subset-delete-window"})


def exploration_quotas(maximum: int) -> dict[str, int]:
    """Return per-inventory bounds, scaled down for small candidate budgets."""
    if type(maximum) is not int or not 0 <= maximum <= 4096:
        raise ValueError("maximum must be an integer in 0..4096")
    return {"native_terms": min(MAX_TERM_EXPLORATION, maximum // 16),
            "blind_windows": min(MAX_WINDOW_EXPLORATION, maximum // 32)}


def _balanced(items: list[dict], family_order: tuple[str, ...] = ()) -> deque[dict]:
    """Round-robin across families, retaining original order within each family."""
    groups: dict[str, deque[dict]] = defaultdict(deque)
    for item in items:
        groups[str(item.get("family", "")) if isinstance(item, dict) else ""].append(item)
    preferred = {family: index for index, family in enumerate(family_order)}
    # Dict insertion order keeps unfamiliar generic families stable, without
    # deriving priority from task names, source content or source hashes.
    families = sorted(groups, key=lambda family: preferred.get(family, len(preferred)))
    result = deque()
    while families:
        for family in families:
            result.append(groups[family].popleft())
        families = [family for family in families if groups[family]]
    return result


def order_candidates(items: Iterable[dict], *, policy: str, maximum: int) -> list[dict]:
    """Order one parent inventory, with explicit exploration bounds when enabled.

    ``legacy`` does not truncate: its historic merged inventory can exceed the
    evaluation cap, and duplicate skipping belongs to the caller. Opt-in policies
    return at most ``maximum`` entries. All policies preserve candidate metadata.
    """
    if not isinstance(policy, str) or policy not in POLICIES:
        raise ValueError("policy must be legacy, prioritized, regional, deep or compact")
    quotas = exploration_quotas(maximum)
    inventory = list(items)
    if maximum == 0:
        return []
    if policy == "legacy":
        return inventory
    # Exercise the regional treatment before a standard winner can trigger a
    # rebase and replace this parent inventory. Other policies retain their
    # exact ordering; full candidate validation still decides acceptance.
    priority_order = (COMPACT_PRIORITY_FAMILIES if policy == "compact" else
                      DEEP_PRIORITY_FAMILIES if policy == "deep" else
                      REGIONAL_PRIORITY_FAMILIES + PRIORITY_FAMILIES
                      if policy == "regional" else PRIORITY_FAMILIES)
    if policy == "compact":
        # Deduplicate before the final cap. Prefer semantic metadata for a source
        # also found by cleanup, so duplicate proposals cannot consume its turn.
        semantic = priority_order[0]
        preferred_sources = {item["source"] for item in inventory if isinstance(item, dict)
                             and item.get("family") == semantic and isinstance(item.get("source"), str)}
        seen_sources, unique = set(), []
        for item in inventory:
            source = item.get("source") if isinstance(item, dict) else None
            if isinstance(source, str):
                if source in seen_sources or source in preferred_sources and item.get("family") != semantic:
                    continue
                seen_sources.add(source)
            unique.append(item)
        inventory = unique
    priority_families = frozenset(priority_order)
    groups: dict[str, list[dict]] = {name: [] for name in ("priority", "other", "terms", "windows")}
    for item in inventory:
        family = str(item.get("family", "")) if isinstance(item, dict) else ""
        group = ("priority" if family in priority_families else "terms" if family in TERM_FAMILIES
                 else "windows" if family in WINDOW_FAMILIES else "other")
        groups[group].append(item)
    priority = _balanced(groups["priority"], priority_order)
    other = _balanced(groups["other"])
    terms = _balanced(groups["terms"])
    windows = _balanced(groups["windows"])
    # The caps apply to each whole broad category, rather than independently
    # to every term/window family, so adding variants cannot expand the quota.
    terms = deque(list(terms)[:quotas["native_terms"]])
    windows = deque(list(windows)[:quotas["blind_windows"]])
    ordered = []
    while len(ordered) < maximum and any((priority, other, terms, windows)):
        for queue, count in ((priority, PRIORITY_BATCH), (other, 1), (terms, 1), (windows, 1)):
            for _ in range(min(count, len(queue), maximum - len(ordered))):
                ordered.append(queue.popleft())
    return ordered


def should_rebase(*, enabled: bool, rebases: int, maximum_rebases: int) -> bool:
    """Keep immediate regeneration a separate, explicitly bounded ablation."""
    if type(enabled) is not bool:
        raise ValueError("enabled must be a boolean")
    for name, value in (("rebases", rebases), ("maximum_rebases", maximum_rebases)):
        if type(value) is not int or value < 0:
            raise ValueError(f"{name} must be a nonnegative integer")
    return enabled and rebases < maximum_rebases
