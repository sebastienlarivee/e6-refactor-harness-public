"""Bounded source-only elaborator choices for the opt-in deep portfolio.

The whitelist contains reduction, unification, simplification and instance
algorithm choices only. Availability and complete-source preservation remain
the ordinary Lean evaluator's responsibility. No resource/axiom/kernel/counter
setting is accepted from callers.
"""
from __future__ import annotations

from .source_proposals import _sites, _sequences

DEEP_OPTIONS = (
    "simprocs", "smartUnfolding",
    "backward.isDefEq.respectTransparency",
    "backward.isDefEq.respectTransparency.types",
    "backward.isDefEq.lazyWhnfCore", "backward.isDefEq.lazyProjDelta",
    "backward.isDefEq.implicitBump", "backward.synthInstance.canonInstances",
    "tactic.skipAssignedInstances", "backward.dsimp.proofs", "backward.dsimp.instances",
)
REGIONAL_OPTIONS = ("simprocs", "smartUnfolding", "tactic.skipAssignedInstances")
MAX_REGIONAL_SITES = 8
FAMILIES = ("regional_option_wrapper", "option_wrapper_prune")


def _indent_region(source: str, start: int, end: int) -> str | None:
    column = start - source.rfind("\n", 0, start) - 1
    lines = source[start:end].splitlines(keepends=True)
    output = []
    for index, line in enumerate(lines):
        content = line.rstrip("\r\n")
        ending = line[len(content):]
        if not content.strip():
            output.append(ending)
            continue
        if index:
            prefix = content[:column]
            if prefix != " " * column:
                return None
            content = content[column:]
        output.append(" " * (column + 2) + content + ending)
    return "".join(output) if output else None


def regional_options(source: str, tokens: list, minimum: int,
                     *, max_sites: int = MAX_REGIONAL_SITES) -> list[dict]:
    """Wrap conservative layout sibling suffixes; comments/bullets abstain.

    Regions are alternatives, never simultaneous edits. Bigger suffixes and
    diverse end locations precede finer suffixes; at most eight are emitted.
    The unchanged continuation is retained by the source-span edit contract.
    """
    if type(max_sites) is not int or not 0 <= max_sites <= MAX_REGIONAL_SITES:
        raise ValueError(f"max_sites must be an integer in 0..{MAX_REGIONAL_SITES}")
    sites = _sites(source, tokens, minimum)
    regions = set()
    for sequence in _sequences(source, sites):
        # A singleton site is useful too: it scopes an option to a normalizer
        # without changing elaboration of the subsequent tactic sequence.
        for index in range(len(sequence)):
            start, end = sequence[index].start, sequence[-1].end
            text = source[start:end]
            if not any(marker in text for marker in ("--", "/-", "-/", "\t", "`")):
                regions.add((start, end))
    ranked = sorted(regions, key=lambda span: (-(span[1] - span[0]), span))
    # One region per end location first; do not spend all eight sites on the
    # suffixes of a single long outer sequence.
    diverse, remaining, ends = [], [], set()
    for span in ranked:
        if span[1] in ends:
            remaining.append(span)
        else:
            diverse.append(span)
            ends.add(span[1])
    newline = "\r\n" if "\r\n" in source else "\n"
    result = []
    for start, end in (diverse + remaining)[:max_sites]:
        nested = _indent_region(source, start, end)
        if nested is None:
            continue
        for name in REGIONAL_OPTIONS:
            for value in ("false", "true"):
                result.append({"family": "regional_option_wrapper", "site": start,
                               "description": f"Set regional {name} {value}",
                               "option": name, "value": value,
                               "region_start": start, "region_end": end,
                               "edits": [{"start": start, "end": end,
                                          "old": source[start:end],
                                          "new": f"set_option {name} {value} in{newline}" + nested}]})
    return result


def outer_wrapper_pruning(source: str, tokens: list, assignment: int) -> list[dict]:
    """Remove one whitelisted outer term wrapper while keeping its term exact."""
    result = []
    cursor = assignment + 1
    while cursor + 4 < len(tokens) and tokens[cursor].text == "set_option":
        head, name, value, scope, term = tokens[cursor:cursor + 5]
        if name.text not in DEEP_OPTIONS or value.text not in {"true", "false"} or scope.text != "in":
            break
        gap = source[head.start:term.start]
        if any(marker in gap for marker in ("--", "/-", "-/")):
            break
        result.append({"family": "option_wrapper_prune", "site": head.start,
                       "description": f"Remove outer proof-local {name.text} wrapper",
                       "option": name.text,
                       "edits": [{"start": head.start, "end": term.start,
                                  "old": gap, "new": ""}]})
        cursor += 4
    return result
