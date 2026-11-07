"""Bounded generic Lean proposals derived solely from the current source.

This module does no I/O, starts no process and knows no benchmark labels. A
proposal is evidence for the ordinary full-source evaluator, never a proof of
preservation or an assertion that a transformation improves performance.

The source-span cleanup helpers were adapted from the October deterministic
cleanup experiment; scheduling and normalization helpers retain its general
source-only mechanisms, without importing its evaluator, inputs or results.
"""
from __future__ import annotations

from collections import defaultdict
from hashlib import sha256
import re
from typing import Any

from lean_tools.proof_specialization import lex
from .deterministic_support import mutations
from .deterministic_support.source_proposals import EXTRA_FAMILIES, extra_proposals
from .deterministic_support import deep_options, edit_packs

MAX_CANDIDATES = 256
# Refuse pathological source inventories before constructing a quadratic scan.
MAX_SOURCE_CHARS = 500_000
MAX_TOKENS = 40_000
FAMILIES = (*mutations.FAMILIES, *EXTRA_FAMILIES, "elaborator_option")
OPTIONS = (
    "backward.isDefEq.respectTransparency",
    "backward.isDefEq.lazyWhnfCore",
    "backward.isDefEq.lazyProjDelta",
    "smartUnfolding",
)
DEEP_FAMILIES = (*FAMILIES, *deep_options.FAMILIES, *edit_packs.FAMILIES)
_COMMAND_HEADS = frozenset({
    "theorem", "lemma", "def", "abbrev", "instance", "example", "axiom", "opaque",
    "structure", "inductive", "coinductive", "class", "initialize", "builtin_initialize", "namespace",
    "section", "end", "open", "set_option", "attribute", "mutual", "export",
    "import", "prelude", "universe", "universes", "variable", "variables",
    "include", "omit", "macro", "macro_rules", "elab", "elab_rules", "notation",
    "syntax", "private", "protected", "public", "noncomputable", "unsafe", "meta",
    "local", "scoped", "nonrec", "partial", "irreducible", "deriving",
})
_TARGET_END = re.compile(r"(?m)^-- ARENA TARGET END(?:\r?\n|$)")


def _digest(source: str) -> str:
    return sha256(source.encode("utf-8")).hexdigest()


def _outer_by(tokens: list, assignment: int) -> int | None:
    cursor = assignment + 1
    while (cursor + 3 < len(tokens) and tokens[cursor].text == "set_option"
           and tokens[cursor + 1].kind == "id"
           and tokens[cursor + 2].text in {"true", "false"}
           and tokens[cursor + 3].text == "in"):
        cursor += 4
    return cursor if cursor < len(tokens) and tokens[cursor].text == "by" else None


def _declaration_end(source: str, tokens: list, assignment: int, signature_start: int) -> int | None:
    """Bound a target by its scaffold marker or a later layout-level command.

    This is intentionally a lexical boundary, not a Lean parser. A marker in an
    unfinished comment/string is not a boundary. At an unmarked module target,
    only line-leading commands at the declaration's indentation end its body.
    Trailing comments and whitespace are retained outside the editable span.
    """
    minimum = tokens[assignment].end
    limit = len(source)
    markers = list(_TARGET_END.finditer(source, minimum))
    if markers:
        if len(markers) != 1:
            return None
        limit = markers[0].start()
        try:
            lex(source[:limit])
        except (ValueError, IndexError):
            return None
    line = source.rfind("\n", 0, signature_start) + 1
    prefix = source[line:signature_start]
    if prefix.strip() or "\t" in prefix:
        return None
    indent = len(prefix)
    outer_by = _outer_by(tokens, assignment)
    stack = []
    end = None
    for index, token in enumerate(tokens[assignment + 1:], assignment + 1):
        if token.start >= limit:
            break
        line = source.rfind("\n", 0, token.start) + 1
        prefix = source[line:token.start]
        if (end is not None and not stack and not prefix.strip()
                and (outer_by is None or index > outer_by)
                and len(prefix) <= indent
                and (token.text in _COMMAND_HEADS or token.text in {"#", "@"})):
            break
        if token.text in mutations._OPEN_TO_CLOSE:
            stack.append(mutations._OPEN_TO_CLOSE[token.text])
        elif token.text in mutations._CLOSE:
            if not stack or stack.pop() != token.text:
                return None
        end = token.end
    return None if stack else end


def _options(source: str, tokens: list, assignment: int, options: tuple = OPTIONS,
             *, bounded_existing: bool = False) -> list[dict]:
    # A term-level scoped option before `by` leaves the tactic layout intact.
    # Recognize existing outer scoped options as well as a direct `:= by`.
    if _outer_by(tokens, assignment) is None:
        return []
    start = tokens[assignment + 1].start
    existing = defaultdict(list)
    for index, token in enumerate(tokens[:-3]):
        if token.start >= start and token.text == "set_option":
            name, value, scope = tokens[index + 1:index + 4]
            if name.text in options and value.text in {"true", "false"} and scope.text == "in":
                existing[name.text].append(value)
    result = []
    for name in options:
        if name in existing:
            values = existing[name]
            if bounded_existing and len(values) > 2:
                values = [values[0], values[-1]]
            for token in values:
                value = "false" if token.text == "true" else "true"
                result.append({"family": "elaborator_option", "site": token.start,
                               "description": f"Toggle proof-local {name}",
                               "edits": [{"start": token.start, "end": token.end, "new": value}]})
        else:
            for value in ("false", "true"):
                new = f"set_option {name} {value} in "
                result.append({"family": "elaborator_option", "site": start,
                               "description": f"Set proof-local {name} {value}",
                               "edits": [{"start": start, "end": start, "new": new}]})
    return result


def _apply(source: str, edits: list[dict], minimum: int, maximum: int) -> str | None:
    """Check source binding and disjoint Unicode spans before applying edits."""
    if any(not isinstance(edit, dict) or type(edit.get("start")) is not int
           or type(edit.get("end")) is not int or not isinstance(edit.get("new"), str)
           for edit in edits):
        return None
    cursor = maximum
    output = source
    for edit in sorted(edits, key=lambda value: (value["start"], value["end"]), reverse=True):
        a, b = edit["start"], edit["end"]
        if not (minimum <= a <= b <= cursor):
            return None
        if "old" in edit and source[a:b] != edit["old"]:
            return None
        output = output[:a] + edit["new"] + output[b:]
        cursor = a
    return output


def generate(source: str, signature: str, *, max_candidates: int = 256,
             deep: bool = False) -> list[dict[str, Any]]:
    """Return deterministic, deduplicated, family/site-balanced proposals.

    The exact signature must occur once and be immediately followed by the
    declaration assignment (apart from whitespace). Every edit stays in that
    declaration's proof body; its prefix and suffix remain exact source slices.
    Offsets are Python Unicode codepoints, zero-based/end-exclusive.
    Invalid or unsupported Lean syntax fails closed; request-shape errors raise.
    """
    if not isinstance(source, str):
        raise TypeError("source must be str")
    if not isinstance(signature, str):
        raise TypeError("signature must be str")
    if type(max_candidates) is not int or not 0 <= max_candidates <= MAX_CANDIDATES:
        raise ValueError(f"max_candidates must be an integer in 0..{MAX_CANDIDATES}")
    if type(deep) is not bool:
        raise ValueError("deep must be a boolean")
    if not max_candidates or not signature or len(source) > MAX_SOURCE_CHARS:
        return []
    try:
        tokens = lex(source)
    except (ValueError, IndexError):
        return []
    if len(tokens) > MAX_TOKENS:
        return []
    assignment = mutations._assignment_index_after_signature(source, tokens, signature)
    if assignment is None:
        return []
    minimum = tokens[assignment].end
    signature_start = source.index(signature)
    # An exact signature inside a comment or identifier is not a declaration.
    signature_tokens = lex(signature)
    if not signature_tokens or [
        (token.kind, token.text, token.start - signature_start, token.end - signature_start)
        for token in tokens if signature_start <= token.start < signature_start + len(signature)
    ] != [(token.kind, token.text, token.start, token.end) for token in signature_tokens]:
        return []
    maximum = _declaration_end(source, tokens, assignment, signature_start)
    if maximum is None:
        return []
    # Existing families see only the target, so suffix syntax cannot become an
    # edit site or a lexical dependency. All original offsets remain unchanged.
    target = source[:maximum]
    tokens = [token for token in tokens if token.start < maximum]
    # Quotations, escaped names and strings may hide identifiers/binder uses;
    # decline rather than draw false source dependency conclusions.
    if any(t.start >= minimum and (t.text == "`" or t.kind in {"escaped", "opaque"}) for t in tokens):
        return []
    stack = []
    for token in tokens:
        if token.start < minimum:
            continue
        if token.text in mutations._OPEN_TO_CLOSE:
            stack.append(mutations._OPEN_TO_CLOSE[token.text])
        elif token.text in mutations._CLOSE:
            if not stack or stack.pop() != token.text:
                return []
    if stack:
        return []

    proposals = []
    # Ask each core family independently: a long deletion inventory cannot
    # exhaust the helper cap before another family's first proposal is seen.
    for family in mutations.FAMILIES:
        proposals.extend(mutations.generate(target, max_candidates=MAX_CANDIDATES,
                                            families=(family,), signature=signature))
    proposals.extend(extra_proposals(target, tokens, minimum))
    proposals.extend(_options(target, tokens, assignment,
                              deep_options.DEEP_OPTIONS if deep else OPTIONS,
                              bounded_existing=deep))
    if deep:
        proposals.extend(deep_options.regional_options(target, tokens, minimum))
        proposals.extend(deep_options.outer_wrapper_pruning(target, tokens, assignment))
        proposals.extend(edit_packs.compose(source, proposals, minimum=minimum, maximum=maximum))
    families = DEEP_FAMILIES if deep else FAMILIES

    by_family: dict[str, dict[int, list[dict]]] = defaultdict(lambda: defaultdict(list))
    for item in proposals:
        edits = item["edits"]
        if edits:
            site = item.get("site", min(edit["start"] for edit in edits))
            by_family[item["family"]][site].append(item)
    queues = {}
    for family in families:
        sites = by_family[family]
        # Round-robin source sites inside a family as well as families outside.
        sites_in_order = sorted(sites)
        queue = []
        for depth in range(max((len(sites[site]) for site in sites_in_order), default=0)):
            for site in sites_in_order:
                if depth < len(sites[site]):
                    queue.append(sites[site][depth])
        queues[family] = queue

    parent = _digest(source)
    seen = {parent}
    result = []

    def admit(item: dict, family: str) -> dict | None:
        child = _apply(source, item["edits"], minimum, maximum)
        if child is None:
            return None
        digest = _digest(child)
        if digest in seen:
            return None
        seen.add(digest)
        metadata = {key: value for key, value in item.items()
                    if key not in {"source", "declaration", "id", "edits"}}
        edits = [{**edit, "old": source[edit["start"]:edit["end"]],
                  "offset_unit": "unicode_codepoints_zero_based_end_exclusive"}
                 for edit in item["edits"]]
        return {**metadata, "id": f"{family}:{digest[:16]}", "family": family,
                "source": child, "parent_sha256": parent,
                "source_sha256": digest, "edits": edits,
                "requires_full_validation": True}

    if deep:
        from .deterministic_support.search_policy import order_candidates
        # Schedule the bounded raw inventory before materializing/capping child
        # sources. Reserve this small whitelist so adding deletion sites cannot
        # hide its latter settings. The engine still owns evaluation ordering.
        option_items = queues["elaborator_option"]
        others = [item for family, queue in queues.items() if family != "elaborator_option" for item in queue]
        ordered = option_items + order_candidates(others, policy="deep", maximum=MAX_CANDIDATES)
        for item in ordered:
            candidate = admit(item, item["family"])
            if candidate is not None:
                result.append(candidate)
            if len(result) == max_candidates:
                break
        return result

    cursors = {family: 0 for family in families}
    while len(result) < max_candidates:
        advanced = False
        for family in families:
            queue = queues[family]
            # Duplicate/invalid candidates do not consume this family's turn.
            while cursors[family] < len(queue):
                advanced = True
                item = queue[cursors[family]]
                cursors[family] += 1
                candidate = admit(item, family)
                if candidate is None:
                    continue
                result.append(candidate)
                break
            if len(result) == max_candidates:
                return result
        if not advanced:
            break
    return result
