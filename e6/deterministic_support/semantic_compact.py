"""Source-bound formatting of native semantic proposals before score pruning.

The default semantic generator is unchanged. This adapter adds at most two
compact forms per known exact-term edit and performs no further native work.
All originals and variants still require the complete ordinary validator.
"""
from __future__ import annotations

from hashlib import sha256

from lean_tools.proof_specialization import lex
from . import mutations as m, semantic_search
from .edit_packs import OFFSET_UNIT

GENERATOR_FILES = (
    "e6/deterministic_support/semantic_compact.py",
    *semantic_search.GENERATOR_FILES,
    "e6/deterministic_support/mutations.py", "e6/deterministic_support/edit_packs.py",
    "e6/deterministic_candidates.py", "lean_tools/proof_specialization.py",
    "lean_tools/lean_launch.py", "lean_tools/resource_gate.py", "lean_tools/process_memory.py",
)
FAMILIES = ("semantic_solvers", "semantic_original")


def _digest(text):
    return sha256(text.encode("utf-8")).hexdigest()


def _wrapped_term(replacement):
    """Recognize exactly one semantic `exact (TERM)` command, not a prefix."""
    if not isinstance(replacement, str) or any(x in replacement for x in ("--", "/-", "-/", "`")):
        return None
    try:
        tokens = lex(replacement)
    except ValueError:
        return None
    if (len(tokens) < 4 or tokens[0].text != "exact" or tokens[1].text != "("
            or m._matching_close(tokens, 1) != len(tokens) - 1
            or replacement[:tokens[0].start].strip()
            or replacement[tokens[-1].end:].strip()):
        return None
    term = replacement[tokens[1].end:tokens[-1].start]
    if not semantic_search._safe_term(term):
        return None
    return term.strip()


def compact_candidates(source: str, signature: str, candidates: list[dict]) -> list[dict]:
    """Replay known edits, returning originals plus bounded compact variants.

    No output cap is applied here: the discovery cap bounds originals, and the
    result has at most three times as many rows. Compact forms sort first so a
    downstream source/score bound sees them before redundant wrappers.
    """
    from e6 import deterministic_candidates as dc
    if not isinstance(source, str) or not isinstance(signature, str):
        raise TypeError("source and signature must be strings")
    if len(source) > dc.MAX_SOURCE_CHARS or not signature:
        return []
    try:
        tokens = lex(source)
        assignment = m._assignment_index_after_signature(source, tokens, signature)
        if assignment is None or len(tokens) > dc.MAX_TOKENS:
            return []
        signature_start = source.index(signature)
        if [(t.kind, t.text, t.start - signature_start, t.end - signature_start)
            for t in tokens if signature_start <= t.start < signature_start + len(signature)] != [
                (t.kind, t.text, t.start, t.end) for t in lex(signature)]:
            return []
        minimum = tokens[assignment].end
        maximum = dc._declaration_end(source, tokens, assignment, signature_start)
        if maximum is None:
            return []
    except (ValueError, IndexError):
        return []
    parent, seen, result = _digest(source), {source}, []

    def emit(row, start, end, new, kind):
        child = dc._apply(source, [{"start": start, "end": end, "new": new}], minimum, maximum)
        if child is None or child in seen:
            return
        seen.add(child)
        digest, old = _digest(child), source[start:end]
        result.append({**row, "source": child, "source_sha256": digest,
                       "parent_sha256": parent, "id": row["family"] + ":compact:" + digest[:16],
                       "site": start, "compaction": kind,
                       "replaced_chars": len(old),
                       "semantic_candidate_sha256": row["source_sha256"],
                       "description": "Compact a source-bound native semantic exact-term representation",
                       "requires_full_validation": True,
                       "validation_required": "complete_source_exact_axioms_and_compatibility",
                       "edits": [{"start": start, "end": end, "old": old, "new": new,
                                  "old_sha256": _digest(old), "new_sha256": _digest(new),
                                  "offset_unit": OFFSET_UNIT}]})

    for row in candidates[:semantic_search.MAX_CANDIDATES]:
        if not isinstance(row, dict) or row.get("family") not in {
                semantic_search.SOLVER_FAMILY, semantic_search.ORIGINAL_FAMILY,
                semantic_search.NORMALIZE_FAMILY}:
            continue
        edits = row.get("edits")
        if not isinstance(edits, list) or len(edits) != 1 or not isinstance(edits[0], dict):
            continue
        edit = edits[0]
        a, b = edit.get("start"), edit.get("end")
        if (type(a) is not int or type(b) is not int or not minimum <= a < b <= maximum
                or edit.get("offset_unit") != OFFSET_UNIT or edit.get("old") != source[a:b]
                or edit.get("old_sha256") != _digest(source[a:b])
                or row.get("parent_sha256") != parent or row.get("requires_full_validation") is not True):
            continue
        replacement = edit.get("new")
        term = _wrapped_term(replacement)
        if term is None or edit.get("new_sha256") != _digest(replacement):
            continue
        child = source[:a] + replacement + source[b:]
        if row.get("source") != child or row.get("source_sha256") != _digest(child):
            continue
        if child not in seen:
            seen.add(child)
            result.append(row)
        if "\n" not in replacement and "\r" not in replacement:
            emit(row, a, b, "exact " + term, "exact_term_parentheses")
        before = [(index, token) for index, token in enumerate(tokens) if token.end <= a]
        after = [token for token in tokens if token.start >= b]
        if len(before) < 2 or not after:
            continue
        (open_index, opening), (_, by) = before[-2:]
        closing = after[0]
        if (opening.text != "(" or by.text != "by" or closing.text != ")"
                or by.start < minimum or source[opening.end:by.start].strip()
                or source[by.end:a].strip() or source[b:closing.start].strip()
                or m._matching_close(tokens, open_index) is None):
            continue
        close_index = m._matching_close(tokens, open_index)
        if tokens[close_index].start != closing.start:
            continue
        emit(row, by.start, b, term, "whole_parenthesized_by_term")
    return sorted(result, key=lambda row: (len(row["source"]), row.get("site", 0), row["id"]))


def generate_candidates(*, config: dict, source: str, signature: str, workdir,
                        timeout_seconds=semantic_search.DEFAULT_TIMEOUT_SECONDS,
                        max_candidates=semantic_search.DEFAULT_MAX_CANDIDATES, family=None):
    """Run one unchanged semantic discovery, then compact before score pruning.

    max_candidates is the native discovery cap; expanded output is <=3x this
    cap (hard maximum 768), ordered shortest-first for the caller's final cap.
    """
    family = "semantic_solvers" if family is None else family
    if family not in FAMILIES:
        raise ValueError("semantic_compact supports semantic_solvers and semantic_original")
    originals = semantic_search.generate_candidates(config=config, source=source, signature=signature,
        workdir=workdir, timeout_seconds=timeout_seconds, max_candidates=max_candidates, family=family)
    return compact_candidates(source, signature, originals)
