"""Deterministic, source-bound Lean proof mutation candidates.

This module proposes small edits only.  It does not parse or validate Lean
proofs; a complete Lean elaboration remains the authority for accepting a
candidate. Edits stay after the declaration assignment, in an outer ``by``
proof or a conservatively recognized interior ``by`` tactic block.
"""
from __future__ import annotations

import re
from typing import Any, Iterable

from lean_tools.proof_specialization import lex as _lex

FAMILIES = (
    "simp_list_delete",
    "solver_list_delete",
    "simp_list_chunk_delete",
    "solver_list_chunk_delete",
    "tactic_toggle",
    "tactic_cost",
    "tactic_line_delete",
    "have_block_delete",
    "rw_simp_conversion",
    "simp_only_removal",
)
MAX_CANDIDATES = 256

_OPEN_TO_CLOSE = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩"}
_CLOSE = set(_OPEN_TO_CLOSE.values())
_FOCUS_PREFIXES = {"·"}
_TACTIC_STARTERS = {
    "all_goals", "apply", "assumption", "aesop", "by_cases", "calc", "case",
    "cases", "choose", "classical", "clear", "contradiction", "constructor",
    "decide", "done", "dsimp", "exact", "exists", "exfalso", "ext", "first",
    "funext", "generalize", "grind", "have", "induction", "intro", "intros",
    "let", "linarith", "norm_num", "nlinarith", "omega", "obtain", "push_neg",
    "rcases", "refine", "rename_i", "repeat", "revert", "ring", "ring_nf", "rfl",
    "rwa", "rw", "simpa", "simp", "simp_all", "solve", "solve_by_elim", "subst",
    "subst_vars", "tauto", "trivial", "unfold", "use", "change", "skip",
}


class MutationError(ValueError):
    """Raised when the request shape or family selection is invalid."""


def _assignment_index(tokens: list[Any]) -> int | None:
    stack: list[str] = []
    for index, token in enumerate(tokens):
        if token.text in _OPEN_TO_CLOSE:
            stack.append(_OPEN_TO_CLOSE[token.text])
        elif stack and token.text == stack[-1]:
            stack.pop()
        elif not stack and token.text == ":=":
            return index
    return None


def _assignment_index_after_signature(
    source: str, tokens: list[Any], signature: str | None = None
) -> int | None:
    """Find the declaration assignment, anchored to an exact frozen signature.

    Without a signature this preserves the standalone heuristic. With one, an
    earlier `:=` inside a return type (for example, a `let` type) cannot be
    mistaken for the proof assignment. Ambiguous/missing signatures fail closed.
    """
    if signature is None:
        return _assignment_index(tokens)
    if not isinstance(signature, str) or not signature:
        return None
    start = source.find(signature)
    if start < 0 or source.find(signature, start + 1) >= 0:
        return None
    signature_end = start + len(signature)
    assignment = re.match(r"[ \t\r\n]*(:=)", source[signature_end:])
    if assignment is None:
        return None
    offset = signature_end + assignment.start(1)
    return next((index for index, token in enumerate(tokens)
                 if token.start == offset and token.text == ":="), None)


def _proof_start_at(tokens: list[Any], assignment_index: int | None) -> int | None:
    if (assignment_index is not None and assignment_index + 1 < len(tokens)
            and tokens[assignment_index + 1].text == "by"):
        return tokens[assignment_index + 1].end
    return None


def _proof_start(source: str, tokens: list[Any]) -> int | None:
    return _proof_start_at(tokens, _assignment_index(tokens))


def _line_start(source: str, offset: int) -> int:
    return source.rfind("\n", 0, offset) + 1


def _line_end(source: str, offset: int) -> int:
    end = source.find("\n", offset)
    return len(source) if end < 0 else end


def _line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset)


def _indent(source: str, offset: int) -> int:
    start = _line_start(source, offset)
    raw = source[start:offset]
    return len(raw) if raw.isspace() else len(raw) - len(raw.lstrip(" \t"))


def _line_indent(source: str, offset: int) -> int:
    start = _line_start(source, offset)
    end = _line_end(source, offset)
    raw = source[start:end]
    return len(raw) - len(raw.lstrip(" \t"))


def _line_starter(tokens: list[Any], after_offset: int | None = None) -> int | None:
    values = [index for index, token in enumerate(tokens)
              if after_offset is None or token.start > after_offset]
    if not values:
        return None
    position = 0
    if tokens[values[0]].text in _FOCUS_PREFIXES:
        position += 1
    if position >= len(values):
        return None
    index = values[position]
    token = tokens[index]
    return index if token.kind == "id" and token.text in _TACTIC_STARTERS else None


def _interior_by_tactic_starts(
    source: str,
    tokens: list[Any],
    assignment_end: int,
) -> set[int]:
    """Find tactic-command heads within lexically visible interior ``by`` blocks.

    A block is considered only when its first command is a known tactic starter.
    Lines at or above the ``by`` line's indentation end its region. This is a
    conservative source heuristic, not a Lean syntax parser.
    """
    token_lines: dict[int, list[int]] = {}
    for index, token in enumerate(tokens):
        if token.start >= assignment_end:
            token_lines.setdefault(_line_number(source, token.start), []).append(index)

    starts: set[int] = set()
    for by_index, by in enumerate(tokens):
        if by.start < assignment_end or by.kind != "id" or by.text != "by":
            continue
        by_line = _line_number(source, by.start)
        base_indent = _line_indent(source, by.start)
        same_line = [index for index in token_lines.get(by_line, []) if tokens[index].start > by.end]
        initial_starter = _line_starter(tokens, by.end) if same_line else None
        initial_line = by_line if initial_starter is not None else None

        if initial_starter is None:
            for line_number in sorted(line for line in token_lines if line > by_line):
                line_tokens = token_lines[line_number]
                first = tokens[line_tokens[0]]
                if _line_indent(source, first.start) <= base_indent:
                    break
                candidate = _line_starter(_tokens_for_line(tokens, line_tokens))
                if candidate is not None:
                    initial_starter = line_tokens[candidate]
                    initial_line = line_number
                break
        if initial_starter is None or initial_line is None:
            continue
        starts.add(initial_starter)

        for line_number in sorted(line for line in token_lines if line > by_line):
            line_tokens = token_lines[line_number]
            first = tokens[line_tokens[0]]
            if _line_indent(source, first.start) <= base_indent:
                break
            starter_local = _line_starter(_tokens_for_line(tokens, line_tokens))
            if starter_local is not None:
                starts.add(line_tokens[starter_local])
    return starts


def _tokens_for_line(tokens: list[Any], token_indices: list[int]) -> list[Any]:
    """Return tokens for one physical source line (kept separate for clarity)."""
    return [tokens[index] for index in token_indices]


def _has_comment_marker(source: str, start: int, end: int) -> bool:
    # Conservative by design: a candidate that would consume comment syntax is
    # omitted, including when the marker happens to be inside a string.
    fragment = source[start:end]
    return "--" in fragment or "/-" in fragment or "-/" in fragment


def _has_opaque(tokens: list[Any], start: int, end: int) -> bool:
    return any(token.kind in {"opaque", "escaped"} and start <= token.start and token.end <= end for token in tokens)


def _matching_close(tokens: list[Any], open_index: int) -> int | None:
    opening = tokens[open_index].text
    if opening not in _OPEN_TO_CLOSE:
        return None
    stack = [_OPEN_TO_CLOSE[opening]]
    for index in range(open_index + 1, len(tokens)):
        text = tokens[index].text
        if text in _OPEN_TO_CLOSE:
            stack.append(_OPEN_TO_CLOSE[text])
        elif text in _CLOSE:
            if not stack or text != stack[-1]:
                return None
            stack.pop()
            if not stack:
                return index
    return None


def _split_list(tokens: list[Any], open_index: int) -> tuple[int, list[list[Any]], list[Any]] | None:
    """Return closing-token index, top-level segments, and comma tokens."""
    close_index = _matching_close(tokens, open_index)
    if close_index is None or tokens[open_index].text != "[":
        return None
    segments: list[list[Any]] = []
    commas: list[Any] = []
    segment: list[Any] = []
    stack: list[str] = []
    for token in tokens[open_index + 1:close_index]:
        if token.text in _OPEN_TO_CLOSE:
            stack.append(_OPEN_TO_CLOSE[token.text])
        elif stack and token.text == stack[-1]:
            stack.pop()
        if token.text == "," and not stack:
            segments.append(segment)
            commas.append(token)
            segment = []
        else:
            segment.append(token)
    if segment or segments:
        segments.append(segment)
    return close_index, segments, commas


def _between_is_plain_space(source: str, left_end: int, right_start: int) -> bool:
    return source[left_end:right_start].isspace()


def _list_deletions(
    source: str,
    tokens: list[Any],
    tactic_index: int,
    open_index: int,
) -> list[tuple[int, int, str, str]]:
    parsed = _split_list(tokens, open_index)
    if parsed is None:
        return []
    _close_index, segments, commas = parsed
    nonempty = [index for index, segment in enumerate(segments) if segment]
    result: list[tuple[int, int, str, str]] = []
    for segment_index in nonempty:
        segment = segments[segment_index]
        if any(token.kind in {"opaque", "escaped"} for token in segment):
            continue
        if len(segments) > 1 and segment_index < len(segments) - 1:
            if not segments[segment_index + 1]:
                continue
            start = segment[0].start
            end = segments[segment_index + 1][0].start
        elif len(segments) > 1:
            if segment_index == 0 or segment_index - 1 >= len(commas):
                continue
            start = commas[segment_index - 1].start
            end = segment[-1].end
        else:
            start = segment[0].start
            end = segment[-1].end
        if start < tokens[tactic_index].start or _has_comment_marker(source, start, end):
            continue
        old = source[start:end]
        label = " ".join(token.text for token in segment)
        result.append((start, end, "", f"Delete simp/rw list argument `{label}`"))
    return result


def _list_chunk_deletions(
    source: str,
    tokens: list[Any],
    tactic_index: int,
    open_index: int,
) -> list[tuple[int, int, str, str]]:
    """Remove contiguous half/quarter partitions from a flat rule list."""
    parsed = _split_list(tokens, open_index)
    if parsed is None:
        return []
    _close_index, segments, commas = parsed
    if not segments or any(not segment for segment in segments):
        return []
    if any(any(token.kind in {"opaque", "escaped"} for token in segment) for segment in segments):
        return []
    count = len(segments)
    ranges: set[tuple[int, int, int]] = set()
    for parts in (2, 4):
        for part in range(parts):
            first = part * count // parts
            last = (part + 1) * count // parts
            if last - first >= 2:
                ranges.add((first, last, parts))

    result: list[tuple[int, int, str, str]] = []
    for first, last, parts in sorted(ranges):
        if first == 0:
            start = segments[first][0].start
            if last == count:
                end = segments[last - 1][-1].end
            else:
                end = segments[last][0].start
            replacement = ""
        elif last == count:
            start = commas[first - 1].start
            end = segments[last - 1][-1].end
            replacement = ""
        else:
            start = commas[first - 1].start
            end = segments[last][0].start
            # Preserve the separator between the retained entries on either
            # side of an interior deletion.
            replacement = ", "
        if start < tokens[tactic_index].start or _has_comment_marker(source, start, end):
            continue
        old = source[start:end]
        result.append((start, end, replacement,
                       f"Delete a contiguous {parts}-way rule-list chunk ({first + 1}..{last})"))
    return result


def _line_tokens(source: str, tokens: list[Any], token: Any) -> list[Any]:
    line = _line_number(source, token.start)
    return [item for item in tokens if _line_number(source, item.start) == line]


def _bare_tactic_line(source: str, tokens: list[Any], token_index: int) -> bool:
    token = tokens[token_index]
    if _line_tokens(source, tokens, token) != [token]:
        return False
    # Do not mistake a tactic whose arguments continue on a more-indented line
    # for a bare tactic line.
    for following in tokens[token_index + 1:]:
        if _line_number(source, following.start) <= _line_number(source, token.start):
            continue
        if _indent(source, following.start) > _indent(source, token.start):
            return False
        break
    return True


def _list_after_tactic(tokens: list[Any], token_index: int, allow_only: bool) -> tuple[int, int] | None:
    cursor = token_index + 1
    if allow_only and cursor < len(tokens) and tokens[cursor].text == "only":
        cursor += 1
    if cursor >= len(tokens) or tokens[cursor].text != "[":
        return None
    close_index = _matching_close(tokens, cursor)
    if close_index is None:
        return None
    return cursor, close_index


def _simpa_using_prefix(source: str, tokens: list[Any], token_index: int) -> Any | None:
    """Find a conservative top-level ``using`` in a supported simpa prefix."""
    simpa = tokens[token_index]
    cursor = token_index + 1
    has_only = cursor < len(tokens) and tokens[cursor].text == "only"
    if has_only:
        cursor += 1
    if cursor < len(tokens) and tokens[cursor].text == "[":
        close_index = _matching_close(tokens, cursor)
        if close_index is None:
            return None
        cursor = close_index + 1
    elif has_only:
        return None
    if cursor >= len(tokens) or tokens[cursor].text != "using":
        return None
    using = tokens[cursor]
    if _has_comment_marker(source, simpa.start, using.end) or _has_opaque(tokens, simpa.start, using.end):
        return None
    term_index = cursor + 1
    if term_index >= len(tokens):
        return None
    term = tokens[term_index]
    if not _between_is_plain_space(source, using.end, term.start):
        return None
    # A term starting on a later line must be indented under the tactic. This
    # avoids treating the next sibling tactic as a missing ``using`` argument.
    if _line_number(source, term.start) > _line_number(source, using.start):
        if _indent(source, term.start) <= _indent(source, simpa.start):
            return None
    return using


def _candidate_have_blocks(
    source: str,
    tokens: list[Any],
    proof_start: int,
    eligible_start_offsets: set[int] | None = None,
) -> list[tuple[int, int, str]]:
    lines = source.splitlines(keepends=True)
    starts: list[int] = []
    cursor = 0
    for line in lines:
        starts.append(cursor)
        cursor += len(line)
    token_by_line: dict[int, list[Any]] = {}
    for token in tokens:
        token_by_line.setdefault(_line_number(source, token.start), []).append(token)
    result: list[tuple[int, int, str]] = []
    for line_index, line in enumerate(lines):
        start = starts[line_index]
        if start < proof_start:
            continue
        line_tokens = token_by_line.get(line_index, [])
        if not line_tokens or line_tokens[0].text != "have" or line_tokens[0].start < proof_start:
            continue
        if eligible_start_offsets is not None and line_tokens[0].start not in eligible_start_offsets:
            continue
        if "\t" in line[:len(line) - len(line.lstrip(" \t"))]:
            continue
        base_indent = len(line) - len(line.lstrip(" "))
        last_index = line_index
        unsafe = False
        for child_index in range(line_index + 1, len(lines)):
            child = lines[child_index]
            stripped = child.strip()
            if not stripped:
                continue
            if "\t" in child[:len(child) - len(child.lstrip(" \t"))]:
                unsafe = True
            child_tokens = token_by_line.get(child_index, [])
            if not child_tokens:
                # Comment-only lines are opaque. We may not delete across one.
                unsafe = True
                continue
            child_indent = len(child) - len(child.lstrip(" "))
            if child_indent <= base_indent:
                break
            last_index = child_index
        end_line = lines[last_index]
        end = starts[last_index] + len(end_line)
        if unsafe or _has_comment_marker(source, start, end) or _has_opaque(tokens, start, end):
            continue
        result.append((start, end, "Remove the indented `have` statement block"))
    return result


def _normalize_families(families: Iterable[str] | str | None) -> set[str]:
    if families is None:
        return set(FAMILIES)
    if isinstance(families, str):
        selected = {families}
    else:
        try:
            selected = set(families)
        except TypeError as error:
            raise MutationError("families must be a family name or iterable of family names") from error
    if not all(isinstance(family, str) for family in selected):
        raise MutationError("family names must be strings")
    unknown = selected - set(FAMILIES)
    if unknown:
        raise MutationError(f"unknown mutation family: {sorted(unknown)[0]}")
    return selected


def generate(
    declaration: str,
    max_candidates: int = 64,
    families: Iterable[str] | str | None = None,
    signature: str | None = None,
) -> list[dict[str, Any]]:
    """Generate bounded mutations within the declaration's proof expression.

    Offsets use Python Unicode code points with zero-based, end-exclusive
    ranges. Edits are source-bound and never reach the outer signature. For a
    term-style proof, only recognized tactic heads inside a visible interior
    ``by`` block are eligible.
    """
    if not isinstance(declaration, str):
        raise MutationError("declaration must be a string")
    if type(max_candidates) is not int or not 0 <= max_candidates <= MAX_CANDIDATES:
        raise MutationError(f"max_candidates must be an integer in 0..{MAX_CANDIDATES}")
    selected = _normalize_families(families)
    if max_candidates == 0 or not selected:
        return []
    try:
        tokens = _lex(declaration)
    except Exception as error:
        # The shared lexer rejects unterminated opaque syntax; no safe span
        # edits can be made in that case.
        return []
    assignment_index = _assignment_index_after_signature(declaration, tokens, signature)
    if assignment_index is None:
        return []
    assignment_end = tokens[assignment_index].end
    outer_proof_start = _proof_start_at(tokens, assignment_index)
    if outer_proof_start is not None:
        proof_start = outer_proof_start
        eligible_starts: set[int] | None = None
        proof_tokens = [(index, token) for index, token in enumerate(tokens)
                        if token.start >= proof_start]
    else:
        proof_start = assignment_end
        eligible_starts = _interior_by_tactic_starts(declaration, tokens, assignment_end)
        proof_tokens = [(index, tokens[index]) for index in sorted(eligible_starts)]
    # Quoted Lean syntax can contain arbitrary tactic-looking tokens. Keep the
    # old whole-proof conservative guard for outer tactic proofs, and check
    # the term body before trusting any interior ``by`` offsets.
    if any(token.text == "`" and token.start >= proof_start for token in tokens):
        return []
    if not proof_tokens:
        return []

    proposals: list[dict[str, Any]] = []

    def propose(
        family: str,
        start: int,
        end: int,
        replacement: str,
        description: str,
        site: int | None = None,
    ) -> None:
        if family not in selected or start < proof_start or end < start:
            return
        old = declaration[start:end]
        if old == replacement:
            return
        proposals.append({
            "family": family,
            "description": description,
            "start": start,
            "end": end,
            "old": old,
            "new": replacement,
            "site": start if site is None else site,
        })

    # Propose one simp/rw entry deletion per source entry, including entries
    # in ``... at h`` sites. The location clause remains outside each edit.
    if "simp_list_delete" in selected:
        for token_index, token in proof_tokens:
            if token.kind != "id" or token.text not in {"simp", "simpa", "rw"}:
                continue
            list_info = _list_after_tactic(tokens, token_index, allow_only=(token.text in {"simp", "simpa"}))
            if list_info is None:
                continue
            open_index, _close_index = list_info
            for start, end, replacement, description in _list_deletions(declaration, tokens, token_index, open_index):
                propose("simp_list_delete", start, end, replacement, description, site=token.start)

    # These solver tactics also accept explicit hypothesis/rule lists. Removing
    # one entry at a time is a useful bounded generic probe and leaves all
    # surrounding tactic syntax and source comments intact.
    if "solver_list_delete" in selected:
        for token_index, token in proof_tokens:
            if token.kind != "id" or token.text not in {"simp_all", "linarith", "nlinarith"}:
                continue
            list_info = _list_after_tactic(tokens, token_index, allow_only=(token.text == "simp_all"))
            if list_info is None:
                continue
            open_index, _close_index = list_info
            for start, end, replacement, description in _list_deletions(declaration, tokens, token_index, open_index):
                propose("solver_list_delete", start, end, replacement,
                        f"Prune `{token.text}` list: {description.removeprefix('Delete simp/rw list argument ')}",
                        site=token.start)

    if "simp_list_chunk_delete" in selected:
        for token_index, token in proof_tokens:
            if token.kind != "id" or token.text not in {"simp", "simp_all", "simpa", "rw"}:
                continue
            list_info = _list_after_tactic(
                tokens, token_index, allow_only=(token.text in {"simp", "simp_all", "simpa"})
            )
            if list_info is None:
                continue
            open_index, _close_index = list_info
            for start, end, replacement, description in _list_chunk_deletions(
                declaration, tokens, token_index, open_index
            ):
                propose("simp_list_chunk_delete", start, end, replacement,
                        f"Prune `{token.text}` list: {description}", site=token.start)

    if "solver_list_chunk_delete" in selected:
        for token_index, token in proof_tokens:
            if token.kind != "id" or token.text not in {"linarith", "nlinarith"}:
                continue
            list_info = _list_after_tactic(tokens, token_index, allow_only=False)
            if list_info is None:
                continue
            open_index, _close_index = list_info
            for start, end, replacement, description in _list_chunk_deletions(
                declaration, tokens, token_index, open_index
            ):
                propose("solver_list_chunk_delete", start, end, replacement,
                        f"Prune `{token.text}` list: {description}", site=token.start)

    for token_index, token in proof_tokens:
        if token.kind != "id":
            continue
        if token.text in {"simp", "simp_all", "simpa"} and "tactic_toggle" in selected:
            if token.text in {"simp", "simp_all"}:
                only_index = token_index + 1 if token_index + 1 < len(tokens) and tokens[token_index + 1].text == "only" else None
                if only_index is None:
                    replacement = "simp only" if token.text == "simp" else "simp_all only"
                    propose("tactic_toggle", token.start, token.end, replacement,
                            f"Change `{token.text}` to `{replacement}`", site=token.start)
                    if token.text == "simp":
                        propose("tactic_toggle", token.start, token.end, "dsimp", "Change `simp` to `dsimp`", site=token.start)
                else:
                    only_token = tokens[only_index]
                    if _between_is_plain_space(declaration, token.end, only_token.start):
                        replacement = "dsimp" if token.text == "simp" else "simp_all"
                        propose("tactic_toggle", token.start, only_token.end, replacement,
                                f"Change `{token.text} only` to `{replacement}`", site=token.start)
            else:
                # Only the tactic prefix is edited. The complete supplied term,
                # including applications and multiline `by` blocks, remains an
                # exact source slice for Lean's parser and elaborator to judge.
                using_token = _simpa_using_prefix(declaration, tokens, token_index)
                if using_token is not None:
                    propose("tactic_toggle", token.start, using_token.end, "exact",
                            "Change `simpa ... using term` to `exact term`", site=token.start)

        # Cost ladder edits are restricted to an invocation with no arguments
        # on its physical line (and no indented continuation).
        if "tactic_cost" in selected and _bare_tactic_line(declaration, tokens, token_index):
            replacements = {
                "simp": ("rfl", "assumption"),
                "aesop": ("simp_all", "solve_by_elim"),
                "tauto": ("simp_all", "solve_by_elim"),
                "nlinarith": ("linarith", "omega"),
                "linarith": ("omega",),
                "ring_nf": ("ring",),
            }
            for replacement in replacements.get(token.text, ()):
                propose("tactic_cost", token.start, token.end, replacement,
                        f"Try `{replacement}` in place of `{token.text}`", site=token.start)

        if "tactic_line_delete" in selected and token.text in {
            "simp", "simpa", "simp_all", "rfl", "assumption", "aesop", "tauto",
            "solve_by_elim", "nlinarith", "linarith", "omega", "ring_nf", "ring",
            "trivial", "decide", "contradiction", "done", "skip", "constructor",
        } and _bare_tactic_line(declaration, tokens, token_index):
            propose("tactic_line_delete", token.start, token.end, "",
                    f"Remove standalone `{token.text}` tactic line", site=token.start)

        if token.text == "rw" and "rw_simp_conversion" in selected:
            list_info = _list_after_tactic(tokens, token_index, allow_only=False)
            if list_info is not None:
                propose("rw_simp_conversion", token.start, token.end, "simp only",
                        "Change `rw [..]` to `simp only [..]`", site=token.start)

        if token.text == "simp" and token_index + 1 < len(tokens) and tokens[token_index + 1].text == "only":
            only_token = tokens[token_index + 1]
            if not _between_is_plain_space(declaration, token.end, only_token.start):
                continue
            if "simp_only_removal" in selected:
                propose("simp_only_removal", token.start, only_token.end, "simp",
                        "Remove `only` from `simp only`", site=token.start)
            if "rw_simp_conversion" in selected and token_index + 2 < len(tokens) and tokens[token_index + 2].text == "[":
                if _matching_close(tokens, token_index + 2) is not None:
                    propose("rw_simp_conversion", token.start, only_token.end, "rw",
                            "Change `simp only [..]` to `rw [..]`", site=token.start)

    if "have_block_delete" in selected:
        eligible_have_offsets = (
            {tokens[index].start for index in eligible_starts}
            if eligible_starts is not None else None
        )
        for start, end, description in _candidate_have_blocks(
            declaration, tokens, proof_start, eligible_have_offsets
        ):
            propose("have_block_delete", start, end, "", description, site=start)

    # Round-robin across tactic anchors first, then across families within each
    # anchor. A long lemma list near the start of a proof cannot consume the
    # entire candidate cap before later tactic sites are represented.
    by_site: dict[int, dict[str, list[dict[str, Any]]]] = {}
    for item in proposals:
        by_site.setdefault(item["site"], {}).setdefault(item["family"], []).append(item)
    site_queues: dict[int, list[dict[str, Any]]] = {}
    for site, by_family in by_site.items():
        for values in by_family.values():
            values.sort(key=lambda item: (item["start"], item["end"], item["new"], item["description"]))
        queue: list[dict[str, Any]] = []
        family_queues = {family: by_family.get(family, []) for family in FAMILIES}
        rounds = max((len(values) for values in family_queues.values()), default=0)
        for round_index in range(rounds):
            for family in FAMILIES:
                values = family_queues[family]
                if round_index < len(values):
                    queue.append(values[round_index])
        site_queues[site] = queue

    ordered_sites = sorted(site_queues)
    # If the caller's cap is smaller than the number of sites, sample sites
    # evenly across the declaration so the tail remains eligible.
    if len(ordered_sites) > max_candidates:
        if max_candidates == 1:
            ordered_sites = [ordered_sites[len(ordered_sites) // 2]]
        else:
            last = len(ordered_sites) - 1
            indexes = sorted({round(index * last / (max_candidates - 1)) for index in range(max_candidates)})
            ordered_sites = [ordered_sites[index] for index in indexes]
    unique: list[dict[str, Any]] = []
    seen: set[tuple[int, int, str]] = set()
    depth = 0
    while len(unique) < max_candidates:
        advanced = False
        for site in ordered_sites:
            queue = site_queues[site]
            if depth >= len(queue):
                continue
            advanced = True
            item = queue[depth]
            key = (item["start"], item["end"], item["new"])
            if key not in seen:
                seen.add(key)
                unique.append(item)
                if len(unique) >= max_candidates:
                    break
        if not advanced:
            break
        depth += 1

    output: list[dict[str, Any]] = []
    for index, item in enumerate(unique, start=1):
        start, end = item["start"], item["end"]
        edited = declaration[:start] + item["new"] + declaration[end:]
        if edited[:proof_start] != declaration[:proof_start]:
            raise AssertionError("mutation changed the declaration signature or tactic prefix")
        output.append({
            "id": f"mutation-{index:03d}",
            "family": item["family"],
            "description": item["description"],
            "declaration": edited,
            "edits": [{
                "start": start,
                "end": end,
                "old": item["old"],
                "new": item["new"],
                "offset_unit": "unicode_codepoints_zero_based_end_exclusive",
            }],
        })
    return output
