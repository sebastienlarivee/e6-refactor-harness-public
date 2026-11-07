"""Pure lexical proposals; full Lean evaluation is the acceptance authority.

Only current-source spans and identifiers are used. Layout recognition is
deliberately narrow: structural moves require sibling, line-leading commands,
plain whitespace gaps and no comment syntax. No compiler or archive is read.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
import re

from . import mutations as m

EXTRA_FAMILIES = (
    "application_dollar", "annotation_prune", "annotation_infer", "annotation_partial",
    "have_anonymize", "have_reorder", "have_sink", "letI_motion",
    "simp_list_normalize", "normalization_fusion", "normalization_delay",
)
_LIMIT = 256
_OPEN = m._OPEN_TO_CLOSE
_CLOSE = m._CLOSE
_HEADS = m._TACTIC_STARTERS | {"letI", "haveI", "simp_rw", "ring1"}
_NORMALIZERS = {"simp", "simp_all", "simpa", "rw", "simp_rw", "dsimp"}
_CONTEXT_STEPS = {"simp", "rw", "simp_rw", "dsimp", "ring_nf", "change"}


@dataclass(frozen=True)
class Site:
    head: str
    start: int
    end: int
    indent: int
    text: str
    token_index: int


def _plain(text: str) -> bool:
    return not any(marker in text for marker in ("--", "/-", "-/", "\t", "`"))


def _end(source: str, tokens: list, index: int) -> int:
    head = tokens[index]
    line = source.rfind("\n", 0, head.start) + 1
    indent = len(source[line:head.start])
    stack = []
    previous = head
    for token in tokens[index + 1:]:
        if not stack:
            if token.text in {";", "<;>", "|", "·"} | _CLOSE:
                return previous.end
            if "\n" in source[previous.end:token.start]:
                start = source.rfind("\n", 0, token.start) + 1
                prefix = source[start:token.start]
                if len(prefix) <= indent:
                    return previous.end
        if token.text in _OPEN:
            stack.append(_OPEN[token.text])
        elif token.text in _CLOSE:
            if not stack or stack.pop() != token.text:
                return previous.end
        previous = token
    return previous.end


def _sites(source: str, tokens: list, minimum: int) -> list[Site]:
    result = []
    for index, token in enumerate(tokens):
        if token.start < minimum or token.kind != "id" or token.text not in _HEADS:
            continue
        line = source.rfind("\n", 0, token.start) + 1
        prefix = source[line:token.start]
        # Inline/bulleted tactics remain eligible for the mutation core; moves
        # and fusions require an unambiguous whitespace-only line prefix.
        if prefix.strip() or "\t" in prefix:
            continue
        end = _end(source, tokens, index)
        if end < token.end or not _plain(source[token.start:end]):
            continue
        result.append(Site(token.text, token.start, end, len(prefix),
                           source[token.start:end], index))
    return result


def _siblings(source: str, left: Site, right: Site) -> bool:
    return left.end <= right.start and left.indent == right.indent and not source[left.end:right.start].strip()


def _sequences(source: str, sites: list[Site]) -> list[list[Site]]:
    """Group direct layout siblings, allowing nested proof sites separately."""
    by_indent = defaultdict(list)
    for site in sites:
        by_indent[site.indent].append(site)
    result = []
    for indent in sorted(by_indent):
        run = []
        for site in by_indent[indent]:
            if run and not _siblings(source, run[-1], site):
                result.append(run)
                run = []
            run.append(site)
        if run:
            result.append(run)
    return result


def _names(tokens: list, start: int, end: int) -> set[str]:
    names = set()
    for token in tokens:
        if start <= token.start < end and token.kind == "id":
            # A local reference such as h.symm is one lexer token. Treat every
            # dotted prefix as potentially referring to a local binder.
            pieces = token.text.split(".")
            names.update(".".join(pieces[:index]) for index in range(1, len(pieces) + 1))
    return names


def _binding(site: Site, tokens: list) -> dict | None:
    if site.head not in {"have", "let", "letI", "haveI"}:
        return None
    group = [t for t in tokens if site.start <= t.start < site.end]
    if len(group) < 4:
        return None
    cursor = 1
    name = None
    name_token = None
    if group[cursor].kind == "id" and group[cursor].text not in {"mut"}:
        name_token = group[cursor]
        name = name_token.text
        if "." in name:
            return None
        cursor += 1
    colon = group[cursor] if cursor < len(group) and group[cursor].text == ":" else None
    if colon is None and (cursor >= len(group) or group[cursor].text != ":="):
        return None  # Parameterized bindings need proper parser scope data.
    stack = []
    assignment = None
    for pos in range(cursor + bool(colon), len(group)):
        token = group[pos]
        if token.text in _OPEN:
            stack.append(_OPEN[token.text])
        elif token.text in _CLOSE:
            if not stack or stack.pop() != token.text:
                return None
        elif not stack and token.text == ":=":
            assignment = pos
            break
    if assignment is None or assignment + 1 >= len(group):
        return None
    return {"name": name, "name_token": name_token, "colon": colon,
            "assignment": group[assignment], "rhs": group[assignment + 1],
            "type_tokens": group[cursor + 1:assignment] if colon else [],
            "tokens": group}


def _list(site: Site, tokens: list) -> dict | None:
    if site.head not in _NORMALIZERS:
        return None
    local = [t for t in tokens if site.start <= t.start < site.end]
    first = next((i for i, t in enumerate(local) if t.text == "["), None)
    if first is None:
        return None
    parsed = m._split_list(local, first)
    if parsed is None:
        return None
    close, segments, _commas = parsed
    if close != len(local) - 1 or not segments or any(not part for part in segments):
        return None  # Locations, using terms and incomplete lists abstain.
    prefix = site.text[:local[first].start - site.start]
    if not re.fullmatch(r"(?:rw|simp_rw)\s*|(?:simp|simp_all|simpa|dsimp)\s+(?:-dsimp\s+)?only\s*", prefix):
        return None
    return {"prefix": prefix.strip(), "entries": [
                site.text[part[0].start - site.start:part[-1].end - site.start] for part in segments],
            "keys": [tuple(t.text for t in part) for part in segments],
            "start": local[first].end, "end": local[close].start}


def extra_proposals(source: str, tokens: list, minimum: int) -> list[dict]:
    """Return per-family-bounded span proposals without executing Lean."""
    proposals = []
    counts = defaultdict(int)
    seen = set()

    def add(family, edits, site, description, **metadata):
        if counts[family] >= _LIMIT:
            return
        key = tuple((e["start"], e["end"], e["new"]) for e in edits)
        if key in seen or any(not minimum <= e["start"] <= e["end"] <= len(source) for e in edits):
            return
        if all(source[e["start"]:e["end"]] == e["new"] for e in edits):
            return
        seen.add(key)
        counts[family] += 1
        proposals.append({"family": family, "site": site, "description": description,
                          "edits": edits, **metadata})

    def replace(family, a, b, new, site, description, **metadata):
        add(family, [{"start": a, "end": b, "new": new}], site, description, **metadata)

    sites = _sites(source, tokens, minimum)
    sequences = _sequences(source, sites)
    bindings = {site.start: _binding(site, tokens) for site in sites}
    for site in sites:
        info = bindings[site.start]
        if info is not None:
            colon, assignment = info["colon"], info["assignment"]
            name, name_token = info["name"], info["name_token"]
            if site.head == "have" and name and name != "_" and name not in _names(tokens, name_token.end, len(source)):
                replace("have_anonymize", name_token.start, name_token.end, "_", site.start,
                        "Anonymize a have binder with no later lexical use", name=name)
            if colon is not None and _plain(source[colon.start:assignment.start]):
                type_tokens = info["type_tokens"]
                if info["rhs"].text != "by":
                    replace("annotation_prune", colon.start, assignment.start, "", site.start,
                            "Infer a local term binding's complete type")
                    replace("annotation_infer", colon.end, assignment.start, " _ ", site.start,
                            "Replace a local term binding type by an inference hole")
                # Keep the proposition's equality relation while asking Lean
                # to infer one side from the remaining type and supplied term.
                stack = []
                relations = []
                for token in type_tokens:
                    if token.text in _OPEN:
                        stack.append(_OPEN[token.text])
                    elif token.text in _CLOSE:
                        if not stack or stack.pop() != token.text:
                            break
                    elif not stack and token.text in {"=", "↔", "≤", "<", "≥", ">"}:
                        relations.append(token)
                if len(relations) == 1 and type_tokens and not any(t.text in {"∀", "fun", "=>", "→", "->", "let", "match"} for t in type_tokens):
                    relation = relations[0]
                    for a, b in ((type_tokens[0].start, relation.start),
                                 (relation.end, type_tokens[-1].end)):
                        if source[a:b].strip():
                            replace("annotation_partial", a, b, " _ ", site.start,
                                    "Infer one side of a local relational type")

        # Dollar is normalized only in one-line explicit term arguments or
        # binding RHSs. Lowest-precedence binder/control terms abstain.
        if site.head in {"exact", "refine", "apply"}:
            term_start = tokens[site.token_index].end
        elif info is not None:
            term_start = info["assignment"].end
        else:
            term_start = None
        if term_start is not None:
            term = [t for t in tokens if term_start <= t.start < site.end]
            if "\n" not in source[term_start:site.end] and not any(t.text in {"by", "fun", "=>", "∀", "match", "let", "have", "if", "then", "else"} for t in term):
                dollars = []
                stack = []
                for index, token in enumerate(term):
                    if token.text in _OPEN:
                        stack.append(_OPEN[token.text])
                    elif token.text in _CLOSE:
                        if stack:
                            stack.pop()
                    elif token.text == "$" and index and index + 1 < len(term):
                        depth = len(stack)
                        end = site.end
                        nested = 0
                        for next_token in term[index + 1:]:
                            if next_token.text in _OPEN:
                                nested += 1
                            elif next_token.text in _CLOSE:
                                if nested == 0:
                                    end = next_token.start
                                    break
                                nested -= 1
                            elif nested == 0 and next_token.text == ",":
                                end = next_token.start
                                break
                        argument = source[token.end:end].strip()
                        if argument:
                            dollars.append((token, end, argument, depth))
                for token, end, argument, _depth in dollars:
                    replace("application_dollar", token.start, end, "(" + argument + ")", site.start,
                            "Parenthesize a dollar application argument")

    # Compact literal rule lists by exact token identity, preserving first-use
    # order. No lemma is fetched or invented.
    parsed_lists = {site.start: _list(site, tokens) for site in sites}
    for site in sites:
        parsed = parsed_lists[site.start]
        if parsed is None:
            continue
        retained = []
        keys = set()
        for key, entry in zip(parsed["keys"], parsed["entries"]):
            if key not in keys:
                keys.add(key)
                retained.append(entry)
        if len(retained) < len(parsed["entries"]):
            replace("simp_list_normalize", parsed["start"], parsed["end"], ", ".join(retained), site.start,
                    "Deduplicate source-identical rewrite/simp list terms")

    pairs = [(left, right) for sequence in sequences for left, right in zip(sequence, sequence[1:])]
    for left, right in pairs:
        if not _siblings(source, left, right):
            continue
        lp, rp = parsed_lists[left.start], parsed_lists[right.start]
        if lp and rp:
            heads = ["simp only", "simp -dsimp only", "simp_rw"]
            if left.head == right.head == "rw":
                heads.insert(0, "rw")
            if left.head == "simp_all" or right.head == "simp_all":
                heads.append("simp_all only")
            for head in heads:
                new = head + " [" + ", ".join(lp["entries"] + rp["entries"]) + "]"
                replace("normalization_fusion", left.start, right.end, new, left.start,
                        "Fuse neighboring explicit normalization lists", replacement_head=head)
        if lp and left.head in {"simp", "simp_all", "simpa"} and right.head in _NORMALIZERS | {"exact", "apply", "refine", "ring", "ring1", "ring_nf", "rfl"}:
            for rule_index, rule in enumerate(lp["entries"][:16]):
                remaining = lp["entries"][:rule_index] + lp["entries"][rule_index + 1:]
                reduced = source[left.start:lp["start"]] + ", ".join(remaining) + source[lp["end"]:left.end]
                for head in ("simp only", "dsimp only"):
                    add("normalization_delay", [
                        {"start": left.start, "end": left.end, "new": reduced},
                        {"start": right.start, "end": right.end,
                         "new": "(" + head + " [" + rule + "]; " + right.text + ")"}],
                        left.start, "Delay one source normalization rule to the adjacent consumer")

    # Adjacent independent facts can be reordered by an explicit dependency
    # DAG. Lexical independence is a proposal filter, not a semantic guarantee:
    # typeclass synthesis and implicit tactic search still require validation.
    # A sentinel separates unrelated sequences without discarding nested ones.
    fact_sites = []
    for sequence in sequences:
        fact_sites.extend(sequence)
        fact_sites.append(None)
    cursor = 0
    while cursor < len(fact_sites):
        run = []
        while cursor < len(fact_sites):
            site = fact_sites[cursor]
            if site is None:
                break
            info = bindings[site.start]
            if site.head != "have" or info is None or not info["name"] or info["name"] == "_":
                break
            if run and not _siblings(source, run[-1], site):
                break
            run.append(site)
            cursor += 1
        if len(run) >= 2:
            run = run[:12]
            names = [bindings[s.start]["name"] for s in run]
            if len(set(names)) == len(names):
                dependencies = []
                for site in run:
                    binding = bindings[site.start]
                    used = _names(tokens, binding["name_token"].end, site.end)
                    dependencies.append({i for i, name in enumerate(names) if name in used})
                def order(priority):
                    remaining, out = set(range(len(run))), []
                    while remaining:
                        ready = [i for i in remaining if dependencies[i] <= set(out)]
                        if not ready:
                            return []
                        chosen = min(ready, key=priority)
                        remaining.remove(chosen)
                        out.append(chosen)
                    return out
                orders = [order(lambda i: -i), order(lambda i: (len(run[i].text), i)),
                          order(lambda i: (-len(run[i].text), i))]
                for position in range(len(run) - 1):
                    permutation = list(range(len(run)))
                    permutation[position:position + 2] = reversed(permutation[position:position + 2])
                    if all(dependencies[node] <= set(permutation[:j]) for j, node in enumerate(permutation)):
                        orders.append(permutation)
                gaps = [source[a.end:b.start] for a, b in zip(run, run[1:])]
                for permutation in orders:
                    if not permutation or permutation == list(range(len(run))):
                        continue
                    new = "".join(run[node].text + (gaps[j] if j < len(gaps) else "") for j, node in enumerate(permutation))
                    replace("have_reorder", run[0].start, run[-1].end, new, run[0].start,
                            "Topologically reorder explicitly independent sibling facts",
                            original_order=names, new_order=[names[i] for i in permutation])
        if not run:
            cursor += 1

    motions = [(sequence, index, site) for sequence in sequences for index, site in enumerate(sequence)]
    for sequence, index, site in motions:
        binding = bindings[site.start]
        if binding is None or site.head not in {"have", "letI"}:
            continue
        name = binding["name"]
        if name == "_":
            name = None
        # Bounded downward motion over commands with unchanged local-binder
        # shape; explicit name references and location clauses block movement.
        last = site
        for other in sequence[index + 1:index + 5]:
            if not _siblings(source, last, other):
                break
            used = _names(tokens, other.start, other.end)
            if name and name in used:
                break
            allowed = other.head in _CONTEXT_STEPS or (site.head == "letI" and other.head == "have" and bindings[other.start] is not None)
            if not allowed or "at" in used or "*" in {t.text for t in tokens if other.start <= t.start < other.end}:
                break
            # Rotate complete command slices while retaining original gaps.
            middle = source[site.end:other.end]
            first_gap = source[site.end:sequence[index + 1].start]
            rotated = middle[len(first_gap):] + first_gap + site.text
            family = "letI_motion" if site.head == "letI" else "have_sink"
            replace(family, site.start, other.end, rotated, site.start,
                    "Delay a binding across explicitly independent sibling commands", name=name)
            last = other
        # A local instance can also be moved before one preceding explicit
        # fact if its own term does not mention that fact's binder.
        if site.head == "letI" and index:
            previous = sequence[index - 1]
            previous_binding = bindings[previous.start]
            if previous.head == "have" and previous_binding and _siblings(source, previous, site):
                previous_name = previous_binding["name"]
                used = _names(tokens, site.start, site.end)
                if previous_name and previous_name not in used:
                    gap = source[previous.end:site.start]
                    replace("letI_motion", previous.start, site.end, site.text + gap + previous.text,
                            site.start, "Move a local instance before an explicitly independent fact", name=name)
    return proposals
