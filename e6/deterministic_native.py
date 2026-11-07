"""Native syntax and TermInfo proposals for the supplied current incumbent.

This module only proposes edits. Every returned source needs ordinary complete
source validation, axiom auditing, exact measurement, and compatibility checks.
The helper elaborates the target once in its original pre-target environment;
it never replays tactics in captured local states or imports the completed target.
"""
from __future__ import annotations

from collections import defaultdict, deque
import hashlib
import json
import math
import os
from pathlib import Path
import re
import tempfile
import time
from typing import Any

from lean_tools import arena_workflow as arena, lean_launch, lean_source
from lean_tools.proof_specialization import lex

from .config import configure_native_environment
from .runtime import RuntimeContext, scoped_environment

SUPPORT = Path(__file__).with_name("deterministic_native_support")
HELPER_SOURCE = (SUPPORT / "Inventory.lean.inc").read_text(encoding="utf-8")
MODULE_NAME = "E6NativeInventoryHelper"
SCHEMA_VERSION = 1


class NativeProposalError(RuntimeError):
    """A native inventory could not be collected; evidence remains in workdir."""


def _sha(value: str | bytes) -> str:
    return hashlib.sha256(value.encode("utf-8") if isinstance(value, str) else value).hexdigest()


def _write(path: Path, value: Any) -> None:
    arena.write_json_atomic(path, value)


def _remaining(deadline: float) -> float:
    value = deadline - time.perf_counter()
    if value <= 0:
        raise TimeoutError("Native proposal request deadline expired")
    return value


def _helper_text(module: bool) -> str:
    # Lean's module system requires explicitly public meta imports. Older
    # compiler releases use the ordinary header and the identical helper body.
    header = ("module\npublic import Lean\npublic meta import Lean.Elab.Tactic.Meta\n"
              "public meta import Init.Data.String.Legacy\npublic meta section\n" if module
              else "import Lean\n")
    return header + HELPER_SOURCE


def _run(path: Path, project: Path, deadline: float, out: Path, **kwargs) -> dict:
    run = arena.run_lean(path, project, _remaining(deadline), **kwargs)
    out.write_text(run.output, encoding="utf-8")
    return {name: getattr(run, name, None) for name in (
        "returncode", "timed_out", "seconds", "queue_wait_seconds", "command")}


def _helper(config: dict, project: Path, workdir: Path, module: bool,
            deadline: float) -> tuple[Path, dict, dict]:
    # workspace_guard is read-only and fingerprints the actual compiler, pinned
    # package environment, compiled Lake configuration and relevant ambient vars.
    # It rejects missing caches instead of rebuilding a cached project.
    environment = lean_launch.workspace_guard(project, os.environ)
    text = _helper_text(module)
    key = _sha(json.dumps({"environment": environment, "helper": text}, sort_keys=True))
    run_root = Path(config.get("root", workdir)).resolve()
    cache = run_root / "deterministic" / "native-helper-cache" / key
    if cache.is_relative_to(project.resolve()):
        raise NativeProposalError("Native helper cache must be outside the cached Lean project")
    cache.mkdir(parents=True, exist_ok=True)
    source = cache / (MODULE_NAME + ".lean")
    olean = cache / (MODULE_NAME + ".olean")
    marker = cache / "ready.json"
    with arena.exclusive_file_lock(cache / ".build.lock", _remaining(deadline)):
        if marker.is_file() and olean.is_file():
            receipt = json.loads(marker.read_text(encoding="utf-8"))
            if (receipt.get("key") == key and receipt.get("source_sha256") == _sha(text)
                    and receipt.get("olean_sha256") == _sha(olean.read_bytes())):
                return cache, {**receipt, "reused": True}, environment
        failure_path = cache / "build.json"
        log_path = cache / "build.log"
        if failure_path.is_file() and log_path.is_file():
            previous = json.loads(failure_path.read_text(encoding="utf-8"))
            if (previous.get("key") == key and previous.get("returncode") not in (None, 0)
                    and not previous.get("timed_out") and "error:" in log_path.read_text(encoding="utf-8").lower()):
                raise NativeProposalError(f"Cached source-identical native helper compile failure; see {log_path}")
        source.write_text(text, encoding="utf-8")
        receipt = {"key": key, "source_sha256": _sha(text), "source_path": str(source),
                   "cache_path": str(cache), "environment_sha256": _sha(json.dumps(environment, sort_keys=True)),
                   "toolchain": environment["toolchain"], "reused": False}
        _write(cache / "environment.json", environment)
        build = _run(source, project, deadline, cache / "build.log",
                     lean_args=["-R", str(cache), "-o", str(olean)])
        receipt.update(build)
        _write(cache / "build.json", receipt)
        if build["returncode"] != 0 or build["timed_out"] or not olean.is_file():
            raise NativeProposalError(f"Native inventory helper compile failed; see {cache / 'build.log'}")
        receipt["olean_sha256"] = _sha(olean.read_bytes())
        _write(marker, receipt)
        return cache, receipt, environment


def _current_source(row: dict, source: str) -> tuple[str, int, int]:
    """Return declaration and its code-point declaration/body offsets in input."""
    if source.startswith(row["signature"]):
        declaration = source.rstrip("\r\n")
        body = lean_source.validate_declaration(row, declaration)
        start = 0
    else:
        declaration, body = lean_source.extract_candidate_declaration(row, source)
        snapshot = lean_source.snapshot_candidate(row, source, Path("Current.lean"))
        start = snapshot.declaration_start
    return declaration, start, start + len(declaration.rstrip()) - len(body)


def _inventory(config: dict, source: str, row: dict, workdir: Path,
               deadline: float) -> tuple[dict, dict]:
    declaration, input_start, input_body = _current_source(row, source)
    project = Path(config["primary"]).resolve()
    prefix = lean_source.exact_source_prefix(row, project)
    _, module = lean_source.import_header_end(prefix.text)
    directory, helper, environment = _helper(config, project, workdir, module, deadline)
    raw_output = workdir / "inventory.raw.json"
    proof_offset = len(declaration[:input_body - input_start].encode("utf-8"))
    command = ("#e6_native_inventory " + json.dumps(str(raw_output), ensure_ascii=False)
               + f" after {proof_offset} in\n")
    instrumented = command + declaration
    harness = prefix.text + instrumented.rstrip() + "\n"
    insertion, _ = lean_source.import_header_end(harness)
    imported = ("\nmeta import " if module else "\nimport ") + MODULE_NAME + "\n"
    harness = harness[:insertion] + imported + harness[insertion:]
    # The exact harness must end in our supplied target, so repeated declarations
    # or an accidental occurrence in an earlier comment cannot skew offsets.
    suffix = instrumented.rstrip() + "\n"
    if not harness.endswith(suffix):
        raise NativeProposalError("Native inventory harness lost the exact target suffix")
    decl_start = len(harness[:-len(suffix)].encode("utf-8")) + len(command.encode("utf-8"))
    input_byte_start = len(source[:input_start].encode("utf-8"))
    path = workdir / "Inventory.lean"
    path.write_text(harness, encoding="utf-8")
    run = _run(path, project, deadline, workdir / "inventory.log",
               lean_args=["-DmaxHeartbeats=100000000"], lean_path_prefixes=[directory])
    receipt = {"helper_build": helper, "run": run, "prefix_sha256": prefix.sha256,
               "environment_sha256": _sha(json.dumps(environment, sort_keys=True)),
               "source_form": "module" if module else "ordinary", "harness_path": str(path),
               "raw_inventory_path": str(raw_output)}
    _write(workdir / "native-run.json", receipt)
    if run["returncode"] != 0 or run["timed_out"] or not raw_output.is_file():
        raise NativeProposalError(f"Current-source native inventory failed; see {workdir / 'inventory.log'}")
    scan = json.loads(raw_output.read_text(encoding="utf-8"))
    if scan.get("schema_version") != SCHEMA_VERSION or scan.get("native_environment_target_present") is not False:
        raise NativeProposalError("Native inventory lacks its pre-target environment guard")
    shift = input_byte_start - decl_start
    for sequence in scan["sequences"]:
        sequence["start_byte"] += shift
        sequence["end_byte"] += shift
        for child in sequence["children"]:
            child["start_byte"] += shift
            child["end_byte"] += shift
    for term in scan["terms"]:
        for key in ("start_byte", "end_byte", "head_end_byte"):
            term[key] += shift
    scan["proof_start_byte"] += shift
    scan["declaration_start_byte"] = input_byte_start
    scan["declaration_end_byte"] = input_byte_start + len(declaration.encode("utf-8"))
    _write(workdir / "inventory.json", scan)
    return scan, receipt


def _rule_subsets(text: str, limit: int = 16) -> list[dict]:
    """Remove complete entries from a native-child simp/rw list, preserving suffix."""
    tokens = lex(text)
    if not tokens or tokens[0].text not in {"simp", "simpa", "simp_all", "rw", "erw"}:
        return []
    first = next((i for i, token in enumerate(tokens) if token.text == "["), None)
    if first is None:
        return []
    pairs = {"[": "]", "(": ")", "{": "}", "⟨": "⟩"}
    stack: list[str] = []
    boundaries = []
    begin = tokens[first].end
    close = None
    for token in tokens[first:]:
        if token.text in pairs:
            stack.append(pairs[token.text])
        elif stack and token.text == stack[-1]:
            stack.pop()
            if not stack:
                boundaries.append((begin, token.start))
                close = token.start
                break
        elif token.text == "," and len(stack) == 1:
            boundaries.append((begin, token.start))
            begin = token.end
    if close is None:
        return []
    rules = [text[a:b].strip() for a, b in boundaries]
    if not rules or not all(rules):
        return []
    masks = [[i] for i in range(len(rules))]
    if len(rules) > 2:
        half = len(rules) // 2
        masks += [list(range(half)), list(range(half, len(rules)))]
    masks.append(list(range(len(rules))))
    result = []
    for removed in masks[:limit]:
        replacement = (text[:tokens[first].end]
                       + ", ".join(rule for i, rule in enumerate(rules) if i not in removed)
                       + text[close:])
        result.append({"replacement": replacement, "removed_rule_indices": removed,
                       "removed_rules": [rules[i] for i in removed]})
    return result


def _safe_text(text: Any, limit: int = 240) -> bool:
    return (isinstance(text, str) and bool(text.strip()) and len(text) <= limit
            and not any(item in text for item in ("✝", "⋯", "?m.", "?u.", "sorry", "``", "\n", "\r")))


def _replay_text(text: Any, limit: int = 240) -> bool:
    """A printed value must contain no pretty-printer holes or opaque payloads.

    Deliberate inference holes in a newly built selective application are dealt
    with separately. A hole *inside* a printed argument is never evidence that
    the original elaborated argument can be reconstructed at the edit site.
    """
    if not _safe_text(text, limit):
        return False
    try:
        return all(token.kind != "opaque" and token.text != "_"
                   and not token.text.startswith("?") for token in lex(text))
    except ValueError:
        return False


def _term_replacements(old: str, record: dict) -> list[tuple[str, str, dict]]:
    out = []
    if old in {"_", ".."} or record.get("kind") in {"Lean.Parser.Term.hole", "num"}:
        return out
    atomic = re.fullmatch(r"[\w'.]+", old, re.UNICODE)
    for mode in ("normal", "explicit"):
        text = record.get(mode, "")
        if _replay_text(text) and text != old:
            text = text if re.fullmatch(r"[\w'.]+", text, re.UNICODE) or text.startswith("⟨") else "(" + text + ")"
            out.append(("native-" + mode, text, {}))
    for key, family in (("type", "inferred-type"), ("whnf_type", "normalized-type")):
        type_text = record.get(key, "")
        if _replay_text(type_text, 180) and len(old) < 180:
            if old == "‹_›":
                out.append((family, "‹" + type_text + "›", {"type": type_text}))
            elif not atomic:
                out.append((family, "(" + old + " : " + type_text + ")", {"type": type_text}))
    head_end = record.get("head_end_byte", record["start_byte"]) - record["start_byte"]
    raw = old.encode("utf-8")
    args = record.get("application", [])
    head = record.get("head_constant", "")
    head_text = raw[:head_end].decode("utf-8") if 0 < head_end <= len(raw) else ""
    # Native head TermInfo must resolve to the same unapplied constant as the
    # application. Dot notation, coercions and macros can elaborate to another
    # function with different binders. The exact spelling fallback supports old
    # inventories only; fresh inventories always carry an explicit decision.
    direct_head = record.get("surface_head_matches")
    if direct_head is None:
        direct_head = head_text == head and bool(re.fullmatch(r"[\w'.]+", head_text, re.UNICODE))
    if direct_head and 0 < head_end < len(raw) and not old.lstrip().startswith("@"):
        for argument in args:
            name = argument.get("name", "")
            if (argument.get("explicit") or argument.get("name_is_accessible") is False
                    or not re.fullmatch(r"(?:[^\W\d]|_)[\w']*", name, re.UNICODE)):
                continue
            if re.search(r"\(" + re.escape(name) + r"\s*:=", old):
                continue
            for value_key, family in (("value", "named-instance" if argument.get("instance") else "named-implicit"),
                                      ("whnf_type_value", "normalized-type-argument")):
                value = argument.get(value_key, "")
                if not _replay_text(value, 140):
                    continue
                added = " (" + name + " := " + value + ")"
                new = raw[:head_end].decode("utf-8") + added + raw[head_end:].decode("utf-8")
                out.append((family, new, argument))
    if args and _replay_text(head, 180):
        for selected in args:
            if selected.get("explicit") or not _replay_text(selected.get("value"), 150):
                continue
            if any(argument.get("explicit") and not _replay_text(argument.get("value"), 180) for argument in args):
                continue
            # Only omit parameters occurring in a later explicit binder's type.
            # An arbitrary omitted proof/instance parameter may leave an
            # unsynthesizable hole even though the original expression is closed.
            if any(not argument.get("explicit") and argument.get("index") != selected.get("index")
                   and not argument.get("inferable_from_explicit", False) for argument in args):
                continue
            values = [argument["value"] if argument.get("explicit") or argument.get("index") == selected.get("index") else "_"
                      for argument in args]
            def parenthesize(value):
                return value if re.fullmatch(r"[\w'.]+", value, re.UNICODE) else "(" + value + ")"
            new = "(@" + head + " " + " ".join(map(parenthesize, values)) + ")"
            if _safe_text(new, 420):
                out.append(("selective-instance" if selected.get("instance") else "selective-implicit", new, selected))
    return out


def _reindent(fragment: str, old_column: int, new_column: int) -> str:
    """Move an AST sequence out of a wrapper without disturbing internal layout."""
    lines = fragment.splitlines()
    if not lines:
        return fragment
    delta = old_column - new_column
    if delta >= 0:
        return "\n".join([lines[0], *[line[min(delta, len(line) - len(line.lstrip())):] for line in lines[1:]]])
    return "\n".join([lines[0], *[" " * -delta + line if line else line for line in lines[1:]]])


def _local_binding(tokens) -> str | None:
    """Recognize a named, non-instance local declaration, never a pattern binder."""
    if (len(tokens) < 4 or tokens[0].text not in {"have", "let"}
            or tokens[1].kind != "id" or tokens[1].text == "_"):
        return None
    # The saved proofs contain `have hq k := ...` and `have hEd j k := ...`.
    # Accept only simple named parameters; typed/pattern/instance binders still
    # abstain. An assignment nested in the type is not the declaration's RHS.
    depth, assignment = 0, None
    for i, token in enumerate(tokens[2:], 2):
        if token.text in {"(", "[", "{", "⟨"}:
            depth += 1
        elif token.text in {")", "]", "}", "⟩"}:
            depth -= 1
        elif token.text == ":=" and depth == 0:
            assignment = i
            break
    if assignment is None:
        return None
    head = tokens[2:assignment]
    colon = next((i for i, token in enumerate(head) if token.text == ":"), len(head))
    if not all(token.kind == "id" and token.text != "_" for token in head[:colon]):
        return None
    return tokens[1].text


def _normalization_list_index(tokens) -> int | None:
    """Locate an explicit rule list, including native simp option modifiers."""
    if not tokens or tokens[0].text not in {"simp", "simpa", "dsimp", "rw", "erw", "simp_rw"}:
        return None
    first = next((i for i, token in enumerate(tokens) if token.text == "["), None)
    if first is None:
        return None
    if tokens[0].text in {"simp", "simpa", "dsimp"}:
        return first if first > 1 and tokens[first - 1].text == "only" else None
    return first if first == 1 else None


def _transparent_continuation(tokens) -> bool:
    """Abstain on tactics whose local-context use is opaque to this analysis.

    This is a proposal recognizer, not a Lean parser or a validity certificate.
    Native child spans establish the boundaries; the small lexical fallback
    deliberately excludes automation, branch combinators, quotations and holes.
    """
    if not tokens or any(token.kind in {"opaque", "escaped"} for token in tokens):
        return False
    if any(token.text in {"by", "fun", "match", "`", ";", "<;>", "|", "?", "_"}
           or token.text.startswith("?") for token in tokens):
        return False
    if any(token.text == "at" for token in tokens) and any(token.text == "*" for token in tokens):
        return False
    first = tokens[0].text
    if first in {"have", "let"}:
        return _local_binding(tokens) is not None
    if first in {"simp", "simpa", "dsimp"}:
        return _normalization_list_index(tokens) is not None
    return first in {"exact", "apply", "refine", "rfl", "skip", "done", "clear", "rw", "erw"}


def _region_facts(raw: bytes, sequence: dict, terms: list[dict]) -> list[dict] | None:
    children = sequence.get("children", [])
    if len(children) > 256:
        return None
    facts = []
    for child in children:
        a, b = child["start_byte"], child["end_byte"]
        if not 0 <= a < b <= len(raw) or (facts and a < facts[-1]["end_byte"]):
            return None
        text = raw[a:b].decode("utf-8")
        try:
            tokens = lex(text)
        except ValueError:
            return None
        native_terms = [term for term in terms if a <= term["start_byte"] < term["end_byte"] <= b
                        and "free_variables" in term]
        lexical = {name for token in tokens if token.kind == "id"
                   for name in (token.text, token.text.split(".", 1)[0])}
        native = {name for term in native_terms for key in ("free_variables", "type_free_variables")
                  for name in term.get(key, [])}
        facts.append({**child, "text": text, "tokens": tokens, "binding": _local_binding(tokens),
                      "references": lexical | native, "native_references": native,
                      "native_term_count": len(native_terms),
                      "transparent": _transparent_continuation(tokens)})
    return facts


def _drop_local_rules(text: str, names: set[str]) -> str | None:
    """Remove only whole named-local entries in an explicit normalization list."""
    tokens = lex(text)
    first = _normalization_list_index(tokens)
    if first is None:
        return None
    pairs = {"[": "]", "(": ")", "{": "}", "⟨": "⟩"}
    stack, entries, start, close = [], [], tokens[first].end, None
    for token in tokens[first:]:
        if token.text in pairs:
            stack.append(pairs[token.text])
        elif stack and token.text == stack[-1]:
            stack.pop()
            if not stack:
                entries.append((start, token.start))
                close = token.start
                break
        elif token.text == "," and len(stack) == 1:
            entries.append((start, token.start))
            start = token.end
    if close is None:
        return None
    kept, dropped = [], False
    for a, b in entries:
        entry = text[a:b].strip()
        entry_tokens = lex(entry)
        bare = entry_tokens[1:] if entry_tokens and entry_tokens[0].text == "←" else entry_tokens
        if len(bare) == 1 and bare[0].text in names:
            dropped = True
        else:
            kept.append(entry)
    if not dropped:
        return None
    replacement = text[:tokens[first].end] + ", ".join(kept) + text[close:]
    # References in a location, a `using` term or a complex retained rule need
    # the deleted local. We only repair standalone local rule references.
    if any(token.text.split(".", 1)[0] in names for token in lex(replacement)):
        return None
    return replacement


def _normalizer_location(tokens) -> tuple[int | None, set[str]] | None:
    """Recognize a complete normalizer with a simple explicit location suffix.

    This establishes an edit shape, never independence from an opaque tactic.
    In particular, `at *`, combinators and `using` terms are outside the shape.
    """
    if not tokens or (tokens[0].text != "unfold" and _normalization_list_index(tokens) is None):
        return None
    depth, at = 0, None
    for i, token in enumerate(tokens):
        if token.kind in {"opaque", "escaped"}:
            return None
        if token.text in {"(", "[", "{", "⟨"}:
            depth += 1
        elif token.text in {")", "]", "}", "⟩"}:
            depth -= 1
        elif depth == 0:
            if token.text in {";", "<;>", "|", "using"}:
                return None
            if token.text == "at":
                at = i
                break
    if at is None:
        return None, {"⊢"}
    locations = tokens[at + 1:]
    if not locations or any(token.text == "*" or (token.kind != "id" and token.text != "⊢")
                            for token in locations):
        return None
    return at, {token.text for token in locations}


def _repair_local_normalizer(text: str, names: set[str]) -> tuple[str | None, str] | None:
    """Drop deleted locals from locations and whole explicit rule entries.

    None as a replacement means the tactic operated only on removed locals.
    A failed recognizer returns None for the entire result instead.
    """
    tokens = lex(text)
    location = _normalizer_location(tokens)
    if location is None:
        return None
    at, targets = location
    if at is not None and targets <= names:
        return None, "deleted_local_normalization_prune"
    replacement = text
    repaired = False
    if at is not None and targets & names:
        kept = [token.text for token in tokens[at + 1:] if token.text not in names]
        replacement = text[:tokens[at].end] + " " + " ".join(kept)
        repaired = True
    if any(token.text.split(".", 1)[0] in names for token in lex(replacement)):
        rules = _drop_local_rules(replacement, names)
        if rules is None:
            return None
        replacement, repaired = rules, True
    if not repaired or any(token.text.split(".", 1)[0] in names for token in lex(replacement)):
        return None
    return replacement, "explicit_local_normalizer_repair"


def _obvious_nonprogress_repeat(text: str) -> bool:
    """Reject only literal skip loops, including alternatives of `repeat first`.

    Native child deletion can turn the final tactic of a repeat body or a first
    branch into `skip`. Lean's repeat combinators need failure/progress, so full
    compilation would otherwise spend the candidate budget on this known loop.
    This is a narrow lexical guard, not a general termination analysis.
    """
    try:
        tokens = lex(text)
    except ValueError:
        return False

    def skip_end(index):
        opened = 0
        while index < len(tokens) and tokens[index].text == "(":
            opened += 1
            index += 1
        if index >= len(tokens) or tokens[index].text != "skip":
            return None
        index += 1
        for _ in range(opened):
            if index >= len(tokens) or tokens[index].text != ")":
                return None
            index += 1
        return index

    def column(token):
        return token.start - text.rfind("\n", 0, token.start) - 1

    for i, token in enumerate(tokens):
        if token.text not in {"repeat", "repeat'"} or token.kind != "id":
            continue
        body = i + 1
        if skip_end(body) is not None:
            return True
        while body < len(tokens) and tokens[body].text == "(":
            body += 1
        if body >= len(tokens) or tokens[body].text != "first":
            continue
        branch = body + 1
        if branch >= len(tokens) or tokens[branch].text != "|":
            continue
        pipe_column, first_line = column(tokens[branch]), text.count("\n", 0, tokens[branch].start)
        depth = 0
        for j in range(branch, len(tokens)):
            current = tokens[j]
            line = text.count("\n", 0, current.start)
            if line > first_line and column(current) < pipe_column:
                break
            if current.text in {"(", "[", "{", "⟨"}:
                depth += 1
            elif current.text in {")", "]", "}", "⟩"}:
                if depth == 0:
                    break
                depth -= 1
            if (current.text != "|" or depth
                    or (line > first_line and column(current) != pipe_column)):
                continue
            end = skip_end(j + 1)
            if end is None:
                continue
            if end == len(tokens) or tokens[end].text in {"|", ")", "]", "}"}:
                return True
            if ("\n" in text[tokens[end - 1].end:tokens[end].start]
                    and column(tokens[end]) <= column(current)):
                return True
    return False


def _regional_edits(raw: bytes, scan: dict, sequences: list[dict], max_window: int):
    """Bounded dependency-informed full-continuation edits; no local replay.

    Only outer proof sequences are used. Inner branch contexts may export
    locals through tactic combinators, so analyzing their suffix in isolation
    would be insufficient. Native free variables supplement lexical references,
    including dependencies inserted by implicit elaboration.
    """
    terms = scan.get("terms", [])
    minimum, maximum = scan["proof_start_byte"], scan.get("declaration_end_byte", len(raw))
    # Bounds precede containment and quotas: signature-side `by` sequences must
    # not consume the target proof's eight root slots (or its 512 sequence cap).
    sequences = [seq for seq in sequences
                 if minimum <= seq["start_byte"] < seq["end_byte"] <= maximum]
    outer = [seq for seq in sequences if not any(
        other["start_byte"] <= seq["start_byte"] < seq["end_byte"] <= other["end_byte"]
        and (other["start_byte"], other["end_byte"]) != (seq["start_byte"], seq["end_byte"])
        for other in sequences)]
    for sequence in outer[:8]:
        facts = _region_facts(raw, sequence, terms)
        if not facts:
            continue
        # A region may not discard an unexamined suffix of the declaration.
        if raw[sequence["end_byte"]:maximum].strip():
            continue
        def deletion(i, after):
            return ((facts[after]["start_byte"], "") if after < len(facts)
                    else (facts[after - 1]["end_byte"], "skip"))

        for i, fact in enumerate(facts):
            name = fact["binding"]
            if name:
                names = {name}
                # Grow only across named declarations dependent on this region.
                # Independent dead locals already have a single-site proposal.
                for after in range(i + 1, min(len(facts), i + max_window) + 1):
                    if after > i + 1:
                        next_fact = facts[after - 1]
                        if not next_fact["binding"] or not (next_fact["references"] & names):
                            break
                        if next_fact["binding"] in names:
                            break
                        names.add(next_fact["binding"])
                    suffix = facts[after:]
                    if not all(item["transparent"] for item in suffix):
                        # Opaque automation can use locals absent from all
                        # recorded terms. Propose only a bounded deletion plus
                        # explicit follow-up repairs; never call it unused or
                        # claim native dependency certification. Full-source
                        # compilation and the usual exact/axiom/compatibility
                        # checks are the sole arbiter for these trial families.
                        if len(suffix) > 12:
                            continue
                        changes, repairs, possible = [], [], True
                        for j in range(after, len(facts)):
                            item = facts[j]
                            if not item["references"] & names:
                                continue
                            tokens = item["tokens"]
                            if tokens and tokens[0].text == "clear" and all(token.kind == "id" for token in tokens):
                                kept = [token.text for token in tokens[1:] if token.text not in names]
                                replacement, repair = ("clear " + " ".join(kept) if kept else None), "clear_local_prune"
                            else:
                                fixed = _repair_local_normalizer(item["text"], names)
                                if fixed is None:
                                    possible = False
                                    break
                                replacement, repair = fixed
                            end = item["end_byte"]
                            if replacement is None:
                                end, replacement = deletion(j, j + 1)
                            changes.append((item["start_byte"], end, replacement))
                            repairs.append({"start_byte": item["start_byte"], "repair": repair})
                        if not possible or not repairs or len(repairs) > min(3, max_window):
                            continue
                        end, replacement = deletion(i, after)
                        changes.append((fact["start_byte"], end, replacement))
                        start, stop = fact["start_byte"], facts[-1]["end_byte"]
                        edited = raw[start:stop]
                        for a, b, replacement in sorted(changes, reverse=True):
                            edited = edited[:a - start] + replacement.encode("utf-8") + edited[b - start:]
                        yield (start, stop, edited.decode("utf-8"), "native-regional-opaque-repair",
                               {"removed_local_names": sorted(names), "width": after - i,
                                "continuation_repairs": repairs, "opaque_trial": True,
                                "opaque_continuation_start_bytes": [item["start_byte"] for item in suffix
                                                                     if not item["transparent"]],
                                "dependency_evidence": "bounded_explicit_reference_repairs_only",
                                "native_dependency_certified": False,
                                "retains_complete_continuation": True,
                                "candidate_validity": "requires_full_source_validation"})
                        continue
                    native_count = sum(item["native_term_count"] for item in suffix)
                    metadata = {"removed_local_names": sorted(names), "width": after - i,
                                "dependency_evidence": ("native_term_free_variables_and_conservative_lexical_suffix"
                                                        if native_count else "conservative_lexical_suffix"),
                                "native_suffix_terms": native_count,
                                "retains_complete_continuation": True,
                                "candidate_validity": "requires_full_source_validation"}
                    if not any(item["references"] & names for item in suffix):
                        end, replacement = deletion(i, after)
                        yield (fact["start_byte"], end, replacement,
                               "native-regional-unused-local" if after == i + 1 else "native-regional-prune", metadata)
                        continue
                    # Cheap repair only removes explicit references in `clear`
                    # or whole simp-only rule entries. It never starts a solver.
                    if len(suffix) > 8:
                        continue
                    changes, repair_sites, possible = [], [], True
                    for j in range(after, len(facts)):
                        item = facts[j]
                        if not item["references"] & names:
                            continue
                        tokens = item["tokens"]
                        if tokens[0].text == "clear" and all(token.kind == "id" for token in tokens):
                            kept = [token.text for token in tokens[1:] if token.text not in names]
                            if kept:
                                changes.append((item["start_byte"], item["end_byte"], "clear " + " ".join(kept)))
                            else:
                                end, replacement = deletion(j, j + 1)
                                changes.append((item["start_byte"], end, replacement))
                            repair_sites.append({"start_byte": item["start_byte"], "repair": "clear_local_prune"})
                        else:
                            repaired = _drop_local_rules(item["text"], names)
                            if repaired is None:
                                possible = False
                                break
                            changes.append((item["start_byte"], item["end_byte"], repaired))
                            repair_sites.append({"start_byte": item["start_byte"], "repair": "explicit_local_rule_prune"})
                    if not possible or not repair_sites or len(repair_sites) > 2:
                        continue
                    end, replacement = deletion(i, after)
                    changes.append((fact["start_byte"], end, replacement))
                    start, stop = fact["start_byte"], facts[-1]["end_byte"]
                    edited = raw[start:stop]
                    for a, b, replacement in sorted(changes, reverse=True):
                        edited = edited[:a - start] + replacement.encode("utf-8") + edited[b - start:]
                    yield (start, stop, edited.decode("utf-8"), "native-regional-repair",
                           {**metadata, "continuation_repairs": repair_sites})

            # Move explicit normalizers across independent local declarations
            # to the next continuation site, keeping native separators intact.
            tokens = fact["tokens"]
            if (not tokens or tokens[0].text not in {"simp", "dsimp", "rw", "erw"}
                    or _normalization_list_index(tokens) is None):
                continue
            location = _normalizer_location(tokens)
            if location is None:
                continue
            _, targets = location
            affected = targets - {"⊢"}
            opaque = not fact["transparent"]
            for j in range(i + 1, min(len(facts) - 1, i + max_window) + 1):
                moved = facts[j]
                if (not moved["binding"]
                        or moved["references"] & affected or moved["binding"] in fact["references"]):
                    break
                opaque = opaque or not moved["transparent"]
                separator = raw[fact["end_byte"]:facts[i + 1]["start_byte"]]
                block = raw[facts[i + 1]["start_byte"]:moved["end_byte"]]
                replacement = (block + separator + raw[fact["start_byte"]:fact["end_byte"]]).decode("utf-8")
                yield (fact["start_byte"], moved["end_byte"], replacement,
                       "native-regional-opaque-normalization-delay" if opaque else "native-regional-normalization-delay",
                       {"moved_across_local_names": [item["binding"] for item in facts[i + 1:j + 1]],
                        "affected_local_names": sorted(affected),
                        "continuation_start_byte": facts[j + 1]["start_byte"] if j + 1 < len(facts) else sequence["end_byte"],
                        "dependency_evidence": ("bounded_explicit_reference_screen_only" if opaque else
                                                "native_term_free_variables_and_conservative_lexical_suffix"
                                                if any(item["native_term_count"] for item in facts[i + 1:j + 1])
                                                else "conservative_lexical_suffix"),
                        **({"opaque_trial": True, "native_dependency_certified": False} if opaque else {}),
                        "retains_complete_continuation": True,
                        "candidate_validity": "requires_full_source_validation"})

            # One adjacent explicit normalizer at a disjoint location is a
            # useful bounded trial even when its rule terms or the continuation
            # contain opaque syntax. Do not move across arbitrary automation.
            if i + 1 >= len(facts) or max_window < 1:
                continue
            moved = facts[i + 1]
            moved_location = _normalizer_location(moved["tokens"])
            if moved_location is None:
                continue
            _, moved_targets = moved_location
            if (targets & moved_targets or moved["references"] & affected
                    or fact["references"] & (moved_targets - {"⊢"})):
                continue
            separator = raw[fact["end_byte"]:moved["start_byte"]]
            replacement = (raw[moved["start_byte"]:moved["end_byte"]] + separator
                           + raw[fact["start_byte"]:fact["end_byte"]]).decode("utf-8")
            yield (fact["start_byte"], moved["end_byte"], replacement,
                   "native-regional-opaque-normalization-delay",
                   {"affected_local_names": sorted(affected), "moved_across_targets": sorted(moved_targets),
                    "continuation_start_byte": facts[i + 2]["start_byte"] if i + 2 < len(facts) else sequence["end_byte"],
                    "opaque_trial": True, "native_dependency_certified": False,
                    "dependency_evidence": "bounded_explicit_reference_screen_only",
                    "retains_complete_continuation": True,
                    "candidate_validity": "requires_full_source_validation"})


def proposals_from_inventory(source: str, scan: dict, *, max_candidates: int = 128,
                             max_window: int = 4, regional: bool = False,
                             policy: str = "legacy", policy_maximum: int | None = None,
                             inventory_summary: dict | None = None) -> list[dict]:
    """Create deterministic full-source edits from native, UTF-8 byte spans.

    Legacy keeps its original bounded round-robin prefix. Opt-in policies see
    every family in that bounded inventory before applying the output cap, so
    exploration quotas can refill from later cleanup proposals. Canonical IDs
    are assigned in the original round-robin order before policy selection.
    """
    from .deterministic_support.search_policy import POLICIES, exploration_quotas, order_candidates
    if not isinstance(policy, str) or policy not in POLICIES:
        raise ValueError("Unknown native proposal policy")
    if type(max_candidates) is not int or max_candidates < 0:
        raise ValueError("max_candidates must be a nonnegative integer")
    policy_maximum = max_candidates if policy_maximum is None else policy_maximum
    if policy != "legacy":
        exploration_quotas(policy_maximum)
        if policy_maximum < max_candidates:
            raise ValueError("policy_maximum must cover the native candidate cap")
    regional = regional or policy in {"regional", "deep"}
    raw = source.encode("utf-8")
    minimum = scan["proof_start_byte"]
    maximum = scan.get("declaration_end_byte", len(raw))
    groups: dict[str, deque] = defaultdict(deque)
    seen: set[str] = set()
    has_repeat = b"repeat" in raw

    def add(a: int, b: int, replacement: str, family: str, **metadata):
        if not minimum <= a < b <= maximum:
            return
        if len(groups.get(family, ())) >= max_candidates:
            return
        try:
            old = raw[a:b].decode("utf-8")
            edited = (raw[:a] + replacement.encode("utf-8") + raw[b:]).decode("utf-8")
        except UnicodeDecodeError:
            return
        if has_repeat and _obvious_nonprogress_repeat(edited):
            return
        digest = _sha(edited)
        if edited == source or digest in seen:
            return
        seen.add(digest)
        groups[family].append({"family": family, "source": edited, "source_sha256": digest,
                               "start_byte": a, "end_byte": b, "old": old, "replacement": replacement,
                               "validation_required": "complete_source_exact_axioms_and_compatibility",
                               "provenance": "native_current_source_inventory", **metadata})

    sequences = sorted((seq for seq in scan.get("sequences", [])
                        if minimum <= seq["start_byte"] < seq["end_byte"] <= maximum),
                       key=lambda seq: (seq["end_byte"] - seq["start_byte"], seq["start_byte"]))[:512]
    if regional:
        for a, b, replacement, family, metadata in _regional_edits(raw, scan, sequences, max_window):
            add(a, b, replacement, family, **metadata)
    wrappers_seen = set()
    for sequence in sequences:
        children = sequence["children"]
        for i, child in enumerate(children):
            a, ce = child["start_byte"], child["end_byte"]
            if not minimum <= a < ce <= maximum:
                continue
            original = raw[a:ce].decode("utf-8")
            metadata = {"child_end_byte": ce, "sequence_end_byte": sequence["end_byte"],
                        "retains_complete_continuation": True, "syntax_kind": child.get("kind")}
            for width in range(1, (1 if regional else min(max_window, len(children) - i)) + 1):
                after = i + width
                if after < len(children):
                    # Consume separator/indentation before the following child.
                    end, replacement = children[after]["start_byte"], ""
                else:
                    end, replacement = children[after - 1]["end_byte"], "skip"
                add(a, end, replacement, "native-delete" if width == 1 else "native-delete-window", width=width, **metadata)
            for subset in _rule_subsets(original):
                add(a, ce, subset["replacement"], "native-rule-subset", **metadata,
                    **{key: value for key, value in subset.items() if key != "replacement"})
                for width in range(2, (1 if regional else min(max_window, len(children) - i)) + 1):
                    end = children[i + width - 1]["end_byte"]
                    add(a, end, subset["replacement"], "native-subset-delete-window", width=width, **metadata,
                        **{key: value for key, value in subset.items() if key != "replacement"})
            # Only direct nested sequence bodies are flattened. Case/goal
            # dispatch wrappers may need their binders and will fail complete
            # validation if flattening changes scope; no local replay certifies it.
            nested = [seq for seq in sequences if a <= seq["start_byte"] < seq["end_byte"] <= ce
                      and (seq["start_byte"], seq["end_byte"]) != (a, ce)]
            direct = [seq for seq in nested if not any(
                a <= other["start_byte"] <= seq["start_byte"] < seq["end_byte"] <= other["end_byte"] <= ce
                and other is not seq and (other["start_byte"], other["end_byte"]) != (seq["start_byte"], seq["end_byte"])
                for other in nested)]
            for inner in direct:
                key = a, ce, inner["start_byte"], inner["end_byte"]
                if key in wrappers_seen or not inner["children"]:
                    continue
                wrappers_seen.add(key)
                ia, ib = inner["children"][0]["start_byte"], inner["children"][-1]["end_byte"]
                outer_col = len(raw[:a].decode("utf-8").rsplit("\n", 1)[-1])
                inner_col = len(raw[:ia].decode("utf-8").rsplit("\n", 1)[-1])
                body = _reindent(raw[ia:ib].decode("utf-8"), inner_col, outer_col)
                add(a, ce, body, "native-delete-wrapper", inner_sequence_start_byte=ia, **metadata)

    terms_by_span: dict[tuple[int, int], list[dict]] = defaultdict(list)
    for term in scan.get("terms", []):
        a, b = term["start_byte"], term["end_byte"]
        if minimum <= a < b <= maximum:
            terms_by_span[a, b].append(term)
    for (a, b), records in sorted(terms_by_span.items()):
        if all(record.get("is_constant") for record in records):
            continue
        old = raw[a:b].decode("utf-8")
        if not _safe_text(old, 500):
            continue
        per_context = []
        for record in records:
            head_end = record.get("head_end_byte", a)
            heads = terms_by_span.get((a, head_end), [])
            # Require consensus if overloaded/macro syntax recorded more than
            # one head. Constant-only records are inventory evidence, not edits.
            if "is_constant" in record:
                record = {**record, "surface_head_matches": bool(heads) and all(
                    head.get("is_constant") and head.get("constant_name") == record.get("head_constant")
                    for head in heads)}
            per_context.append({(family, replacement): metadata
                                for family, replacement, metadata in _term_replacements(old, record)})
        shared = set.intersection(*(set(values) for values in per_context))
        for family, replacement in sorted(shared):
            add(a, b, replacement, family, observed_contexts=len(records),
                type_hint=records[0].get("type"), normalized_type_hint=records[0].get("whnf_type"),
                native_argument=per_context[0][family, replacement])

    # A bounded search should reach every proposal family before it exhausts
    # the much larger deletion or pretty-print families.
    if inventory_summary is not None:
        inventory_summary.update(bounded_candidate_count=sum(map(len, groups.values())),
            bounded_family_counts={family: len(items) for family, items in groups.items()},
            per_family_cap=max_candidates, policy_maximum=policy_maximum)
    result = []
    while groups and (policy != "legacy" or len(result) < max_candidates):
        for family in list(groups):
            proposal = groups[family].popleft()
            proposal["id"] = "native-" + str(len(result))
            result.append(proposal)
            if not groups[family]:
                del groups[family]
            if policy == "legacy" and len(result) >= max_candidates:
                break
    return result if policy == "legacy" else order_candidates(
        result, policy=policy, maximum=policy_maximum)[:max_candidates]


def generate(config: dict, source: str, workdir: Path, *, timeout_seconds: int = 90,
             max_candidates: int = 128, regional: bool = False,
             policy: str = "legacy", policy_maximum: int | None = None) -> list[dict]:
    """Collect native metadata and propose edits to this exact current source.

    config requires task, primary, and optionally root/elan_home. Artifacts are
    private to workdir; the stable helper cache lives in the private run root.
    A helper failure is recorded and raised so callers can distinguish a broken
    compiler integration from a successful inventory with no applicable edits.
    """
    if (isinstance(timeout_seconds, bool) or not isinstance(timeout_seconds, (int, float))
            or not math.isfinite(timeout_seconds) or timeout_seconds <= 0):
        raise ValueError("timeout_seconds must be finite and positive")
    if type(max_candidates) is not int or max_candidates < 0:
        raise ValueError("max_candidates must be a nonnegative integer")
    if type(regional) is not bool:
        raise ValueError("regional must be a boolean")
    from .deterministic_support.search_policy import POLICIES
    if not isinstance(policy, str) or policy not in POLICIES:
        raise ValueError("Unknown native proposal policy")
    if policy != "legacy":
        from .deterministic_support.search_policy import exploration_quotas
        exploration_quotas(max_candidates if policy_maximum is None else policy_maximum)
        if policy_maximum is not None and policy_maximum < max_candidates:
            raise ValueError("policy_maximum must cover the native candidate cap")
    regional = regional or policy in {"regional", "deep"}
    if not isinstance(source, str) or not source.strip() or "\r" in source:
        raise ValueError("Native proposals require nonempty LF source")
    workdir = Path(workdir).resolve()
    project = Path(config["primary"]).resolve()
    if workdir.is_relative_to(project):
        raise ValueError("Native proposal workdir must be outside the cached Lean project")
    workdir.mkdir(parents=True, exist_ok=True)
    receipt = {"schema_version": SCHEMA_VERSION, "status": "running", "source_sha256": _sha(source),
               "helper_source_sha256": _sha(HELPER_SOURCE), "model_calls": 0,
               "timeout_seconds": timeout_seconds, "max_candidates": max_candidates, "regional": regional,
               "policy": policy, "policy_maximum": policy_maximum,
               "validation_required": "complete_source_exact_axioms_and_compatibility"}
    _write(workdir / "native-proposals.json", receipt)
    started = time.perf_counter()
    deadline = started + timeout_seconds
    try:
        _, row = arena.load_task(Path(config["task"]))
        _current_source(row, source)
        if max_candidates == 0:
            candidates = []
        else:
            values = RuntimeContext.resolve(Path(config.get("root", workdir)), config).environment(workdir)
            # Respect the panel's shared gate/priority when they are already
            # configured; host-only defaults fill any missing values.
            values = {key: os.environ.get(key, value) for key, value in values.items()}
            values["LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE"] = "request"
            values["LEAN_REFACTOR_LAUNCH_CACHE"] = str(Path(config.get("root", workdir)) / "deterministic" / "native-launch-cache")
            configured = configure_native_environment(elan_home=config.get("elan_home"))
            with scoped_environment({**values, **configured}):
                request_dir = Path(tempfile.mkdtemp(prefix="inventory-" + _sha(source)[:12] + "-", dir=workdir))
                scan, run = _inventory(config, source, row, request_dir, deadline)
            receipt.update(run)
            receipt["inventory_counts"] = {"sequences": len(scan.get("sequences", [])),
                                            "terms": len(scan.get("terms", [])),
                                            "term_failures": scan.get("term_failures", 0)}
            proposal_inventory = {}
            candidates = proposals_from_inventory(source, scan, max_candidates=max_candidates,
                regional=regional, policy=policy, policy_maximum=policy_maximum,
                inventory_summary=proposal_inventory)
            receipt["proposal_inventory"] = proposal_inventory
            # Defense in depth at the pure proposal boundary: native byte spans
            # can never authorize edits to the statement or scaffold.
            admitted, rejected = [], []
            for candidate in candidates:
                try:
                    _current_source(row, candidate["source"])
                    admitted.append(candidate)
                except arena.WorkflowError as error:
                    rejected.append({"id": candidate["id"], "family": candidate["family"], "error": str(error)})
            candidates = admitted
            receipt["admission_rejections"] = rejected
        receipt.update(status="completed", candidate_count=len(candidates),
                       candidates=[{key: value for key, value in candidate.items() if key != "source"}
                                   for candidate in candidates])
        return candidates
    except Exception as error:
        receipt.update(status="failed", error_type=type(error).__name__, error=str(error))
        raise NativeProposalError(f"Native proposal generation failed; see {workdir / 'native-proposals.json'}: {error}") from error
    finally:
        receipt["wall_seconds"] = time.perf_counter() - started
        _write(workdir / "native-proposals.json", receipt)
