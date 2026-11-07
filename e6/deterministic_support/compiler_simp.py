"""Harvest native sufficient-simp suggestions for one immutable current source.

Discovery elaborates the exact pre-target prefix with query heads, then reads
Lean's structured TryThis TextEdits through the existing LSP probe interface.
Printed diagnostic text is never parsed as a replacement. A failed or timed-out
query contributes no partial candidates. This is only proposal generation;
fresh complete-source exact, axiom and compatibility validation is mandatory.
"""
from __future__ import annotations

from bisect import bisect_left
from dataclasses import dataclass
import json
import math
import os
from pathlib import Path
import tempfile
import time

from lean_tools import arena_workflow as arena, lean_launch, lean_source
from lean_tools import persistent_quick_workflow as persistent
from lean_tools.proof_specialization import lex
from .. import deterministic_native as native
from ..config import configure_native_environment
from ..runtime import RuntimeContext, scoped_environment
from . import edit_packs
from .source_proposals import _end

SCHEMA_VERSION = 1
MAX_SITES = 32
MAX_CANDIDATES = 32
MAX_ACTIONS = 128
MAX_ACTION_BYTES = 4_000_000
MAX_REPLACEMENT_CHARS = 4096
MAX_TIMEOUT_SECONDS = 90
HEADS = frozenset({"simp", "simpa", "simp_all"})
FAMILY = "compiler_simp_specialization"


class CompilerSimpError(RuntimeError):
    pass


@dataclass(frozen=True)
class Site:
    start: int
    head_end: int
    end: int
    tactic: str


def discover_sites(declaration: str, signature: str, *, max_sites: int = MAX_SITES) -> list[Site]:
    """Recognize ordinary tactic heads; opaque syntax and quotes fail closed."""
    if type(max_sites) is not int or not 0 <= max_sites <= MAX_SITES:
        raise ValueError(f"max_sites must be an integer in 0..{MAX_SITES}")
    if len(declaration) > 500_000:
        return []
    try:
        tokens = lex(declaration)
    except ValueError:
        return []
    from .mutations import _assignment_index_after_signature
    assignment = _assignment_index_after_signature(declaration, tokens, signature)
    if assignment is None or len(tokens) > 40_000:
        return []
    minimum = tokens[assignment].end
    if any(token.start >= minimum and (token.kind == "opaque" or token.text == "`") for token in tokens):
        return []
    found = []
    for index, token in enumerate(tokens):
        if token.start < minimum or token.kind != "id" or token.text not in HEADS:
            continue
        if index + 1 < len(tokens) and tokens[index + 1].text == "?":
            continue
        previous = tokens[index - 1].text if index else ""
        line_start = declaration.rfind("\n", 0, token.start) + 1
        prefix = declaration[line_start:token.start]
        after_boundary = previous in {"by", "=>", ";", "<;>", "·", "|", "all_goals", "any_goals"}
        if prefix.strip() and not after_boundary:
            continue
        end = _end(declaration, tokens, index)
        if end > token.end:
            found.append(Site(token.start, token.end, end, token.text))
        else:
            # Bare simp/simp_all is a particularly useful specialization site.
            found.append(Site(token.start, token.end, token.end, token.text))
        if len(found) == max_sites:
            break
    return found if max_sites else []


def query_source(declaration: str, sites: list[Site]) -> str:
    output = declaration
    for site in reversed(sites):
        if declaration[site.start:site.head_end] != site.tactic:
            raise ValueError("Query site is not bound to the source tactic")
        output = output[:site.head_end] + "?" + output[site.head_end:]
    return output


def lsp_offset(source: str, position: dict) -> int:
    """Convert strict UTF-16 positions; reject surrogate-interior/outside spans."""
    if (not isinstance(position, dict) or type(position.get("line")) is not int
            or type(position.get("character")) is not int
            or position["line"] < 0 or position["character"] < 0):
        raise ValueError("Invalid LSP position")
    lines = source.split("\n")
    line, character = position["line"], position["character"]
    if line >= len(lines):
        raise ValueError("LSP position is outside document")
    content = lines[line]
    offset = sum(len(value) + 1 for value in lines[:line])
    units = 0
    for index, char in enumerate(content):
        if units == character:
            return offset + index
        units += len(char.encode("utf-16-le")) // 2
        if units > character:
            raise ValueError("LSP position splits a surrogate pair")
    if units == character:
        return offset + len(content)
    raise ValueError("LSP character is outside line")


def _replacement(text: object) -> bool:
    if (not isinstance(text, str) or not text.strip() or len(text) > MAX_REPLACEMENT_CHARS
            or any(marker in text for marker in ("✝", "⋯", "?m.", "?u.", "--", "/-", "-/", "`"))):
        return False
    try:
        tokens = lex(text)
    except ValueError:
        return False
    return (len(tokens) >= 2 and tokens[0].text in HEADS and tokens[1].text == "only"
            and not any(token.kind == "opaque" or token.text in {"_", "sorry", "admit", "sorryAx"}
                        for token in tokens))


def map_edits(source: str, declaration: str, input_start: int, proof_start: int,
              sites: list[Site], query: str, harness: str, harness_start: int,
              edits: list[dict], *, max_candidates: int = MAX_CANDIDATES) -> tuple[list[dict], list[dict]]:
    """Map query-only insertions back to codepoints in the immutable source."""
    if harness[harness_start:harness_start + len(query)] != query or query != query_source(declaration, sites):
        raise ValueError("Query source binding mismatch")
    if source[input_start:input_start + len(declaration)] != declaration:
        raise ValueError("Current declaration binding mismatch")
    parent = edit_packs.digest(source)
    query_starts = {site.start + index: site for index, site in enumerate(sites)}
    markers = [site.head_end + index for index, site in enumerate(sites)]
    singles, rejected, seen = [], [], {parent}
    for number, edit in enumerate(edits):
        try:
            if not isinstance(edit, dict) or not _replacement(edit.get("newText")):
                raise ValueError("not a sufficient-simp replacement")
            value = edit.get("range", {})
            begin = lsp_offset(harness, value.get("start")) - harness_start
            end = lsp_offset(harness, value.get("end")) - harness_start
            site = query_starts.get(begin)
            if site is None or not begin < end <= len(query):
                raise ValueError("edit lacks a unique query-site start")
            raw_start = begin - bisect_left(markers, begin)
            raw_end = end - bisect_left(markers, end)
            if (raw_start != site.start or not site.head_end <= raw_end <= site.end
                    or not proof_start <= input_start + raw_start < input_start + raw_end
                    or end <= site.head_end + len([point for point in markers if point < begin])):
                raise ValueError("edit exceeds its original tactic span")
            a, b, new = input_start + raw_start, input_start + raw_end, edit["newText"]
            old = source[a:b]
            child = source[:a] + new + source[b:]
            hashed = edit_packs.digest(child)
            if hashed in seen:
                continue
            seen.add(hashed)
            bound = {"start": a, "end": b, "old": old, "new": new,
                     "old_sha256": edit_packs.digest(old), "new_sha256": edit_packs.digest(new),
                     "offset_unit": edit_packs.OFFSET_UNIT}
            singles.append({"id": FAMILY + ":" + hashed[:16], "family": FAMILY,
                            "description": "Native compiler sufficient-simp specialization",
                            "source": child, "parent_sha256": parent, "source_sha256": hashed,
                            "site": a, "edits": [bound], "requires_full_validation": True,
                            "validation_required": "complete_source_exact_axioms_and_compatibility",
                            "mapped_by": "Lean TryThisInfo LSP TextEdit"})
        except (ValueError, TypeError, AttributeError, KeyError) as error:
            rejected.append({"edit_index": number, "reason": str(error)})
    # Preserve individual compiler evidence, then add a few compatible subsets.
    # No local-state equivalence is claimed; unchanged continuations replay in
    # the engine's ordinary complete-source evaluator.
    packs = edit_packs.compose(source, singles, minimum=proof_start,
                              maximum=input_start + len(declaration), max_candidates=8,
                              allow_same_family_packs=True)
    result = []
    # Reserve up to one quarter for bundles when several simp sites can compose.
    single_cap = max_candidates - min(len(packs), max_candidates // 4)
    for item in singles[:single_cap]:
        result.append(item)
    for pack in packs[:max_candidates - len(result)]:
        edits = pack["edits"]
        child = source
        for edit in sorted(edits, key=lambda value: value["start"], reverse=True):
            child = child[:edit["start"]] + edit["new"] + child[edit["end"]:]
        hashed = edit_packs.digest(child)
        result.append({**pack, "id": FAMILY + ":" + hashed[:16], "family": FAMILY,
                       "source": child, "parent_sha256": parent, "source_sha256": hashed,
                       "requires_full_validation": True,
                       "validation_required": "complete_source_exact_axioms_and_compatibility",
                       "mapped_by": "Lean TryThisInfo LSP TextEdit", "compiler_edit_pack": True})
    return result, rejected


def _remaining(deadline: float) -> float:
    value = deadline - time.monotonic()
    if value <= 0:
        raise TimeoutError("Compiler simp discovery deadline expired")
    return value


def _discover(harness: str, project: Path, directory: Path, deadline: float) -> tuple[list[dict], dict]:
    path = directory / "Query.lean"
    path.write_text(harness, encoding="utf-8")
    started = time.monotonic()
    receipt = {"status": "running", "harness_path": str(path), "harness_sha256": edit_packs.digest(harness)}
    with arena.resource_gate.permit_from_environment("lean", timeout_seconds=_remaining(deadline),
            metadata={"purpose": "deterministic-compiler-simp", "project_root": str(project)}) as lease:
        session = persistent.LeanLspSession(project, path, directory / "lsp.stderr.log", _remaining(deadline))
        session.request_deadline = deadline
        try:
            session.start()
            elapsed, diagnostics = session.open_document(harness)
            counts = {kind: sum(item.severity == kind for item in diagnostics)
                      for kind in ("error", "warning", "information")}
            receipt.update(compile_completed=True, diagnostic_counts=counts, compile_seconds=elapsed,
                           queue_wait_seconds=lease.queue_wait_seconds,
                           startup_seconds=session.startup_seconds)
            arena.write_json_atomic(directory / "diagnostics.json", [item.as_json() for item in diagnostics])
            if counts["error"]:
                raise CompilerSimpError("Query document has compiler errors; all partial suggestions discarded")
            end = {"line": harness.count("\n"), "character": len(harness.rsplit("\n", 1)[-1].encode("utf-16-le")) // 2}
            contextual = [{"range": {"start": {"line": item.line, "character": item.character},
                                      "end": {"line": item.line, "character": item.character}},
                           "severity": 3, "message": "Try this"}
                          for item in diagnostics if item.line is not None and item.character is not None
                          and item.severity == "information"]
            actions = session._request("textDocument/codeAction", {
                "textDocument": {"uri": session.uri}, "range": {"start": {"line": 0, "character": 0}, "end": end},
                "context": {"diagnostics": contextual, "triggerKind": 1}})
            if not isinstance(actions, list) or len(actions) > MAX_ACTIONS:
                raise CompilerSimpError("Unsupported or over-limit native code-action response")
            if len(json.dumps(actions, ensure_ascii=False)) > MAX_ACTION_BYTES:
                raise CompilerSimpError("Native code-action response exceeds byte cap")
            collected, rejected, resolved_count = [], [], 0
            for number, action in enumerate(actions):
                if not isinstance(action, dict):
                    rejected.append({"action": number, "reason": "invalid code action"})
                    continue
                if not isinstance(action.get("edit"), dict) and action.get("data") is not None:
                    _remaining(deadline)
                    action = session._request("codeAction/resolve", action)
                    resolved_count += 1
                if not isinstance(action, dict) or not isinstance(action.get("edit"), dict):
                    continue
                edit = action["edit"]
                changes = []
                valid = True
                if "changes" in edit:
                    mapping = edit["changes"]
                    if not isinstance(mapping, dict) or set(mapping) - {session.uri}:
                        valid = False
                    elif isinstance(mapping.get(session.uri), list):
                        changes.extend(mapping[session.uri])
                if "documentChanges" in edit:
                    documents = edit["documentChanges"]
                    if not isinstance(documents, list):
                        valid = False
                    else:
                        for document in documents:
                            if (not isinstance(document, dict) or not isinstance(document.get("textDocument"), dict)
                                    or document["textDocument"].get("uri") != session.uri
                                    or document["textDocument"].get("version") not in (None, session.version)
                                    or not isinstance(document.get("edits"), list)):
                                valid = False
                                break
                            changes.extend(document["edits"])
                if not valid or len(changes) != 1:
                    rejected.append({"action": number, "reason": "foreign, stale, or non-singleton edit action"})
                    continue
                collected.extend(changes)
            receipt.update(status="completed", action_count=len(actions), resolved_action_count=resolved_count,
                           edit_count=len(collected), rejected_actions=rejected)
            arena.write_json_atomic(directory / "native-actions.json", actions)
            arena.write_json_atomic(directory / "native-edits.json", collected)
            _remaining(deadline)
            return collected, receipt
        except Exception as error:
            receipt.update(status="failed", error_type=type(error).__name__, error=str(error),
                           partial_candidates_discarded=True)
            raise
        finally:
            session.close()
            receipt["wall_seconds"] = time.monotonic() - started
            arena.write_json_atomic(directory / "discovery.json", receipt)


def generate(config: dict, source: str, workdir: Path, *, max_candidates: int = MAX_CANDIDATES,
             timeout_seconds: float = MAX_TIMEOUT_SECONDS) -> list[dict]:
    """Discover once, atomically publish proposals/telemetry, never rebuild/retry."""
    if type(max_candidates) is not int or not 0 <= max_candidates <= MAX_CANDIDATES:
        raise ValueError(f"max_candidates must be an integer in 0..{MAX_CANDIDATES}")
    if (isinstance(timeout_seconds, bool) or not isinstance(timeout_seconds, (int, float))
            or not math.isfinite(timeout_seconds) or not 0 < timeout_seconds <= MAX_TIMEOUT_SECONDS):
        raise ValueError(f"timeout_seconds must be finite and in (0, {MAX_TIMEOUT_SECONDS}]")
    if not isinstance(source, str) or not source.strip() or "\r" in source:
        raise ValueError("Compiler simp proposals require nonempty LF source")
    workdir, project = Path(workdir).resolve(), Path(config["primary"]).resolve()
    if workdir.is_relative_to(project):
        raise ValueError("Compiler discovery must be outside the cached Lean project")
    workdir.mkdir(parents=True, exist_ok=True)
    started, deadline = time.monotonic(), time.monotonic() + timeout_seconds
    receipt = {"schema_version": SCHEMA_VERSION, "status": "running",
               "source_sha256": edit_packs.digest(source), "model_calls": 0,
               "limits": {"max_sites": MAX_SITES, "max_candidates": max_candidates,
                          "max_actions": MAX_ACTIONS, "timeout_seconds": timeout_seconds},
               "validation_required": "complete_source_exact_axioms_and_compatibility"}
    output = workdir / "compiler-simp-proposals.json"
    arena.write_json_atomic(output, receipt)
    try:
        _, row = arena.load_task(Path(config["task"]))
        declaration, input_start, proof_start = native._current_source(row, source)
        sites = discover_sites(declaration, row["signature"])
        receipt["site_count"] = len(sites)
        candidates = []
        if max_candidates and sites:
            values = RuntimeContext.resolve(Path(config.get("root", workdir)), config).environment(workdir)
            values = {key: os.environ.get(key, value) for key, value in values.items()}
            values["LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE"] = "compile"
            values["LEAN_REFACTOR_LAUNCH_CACHE"] = str(Path(config.get("root", workdir)) / "deterministic/native-launch-cache")
            configured = configure_native_environment(elan_home=config.get("elan_home"))
            with scoped_environment({**values, **configured}):
                environment = lean_launch.workspace_guard(project, os.environ)
                prefix = lean_source.exact_source_prefix(row, project)
                # A compiled target in the discovery environment must never
                # make its own simplifier suggestion succeed by circular reuse.
                guard = ("\nrun_cmd do\n  if (← Lean.getEnv).contains "
                         + json.dumps(row["name"], ensure_ascii=False)
                         + ".toName then\n    throwError \"compiler simp target already present before command\"\n")
                before = prefix.text + guard + "\nset_option Elab.async false in\n"
                query = query_source(declaration, sites)
                harness = before + query + "\n"
                request = Path(tempfile.mkdtemp(prefix="query-" + edit_packs.digest(source)[:12] + "-", dir=workdir))
                receipt["request_directory"] = str(request)
                edits, run = _discover(harness, project, request, deadline)
                receipt.update(run, prefix_sha256=prefix.sha256, request_directory=str(request),
                               environment_sha256=edit_packs.digest(json.dumps(environment, sort_keys=True)))
                candidates, rejected = map_edits(source, declaration, input_start, proof_start, sites,
                                                query, harness, len(before), edits, max_candidates=max_candidates)
                receipt["mapping_rejections"] = rejected
            for candidate in candidates:
                native._current_source(row, candidate["source"])
        receipt.update(status="completed", candidate_count=len(candidates),
                       candidates=[{key: value for key, value in candidate.items() if key != "source"}
                                   for candidate in candidates])
        return candidates
    except Exception as error:
        receipt.update(status="failed", candidate_count=0, partial_candidates_discarded=True,
                       error_type=type(error).__name__, error=str(error))
        raise CompilerSimpError(f"Compiler simp discovery failed; see {output}: {error}") from error
    finally:
        receipt["wall_seconds"] = time.monotonic() - started
        arena.write_json_atomic(output, receipt)
