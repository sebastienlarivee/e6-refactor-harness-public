"""Bounded, context-derived specialization of interior Lean rewrite lemmas.

JSON in/out; independent of task registries and benchmark solution files.  This
is candidate generation, not proof validation or a promise of improved timing.
Only original-source identifier spans are edited in emitted declarations.
"""
from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import argparse
import hashlib
import json
import os
import signal
import subprocess
import sys
import tempfile
import time
import unicodedata
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from lean_tools import lean_launch

SCHEMA_VERSION = 1
MARKER = "__LRH_SPECIALIZATION_V1__"
DEFAULT_LIMITS = {
    "max_sites": 8,
    "max_entries": 24,
    "max_candidates": 16,
    "max_prefix_names": 2048,
    "max_type_constants": 96,
    "max_site_candidates": 12,
    "timeout_seconds": 90,
}
HARD_LIMITS = {
    "max_sites": 32,
    "max_entries": 64,
    "max_candidates": 64,
    "max_prefix_names": 8192,
    "max_type_constants": 256,
    "max_site_candidates": 32,
    "timeout_seconds": 180,
}


class SpecializationError(ValueError):
    pass


@dataclass(frozen=True)
class Token:
    kind: str
    text: str
    start: int
    end: int


@dataclass(frozen=True)
class Entry:
    name: str
    start: int
    end: int
    modifier: str = ""


@dataclass(frozen=True)
class Site:
    index: int
    tactic: str
    start: int
    end: int
    entries: tuple[Entry, ...]


def _id_start(char: str) -> bool:
    return char == "_" or char.isalpha() or unicodedata.category(char) == "Nl"


def _id_continue(char: str) -> bool:
    return _id_start(char) or char.isdigit() or char in "'!?" or unicodedata.category(char) in {"Mn", "Mc", "Pc", "No"}


def lex(source: str) -> list[Token]:
    """Small lossless-span lexer; comments and string payloads are opaque.

    It deliberately does not claim to parse arbitrary Lean syntax.  Escaped
    names, syntax quotations and complex simp terms are excluded downstream.
    """
    result: list[Token] = []
    index = 0
    while index < len(source):
        start = index
        char = source[index]
        if char.isspace():
            index += 1
            continue
        if source.startswith("--", index):
            end = source.find("\n", index)
            index = len(source) if end < 0 else end + 1
            continue
        if source.startswith("/-", index):
            depth = 1
            index += 2
            while index < len(source) and depth:
                if source.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise SpecializationError("unterminated block comment")
            continue
        if char == "r":
            hashes_end = index + 1
            while hashes_end < len(source) and source[hashes_end] == "#":
                hashes_end += 1
            if hashes_end < len(source) and source[hashes_end] == '"':
                delimiter = '"' + source[index + 1:hashes_end]
                end = source.find(delimiter, hashes_end + 1)
                if end < 0:
                    raise SpecializationError("unterminated raw string")
                index = end + len(delimiter)
                result.append(Token("opaque", source[start:index], start, index))
                continue
        if char == "'" and index + 2 < len(source):
            char_end = index + (3 if source[index + 1] == "\\" else 2)
            if char_end < len(source) and source[char_end] == "'":
                index = char_end + 1
                result.append(Token("opaque", source[start:index], start, index))
                continue
        if char == '"':
            index += 1
            while index < len(source):
                if source[index] == "\\":
                    index += 2
                elif source[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            else:
                raise SpecializationError("unterminated string")
            result.append(Token("opaque", source[start:index], start, index))
            continue
        if char == "«":
            end = source.find("»", index + 1)
            if end < 0:
                raise SpecializationError("unterminated escaped identifier")
            index = end + 1
            result.append(Token("escaped", source[start:index], start, index))
            continue
        if _id_start(char):
            index += 1
            while index < len(source):
                if _id_continue(source[index]):
                    index += 1
                elif source[index] == "." and index + 1 < len(source) and _id_start(source[index + 1]):
                    index += 2
                else:
                    break
            result.append(Token("id", source[start:index], start, index))
            continue
        punctuation = next((value for value in ("<;>", ":=", "=>", "->", "←", "||", "&&") if source.startswith(value, index)), None)
        if punctuation is not None:
            index += len(punctuation)
        else:
            index += 1
        result.append(Token("symbol", source[start:index], start, index))
    return result


def proof_start(source: str, tokens: list[Token]) -> int:
    stack: list[str] = []
    opening = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    for index, token in enumerate(tokens):
        if token.text in opening:
            stack.append(opening[token.text])
        elif stack and token.text == stack[-1]:
            stack.pop()
        elif not stack and token.text == ":=":
            if index + 1 >= len(tokens) or tokens[index + 1].text != "by":
                raise SpecializationError("only declarations with a top-level ':= by' proof are supported")
            return tokens[index + 1].end
    raise SpecializationError("no top-level ':= by' proof found")


def position(source: str, offset: int) -> dict[str, int]:
    line_start = source.rfind("\n", 0, offset) + 1
    return {
        "line": source.count("\n", 0, offset) + 1,
        "column": offset - line_start + 1,
        "lsp_line": source.count("\n", 0, offset),
        "lsp_character": len(source[line_start:offset].encode("utf-16-le")) // 2,
    }


def limits_from(value: Any) -> dict[str, int]:
    if value is None:
        return dict(DEFAULT_LIMITS)
    if not isinstance(value, dict) or set(value) - set(DEFAULT_LIMITS):
        raise SpecializationError("limits must contain only documented limit names")
    result = dict(DEFAULT_LIMITS)
    for key, limit in value.items():
        if type(limit) is not int or not 1 <= limit <= HARD_LIMITS[key]:
            raise SpecializationError(f"{key} must be an integer in 1..{HARD_LIMITS[key]}")
        result[key] = limit
    return result


def scan_sites(source: str, limits: dict[str, int]) -> tuple[int, list[Site], list[dict[str, Any]]]:
    tokens = lex(source)
    body_start = proof_start(source, tokens)
    diagnostics: list[dict[str, Any]] = []
    # Lean quotations can contain arbitrary tactic-shaped data.  A deliberately
    # conservative refusal prevents us editing syntax definitions as proof code.
    if any(token.text == "`" and token.start >= body_start for token in tokens):
        return body_start, [], [{"code": "syntax_quotation_unsupported", "message": "proof contains Lean quotation syntax; no edits proposed"}]
    sites: list[Site] = []
    entries_used = 0
    index = 0
    while index < len(tokens):
        token = tokens[index]
        if token.start < body_start or token.kind != "id" or token.text not in {"simp", "rw"}:
            index += 1
            continue
        cursor = index + 1
        tactic = token.text
        if tactic == "simp":
            if cursor >= len(tokens) or tokens[cursor].text != "only":
                diagnostics.append({"code": "simp_without_only_unsupported", "offset": token.start})
                index += 1
                continue
            tactic = "simp only"
            cursor += 1
        if cursor >= len(tokens) or tokens[cursor].text != "[":
            diagnostics.append({"code": "tactic_form_unsupported", "offset": token.start, "tactic": tactic})
            index += 1
            continue
        cursor += 1
        depth = 0
        segment: list[Token] = []
        segments: list[list[Token]] = []
        closed = False
        while cursor < len(tokens):
            current = tokens[cursor]
            if current.text == "]" and depth == 0:
                segments.append(segment)
                closed = True
                break
            if current.text == "," and depth == 0:
                segments.append(segment)
                segment = []
            else:
                if current.text in {"[", "(", "{", "⦃"}:
                    depth += 1
                elif current.text in {"]", ")", "}", "⦄"}:
                    depth -= 1
                    if depth < 0:
                        break
                segment.append(current)
            cursor += 1
        if not closed:
            diagnostics.append({"code": "malformed_lemma_list", "offset": token.start})
            index += 1
            continue
        entries: list[Entry] = []
        for segment in segments:
            modifier = ""
            if segment and segment[0].text in {"←", "-"}:
                modifier = segment[0].text
                segment = segment[1:]
            if len(segment) == 1 and segment[0].kind == "id" and segment[0].text not in {"_", "this"}:
                name_token = segment[0]
                if entries_used < limits["max_entries"]:
                    entries.append(Entry(name_token.text, name_token.start, name_token.end, modifier))
                    entries_used += 1
                else:
                    diagnostics.append({"code": "entry_limit", "offset": name_token.start})
            elif segment:
                diagnostics.append({"code": "complex_lemma_entry_unsupported", "offset": segment[0].start})
        end = tokens[cursor].end
        # Include a narrow optional location, so probe wrapping does not detach
        # `at h` from its tactic.  Other syntax remains for Lean to reject safely.
        tail = cursor + 1
        if tail < len(tokens) and tokens[tail].text == "at":
            tail += 1
            while tail < len(tokens):
                loc = tokens[tail]
                gap = source[end:loc.start]
                if "\n" in gap or not (loc.kind == "id" or loc.text in {"*", "⊢"}):
                    break
                end = loc.end
                tail += 1
            if end == tokens[cursor].end:
                diagnostics.append({"code": "multiline_location_unsupported", "offset": token.start})
                entries = []
        if entries:
            if len(sites) < limits["max_sites"]:
                sites.append(Site(len(sites), tactic, token.start, end, tuple(entries)))
            else:
                diagnostics.append({"code": "site_limit", "offset": token.start})
        index = cursor + 1
    return body_start, sites, diagnostics


def _lean_string(value: str) -> str:
    # JSON string escaping overlaps Lean for all emitted identifier strings.
    return json.dumps(value, ensure_ascii=False)


def _emit(expression: str) -> str:
    return f"Lean.logInfo (Lean.toMessageData ({_lean_string(MARKER)} ++ ({expression}).compress))"


def prefix_probe(sites: list[Site], limits: dict[str, int]) -> str:
    suffixes = sorted({entry.name.split(".")[-1] for site in sites for entry in site.entries})
    names = "#[" + ", ".join(_lean_string(name) for name in suffixes) + "]"
    payload = 'Lean.Json.mkObj [("kind", Lean.toJson "prefix"), ("names", Lean.toJson found), ("truncated", Lean.toJson truncated)]'
    return (
        "\nrun_cmd do\n"
        f"  let suffixes : Array String := {names}\n"
        "  let mut found : Array String := #[]\n"
        "  let mut truncated := false\n"
        "  let env ← Lean.getEnv\n"
        "  for (name, _) in env.constants.toList do\n"
        "    if Lean.wasOriginallyTheorem env name && !name.isInternal && !Lean.isPrivateName name && suffixes.contains name.getString! then\n"
        f"      if found.size < {limits['max_prefix_names']} then\n"
        "        found := found.push name.toString\n"
        "      else\n"
        "        truncated := true\n"
        f"  {_emit(payload)}\n\n"
    )


def site_probe(site: Site, limits: dict[str, int]) -> str:
    entries = "#[" + ", ".join("(" + str(entry.start) + ", " + _lean_string(entry.name) + ")" for entry in site.entries) + "]"
    # Braced do notation makes the wrapper independent of caller indentation.
    # Queries do not assign metavariables or synthesize tactic goals.
    statements = [
        f"let entries : Array (Nat × String) := {entries}",
        "let mut types : Array Lean.Expr := #[(← (← Lean.Elab.Tactic.getMainGoal).getType)]",
        "for localDecl in (← Lean.getLCtx) do { if !localDecl.isImplementationDetail then types := types.push localDecl.type }",
        "let mut constants : Array Lean.Name := #[]",
        "let mut constantsTruncated := false",
        "for type in types do { for name in (← Lean.instantiateMVars type).getUsedConstants do { if !constants.contains name then { "
        f"if constants.size < {limits['max_type_constants']} then constants := constants.push name else constantsTruncated := true"
        " } } }",
        "let mut namespaces : Array Lean.Name := #[]",
        "for constant in constants do { let mut name := constant; while !name.isAnonymous do { if !namespaces.contains name then { namespaces := namespaces.push name }; name := name.getPrefix } }",
        "let mut results : Array Lean.Json := #[]",
        "for (offset, spelling) in entries do { "
        "let original : Option Lean.Expr ← (do try { Lean.Elab.Term.resolveId? (Lean.mkIdent spelling.toName) } catch _ => { pure none }); "
        "let resolved := match original with | some (.const name _) => name.toString | _ => \"\"; "
        "let mut candidates : Array Lean.Json := #[]; "
        "if !resolved.isEmpty then { "
        "for ns in namespaces do { "
        "let candidate := Lean.Name.str ns spelling.toName.getString!; "
        "if candidate.toString != resolved then { "
        "match (← Lean.getEnv).find? candidate with "
        "| some _ => if Lean.wasOriginallyTheorem (← Lean.getEnv) candidate && !candidate.isInternal && !Lean.isPrivateName candidate then { "
        f"if candidates.size < {limits['max_site_candidates']} then {{ "
        "let short : Option Lean.Expr ← (do try { Lean.Elab.Term.resolveId? (Lean.mkIdent candidate) } catch _ => { pure none }); "
        "let shortOK := match short with | some (.const name _) => name == candidate | _ => false; "
        "let replacement := if shortOK then candidate.toString else \"_root_.\" ++ candidate.toString; "
        "candidates := candidates.push (Lean.Json.mkObj [(\"name\", Lean.toJson candidate.toString), (\"spelling\", Lean.toJson replacement), (\"namespace\", Lean.toJson ns.toString), (\"short_resolution_verified\", Lean.toJson shortOK)]) "
        "} } | none => pure () } } }; "
        "results := results.push (Lean.Json.mkObj [(\"offset\", Lean.toJson offset), (\"original\", Lean.toJson spelling), (\"resolved_original\", Lean.toJson resolved), (\"candidates\", Lean.toJson candidates)]) }",
        _emit(f'Lean.Json.mkObj [("kind", Lean.toJson "site"), ("site", Lean.toJson ({site.index} : Nat)), ("constants", Lean.toJson (constants.map Lean.Name.toString)), ("constants_truncated", Lean.toJson constantsTruncated), ("entries", Lean.toJson results)]'),
    ]
    return "run_tac (Lean.Elab.Tactic.withMainContext do { " + "; ".join(statements) + " })"


def probe_source(prefix: str, declaration: str, sites: list[Site], limits: dict[str, int]) -> str:
    instrumented = declaration
    for site in reversed(sites):
        original = declaration[site.start:site.end]
        replacement = f"(({site_probe(site, limits)}); {original})"
        instrumented = instrumented[:site.start] + replacement + instrumented[site.end:]
    return prefix + prefix_probe(sites, limits) + instrumented + "\n"


def parse_probe_output(stdout: str) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    records: list[dict[str, Any]] = []
    diagnostics: list[dict[str, Any]] = []
    for line in stdout.splitlines():
        try:
            diagnostic = json.loads(line)
        except json.JSONDecodeError:
            if line.strip():
                diagnostics.append({"code": "lean_output", "message": line[:2000]})
            continue
        if not isinstance(diagnostic, dict):
            continue
        message = diagnostic.get("data", diagnostic.get("message", ""))
        if isinstance(message, str) and message.startswith(MARKER):
            try:
                record = json.loads(message[len(MARKER):])
            except json.JSONDecodeError:
                diagnostics.append({"code": "invalid_probe_payload", "message": message[:2000]})
            else:
                if isinstance(record, dict):
                    records.append(record)
        elif diagnostic.get("severity") in {"error", "warning"}:
            diagnostics.append({"code": "lean_diagnostic", **diagnostic})
    return records, diagnostics


def run_probe(source: str, project_root: Path, timeout: int) -> dict[str, Any]:
    project_root = project_root.resolve()
    if not (project_root / "lean-toolchain").is_file():
        raise SpecializationError("project_root must contain a cached Lean project's lean-toolchain")
    started = time.perf_counter()
    artifact = {"source": source, "source_utf8_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest()}
    with tempfile.TemporaryDirectory(prefix="lrh-specialization-") as temporary:
        path = Path(temporary) / "Probe.lean"
        path.write_bytes(source.encode("utf-8"))
        try:
            process = subprocess.Popen(
                lean_launch.native_command(["lake", "env", "lean", "--json", str(path)]),
                env=lean_launch.native_environment(),
                cwd=project_root,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                encoding="utf-8",
                errors="replace",
                creationflags=subprocess.CREATE_NEW_PROCESS_GROUP if os.name == "nt" else 0,
                start_new_session=os.name != "nt",
            )
            lean_launch.process_memory.capture_process_identity(process)
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            lean_launch._terminate(process)
            stdout, stderr = process.communicate()
            records, diagnostics = parse_probe_output(stdout)
            return {**artifact, "ok": False, "seconds": round(time.perf_counter() - started, 6), "stdout": stdout, "stderr": stderr, "records": records, "diagnostics": diagnostics + [{"code": "probe_timeout", "seconds": timeout}]}
        except OSError as error:
            return {**artifact, "ok": False, "seconds": round(time.perf_counter() - started, 6), "stdout": "", "stderr": "", "records": [], "diagnostics": [{"code": "probe_launch_failed", "message": str(error)}]}
        records, diagnostics = parse_probe_output(stdout)
        if stderr.strip():
            diagnostics.append({"code": "lean_stderr", "message": stderr[-4000:]})
        return {**artifact, "ok": process.returncode == 0, "returncode": process.returncode, "seconds": round(time.perf_counter() - started, 6), "stdout": stdout, "stderr": stderr, "records": records, "diagnostics": diagnostics}


def make_candidates(declaration: str, sites: list[Site], records: list[dict[str, Any]], limits: dict[str, int]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    prefixes = [record for record in records if record.get("kind") == "prefix"]
    if len(prefixes) != 1:
        return [], [{"code": "prefix_visibility_unavailable", "message": "exactly one pre-target environment record is required"}]
    visible = set(prefixes[0].get("names", []))
    diagnostics: list[dict[str, Any]] = []
    if prefixes[0].get("truncated"):
        diagnostics.append({"code": "prefix_name_limit"})
    by_site = {record.get("site"): record for record in records if record.get("kind") == "site"}
    for site in sites:
        context_count = sum(record.get("kind") == "site" and record.get("site") == site.index for record in records)
        if context_count > 1:
            diagnostics.append({"code": "repeated_site_context", "site": site.index, "observations": context_count, "used": "last", "message": "a repeated tactic site may admit different contexts; all candidates still require complete proof validation"})
    candidates: list[dict[str, Any]] = []
    seen: set[tuple[int, str]] = set()
    for site in sites:
        record = by_site.get(site.index)
        if record is None:
            diagnostics.append({"code": "site_context_unavailable", "site": site.index})
            continue
        if record.get("constants_truncated"):
            diagnostics.append({"code": "type_constant_limit", "site": site.index})
        by_offset = {entry.get("offset"): entry for entry in record.get("entries", [])}
        for entry in site.entries:
            observed = by_offset.get(entry.start)
            if not observed or not observed.get("resolved_original"):
                diagnostics.append({"code": "original_not_resolved_constant", "site": site.index, "offset": entry.start})
                continue
            resolved = observed["resolved_original"]
            if len(observed.get("candidates", [])) >= limits["max_site_candidates"]:
                diagnostics.append({"code": "site_candidate_limit_reached", "site": site.index, "offset": entry.start})
            # Both sides must be pre-target theorems, excluding local hypotheses
            # and provisional/self constants introduced during elaboration.
            if resolved not in visible:
                diagnostics.append({"code": "original_not_prefix_theorem", "offset": entry.start, "resolved": resolved})
                continue
            for proposal in observed.get("candidates", []):
                name, replacement = proposal.get("name"), proposal.get("spelling")
                if not isinstance(name, str) or not isinstance(replacement, str) or name not in visible:
                    continue
                if name == resolved or (entry.start, replacement) in seen:
                    continue
                if len(candidates) >= limits["max_candidates"]:
                    diagnostics.append({"code": "candidate_limit"})
                    return candidates, diagnostics
                seen.add((entry.start, replacement))
                edited = declaration[:entry.start] + replacement + declaration[entry.end:]
                candidates.append({
                    "id": f"specialization-{len(candidates) + 1:03d}",
                    "edit": {"start": entry.start, "end": entry.end, "old": entry.name, "new": replacement, "start_position": position(declaration, entry.start), "end_position": position(declaration, entry.end)},
                    "declaration": edited,
                    "provenance": {"site": site.index, "tactic": site.tactic, "modifier": entry.modifier, "resolved_original": resolved, "resolved_replacement": name, "namespace": proposal.get("namespace"), "type_constants": record.get("constants", []), "visibility": "exact_source_prefix", "short_resolution_verified": bool(proposal.get("short_resolution_verified")), "validation": "candidate_only_requires_uninstrumented_lean_check"},
                })
    return candidates, diagnostics


def specialize(request: dict[str, Any]) -> dict[str, Any]:
    started = time.perf_counter()
    prefix, declaration = request.get("source_prefix"), request.get("declaration")
    if not isinstance(prefix, str) or not isinstance(declaration, str):
        raise SpecializationError("source_prefix and declaration must be strings")
    limits = limits_from(request.get("limits"))
    body_start, sites, diagnostics = scan_sites(declaration, limits)
    result: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "ok": True,
        "original": declaration,
        "original_sha256": hashlib.sha256(declaration.encode("utf-8")).hexdigest(),
        "source_prefix_sha256": hashlib.sha256(prefix.encode("utf-8")).hexdigest(),
        "proof_start": body_start,
        "offset_units": "unicode_codepoints_zero_based_end_exclusive",
        "limits": limits,
        "sites": [asdict(site) for site in sites],
        "candidates": [],
        "diagnostics": diagnostics,
        "baseline_retained": True,
    }
    if sites:
        source = probe_source(prefix, declaration, sites, limits)
        if request.get("scan_only", False):
            result["probe_source"] = source
            result["diagnostics"].append({"code": "scan_only", "message": "no names or contexts verified; no candidates emitted"})
        else:
            project = request.get("project_root")
            if not isinstance(project, str):
                raise SpecializationError("project_root is required unless scan_only is true")
            probe = run_probe(source, Path(project), limits["timeout_seconds"])
            result["probe"] = probe
            result["diagnostics"].extend(probe["diagnostics"])
            if probe["ok"]:
                candidates, candidate_diagnostics = make_candidates(declaration, sites, probe["records"], limits)
                result["candidates"] = candidates
                result["diagnostics"].extend(candidate_diagnostics)
            else:
                result["ok"] = False
                result["diagnostics"].append({"code": "instrumented_probe_failed", "message": "original declaration retained; no candidate emitted"})
    else:
        result["diagnostics"].append({"code": "no_supported_sites"})
    result["total_seconds"] = round(time.perf_counter() - started, 6)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, help="JSON input path; omitted reads stdin")
    parser.add_argument("--output", type=Path, help="JSON output path; omitted writes stdout")
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    try:
        request = json.loads(args.input.read_text(encoding="utf-8-sig") if args.input else sys.stdin.read())
        if not isinstance(request, dict):
            raise SpecializationError("input must be a JSON object")
        result = specialize(request)
    except (OSError, json.JSONDecodeError, SpecializationError) as error:
        result = {"schema_version": SCHEMA_VERSION, "ok": False, "candidates": [], "diagnostics": [{"code": "request_error", "message": str(error)}]}
    rendered = json.dumps(result, ensure_ascii=False, indent=2 if args.pretty else None) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
