"""Read-only Lean source examples from an explicit, masked import closure.

This is a lexical source index, not a Lean parser or semantic dependency index.
Only the exact source prefix and recursively imported cached source are admitted.
The target file is always replaced by its prefix, including through an import.
No directory-wide source scan, original-proof body, or run history is indexed.
"""
from __future__ import annotations

import hashlib
import json
import math
import os
import re
import sqlite3
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

from lean_tools import lean_source

FORMAT_VERSION = 1
POLICY = "exact-prefix-import-closure-v1"
IDENTIFIER = re.compile(r"(?:[^\W\d]|_)[\w']*(?:\.(?:[^\W\d]|_)[\w']*)*")
IMPORT = re.compile(r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)")
DECL_KINDS = "theorem|lemma|def|abbrev|opaque|instance|example|inductive|structure|class|axiom"
# Column-zero commands are deliberately conservative: nested `where` definitions
# and local terms are retained inside their enclosing example.
COMMAND = re.compile(
    r"(?m)^(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|public|noncomputable|partial|"
    r"nonrec|unsafe|meta)\s+)*(?P<kind>" + DECL_KINDS +
    r"|namespace|section|end|universe|universes|variable|variables|include|omit|open|export|attribute|"
    r"set_option|notation|infixr?|prefix|postfix|syntax|macro_rules|macro|elab_rules|"
    r"elab|initialize|builtin_initialize|mutual|local|scoped|prelude|module|import)\b"
)
TACTICS = frozenset("intro intros rintro induction cases rcases obtain constructor refine exact apply rw rfl simp simpa simp_all aesop grind omega ring linarith nlinarith norm_num decide funext ext congr congrArg have let suffices choose classical by_cases by_contra contradiction subst revert generalize specialize calc use assumption trivial repeat first all_goals next case rename_i generalizing".split())
STOPWORDS = frozenset("a an and are as at be by can do for from has have how if in into is it let of on or proof show that the then theorem this to using with example find goal use uses".split())


class ExampleSearchError(RuntimeError):
    pass


def digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, ensure_ascii=False, sort_keys=True,
                                    separators=(",", ":")).encode()).hexdigest()


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def terms(text: str) -> set[str]:
    text = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", text)
    return {part.casefold() for token in IDENTIFIER.findall(text)
            for part in re.split(r"[._']+", token)
            if len(part) > 1 and part.casefold() not in STOPWORDS}


def imported_modules(text: str) -> list[str]:
    mask = lean_source.lean_code_mask(text)
    modules = []
    for match in IMPORT.finditer(mask):
        modules.extend(word for word in match.group(1).split()
                       if word != "all" and re.fullmatch(r"[A-Za-z_][\w.']*", word))
    # Ordinary Lean modules implicitly import Init. `prelude` opts out.
    if not re.search(r"(?m)^\s*prelude\b", mask):
        modules.append("Init")
    return list(dict.fromkeys(modules))


@dataclass(frozen=True)
class SourceUnit:
    module: str
    path: str
    text: str
    origin: str


@dataclass(frozen=True)
class Corpus:
    identity: dict[str, Any]
    sources: tuple[SourceUnit, ...]
    unresolved_imports: tuple[str, ...] = ()


def default_source_roots(project: Path, *, elan_home: Path | None = None) -> list[Path]:
    """Known Lake package roots only; never recurse over arbitrary host trees."""
    project = project.resolve()
    roots = [project]
    packages = project / ".lake/packages"
    if packages.is_dir():
        roots.extend(path.resolve() for path in sorted(packages.iterdir()) if path.is_dir())
    toolchain = project / "lean-toolchain"
    if toolchain.is_file():
        toolchain_name = toolchain.read_text().strip().replace("/", "--").replace(":", "---")
        home = elan_home or Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan")))
        core = home / "toolchains" / toolchain_name / "src/lean"
        if core.is_dir():
            roots.append(core.resolve())
            if (core / "lake").is_dir():
                roots.append((core / "lake").resolve())
    return list(dict.fromkeys(roots))


def prepare_corpus(row: dict[str, Any], project: Path, environment_fingerprint: str,
                   *, source_roots: Iterable[Path] | None = None,
                   excluded_paths: Iterable[Path] = (),
                   inspiration_modules: Iterable[str] = ()) -> Corpus:
    """Read only reachable files and bind all admitted bytes to this task/view.

    Callers must supply roots from the frozen environment, never experiment/run
    folders. Extra exclusions are an explicit mask, applied before reading bytes.
    Missing cached source is reported; compiled-only imports are not fabricated.
    """
    project = project.resolve()
    prefix = lean_source.exact_source_prefix(row, project)
    roots = tuple(Path(path).resolve() for path in
                  (source_roots if source_roots is not None else default_source_roots(project)))
    if not roots or any(not path.is_dir() for path in roots):
        raise ExampleSearchError("all source roots must be existing frozen source directories")
    forbidden_components = {"research", "archive", "archives", "history", "runs", ".git"}
    if any(forbidden_components.intersection(part.casefold() for part in root.parts) for root in roots):
        raise ExampleSearchError("experiment/archive/history roots are not permitted library source roots")
    inspiration = sorted(set(inspiration_modules))
    if any(not re.fullmatch(r"[A-Za-z_][\w.']*", module)
           or forbidden_components.intersection(part.casefold() for part in module.split("."))
           for module in inspiration):
        raise ExampleSearchError("inspiration modules must name permitted original library modules")
    excluded = frozenset(Path(path).resolve() for path in excluded_paths)
    target_path = prefix.source_path.resolve() if prefix.source_path else None
    if target_path in excluded:
        raise ExampleSearchError("exclude the target via its mandatory prefix mask, not whole-file exclusion")
    prefix_module = (str(row.get("file_path", "")).removesuffix(".lean").replace("/", ".")
                     if target_path else "<supplied-prefix>")
    prefix_unit = SourceUnit(prefix_module, str(target_path) if target_path else "<supplied-prefix>",
                             prefix.text, "exact-prefix")
    sources = {prefix_module: prefix_unit}
    visited: set[str] = set()
    unresolved: set[str] = set()
    for seeds, origin in ((imported_modules(prefix.text), "imported-source"),
                          (inspiration, "inspiration-source")):
        pending = list(seeds)
        while pending:
            module = pending.pop()
            if module in visited or module == prefix_module:
                continue
            visited.add(module)
            if forbidden_components.intersection(part.casefold() for part in module.split(".")):
                raise ExampleSearchError("import closure reached a forbidden history module")
            relative = Path(*module.split(".")).with_suffix(".lean")
            found = None
            for root in roots:
                candidate = (root / relative).resolve()
                if not candidate.is_relative_to(root):
                    raise ExampleSearchError("source module escaped its declared root")
                if candidate == target_path:
                    found = prefix_unit
                    break
                if candidate in excluded:
                    break  # Never fall through to a shadowing source version.
                if candidate.is_file():
                    found = SourceUnit(module, str(candidate), candidate.read_text(encoding="utf-8"), origin)
                    break
            if found is None:
                unresolved.add(module)
                continue
            sources[module] = found
            pending.extend(imported_modules(found.text))
    units = tuple(sorted(sources.values(), key=lambda unit: unit.module))
    masks = {"target_path": str(target_path) if target_path else None,
             "target_and_suffix": "excluded-before-indexing",
             "excluded_paths": sorted(map(str, excluded)),
             "history": "not reachable: no host glob or history directories admitted"}
    material = {"format_version": FORMAT_VERSION,
                "policy": POLICY if not inspiration else "exact-prefix-plus-explicit-inspiration-modules-v1",
                "target": row["name"], "task_signature_sha256": sha256(row["signature"]),
                "prefix_sha256": prefix.sha256, "environment_fingerprint": environment_fingerprint,
                "inspiration_modules": inspiration,
                "source_roots": list(map(str, roots)), "masks": masks,
                "sources": [{"module": unit.module, "path": unit.path,
                             "sha256": sha256(unit.text), "origin": unit.origin} for unit in units],
                "unresolved_imports": sorted(unresolved),
                "implementation_sha256": sha256(Path(__file__).read_text())}
    material["corpus_sha256"] = digest(material)
    return Corpus(material, units, tuple(sorted(unresolved)))


def _assignment_offset(mask: str) -> int:
    depth = 0
    for index, char in enumerate(mask):
        if char in "([{⦃":
            depth += 1
        elif char in ")] }⦄".replace(" ", ""):
            depth = max(0, depth - 1)
        elif depth == 0 and mask.startswith(":=", index):
            return index
        elif depth == 0 and mask.startswith("where", index) and (index == 0 or not mask[index - 1].isalnum()) \
                and (index + 5 == len(mask) or not mask[index + 5].isalnum()):
            return index
        elif depth == 0 and char == "|" and not mask[mask.rfind("\n", 0, index) + 1:index].strip() \
                and re.match(r"\|[^\n]*=>", mask[index:]):
            return index
    where = re.search(r"(?m)^where\b", mask)
    return where.start() if where else len(mask)


def _comment_spans(text: str) -> list[tuple[int, int]]:
    """Outer comment spans, ignoring comment-looking text inside strings."""
    spans: list[tuple[int, int]] = []
    index = 0
    while index < len(text):
        if text[index] == '"':
            index += 1
            while index < len(text):
                if text[index] == "\\":
                    index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index)
            end = len(text) if end < 0 else end
            spans.append((index, end))
            index = end
        elif text.startswith("/-", index):
            start, depth = index, 1
            index += 2
            while index < len(text) and depth:
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            spans.append((start, index))
        else:
            index += 1
    return spans


def _trim_trailing_comments(text: str, end: int, comments_by_end: dict[int, int]) -> int:
    while True:
        while end and text[end - 1].isspace():
            end -= 1
        start = comments_by_end.get(end)
        if start is None:
            return end
        end = start


def declaration_chunks(unit: SourceUnit) -> Iterable[dict[str, Any]]:
    """Conservative column-zero source chunks, preserving statement and scope.

    Scope commands are returned as context, not silently prepended executable
    code. Names/references are lexical estimates requiring Lean validation.
    """
    mask = lean_source.lean_code_mask(unit.text)
    commands = list(COMMAND.finditer(mask))
    comments_by_end = {end: start for start, end in _comment_spans(unit.text)}
    scopes: list[tuple[str, str]] = []
    context: list[tuple[int, str, int]] = []
    scoped_context: list[tuple[int, str, int]] = []
    prior_code_end = 0
    for index, command in enumerate(commands):
        start = command.start()
        end = commands[index + 1].start() if index + 1 < len(commands) else len(mask)
        # Remove trailing blank/comment blocks so neighboring docstrings do not
        # become part of the previous proof. Keep inline comments in the source.
        code_end = _trim_trailing_comments(unit.text, end, comments_by_end)
        leading_comments = unit.text[prior_code_end:start].strip()
        comment_start = prior_code_end
        while comment_start < start and unit.text[comment_start].isspace():
            comment_start += 1
        comment_end = start
        while comment_end > comment_start and unit.text[comment_end - 1].isspace():
            comment_end -= 1
        prior_code_end = code_end
        text = unit.text[start:code_end]
        command_mask = mask[start:code_end]
        kind = command.group("kind")
        head = command_mask[command.end() - start:].strip()
        if kind in {"namespace", "section", "mutual"}:
            scope_name = head.split()[0] if head else ""
            scopes.append((kind, scope_name))
            context.append((len(scopes), text, start))
            continue
        if kind == "end":
            if scopes:
                depth = len(scopes)
                scopes.pop()
                context = [item for item in context if item[0] < depth]
            continue
        if kind not in DECL_KINDS.split("|"):
            if kind in {"universe", "universes", "variable", "variables", "include", "omit", "open",
                        "local", "scoped", "set_option", "attribute"}:
                if re.search(r"\bin\s*$", command_mask):
                    scoped_context.append((len(scopes), text, start))
                else:
                    context.append((len(scopes), text, start))
            continue
        name_match = re.match(r"([^\s({\[:]+)", head)
        local_name = name_match.group(1) if name_match and kind != "example" else "<anonymous>"
        namespace_parts: list[str] = []
        for tag, scope_name in scopes:
            if tag == "namespace" and scope_name:
                if scope_name.startswith("_root_."):
                    namespace_parts = [scope_name[7:]]
                else:
                    namespace_parts.append(scope_name)
        namespace = ".".join(namespace_parts)
        if local_name.startswith("_root_."):
            name = local_name[7:]
        else:
            name = ".".join(filter(None, (namespace, local_name)))
        assignment = _assignment_offset(command_mask)
        statement = text[:assignment].rstrip()
        body = text[assignment + 2:].lstrip() if command_mask[assignment:assignment + 2] == ":=" \
            else text[assignment:] if command_mask[assignment:].startswith(("where", "|")) else ""
        body_mask = lean_source.lean_code_mask(body)
        references = set(IDENTIFIER.findall(body_mask))
        tactics = sorted(references & TACTICS)
        private = bool(re.search(r"\bprivate\b", command_mask[:command.end() - start]))
        anonymous = local_name == "<anonymous>"
        visible_context = [*context, *scoped_context]
        scoped_context.clear()
        yield {"name": name, "local_name": local_name, "kind": kind,
               "module": unit.module, "path": unit.path, "origin": unit.origin,
               "line_start": unit.text.count("\n", 0, start) + 1,
               "line_end": unit.text.count("\n", 0, code_end) + 1,
               "offset_start": start, "offset_end": code_end,
               "statement": statement, "body": body, "source": text,
               "leading_comments": leading_comments,
               "comment_line_start": unit.text.count("\n", 0, comment_start) + 1 if leading_comments else None,
               "comment_line_end": unit.text.count("\n", 0, comment_end) + 1 if leading_comments else None,
               "comment_offset_start": comment_start if leading_comments else None,
               "comment_offset_end": comment_end if leading_comments else None,
               "context": [{"source": value, "line": unit.text.count("\n", 0, offset) + 1}
                           for _, value, offset in visible_context],
               "lexical_references": sorted(references), "tactic_shapes": tactics,
               "usage": "inspiration_only" if private or anonymous or unit.origin == "inspiration-source"
                        else "callable_candidate",
               "callable_verified": False,
               "availability": "outside_exact_import_closure" if unit.origin == "inspiration-source"
                               else "private_or_anonymous" if private or anonymous
                               else "source_in_exact_prefix_or_import_closure",
               "parse_quality": "lexical_column_zero_commands"}


def build_index(corpus: Corpus, cache_root: Path) -> tuple[Path, dict[str, Any]]:
    """Create one immutable database; no Lean or external provider is launched."""
    cache_root.mkdir(parents=True, exist_ok=True)
    key = corpus.identity["corpus_sha256"]
    output = cache_root / (key + ".sqlite3")
    started = time.perf_counter()
    if output.exists():
        with sqlite3.connect(output.resolve().as_uri() + "?mode=ro", uri=True) as db:
            identity = json.loads(db.execute("SELECT value FROM metadata WHERE key='identity'").fetchone()[0])
            summary = json.loads(db.execute("SELECT value FROM metadata WHERE key='summary'").fetchone()[0])
        if identity != corpus.identity:
            raise ExampleSearchError("cached example index identity mismatch")
        return output, {**summary, "cache_hit": True, "seconds": round(time.perf_counter() - started, 6)}
    temporary = output.with_name(output.name + f".{os.getpid()}.tmp")
    count = 0
    try:
        with sqlite3.connect(temporary) as db:
            db.executescript("PRAGMA journal_mode=OFF; PRAGMA synchronous=OFF;"
                             "CREATE TABLE metadata(key TEXT PRIMARY KEY,value TEXT NOT NULL);"
                             "CREATE TABLE examples(id INTEGER PRIMARY KEY,record TEXT NOT NULL);"
                             "CREATE TABLE terms(term TEXT NOT NULL,example_id INTEGER NOT NULL,field TEXT NOT NULL,"
                             "PRIMARY KEY(term,example_id,field)) WITHOUT ROWID;")
            for unit in corpus.sources:
                for record in declaration_chunks(unit):
                    # A target-name defense in depth; same-file target/suffix
                    # have already been removed before parsing/tokenization.
                    if record["name"] == corpus.identity["target"]:
                        continue
                    count += 1
                    db.execute("INSERT INTO examples VALUES (?,?)", (count, json.dumps(record, ensure_ascii=False)))
                    fields = {"name": terms(record["name"]), "statement": terms(record["statement"]),
                              "body": terms(lean_source.lean_code_mask(record["body"])),
                              "comment": terms(record["leading_comments"]),
                              "tactic": set(record["tactic_shapes"]),
                              "symbol": set(record["lexical_references"])}
                    db.executemany("INSERT INTO terms VALUES (?,?,?)",
                                   ((term, count, field) for field, values in fields.items() for term in values))
            summary = {"source_files": len(corpus.sources), "examples": count,
                       "unresolved_imports": list(corpus.unresolved_imports),
                       "source_bytes": sum(len(unit.text.encode()) for unit in corpus.sources)}
            db.execute("INSERT INTO metadata VALUES ('identity',?)", (json.dumps(corpus.identity, ensure_ascii=False),))
            db.execute("INSERT INTO metadata VALUES ('summary',?)", (json.dumps(summary),))
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)
    return output, {**summary, "cache_hit": False, "seconds": round(time.perf_counter() - started, 6),
                    "bytes": output.stat().st_size}


def inspect_index(path: Path) -> dict[str, Any]:
    with sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True) as db:
        return {key: json.loads(value) for key, value in db.execute("SELECT key,value FROM metadata")}


def binding(identity: dict[str, Any]) -> dict[str, Any]:
    """Small exported identity; full source inventory remains in the host index."""
    result = {key: identity[key] for key in ("format_version", "policy", "target",
            "task_signature_sha256", "prefix_sha256", "environment_fingerprint",
            "corpus_sha256", "implementation_sha256", "masks")}
    result["inspiration_modules"] = identity.get("inspiration_modules", [])
    return result


def prepare_index(row: dict[str, Any], project: Path, cache_root: Path, *,
                  environment_fingerprint: str | None = None,
                  fingerprint_registry: Path | None = None,
                  source_roots: Iterable[Path] | None = None,
                  excluded_paths: Iterable[Path] = (),
                  inspiration_modules: Iterable[str] = ()) -> dict[str, Any]:
    """Host preparation artifact, suitable for one read-only capsule mount."""
    if environment_fingerprint is None:
        from lean_tools import arena_workflow as arena
        environment_fingerprint = arena.measurement_environment_fingerprint(
            row, project, registry_path=fingerprint_registry)
    corpus = prepare_corpus(row, project, environment_fingerprint, source_roots=source_roots,
                            excluded_paths=excluded_paths, inspiration_modules=inspiration_modules)
    path, telemetry = build_index(corpus, cache_root)
    return {"schema_version": 1, "path": str(path), "identity": binding(corpus.identity),
            "key": corpus.identity["corpus_sha256"],
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "build": telemetry}


def validate_prepared_index(artifact: dict[str, Any], row: dict[str, Any], project: Path, *,
                            environment_fingerprint: str,
                            source_roots: Iterable[Path] | None = None,
                            excluded_paths: Iterable[Path] = (),
                            inspiration_modules: Iterable[str] = ()) -> Path:
    """Read-only host revalidation against current source bytes and masks."""
    corpus = prepare_corpus(row, project, environment_fingerprint, source_roots=source_roots,
                            excluded_paths=excluded_paths, inspiration_modules=inspiration_modules)
    path = Path(artifact["path"])
    if (artifact.get("schema_version") != 1 or artifact.get("identity") != binding(corpus.identity)
            or artifact.get("key") != corpus.identity["corpus_sha256"]
            or hashlib.sha256(path.read_bytes()).hexdigest() != artifact.get("sha256")
            or inspect_index(path).get("identity") != corpus.identity):
        raise ExampleSearchError("prepared example index does not match task/environment/source mask/hash")
    return path


def search(path: Path, query: str = "", *, used_names: Iterable[str] = (),
           tactic_shapes: Iterable[str] = (), limit: int = 5, max_source_chars: int = 8000,
           expected_identity: dict[str, Any] | None = None) -> dict[str, Any]:
    """IDF-weighted lexical/body-symbol/tactic search with explicit match reasons.

    used_names matches literal identifiers, not resolved Lean constants. Qualified
    names and local short names differ. All requested body symbols/tactics are
    mandatory; free-text terms are OR ranked and length-normalized per field.
    Oversized examples retain their complete statement and scope but expose an
    explicitly partial body window. Source ranges remain those of the full chunk.
    """
    if not 1 <= limit <= 12 or not 256 <= max_source_chars <= 32000:
        raise ExampleSearchError("limit must be 1..12 and max_source_chars 256..32000")
    query_terms = sorted(terms(query))[:64]
    symbols, tactics = sorted(set(used_names)), sorted(set(tactic_shapes))
    if not query_terms and not symbols and not tactics:
        raise ExampleSearchError("supply query text, a used name, or a tactic shape")
    started = time.perf_counter()
    with sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True) as db:
        material = json.loads(db.execute("SELECT value FROM metadata WHERE key='identity'").fetchone()[0])
        summary = json.loads(db.execute("SELECT value FROM metadata WHERE key='summary'").fetchone()[0])
        if expected_identity is not None and material != expected_identity and binding(material) != expected_identity:
            raise ExampleSearchError("example index does not match this task/environment/source mask")
        wanted = [(term, field, weight) for term in query_terms
                  for field, weight in (("name", 3.0), ("statement", 1.5), ("body", 1.0), ("comment", 1.25))]
        wanted += [(name, "symbol", 4.0) for name in symbols]
        wanted += [(name, "tactic", 2.0) for name in tactics]
        scores: dict[int, float] = {}
        evidence: dict[int, list[dict[str, str]]] = {}
        mandatory: dict[int, set[tuple[str, str]]] = {}
        for term, field, weight in wanted:
            matches = [row[0] for row in db.execute("SELECT example_id FROM terms WHERE term=? AND field=?", (term, field))]
            idf = math.log(1 + summary["examples"] / (1 + len(matches)))
            for example_id in matches:
                scores[example_id] = scores.get(example_id, 0.0) + weight * idf
                evidence.setdefault(example_id, []).append({"term": term, "field": field})
                if field in {"symbol", "tactic"}:
                    mandatory.setdefault(example_id, set()).add((term, field))
        required = {(name, "symbol") for name in symbols} | {(name, "tactic") for name in tactics}
        candidates = []
        for example_id, score in scores.items():
            if not required.issubset(mandatory.get(example_id, set())):
                continue
            record = json.loads(db.execute("SELECT record FROM examples WHERE id=?", (example_id,)).fetchone()[0])
            # Very long source examples and meta-tool implementation details
            # otherwise dominate short strategy queries with incidental tokens.
            score /= 1 + 0.12 * math.log1p(len(record["body"]) / 400)
            if record["module"].split(".")[0] in {"Lean", "Lake", "Qq", "Aesop"}:
                score *= 0.65
            if len(record["statement"]) + 4 > max_source_chars:
                continue  # Never sever a declaration's binders to fit a window.
            candidates.append((score, record["name"], example_id, record))
        candidates.sort(key=lambda item: (-item[0], item[1], item[2]))
        matches = []
        for score, _, example_id, record in candidates[:limit]:
            full_source = record.pop("source")
            record.pop("body")
            complete = len(full_source) <= max_source_chars
            snippet = full_source if complete else full_source[:max_source_chars]
            references = record["lexical_references"]
            record["lexical_reference_count"] = len(references)
            record["lexical_references"] = references[:100]
            record["lexical_references_complete"] = len(references) <= 100
            comments = record.get("leading_comments", "")
            record["leading_comments"] = comments[:2000]
            record["leading_comments_complete"] = len(comments) <= 2000
            record["context_chars"] = sum(len(item["source"]) for item in record["context"])
            record.update(score=round(score, 6), matches=evidence[example_id],
                          source=snippet,
                          source_complete=complete, body_window_offset=0,
                          snippet_line_start=record["line_start"],
                          snippet_line_end=record["line_start"] + snippet.count("\n"),
                          source_sha256=sha256(full_source),
                          dependency_precision="lexical identifiers; unresolved, includes locals/tactics",
                          availability_note="Validate any premise name in the unchanged exact prefix; source visibility is not a Lean availability check.")
            matches.append(record)
    return {"status": "ok" if matches else "empty", "identity": binding(material),
            "corpus_summary": summary, "query": {"text": query, "terms": query_terms,
              "used_names": symbols, "tactic_shapes": tactics},
            "total_hits": len(candidates), "matches": matches,
            "ranking": "idf-weighted-lexical-body-symbol-tactic-v1",
            "seconds": round(time.perf_counter() - started, 6)}
