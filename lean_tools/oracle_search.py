"""Prefix-bounded proof-search helpers for Lean Refactor Arena tasks.

The tool has two deliberately separate commands:

``search``
    Search declaration names (and optionally their rendered types) in the Lean
    environment immediately before the benchmark declaration.  For a
    repository task, the file is the evaluator's exact source prefix; it never
    imports the completed target module.

``aesop``
    Run ``show_term aesop`` in an enriched copy of that same prefix, optionally
    using a compatibility checkout selected by ``--oracle-project-root``.
    Extract Lean's suggested explicit script and automatically replay it through
    the untouched primary Arena environment selected by ``--project-root``.
    The command only reuses an already-built Aesop package from the oracle Lean
    release family.  Every candidate package is probe-loaded by that oracle
    checkout's actual toolchain before use.  The command never fetches, builds,
    or changes an environment.

Both commands accept ``--task`` and ``--project-root`` and emit JSON on stdout.
The JSON includes a prefix fingerprint so callers can record which source
position was searched without exposing the source text itself.
"""

from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import argparse
import json
import os
import re
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any


from lean_tools import arena_workflow as arena
from lean_tools import lean_source
from lean_tools.lean_source import SourcePrefix as PrefixContext
SCHEMA_VERSION = 1
DECLARATION_PREFIX = "LRH_DECL\t"
DECLARATION_TOTAL_PREFIX = "LRH_DECL_TOTAL\t"


class OracleError(RuntimeError):
    pass


@dataclass(frozen=True)
class AesopResolution:
    root: Path
    library_paths: tuple[Path, ...]
    target_toolchain: str
    package_toolchain: str
    probe: arena.LeanRun


def exact_source_prefix(row: dict[str, Any], project_root: Path) -> PrefixContext:
    """Return the shared evaluator prefix before the target declaration."""
    try:
        return lean_source.exact_source_prefix(row, project_root)
    except lean_source.SourceDocumentError as error:
        raise OracleError(str(error)) from error


def prefix_payload(context: PrefixContext) -> dict[str, Any]:
    return {
        "kind": context.kind,
        "source_path": str(context.source_path) if context.source_path else None,
        "sha256": context.sha256,
        "target_visible": False,
        "later_declarations_visible": False,
    }


def lean_string_literal(value: str) -> str:
    if "\x00" in value:
        raise OracleError("search text may not contain NUL")
    return json.dumps(value, ensure_ascii=False)


def build_search_harness(
    context: PrefixContext,
    *,
    name_query: str,
    type_query: str | None,
    limit: int,
    broad: bool = False,
    complete_signatures: bool = False,
) -> str:
    if not name_query and not type_query and not broad:
        raise OracleError("search requires a non-empty name or type query")
    if limit <= 0:
        raise OracleError("search limit must be positive")

    name_literal = lean_string_literal(name_query)
    type_literal = lean_string_literal(type_query or "")
    name_condition = (
        "true"
        if not name_query
        else f"«lrhSearchContainsText» «lrhSearchName».toString {name_literal}"
    )
    type_condition = (
        "true"
        if not type_query
        else f"«lrhSearchContainsText» «lrhSearchTypeText» {type_literal}"
    )
    type_render = "let «lrhSearchTypeText» := toString (← _root_.Lean.Meta.ppExpr «lrhSearchInfo».type)"
    if complete_signatures:
        type_render = "let «lrhSearchTypeText» ← _root_.Lean.MonadWithOptions.withOptions (fun «lrhSearchOptions» => _root_.Lean.Option.set ((«lrhSearchOptions».setBool `pp.deepTerms true).setBool `pp.proofs true) _root_.Lean.pp.maxSteps 1000000000) do\n        pure (toString (← _root_.Lean.Meta.ppExpr «lrhSearchInfo».type))"
    return arena.ensure_section_gap(context.text) + f"""
open Lean

run_elab do
  let rec «lrhSearchStartsWithChars» : _root_.List _root_.Char → _root_.List _root_.Char → _root_.Bool
    | [], _ => true
    | _, [] => false
    | «lrhSearchNeedleHead» :: «lrhSearchNeedleTail», «lrhSearchHayHead» :: «lrhSearchHayTail» =>
        «lrhSearchNeedleHead» == «lrhSearchHayHead» && «lrhSearchStartsWithChars» «lrhSearchNeedleTail» «lrhSearchHayTail»
  let rec «lrhSearchContainsChars» («lrhSearchNeedle» : _root_.List _root_.Char) : _root_.List _root_.Char → _root_.Bool
    | [] => «lrhSearchStartsWithChars» «lrhSearchNeedle» []
    | «lrhSearchHaystack»@(_ :: «lrhSearchHayTail») =>
        «lrhSearchStartsWithChars» «lrhSearchNeedle» «lrhSearchHaystack» || «lrhSearchContainsChars» «lrhSearchNeedle» «lrhSearchHayTail»
  let «lrhSearchContainsText» («lrhSearchHaystack» «lrhSearchNeedle» : _root_.String) : _root_.Bool :=
    «lrhSearchContainsChars» «lrhSearchNeedle».toList «lrhSearchHaystack».toList
  let «lrhSearchEnv» ← _root_.Lean.MonadEnv.getEnv
  let mut «lrhSearchResults» : _root_.Array (_root_.Lean.Name × _root_.String) := #[]
  for («lrhSearchName», «lrhSearchInfo») in «lrhSearchEnv».constants.toList do
    if {name_condition} then
      {type_render}
      if {type_condition} then
        «lrhSearchResults» := «lrhSearchResults».push («lrhSearchName», «lrhSearchTypeText»)
  let «lrhSearchSortedResults» := «lrhSearchResults».qsort fun «lrhSearchLeft» «lrhSearchRight» =>
    «lrhSearchLeft».1.toString < «lrhSearchRight».1.toString
  for («lrhSearchName», «lrhSearchTypeText») in «lrhSearchSortedResults».take {limit} do
    let «lrhSearchOneLineType» := ((«lrhSearchTypeText».replace "\\r" " ").replace "\\n" " ").replace "\\t" " "
    _root_.IO.println s!"LRH_DECL\\t{{«lrhSearchName»}}\\t{{«lrhSearchOneLineType»}}"
  _root_.IO.println s!"LRH_DECL_TOTAL\\t{{«lrhSearchSortedResults».size}}"
"""


def parse_search_output(output: str) -> tuple[list[dict[str, str]], int]:
    declarations: list[dict[str, str]] = []
    totals: list[int] = []
    for line in output.splitlines():
        if line.startswith(DECLARATION_PREFIX):
            fields = line.split("\t", 2)
            if len(fields) == 3:
                declarations.append({"name": fields[1], "type": fields[2]})
        elif line.startswith(DECLARATION_TOTAL_PREFIX):
            try:
                totals.append(int(line[len(DECLARATION_TOTAL_PREFIX) :]))
            except ValueError as error:
                raise OracleError("Lean emitted a malformed declaration total") from error
    if len(totals) != 1:
        raise OracleError(
            f"expected one declaration total from Lean, found {len(totals)}"
        )
    return declarations, totals[0]


def run_generated_lean(
    source: str,
    project_root: Path,
    timeout_seconds: int,
    *,
    lean_path_prefixes: list[Path] | None = None,
    scratch_prefix: str,
) -> arena.LeanRun:
    with arena.temporary_evaluation_directory(scratch_prefix) as temporary:
        scratch_root = Path(temporary)
        source_path = scratch_root / "Oracle.lean"
        source_path.write_text(source, encoding="utf-8")
        return arena.run_lean(
            source_path,
            project_root.resolve(),
            timeout_seconds,
            lean_args=["-R", str(scratch_root)],
            lean_path_prefixes=lean_path_prefixes,
        )


def declaration_search(
    task_path: Path,
    project_root: Path,
    *,
    name_query: str,
    type_query: str | None,
    limit: int,
    timeout_seconds: int,
    candidate_limit: int | None = None,
    ranker: str | None = None,
    model: str | None = None,
    goal: str | None = None,
    hypotheses: list[str] | None = None,
    search_intent: str | None = None,
    context_file: Path | None = None,
    pool_output: Path | None = None,
    include_pool: bool = False,
    broad: bool = False,
    fingerprint_registry: Path | None = None,
    full_types: bool = False,
    source_output: Path | None = None,
) -> dict[str, Any]:
    from lean_tools import rerank_service_client as reranking

    options, automatic = reranking.resolve_options(ranker=ranker, model=model)
    enabled = bool(options) or candidate_limit is not None or pool_output is not None or include_pool or broad or context_file is not None or goal is not None or hypotheses is not None or search_intent is not None
    try:
        pool_limit = reranking.resolve_search_limits(
            limit, candidate_limit, options=options, automatic=automatic, enabled=enabled,
        )
    except reranking.SearchLimitError as error:
        raise OracleError(str(error)) from error
    ranking_context = reranking.load_context(context_file) if enabled else None
    _, row = arena.load_task(task_path.resolve())
    context = exact_source_prefix(row, project_root)
    harness = build_search_harness(
        context,
        name_query=name_query,
        type_query=type_query,
        limit=pool_limit,
        broad=broad,
        complete_signatures=enabled or full_types,
    )
    if source_output is not None:
        source_output = source_output.resolve()
        source_output.parent.mkdir(parents=True, exist_ok=True)
        source_output.write_text(harness, encoding="utf-8")
    result = run_generated_lean(
        harness,
        project_root,
        timeout_seconds,
        scratch_prefix="lrh-search-",
    )
    arena.require_lean_success(result, f"{row['name']}: prefix declaration search")
    declarations, total = parse_search_output(result.output)
    matches = declarations[:limit]
    payload = {
        "schema_version": SCHEMA_VERSION,
        "command": "search",
        "task_id": row["name"],
        "project_root": str(project_root.resolve()),
        "prefix": prefix_payload(context),
        "query": {"name": name_query, "type": type_query},
        "search_limits": reranking.search_limit_contract(options, automatic, enabled=enabled),
        "total_matches": total,
        "returned_matches": len(matches),
        "truncated": total > len(matches),
        "matches": matches,
        "lean_seconds": round(result.seconds, 6),
    }
    if source_output is not None:
        payload["generated_source_output"] = str(source_output)
    if not enabled:
        return payload
    if any("⋯" in declaration["type"] for declaration in declarations):
        raise OracleError("reranking requires complete declaration types without pretty-printer elisions")
    context = ranking_context
    context_sha = payload["prefix"]["sha256"]
    context.update(task_signature=row["signature"], source_sha256=context_sha, query=payload["query"])
    if goal is not None:
        context["goal"] = goal
    if hypotheses is not None:
        context["hypotheses"] = hypotheses
    if search_intent is not None:
        context["search_intent"] = search_intent
    binding = reranking.make_binding(declarations, context, task_id=row["name"], prefix_sha256=context_sha, environment_fingerprint=arena.measurement_environment_fingerprint(row, project_root, registry_path=fingerprint_registry), source_sha256=context_sha)
    payload.update(candidate_limit=pool_limit, candidate_matches=len(declarations), candidate_pool_sha256=binding["pool_sha256"], candidate_pool_truncated=total > len(declarations), broad=broad)
    ranked = reranking.rerank(declarations, context, binding=binding, options=options or {"ranker": "baseline"}, automatic=automatic)
    payload["matches"] = ranked["matches"][:limit]
    payload["reranking"] = reranking.compact_result(ranked, declarations, limit, include_pool=include_pool)
    if pool_output is not None:
        reranking.write_pool(pool_output, declarations, context, binding, reranking=ranked)
        payload["candidate_pool_output"] = str(pool_output.resolve())
    if include_pool:
        payload["candidate_pool"] = declarations
    return payload


def normalized_toolchain(project_root: Path) -> str:
    path = project_root.resolve() / "lean-toolchain"
    if not path.is_file():
        raise OracleError(f"Lean project has no lean-toolchain: {project_root}")
    value = path.read_text(encoding="utf-8").strip()
    if not value:
        raise OracleError(f"Lean project has an empty lean-toolchain: {project_root}")
    return value


def lean_release_family(toolchain: str) -> tuple[int, int] | None:
    """Extract the stable Lean major/minor family from an Elan toolchain name."""
    match = re.search(r"(?:^|:)v?(\d+)\.(\d+)(?:\.\d+)?(?:$|[-+])", toolchain)
    if match is None:
        return None
    return int(match.group(1)), int(match.group(2))


def same_lean_release_family(left: str, right: str) -> bool:
    left_family = lean_release_family(left)
    right_family = lean_release_family(right)
    if left_family is None or right_family is None:
        return left == right
    return left_family == right_family


def normalize_aesop_root(path: Path) -> Path | None:
    root = path.expanduser().resolve()
    if (root / "Aesop.lean").is_file():
        return root
    package = root / ".lake" / "packages" / "aesop"
    return package if (package / "Aesop.lean").is_file() else None


def default_environment_cache_root(platform_name: str | None = None) -> Path:
    """Use the native E6 cache; callers may explicitly override its location."""
    del platform_name
    configured = os.environ.get("LEAN_REFACTOR_ENV_CACHE_ROOT")
    return Path(configured).expanduser() if configured else Path.home() / "lean-e6-env"


def cached_aesop_candidates(project_root: Path) -> list[Path]:
    project_root = project_root.resolve()
    project_local = project_root / ".lake" / "packages" / "aesop"
    candidates: list[tuple[int, Path]] = [
        (0, project_local),
        (2, arena.repo_root_from_script() / ".lake" / "packages" / "aesop"),
    ]
    configured = os.environ.get("LEAN_REFACTOR_AESOP_ROOT")
    if configured:
        candidates.append((1, Path(configured)))
    cache_root = default_environment_cache_root()
    if cache_root.is_dir():
        candidates.extend(
            (3, candidate)
            for candidate in sorted(
                cache_root.glob("*/*/p/.lake/packages/aesop"),
                key=lambda path: os.path.normcase(str(path.resolve())),
            )
        )
    unique: dict[str, tuple[int, Path]] = {}
    for source_priority, candidate in candidates:
        normalized = normalize_aesop_root(candidate)
        if normalized is None:
            continue
        key = os.path.normcase(str(normalized))
        previous = unique.get(key)
        if previous is None or source_priority < previous[0]:
            unique[key] = (source_priority, normalized)

    expected = normalized_toolchain(project_root)
    project_key = os.path.normcase(str(project_local.resolve()))

    def order(item: tuple[str, tuple[int, Path]]) -> tuple[int, int, int, str]:
        key, (source_priority, candidate) = item
        try:
            actual = normalized_toolchain(candidate)
        except OracleError:
            actual = ""
        return (
            0 if key == project_key else 1,
            0 if actual == expected else 1,
            source_priority,
            key,
        )

    return [entry[1][1] for entry in sorted(unique.items(), key=order)]


def aesop_library_paths(aesop_root: Path) -> list[Path]:
    library = aesop_root / ".lake" / "build" / "lib" / "lean"
    if not (library / "Aesop.olean").is_file():
        raise OracleError(
            f"Aesop is not prebuilt at {aesop_root}; this tool will not build it"
        )
    manifest_path = aesop_root / "lake-manifest.json"
    if not manifest_path.is_file():
        raise OracleError(
            f"Aesop has no lake-manifest.json at {aesop_root}; dependency paths "
            "cannot be resolved safely"
        )
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise OracleError(f"invalid Aesop manifest: {manifest_path}") from error
    packages = manifest.get("packages") if isinstance(manifest, dict) else None
    if not isinstance(packages, list):
        raise OracleError(f"Aesop manifest has no package list: {manifest_path}")

    paths = [library]
    seen = {os.path.normcase(str(library.resolve()))}
    for entry in packages:
        name = entry.get("name") if isinstance(entry, dict) else None
        if (
            not isinstance(name, str)
            or not name
            or "/" in name
            or "\\" in name
        ):
            raise OracleError(f"Aesop manifest has an invalid dependency name: {name!r}")
        dependency_roots = [aesop_root / ".lake" / "packages" / name]
        if aesop_root.parent.name.lower() == "packages":
            dependency_roots.append(aesop_root.parent / name)
        dependency_library = next(
            (
                root / ".lake" / "build" / "lib" / "lean"
                for root in dependency_roots
                if (root / ".lake" / "build" / "lib" / "lean").is_dir()
            ),
            None,
        )
        if dependency_library is None:
            raise OracleError(
                f"Aesop dependency {name!r} has no prebuilt Lean library near "
                f"{aesop_root}"
            )
        key = os.path.normcase(str(dependency_library.resolve()))
        if key not in seen:
            seen.add(key)
            paths.append(dependency_library)
    return paths


def probe_aesop_package(
    project_root: Path,
    aesop_root: Path,
    timeout_seconds: float,
) -> arena.LeanRun:
    """Load Aesop and Batteries using the target project's Lean executable."""
    source = """import Aesop

example : True := by
  aesop
"""
    return run_generated_lean(
        source,
        project_root.resolve(),
        timeout_seconds,
        lean_path_prefixes=aesop_library_paths(aesop_root),
        scratch_prefix="lrh-aesop-probe-",
    )


def resolve_aesop_root(
    project_root: Path,
    explicit_root: Path | None = None,
    *,
    timeout_seconds: int = 120,
) -> AesopResolution:
    if timeout_seconds <= 0:
        raise OracleError("Aesop probe timeout must be positive")
    deadline = time.monotonic() + timeout_seconds
    compile_scope = arena.lean_timeout_scope() == "compile"
    expected = normalized_toolchain(project_root)
    if explicit_root is not None:
        normalized = normalize_aesop_root(explicit_root)
        if normalized is None:
            raise OracleError(f"not an Aesop package or provider project: {explicit_root}")
        candidates = [normalized]
    else:
        candidates = cached_aesop_candidates(project_root)
    mismatches: list[str] = []
    for candidate in candidates:
        remaining = timeout_seconds if compile_scope else deadline - time.monotonic()
        if remaining <= 0:
            mismatches.append("aggregate Aesop resolution timeout exhausted")
            break
        try:
            actual = normalized_toolchain(candidate)
            library_paths = aesop_library_paths(candidate)
        except OracleError as error:
            mismatches.append(str(error))
            continue
        if not same_lean_release_family(actual, expected):
            mismatches.append(
                f"{candidate}: {actual} is outside target family {expected}"
            )
            continue
        remaining = timeout_seconds if compile_scope else deadline - time.monotonic()
        if remaining <= 0:
            mismatches.append("aggregate Aesop resolution timeout exhausted")
            break
        probe = probe_aesop_package(project_root, candidate, remaining)
        if probe.returncode == 0 and not probe.timed_out:
            return AesopResolution(
                candidate,
                tuple(library_paths),
                expected,
                actual,
                probe,
            )
        diagnostic = arena.compact_lean_diagnostic(probe.output, limit=2_000)
        mismatches.append(
            f"{candidate}: target-toolchain probe failed"
            + (f" ({diagnostic})" if diagnostic else "")
        )
    detail = "; ".join(mismatches[:5]) or "no cached Aesop packages found"
    raise OracleError(
        f"no prebuilt, probe-compatible Aesop package in Lean release family "
        f"{lean_release_family(expected) or expected} for {project_root}. "
        "Pass --aesop-root pointing to an existing same-family Aesop build; "
        f"nothing was fetched or built. Checked: {detail}"
    )


def add_aesop_import(prefix: str) -> str:
    masked = arena.lean_code_mask(prefix)
    if re.search(
        r"(?m)^[ \t]*(?:(?:public|meta)[ \t]+)*import[ \t]+Aesop\b", masked
    ):
        return prefix
    module = re.search(r"(?m)^[ \t]*module[^\r\n]*(?:\r?\n|$)", masked)
    if module is not None:
        insertion = module.end()
        return prefix[:insertion] + "import Aesop\n" + prefix[insertion:]
    first_import = re.search(
        r"(?m)^[ \t]*(?:(?:public|meta)[ \t]+)*import\b", masked
    )
    if first_import is None:
        raise OracleError("cannot add Aesop safely: prefix has no module header or import")
    insertion = first_import.start()
    return prefix[:insertion] + "import Aesop\n" + prefix[insertion:]


def build_aesop_harness(context: PrefixContext, row: dict[str, Any]) -> str:
    prefix = add_aesop_import(context.text)
    declaration = f"{row['signature']} := by\n  show_term aesop\n"
    return prefix + declaration


def extract_try_suggestions(output: str) -> list[str]:
    lines = output.replace("\r\n", "\n").split("\n")
    suggestions: list[str] = []
    index = 0
    while index < len(lines):
        if lines[index].strip() != "Try this:":
            index += 1
            continue
        index += 1
        block: list[str] = []
        while index < len(lines):
            line = lines[index]
            if line and not line[0].isspace():
                break
            block.append(line)
            index += 1
        while block and not block[0].strip():
            block.pop(0)
        while block and not block[-1].strip():
            block.pop()
        if not block:
            continue
        indentation = min(
            len(line) - len(line.lstrip()) for line in block if line.strip()
        )
        rendered = "\n".join(line[indentation:] for line in block).strip()
        rendered = re.sub(r"^\[apply\][ \t]*", "", rendered)
        if rendered and rendered not in suggestions:
            suggestions.append(rendered)
    return suggestions


def suggestion_proof_body(suggestion: str) -> str:
    stripped = suggestion.strip()
    if re.match(r"^by(?:\s|$)", stripped):
        return stripped
    return "by\n" + "\n".join(
        f"  {line}" if line else "" for line in stripped.splitlines()
    )


def candidate_text_for_body(row: dict[str, Any], body: str) -> str:
    declaration = f"{row['signature']} := {body.rstrip()}"
    rendered = arena.render_environment(row) + arena.TARGET_BEGIN + declaration + "\n"
    return rendered + arena.TARGET_END


def run_aesop_oracle(
    task_path: Path,
    project_root: Path,
    *,
    aesop_root: Path | None,
    timeout_seconds: int,
    candidate_output: Path | None,
    oracle_project_root: Path | None = None,
    fingerprint_registry: Path | None = None,
) -> dict[str, Any]:
    task_path = task_path.resolve()
    project_root = project_root.resolve()
    oracle_project_root = (
        oracle_project_root.resolve()
        if oracle_project_root is not None
        else project_root
    )
    _, row = arena.load_task(task_path)
    context = exact_source_prefix(row, oracle_project_root)
    resolution = resolve_aesop_root(
        oracle_project_root,
        aesop_root,
        timeout_seconds=timeout_seconds,
    )
    harness = build_aesop_harness(context, row)
    oracle_run = run_generated_lean(
        harness,
        oracle_project_root,
        timeout_seconds,
        lean_path_prefixes=list(resolution.library_paths),
        scratch_prefix="lrh-aesop-",
    )
    suggestions = extract_try_suggestions(oracle_run.output)
    attempts: list[dict[str, Any]] = []
    portable_text: str | None = None
    portable_body: str | None = None
    if oracle_run.returncode == 0 and not oracle_run.timed_out:
        for suggestion in suggestions:
            body = suggestion_proof_body(suggestion)
            candidate_text = candidate_text_for_body(row, body)
            attempt: dict[str, Any] = {
                "suggestion": suggestion,
                "proof_body": body,
                "valid": False,
            }
            with arena.temporary_evaluation_directory("lrh-replay-") as temporary:
                candidate_path = Path(temporary) / "Candidate.lean"
                candidate_path.write_text(candidate_text, encoding="utf-8")
                try:
                    evaluation = arena.evaluate_candidate(
                        task_path,
                        candidate_path,
                        project_root,
                        timeout_seconds=timeout_seconds,
                        quick=True,
                        fingerprint_registry=fingerprint_registry,
                    )
                    attempt["valid"] = True
                    attempt["evaluation"] = arena.evaluation_payload(evaluation)
                    portable_text = candidate_text
                    portable_body = body
                except (arena.WorkflowError, OSError, ValueError) as error:
                    attempt["error"] = str(error)
            attempts.append(attempt)
            if portable_text is not None:
                break

    if candidate_output is not None and portable_text is not None:
        candidate_output = candidate_output.resolve()
        candidate_output.parent.mkdir(parents=True, exist_ok=True)
        candidate_output.write_text(portable_text, encoding="utf-8")

    return {
        "schema_version": SCHEMA_VERSION,
        "command": "aesop",
        "task_id": row["name"],
        "project_root": str(project_root),
        "oracle_project_root": str(oracle_project_root),
        "environments": {
            "oracle": {
                "project_root": str(oracle_project_root),
                "toolchain": resolution.target_toolchain,
            },
            "pristine_replay": {
                "project_root": str(project_root),
                "toolchain": normalized_toolchain(project_root),
            },
        },
        "prefix": prefix_payload(context),
        "oracle": {
            "valid": oracle_run.returncode == 0 and not oracle_run.timed_out,
            "returncode": oracle_run.returncode,
            "timed_out": oracle_run.timed_out,
            "seconds": round(oracle_run.seconds, 6),
            "aesop_root": str(resolution.root),
            "target_toolchain": resolution.target_toolchain,
            "package_toolchain": resolution.package_toolchain,
            "probe": {
                "valid": (
                    resolution.probe.returncode == 0
                    and not resolution.probe.timed_out
                ),
                "returncode": resolution.probe.returncode,
                "timed_out": resolution.probe.timed_out,
                "seconds": round(resolution.probe.seconds, 6),
                "diagnostic": arena.compact_lean_diagnostic(
                    resolution.probe.output
                ),
            },
            "diagnostic": arena.compact_lean_diagnostic(oracle_run.output),
        },
        "suggestions": suggestions,
        "pristine_replay": {
            "attempted": bool(attempts),
            "valid": portable_text is not None,
            "proof_body": portable_body,
            "attempts": attempts,
            "candidate_output": (
                str(candidate_output) if candidate_output and portable_text else None
            ),
        },
    }


def build_parser() -> argparse.ArgumentParser:
    from lean_tools import rerank_service_client as reranking

    options, automatic = reranking.resolve_options()
    limits = reranking.search_limit_contract(options, automatic, enabled=bool(options))
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    search = subparsers.add_parser(
        "search", help="search declarations visible immediately before the target"
    )
    search.add_argument("--task", type=Path, required=True)
    search.add_argument("--project-root", type=Path, required=True)
    search.add_argument("--name-query", default="")
    search.add_argument("--type-query")
    maximum = limits["candidate_limit"]["maximum"]
    limit_help = (
        f"frozen host limits: 1 <= --limit <= --candidate-limit <= {maximum}; "
        f"default candidate limit {limits['candidate_limit']['default']}"
        if automatic else
        f"--limit <= --candidate-limit; optional reranking pools are bounded by {reranking.MAX_CANDIDATES}; plain search has no upper limit"
    )
    search.add_argument("--limit", type=int, default=limits["result_limit"]["default"],
                        help=f"maximum returned declarations (default {limits['result_limit']['default']}); {limit_help}")
    search.add_argument("--candidate-limit", type=int,
                        help=f"legal declarations retrieved before reranking; {limit_help}")
    ranker_help = (
        f"Frozen host ranker: {options['ranker']}. Omit this flag to use it; explicit values must match the host configuration."
        if automatic else "optional reranker; default preserves baseline search"
    )
    model_help = (
        f"Frozen host model: {options.get('model') or 'unspecified (host default)'}. Omit this flag; an explicit value must match the host configuration."
        if automatic else "explicit OpenRouter Decisions model (requires --ranker model)"
    )
    search.add_argument("--ranker", choices=("baseline", "lexical", "jev", "openai", "model"), help=ranker_help)
    search.add_argument("--model", help=model_help)
    search.add_argument("--goal", help="current goal text for contextual ranking")
    search.add_argument("--hypothesis", action="append", default=None, help="current hypothesis text; repeat for multiple hypotheses")
    search.add_argument("--search-intent", help="what the desired lemma should help accomplish")
    search.add_argument("--context-file", type=Path, help="JSON object containing goal, hypotheses and same-run context")
    search.add_argument("--pool-output", type=Path, help="save the exact unranked pool and provenance as JSON")
    search.add_argument("--include-pool", action="store_true", help="include the unranked candidate pool in JSON stdout")
    search.add_argument("--broad", action="store_true", help="allow an empty query over the exact prefix; the finite pool is alphabetically bounded")
    search.add_argument("--fingerprint-registry", type=Path, help="reuse the host-prepared environment fingerprint")
    search.add_argument("--full-types", action="store_true", help="render complete declaration types without pretty-printer elisions")
    search.add_argument("--source-output", type=Path, help="save the exact generated legal-prefix search source")
    search.add_argument("--timeout", type=int, default=600)

    aesop = subparsers.add_parser(
        "aesop",
        help=(
            "run cached Aesop in an optional compatibility checkout and replay "
            "its explicit term in the pristine primary checkout"
        ),
    )
    aesop.add_argument("--task", type=Path, required=True)
    aesop.add_argument(
        "--project-root",
        type=Path,
        required=True,
        help="pristine primary Arena environment used for automatic replay",
    )
    aesop.add_argument(
        "--oracle-project-root",
        type=Path,
        help=(
            "optional compatibility checkout used for the source prefix and Aesop; "
            "defaults to --project-root"
        ),
    )
    aesop.add_argument(
        "--aesop-root",
        type=Path,
        help="existing Aesop package (or project containing .lake/packages/aesop)",
    )
    aesop.add_argument("--candidate-output", type=Path)
    aesop.add_argument("--timeout", type=int, default=600)
    aesop.add_argument("--fingerprint-registry", type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    if hasattr(sys.stderr, "reconfigure"):
        sys.stderr.reconfigure(encoding="utf-8")
    args = None
    try:
        args = build_parser().parse_args(argv)
        if args.command == "search":
            payload = declaration_search(
                args.task,
                args.project_root,
                name_query=args.name_query,
                type_query=args.type_query,
                limit=args.limit,
                timeout_seconds=args.timeout,
                candidate_limit=args.candidate_limit,
                ranker=args.ranker,
                model=args.model,
                goal=args.goal,
                hypotheses=args.hypothesis,
                search_intent=args.search_intent,
                context_file=args.context_file,
                pool_output=args.pool_output,
                include_pool=args.include_pool,
                broad=args.broad,
                fingerprint_registry=args.fingerprint_registry,
                full_types=args.full_types,
                source_output=args.source_output,
            )
        else:
            payload = run_aesop_oracle(
                args.task,
                args.project_root,
                aesop_root=args.aesop_root,
                timeout_seconds=args.timeout,
                candidate_output=args.candidate_output,
                oracle_project_root=args.oracle_project_root,
                fingerprint_registry=args.fingerprint_registry,
            )
        print(json.dumps(payload, ensure_ascii=False, indent=2))
        return 0
    except (
        OracleError,
        arena.WorkflowError,
        OSError,
        ValueError,
        json.JSONDecodeError,
    ) as error:
        from lean_tools import rerank_service_client as reranking

        limit_error = error.__cause__ if isinstance(error.__cause__, reranking.SearchLimitError) else error
        details = ({"search_limits": limit_error.contract, "retry_arguments": limit_error.retry}
                   if isinstance(limit_error, reranking.SearchLimitError) else {})
        print(
            json.dumps(
                {
                    "schema_version": SCHEMA_VERSION,
                    "command": getattr(args, "command", None),
                    "error": str(error),
                    **details,
                },
                ensure_ascii=False,
                indent=2,
            ),
            file=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
