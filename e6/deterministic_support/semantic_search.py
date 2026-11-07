"""Propose exact proof terms by bounded solver replay in original tactic states.

This is proposal generation only. Captured environments precede the target;
every source still requires fresh statement/axiom/exact/all-version validation.
No benchmark names or proof-specific terms occur in the generator.
"""
from __future__ import annotations

import json
import math
import os
from pathlib import Path
import time
from types import SimpleNamespace

from lean_tools import arena_workflow as arena, lean_launch, lean_source
from lean_tools.proof_specialization import lex
from .. import deterministic_native as native
from ..config import configure_native_environment
from ..runtime import RuntimeContext, scoped_environment
from .edit_packs import digest, OFFSET_UNIT

GENERATOR_FILES = ["e6/deterministic_support/semantic_search.py",
                   "e6/deterministic_native_support/SemanticSearch.lean.inc"]
HELPER_PATH = Path(__file__).parents[1] / "deterministic_native_support/SemanticSearch.lean.inc"
MODULE_NAME = "E6SemanticSearchHelper"
FAMILY = "semantic_search_suffix_term"
ORIGINAL_FAMILY = "semantic_search_original_term"
SOLVER_FAMILY = "semantic_search_solver_term"
NORMALIZE_FAMILY = "semantic_search_normalized_term"
REUSE_FAMILY = "semantic_search_local_reuse"
REPLAY_FAMILY = "semantic_replay_tactic"
SCHEMA_VERSION = 1
MAX_SITES = 16
DEFAULT_MAX_CANDIDATES = 64
MAX_CANDIDATES = 256
DEFAULT_TIMEOUT_SECONDS = 90
MAX_TIMEOUT_SECONDS = 360
MAX_TERM_CHARS = 8000
ORIGINAL_SOLVERS = ("original_suffix_term",)
NORMALIZE_SOLVERS = ("original_suffix_zeta", "original_suffix_beta_eta", "original_suffix_normalized")
REUSE_SOLVERS = ("original_suffix_local_reuse",)
SEARCH_SOLVERS = ("rfl", "assumption", "solve_by_elim", "exact?", "simp_all", "omega", "aesop", "grind", "ring")
SOLVERS = ORIGINAL_SOLVERS + NORMALIZE_SOLVERS + REUSE_SOLVERS + SEARCH_SOLVERS


def select_solvers(family: str | None, configured: object = None) -> tuple[str, ...]:
    families = {None: SOLVERS, FAMILY: SOLVERS, "semantic_search": SOLVERS, "semantic": SOLVERS,
        ORIGINAL_FAMILY: ORIGINAL_SOLVERS, "semantic_extract": ORIGINAL_SOLVERS,
        "semantic_original": ORIGINAL_SOLVERS + NORMALIZE_SOLVERS,
        SOLVER_FAMILY: SEARCH_SOLVERS, "semantic_solvers": SEARCH_SOLVERS,
        NORMALIZE_FAMILY: NORMALIZE_SOLVERS, "semantic_normalize": NORMALIZE_SOLVERS,
        REUSE_FAMILY: REUSE_SOLVERS, "semantic_local_reuse": REUSE_SOLVERS,
        REPLAY_FAMILY: SEARCH_SOLVERS}
    selected = families.get(family, ())
    if configured is None:
        return selected
    if (not isinstance(configured, (list, tuple)) or any(not isinstance(value, str) or value not in SOLVERS
                                                      for value in configured)):
        raise ValueError("semantic_search_solvers must contain only fixed semantic portfolio names")
    return tuple(value for value in dict.fromkeys(configured) if value in selected)


def solver_family(solver: str) -> str:
    if solver in ORIGINAL_SOLVERS:
        return ORIGINAL_FAMILY
    if solver in NORMALIZE_SOLVERS:
        return NORMALIZE_FAMILY
    if solver in REUSE_SOLVERS:
        return REUSE_FAMILY
    return SOLVER_FAMILY


def resolve_limits(config: dict, timeout_seconds: float, max_candidates: int) -> dict:
    """Validate source-bound discovery caps; never alter evaluator settings."""
    settings = config.get("optimizer_v5_generator", {})
    if not isinstance(settings, dict):
        raise ValueError("optimizer_v5_generator must be an object")
    defaults = {"max_sites": 16, "scan_seconds": 45, "solver_heartbeats": 10000,
                "site_order": "source", "discovery_timeout_seconds": 90, "max_candidates": 64}
    limits = {name: config.get("semantic_search_" + name,
               settings.get(name, settings.get("semantic_search_" + name, value)))
              for name, value in defaults.items()}
    for name, upper in (("max_sites", 128), ("solver_heartbeats", 100000), ("max_candidates", 256)):
        if type(limits[name]) is not int or not 1 <= limits[name] <= upper:
            raise ValueError(f"{name} must be an integer in 1..{upper}")
    for name, upper in (("scan_seconds", 300), ("discovery_timeout_seconds", 360)):
        value = limits[name]
        if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value) or not 0 < value <= upper:
            raise ValueError(f"{name} must be finite and in (0, {upper}]")
    if limits["site_order"] not in ("source", "reverse", "span_short_first"):
        raise ValueError("site_order must be source, reverse, or span_short_first")
    limits["effective_timeout_seconds"] = min(timeout_seconds, limits["discovery_timeout_seconds"])
    limits["effective_max_candidates"] = min(max_candidates, limits["max_candidates"])
    limits["scan_milliseconds"] = math.ceil(limits["scan_seconds"] * 1000)
    return limits


class SemanticSearchError(RuntimeError):
    """Discovery failed, retaining the ordinary Lean-run diagnostic contract."""

    def __init__(self, message: str, result: object | None = None):
        super().__init__(message)
        self.result = result


def _remaining(deadline: float) -> float:
    remaining = deadline - time.perf_counter()
    if remaining <= 0:
        raise TimeoutError("Semantic search discovery deadline expired")
    return remaining


def _helper_text(module: bool) -> str:
    header = ("module\npublic import Lean\npublic meta import Lean.Elab.Tactic.Meta\n"
              "public meta import Init.Data.String.Legacy\npublic meta section\n" if module
              else "import Lean\n")
    return header + HELPER_PATH.read_text(encoding="utf-8")


def _helper(config: dict, project: Path, workdir: Path, module: bool,
            deadline: float) -> tuple[Path, dict, dict]:
    environment = lean_launch.workspace_guard(project, os.environ)
    text = _helper_text(module)
    key = digest(json.dumps({"environment": environment, "helper": text}, sort_keys=True))
    cache = Path(config.get("root", workdir)).resolve() / "deterministic/semantic-search-helper-cache" / key
    if cache.is_relative_to(project.resolve()):
        raise SemanticSearchError("Helper cache must be outside cached Lean project")
    cache.mkdir(parents=True, exist_ok=True)
    source, olean, marker = (cache / (MODULE_NAME + ".lean"), cache / (MODULE_NAME + ".olean"), cache / "ready.json")
    with arena.exclusive_file_lock(cache / ".build.lock", _remaining(deadline)):
        if marker.is_file() and olean.is_file():
            receipt = json.loads(marker.read_text())
            if receipt.get("key") == key and receipt.get("olean_sha256") == native._sha(olean.read_bytes()):
                return cache, {**receipt, "reused": True}, environment
        source.write_text(text, encoding="utf-8")
        receipt = {"key": key, "source_sha256": digest(text), "source_path": str(source),
                   "cache_path": str(cache), "reused": False}
        arena.write_json_atomic(cache / "environment.json", environment)
        run = native._run(source, project, deadline, cache / "build.log",
                          lean_args=["-R", str(cache), "-o", str(olean)])
        receipt.update(run)
        arena.write_json_atomic(cache / "build.json", receipt)
        if run["returncode"] != 0 or run["timed_out"] or not olean.is_file():
            raise SemanticSearchError(f"Semantic helper compile failed: {cache / 'build.log'}",
                                      SimpleNamespace(**run, log_path=str(cache / "build.log")))
        receipt["olean_sha256"] = native._sha(olean.read_bytes())
        arena.write_json_atomic(marker, receipt)
        return cache, receipt, environment


def _safe_term(term: object) -> bool:
    if not isinstance(term, str) or not term.strip() or len(term) > MAX_TERM_CHARS:
        return False
    if any(marker in term for marker in ("✝", "⋯", "?m.", "?u.", "--", "/-", "-/", "`", "\r")):
        return False
    try:
        tokens = lex(term)
    except ValueError:
        return False
    return bool(tokens) and not any(token.kind == "opaque" or token.text in
        {"_", "sorry", "admit", "sorryAx", "native_decide", "implemented_by", "unsafe"}
        or token.text.startswith("?") for token in tokens)


def map_records(source: str, scan: dict, shift: int, minimum: int, maximum: int,
                *, max_candidates: int = DEFAULT_MAX_CANDIDATES, replay_tactics: bool = False,
                telemetry: dict | None = None) -> tuple[list[dict], list[dict]]:
    """Bind native UTF-8 suffix spans and safe rendered terms to current source."""
    if scan.get("schema_version") != SCHEMA_VERSION or scan.get("native_environment_target_present") is not False:
        raise SemanticSearchError("Native search lacks pre-target environment guard")
    raw = source.encode("utf-8")
    parent, seen = digest(source), {digest(source)}
    candidates, rejected = [], []
    for index, record in enumerate(scan.get("records", [])):
        try:
            a, b = record["start_byte"] + shift, record["end_byte"] + shift
            if (type(a) is not int or type(b) is not int or not minimum <= a < b <= maximum
                    or record.get("goal_count") != 1 or record.get("execution_count") != 1
                    or record.get("snapshot_target_present") is not False):
                raise ValueError("Invalid suffix span or unguarded snapshot")
            before, old, after = raw[:a].decode("utf-8"), raw[a:b].decode("utf-8"), raw[b:].decode("utf-8")
            for attempt in record.get("attempts", []):
                result = attempt.get("result", {})
                if result.get("status") != "solved":
                    continue
                term = result.get("term")
                if (result.get("target_present") is not False or result.get("has_metavariables") is not False
                        or result.get("has_sorry") is not False or result.get("is_proposition") is not True
                        or result.get("has_metavariable_leakage") is not False
                        or result.get("prefix_only_constants") is not True
                        or (not replay_tactics and not _safe_term(term))):
                    rejected.append({"record_index": index, "solver": attempt.get("solver"),
                                     "reason": "Incomplete, opaque, or unguarded solved term"})
                    continue
                # PP layout is relative to its expression's origin. Preserve
                # that origin after insertion into a possibly nested tactic.
                if replay_tactics:
                    if attempt.get("solver") not in SEARCH_SOLVERS:
                        rejected.append({"record_index": index, "reason": "not a fixed replay solver"})
                        continue
                    replacement = attempt["solver"]
                else:
                    column = len(before.rsplit("\n", 1)[-1]) + len("exact (")
                    rendered = term.replace("\n", "\n" + " " * column)
                    replacement = "exact (" + rendered + ")"
                child = before + replacement + after
                hashed = digest(child)
                if hashed in seen:
                    continue
                seen.add(hashed)
                actual_family = REPLAY_FAMILY if replay_tactics else solver_family(attempt["solver"])
                candidates.append({"id": actual_family + ":" + hashed[:16], "family": actual_family,
                    "description": ("Native-verified fixed solver replaces a tactic-sequence suffix" if replay_tactics else
                                    "Exact Lean-generated proof term replaces a tactic-sequence suffix"),
                    "source": child, "parent_sha256": parent, "source_sha256": hashed,
                    "solver": attempt["solver"], "term_chars": len(term) if isinstance(term, str) else 0,
                    "local_proof_reuse_count": result.get("local_proof_reuse_count", 0),
                    "replaced_chars": len(old), "site": len(before),
                    "edits": [{"start": len(before), "end": len(before) + len(old),
                               "old": old, "new": replacement, "old_sha256": digest(old),
                               "new_sha256": digest(replacement), "offset_unit": OFFSET_UNIT}],
                    "requires_full_validation": True,
                    "validation_required": "complete_source_exact_axioms_and_compatibility",
                    "mapped_by": "pre-target TacticInfo snapshot and native proof-term extraction"})
        except (ValueError, TypeError, KeyError, UnicodeDecodeError) as error:
            rejected.append({"record_index": index, "reason": str(error)})
    # Shortest proofs get checked first; measured score remains authoritative.
    candidates.sort(key=lambda value: (len(value["source"]), value["site"], value["solver"]))
    if telemetry is not None:
        telemetry.update(generated_before_truncation_count=len(candidates),
                         proposal_truncated_count=max(0, len(candidates) - max_candidates),
                         proposal_cap_reached=len(candidates) > max_candidates)
    return candidates[:max_candidates], rejected


def generate_candidates(*, config: dict, source: str, signature: str, workdir: Path,
                        timeout_seconds: float = DEFAULT_TIMEOUT_SECONDS,
                        max_candidates: int = DEFAULT_MAX_CANDIDATES, family: str | None = None) -> list[dict]:
    if type(max_candidates) is not int or max_candidates < 0:
        raise ValueError("max_candidates must be a nonnegative integer")
    max_candidates = min(max_candidates, MAX_CANDIDATES)
    if (isinstance(timeout_seconds, bool) or not isinstance(timeout_seconds, (int, float))
            or not math.isfinite(timeout_seconds) or timeout_seconds <= 0):
        raise ValueError("timeout_seconds must be finite and positive")
    timeout_seconds = min(timeout_seconds, MAX_TIMEOUT_SECONDS)
    if not isinstance(source, str) or not source.strip() or "\r" in source:
        raise ValueError("Semantic search requires nonempty LF source")
    settings = config.get("optimizer_v5_generator", {})
    if not isinstance(settings, dict):
        raise ValueError("optimizer_v5_generator must be an object")
    solvers = select_solvers(family, config.get("semantic_search_solvers", settings.get("semantic_search_solvers")))
    if not solvers:
        return []
    limits = resolve_limits(config, timeout_seconds, max_candidates)
    timeout_seconds, max_candidates = limits["effective_timeout_seconds"], limits["effective_max_candidates"]
    project, workdir = Path(config["primary"]).resolve(), Path(workdir).resolve()
    if workdir.is_relative_to(project):
        raise ValueError("Discovery must be outside cached Lean project")
    workdir.mkdir(parents=True, exist_ok=True)
    started, deadline = time.perf_counter(), time.perf_counter() + timeout_seconds
    output = workdir / "semantic-search-proposals.json"
    receipt = {"schema_version": SCHEMA_VERSION, "status": "running", "source_sha256": digest(source),
               "model_calls": 0, "solver_portfolio": solvers, "selected_family": family,
               "max_sites": limits["max_sites"], "resolved_limits": limits,
               "hard_limits": {"max_sites": 128, "scan_seconds": 300, "solver_heartbeats": 100000,
                               "discovery_timeout_seconds": 360, "max_candidates": 256},
               "timeout_seconds": timeout_seconds, "max_candidates": max_candidates,
               "validation_required": "complete_source_exact_axioms_and_compatibility"}
    try:
        _, row = arena.load_task(Path(config["task"]))
        if signature != row["signature"]:
            raise ValueError("Signature does not match task")
        declaration, input_start, proof_start = native._current_source(row, source)
        if not max_candidates:
            receipt.update(status="completed", candidate_count=0)
            return []
        values = RuntimeContext.resolve(Path(config.get("root", workdir)), config).environment(workdir)
        values = {key: os.environ.get(key, value) for key, value in values.items()}
        values["LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE"] = "compile"
        values["LEAN_REFACTOR_LAUNCH_CACHE"] = str(Path(config.get("root", workdir)) / "deterministic/native-launch-cache")
        with scoped_environment({**values, **configure_native_environment(elan_home=config.get("elan_home"))}):
            prefix = lean_source.exact_source_prefix(row, project)
            _, module = lean_source.import_header_end(prefix.text)
            directory, helper, environment = _helper(config, project, workdir, module, deadline)
            raw_output = workdir / "semantic-search.raw.json"
            proof_offset = len(declaration[:proof_start - input_start].encode("utf-8"))
            command = ("#e6_semantic_search " + json.dumps(str(raw_output), ensure_ascii=False)
                       + f" after {proof_offset} sites {limits['max_sites']} heartbeats {limits['solver_heartbeats']}"
                       + f" scan_ms {limits['scan_milliseconds']} order " + json.dumps(limits["site_order"])
                       + " solvers "
                       + json.dumps("\n".join(solvers), ensure_ascii=False) + " in\n")
            instrumented = command + declaration
            harness = prefix.text + instrumented.rstrip() + "\n"
            insertion, _ = lean_source.import_header_end(harness)
            imported = ("\nmeta import " if module else "\nimport ") + MODULE_NAME + "\n"
            harness = harness[:insertion] + imported + harness[insertion:]
            suffix = instrumented.rstrip() + "\n"
            if not harness.endswith(suffix):
                raise SemanticSearchError("Harness lost exact target suffix")
            declaration_start = len(harness[:-len(suffix)].encode("utf-8")) + len(command.encode("utf-8"))
            shift = len(source[:input_start].encode("utf-8")) - declaration_start
            path = workdir / "SemanticSearch.lean"
            path.write_text(harness, encoding="utf-8")
            run = native._run(path, project, deadline, workdir / "semantic-search.log", lean_path_prefixes=[directory])
            receipt.update(run=run, helper_build=helper, prefix_sha256=prefix.sha256,
                           environment_sha256=digest(json.dumps(environment, sort_keys=True)))
            if run["returncode"] != 0 or run["timed_out"] or not raw_output.is_file():
                raise SemanticSearchError(f"Native search failed: {workdir / 'semantic-search.log'}",
                                          SimpleNamespace(**run, log_path=str(workdir / "semantic-search.log")))
            scan = json.loads(raw_output.read_text(encoding="utf-8"))
            proposal_counts = {}
            candidates, rejected = map_records(source, scan, shift, len(source[:proof_start].encode("utf-8")),
                len(source[:input_start + len(declaration)].encode("utf-8")), max_candidates=max_candidates,
                replay_tactics=family == REPLAY_FAMILY, telemetry=proposal_counts)
            receipt.update(proposal_counts)
            receipt.update(native_summary={key: value for key, value in scan.items() if key != "records"},
                           mapping_rejections=rejected)
            for candidate in candidates:
                native._current_source(row, candidate["source"])
        receipt.update(status="completed", candidate_count=len(candidates),
                       candidates=[{key: value for key, value in item.items() if key != "source"} for item in candidates])
        return candidates
    except Exception as error:
        receipt.update(status="failed", error_type=type(error).__name__, error=str(error),
                       partial_candidates_discarded=True, candidate_count=0)
        result = getattr(error, "result", None)
        if result is None and isinstance(error, TimeoutError):
            result = SimpleNamespace(timed_out=True)
        raise SemanticSearchError(f"Semantic search failed; see {output}: {error}", result) from error
    finally:
        receipt["wall_seconds"] = time.perf_counter() - started
        arena.write_json_atomic(output, receipt)
