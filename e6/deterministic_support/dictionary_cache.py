"""One bounded current-source dictionary census and at most four letI proposals.

No archived source, learned name list, proof search, or scoring is used here.
The full-source evaluator remains the only authority for validity and score.
"""
from __future__ import annotations

import hashlib
import json
import math
import os
from pathlib import Path
import time

from e6 import deterministic_candidates as core, deterministic_native as native
from e6.config import configure_native_environment
from e6.runtime import RuntimeContext, scoped_environment
from lean_tools import arena_workflow as arena, lean_source, lean_launch
from lean_tools.proof_specialization import lex

GENERATOR_FILES = [
    "e6/deterministic_support/dictionary_cache.py",
    "e6/deterministic_native_support/DictionaryCensus.lean.inc",
]
SUPPORT = Path(__file__).resolve().parents[1] / "deterministic_native_support"
FAMILY = "census_dictionary_cache"
MAX_CANDIDATES = 4
MAX_COMPILE_SECONDS = 180
HARD_LIMITS = {"expr_nodes": 30000, "class_type_checks": 2000, "analysis_ms": 20000,
               "roundtrips": 4, "candidate_count": 4, "compiler_seconds": 180,
               "dictionary_entries": 256, "output_records": 64, "dependency_closure": 512,
               "expression_size_count": 1024, "info_tree_depth": 512,
               "analysis_time_limit_kind": "boundary_checked_cooperative"}


class DictionaryDiscoveryError(RuntimeError):
    pass


def digest(value):
    return hashlib.sha256(value.encode("utf-8") if isinstance(value, str) else value).hexdigest()


def target_site(row, source):
    """Find an exact root `by` line; unsupported layout returns no proposal."""
    declaration, start, body = native._current_source(row, source)
    tokens = lex(source)
    assignment = core.mutations._assignment_index_after_signature(source, tokens, row["signature"])
    if assignment is None:
        return None
    by = core._outer_by(tokens, assignment)
    if by is None or by + 1 >= len(tokens):
        return None
    token, first = tokens[by], tokens[by + 1]
    if source[token.end:token.end + 1] != "\n" or first.start >= start + len(declaration):
        return None
    line_start = source.rfind("\n", 0, first.start) + 1
    indent = source[line_start:first.start]
    if not indent or indent.strip(" ") or "\t" in indent:
        return None
    if token.start < body or source[token.start:token.end] != "by":
        return None
    return {"declaration": declaration, "declaration_start": start, "proof_start": body,
            "by_start": token.start, "insertion": token.end + 1, "indent": indent,
            "proof_offset_bytes": len(source[start:token.start].encode("utf-8"))}


def safe_term(text):
    if not isinstance(text, str) or not text or len(text) > 4000 or any(c in text for c in "\n\r\x00"):
        return False
    try:
        tokens = lex(text)
    except (ValueError, IndexError):
        return False
    return bool(tokens) and not any(t.kind in {"opaque", "escaped"} or t.text in {
        "`", "sorry", "admit", "by", "set_option", "macro", "elab", "import"} for t in tokens)


def proposals(source, row, site, scan, binding, maximum):
    if (scan.get("schema_version") != 2 or scan.get("status") != "completed"
            or scan.get("root_context_kind") != "original_by_tactic_info"
            or scan.get("target_absent_from_analysis_env") is not True
            or scan.get("opened_proof_lambdas") is not False
            or scan.get("local_instance_context") != "captured_original_root_goal"
            or scan.get("root_start_byte") != binding["harness_root_start_byte"]
            or type(scan.get("root_end_byte")) is not int
            or not binding["harness_root_start_byte"] < scan["root_end_byte"] <= binding["harness_declaration_end_byte"]):
        raise DictionaryDiscoveryError("Census lacks its exact original proof-root context guard")
    analysis = scan.get("analysis", {})
    if analysis.get("status") != "completed" or analysis.get("proving_calls") != 0:
        raise DictionaryDiscoveryError("Dictionary analysis did not complete without proving calls")
    if not isinstance(analysis.get("records"), list) or len(analysis["records"]) > 64:
        raise DictionaryDiscoveryError("Malformed bounded dictionary records")
    result, seen = [], {digest(source)}
    for index, record in enumerate(analysis["records"]):
        trip = record.get("roundtrip", {})
        if (record.get("prefix_safe") is not True or record.get("candidate_heuristic") is not True
                or record.get("shape") != "compound" or trip.get("status") != "passed"
                or trip.get("no_proving_calls") is not True
                or type(record.get("count")) is not int or record["count"] < 4
                or type(record.get("nodes")) is not int or record["nodes"] < 12
                or not safe_term(trip.get("type")) or not safe_term(trip.get("value"))):
            continue
        text = site["indent"] + "letI : " + trip["type"] + " := " + trip["value"] + "\n"
        point = site["insertion"]
        child = source[:point] + text + source[point:]
        child_hash = digest(child)
        if child_hash in seen:
            continue
        native._current_source(row, child)
        seen.add(child_hash)
        result.append({"id": FAMILY + ":" + child_hash[:16], "family": FAMILY,
            "description": "Cache one repeated compound dictionary at the original source proof root",
            "source": child, "source_sha256": child_hash, "parent_sha256": digest(source),
            "site": point, "edits": [{"start": point, "end": point, "old": "", "new": text,
                "offset_unit": "unicode_codepoints_zero_based_end_exclusive"}],
            "dictionary_type": trip["type"], "dictionary_value": trip["value"],
            "census_record_index": index, "observed_dictionary_occurrences": record["count"],
            "dictionary_expression_nodes": record["nodes"], "census_binding": binding,
            "root_availability": "captured whole-by pre-goal lctx/localInstances; nested proof binders not opened",
            "counts_are_bounded_syntactic_uses_not_synthesis_events": True,
            "requires_full_validation": True, "native_full_source_validity": False,
            "validation_required": "complete_source_exact_axioms_and_compatibility"})
        if len(result) == maximum:
            break
    return result


def capture(config, source, row, site, workdir, timeout_seconds):
    project = Path(config["primary"]).resolve()
    prefix = lean_source.exact_source_prefix(row, project)
    insertion, module = lean_source.import_header_end(prefix.text)
    helper = (SUPPORT / "DictionaryCensus.lean.inc").read_text(encoding="utf-8")
    raw = workdir / "dictionary-census.json"
    if raw.exists():
        raise DictionaryDiscoveryError("Census output already exists; stale captures are never reused")
    command = ("#e6_generic_dictionary_census " + json.dumps(str(raw), ensure_ascii=False)
               + f" after {site['proof_offset_bytes']} in\n")
    # Keep command-scoped open/omit/options attached to the target, rather
    # than consuming them with the helper's meta section. The helper needs
    # only Lean imports and belongs before the original namespace/local scope.
    imported = "\npublic meta import Lean\n" if module else "\nimport Lean\n"
    helper_section = imported + "\nmeta section\n" + helper + "\nend\n"
    lead = prefix.text[:insertion] + helper_section + prefix.text[insertion:]
    suffix = command + site["declaration"].rstrip() + "\n"
    harness = lead + suffix
    if not harness.endswith(suffix):
        raise DictionaryDiscoveryError("Harness lost its exact unchanged target suffix")
    root_byte = len((harness[:-len(suffix)] + command).encode()) + site["proof_offset_bytes"]
    binding = {"source_sha256": digest(source), "task_sha256": config.get("task_sha256"),
               "signature_sha256": digest(row["signature"]), "prefix_sha256": prefix.sha256,
               "helper_sha256": digest(helper), "harness_sha256": digest(harness),
               "harness_root_start_byte": root_byte,
               "harness_declaration_end_byte": len(harness.rstrip("\n").encode()),
               "source_root_start_byte": len(source[:site["by_start"]].encode()),
               "source_root_start_codepoint": site["by_start"], "hard_limits": HARD_LIMITS}
    path = workdir / "DictionaryCapture.lean"
    path.write_text(harness, encoding="utf-8", newline="")
    values = RuntimeContext.resolve(Path(config.get("root", workdir)), config).environment(workdir)
    values = {key: os.environ.get(key, value) for key, value in values.items()}
    values["LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE"] = "compile"
    values["LEAN_REFACTOR_LAUNCH_CACHE"] = str(Path(config.get("root", workdir)) / "deterministic/native-launch-cache")
    with scoped_environment({**values, **configure_native_environment(elan_home=config.get("elan_home"))}):
        environment = lean_launch.workspace_guard(project, os.environ)
        binding["environment_sha256"] = digest(json.dumps(environment, sort_keys=True))
        run = native._run(path, project, time.monotonic() + timeout_seconds, workdir / "capture.log")
    if run.get("returncode") != 0 or run.get("timed_out") or not raw.is_file():
        arena.write_json_atomic(workdir / "capture-run.json", {"binding": binding, "run": run})
        raise DictionaryDiscoveryError("Current-source dictionary capture failed; see capture.log")
    scan = json.loads(raw.read_text(encoding="utf-8"))
    binding["raw_census_sha256"] = digest(raw.read_bytes())
    arena.write_json_atomic(workdir / "capture-run.json", {"binding": binding, "run": run})
    return scan, binding


def generate_candidates(*, config, source, signature, workdir, timeout_seconds, max_candidates, family=None):
    if family not in {None, FAMILY, "dictionary_cache"}:
        raise ValueError("Unknown dictionary-cache family")
    if type(max_candidates) is not int or max_candidates < 0:
        raise ValueError("max_candidates must be a nonnegative integer")
    if (type(timeout_seconds) not in (int, float) or not math.isfinite(timeout_seconds) or timeout_seconds <= 0):
        raise ValueError("timeout_seconds must be finite and positive")
    if not isinstance(source, str) or not source.strip() or "\r" in source:
        raise ValueError("Current source must be nonempty LF text")
    if not isinstance(config, dict):
        raise TypeError("config must be an object")
    maximum, timeout = min(max_candidates, MAX_CANDIDATES), min(timeout_seconds, MAX_COMPILE_SECONDS)
    workdir = Path(workdir).resolve()
    if workdir.is_relative_to(Path(config["primary"]).resolve()):
        raise ValueError("Discovery must be outside the cached Lean project")
    workdir.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    receipt = {"schema_version": 1, "source_sha256": digest(source), "status": "running",
               "max_candidates": maximum, "compiler_seconds": timeout, "hard_limits": HARD_LIMITS,
               "model_calls": 0, "proof_search_calls": 0, "scoring_calls": 0, "native_capture_calls": 0}
    try:
        _, row = arena.load_task(Path(config["task"]))
        if signature != row["signature"]:
            raise ValueError("Signature does not match the configured task")
        site = target_site(row, source)
        if site is None or not maximum:
            receipt.update(status="unsupported_shape" if site is None else "completed", candidate_count=0)
            return []
        receipt["native_capture_calls"] = 1
        scan, binding = capture(config, source, row, site, workdir, timeout)
        rows = proposals(source, row, site, scan, binding, maximum)
        receipt.update(status="completed", candidate_count=len(rows), binding=binding,
                       analysis={k: v for k, v in scan["analysis"].items() if k != "records"},
                       candidate_sha256=[r["source_sha256"] for r in rows])
        return rows
    except Exception as error:
        receipt.update(status="failed", error_type=type(error).__name__, error=str(error),
                       partial_candidates_discarded=True, candidate_count=0)
        raise
    finally:
        receipt["wall_seconds"] = time.monotonic() - started
        arena.write_json_atomic(workdir / "dictionary-proposals.json", receipt)
