"""Frozen, capsule-scoped native proof suggestions and source-example discovery.

All entrypoints observe a SHA-bound candidate. Example queries only read a host
prepared, digest-pinned exact-prefix index; requests cannot select an index,
source root, search engine, provider or retrieval mode.
"""
from __future__ import annotations

import hashlib
import json
import re
import sqlite3
import time
from pathlib import Path
from typing import Any, Mapping

from lean_tools.feedback_workflow import bind_feedback_scoring_policy
from lean_tools import arena_workflow as arena
from lean_tools import lean_goal_state, lean_source
from lean_tools import proof_example_search as examples
from lean_tools import proof_example_neighbours as neighbours
from lean_tools import structural_search

DEFAULT_LIMIT = 3
MAX_LIMIT = 5
POOL_LIMIT = 12
MAX_SOURCE_CHARS = 4000
MAX_TOTAL_SOURCE_CHARS = 12000
MAX_NATIVE_HEARTBEATS = 200000
MAX_NATIVE_SECONDS = 30
MAX_NATIVE_OUTPUT_CHARS = 32000

_COMMON = {
    "candidate": {"type": "string", "description": "A .lean filename inside this capsule."},
    "expected_sha256": {"type": "string", "pattern": "^[0-9a-f]{64}$"},
    "limit": {"type": "integer", "minimum": 1, "maximum": MAX_LIMIT, "default": DEFAULT_LIMIT},
}
_QUERY = {"type": "string", "maxLength": 16000}
SUGGEST_TOOL = {
    "name": "suggest_proof",
    "description": "Read-only, bounded native Lean library search on one actual pre-tactic goal in the current SHA-bound candidate and unchanged exact prefix. Supply a goal_id returned by edit_check, a one-based cursor (optional zero-based index), or omit the selector for the first tactic in the editable body. Historical goals may already be discharged. Returns proof terms and residual obligations; paste a returned term into the proof and validate with edit_check. This query never edits the candidate or creates a checkpoint. Default 3, maximum 5 suggestions; at most 200000 native heartbeats and 30 seconds.",
    "inputSchema": {"type": "object", "properties": {
        **_COMMON,
        "goal": {"type": "object", "properties": {
            "line": {"type": "integer", "minimum": 1},
            "column": {"type": "integer", "minimum": 1},
            "index": {"type": "integer", "minimum": 0, "maximum": 1000}},
            "required": ["line"], "additionalProperties": False},
        "goal_id": {"type": "string", "pattern": "^goal-[0-9a-f]{64}$"},
        "native_heartbeats": {"type": "integer", "minimum": 1, "maximum": MAX_NATIVE_HEARTBEATS, "default": MAX_NATIVE_HEARTBEATS},
        "timeout_seconds": {"type": "integer", "minimum": 1, "maximum": MAX_NATIVE_SECONDS, "default": MAX_NATIVE_SECONDS}},
        "required": ["expected_sha256"], "additionalProperties": False},
}
SEARCH_TOOL = {
    "name": "search_examples",
    "description": "Find proof-source examples in the frozen exact-prefix/import-closure corpus using lexical statement, body, comment, symbol and tactic evidence. Supply useful query text, literal used_names, or tactic_shapes; all requested symbols/tactics are mandatory lexical filters. Source examples are inspiration only: callable_verified=false, including private or unavailable names. No Lean availability check is performed. Current candidate SHA256 required. Host-configured JEV may rank the same bounded source pool. Default 3, maximum 5 results, at most 4000 source characters each and 12000 aggregate source/statement/context/comment characters; complete binders/context are preserved or the example is omitted.",
    "inputSchema": {"type": "object", "properties": {
        **_COMMON, "query": _QUERY,
        "used_names": {"type": "array", "maxItems": 16, "items": {"type": "string", "minLength": 1, "maxLength": 512}},
        "tactic_shapes": {"type": "array", "maxItems": 16, "items": {"type": "string", "minLength": 1, "maxLength": 128}}},
        "required": ["expected_sha256"], "additionalProperties": False},
}
NEIGHBOURS_TOOL = {
    "name": "example_neighbours",
    "description": "Find one bounded round of lexical neighbours of an exact seed_name from search_examples in the same frozen source corpus. Shared body symbols and direct seed-name uses are unresolved lexical edges, not a semantic dependency graph. Optional query retains the original proof intent. Current candidate SHA256 required. Source examples are inspiration only (callable_verified=false). Host-configured JEV may rank the same bounded pool. Default 3, maximum 5 results; the same 4000-per-source and 12000 aggregate source budgets apply. No caller-selected index, roots, provider or mode.",
    "inputSchema": {"type": "object", "properties": {
        **_COMMON, "query": _QUERY,
        "seed_name": {"type": "string", "minLength": 1, "maxLength": 512}},
        "required": ["expected_sha256", "seed_name"], "additionalProperties": False},
}
TOOLS = [SUGGEST_TOOL, SEARCH_TOOL, NEIGHBOURS_TOOL]
_TOOLS = {tool["name"]: tool for tool in TOOLS}


def validate_settings(settings: Mapping[str, Any]) -> None:
    """Validate host configuration without opening or building an index."""
    enabled = settings.get("search_extensions", False)
    if type(enabled) is not bool:
        raise ValueError("search_extensions must be a boolean")
    keys = ("examples_index", "examples_index_sha256", "examples_index_identity")
    present = any(settings.get(key) is not None for key in keys)
    if present and not enabled:
        raise ValueError("prepared examples index settings require search_extensions=true")
    if not enabled:
        return
    path, digest, identity = (settings.get(key) for key in keys)
    if (not isinstance(path, str) or not path or not Path(path).is_absolute()
            or not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest)
            or not isinstance(identity, dict) or not identity):
        raise ValueError("search_extensions requires host-prepared examples_index (absolute path), examples_index_sha256 and examples_index_identity; prepare the exact-prefix index on the host")
    if identity.get("policy") != examples.POLICY or identity.get("inspiration_modules", []):
        raise ValueError("examples_index_identity must use the exact-prefix/import-closure policy without extra inspiration modules")


def _integer(name: str, value: Any, high: int, low: int = 1) -> int:
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f"{name} must be an integer in {low}..{high}")
    return value


def _validate(name: str, request: Any) -> tuple[dict[str, Any], int]:
    if not isinstance(request, dict):
        raise ValueError("request must be an object")
    unsupported = set(request) - set(_TOOLS[name]["inputSchema"]["properties"])
    if unsupported:
        raise ValueError("unsupported search field(s): " + ", ".join(sorted(unsupported)) + "; the host freezes the index, engine, provider and mode")
    if not isinstance(request.get("expected_sha256"), str) or not re.fullmatch(r"[0-9a-f]{64}", request["expected_sha256"]):
        raise ValueError("expected_sha256 is required and must be 64 lowercase hexadecimal characters; use the current candidate hash")
    limit = _integer("limit", request.get("limit", DEFAULT_LIMIT), MAX_LIMIT)
    if "query" in request and (not isinstance(request["query"], str) or len(request["query"]) > 16000):
        raise ValueError("query must be text with at most 16000 characters")
    if name == "suggest_proof":
        _integer("native_heartbeats", request.get("native_heartbeats", MAX_NATIVE_HEARTBEATS), MAX_NATIVE_HEARTBEATS)
        _integer("timeout_seconds", request.get("timeout_seconds", MAX_NATIVE_SECONDS), MAX_NATIVE_SECONDS)
        if "goal" in request:
            goal = request["goal"]
            if not isinstance(goal, dict) or "line" not in goal or set(goal) - {"line", "column", "index"}:
                raise ValueError("goal must contain a one-based line, optional column and zero-based index")
            for key, value in goal.items():
                _integer("goal " + key, value, 1000 if key == "index" else 10000000, 0 if key == "index" else 1)
        if "goal_id" in request and ("goal" in request or not isinstance(request["goal_id"], str)
                or not re.fullmatch(r"goal-[0-9a-f]{64}", request["goal_id"])):
            raise ValueError("goal_id must be a snapshot-bound handle from edit_check; supply either goal_id or goal")
    elif name == "search_examples":
        for key, bound in (("used_names", 512), ("tactic_shapes", 128)):
            if key in request and (not isinstance(request[key], list) or len(request[key]) > 16
                    or any(not isinstance(value, str) or not value.strip() or len(value) > bound for value in request[key])):
                raise ValueError(f"{key} must contain at most 16 nonempty strings of at most {bound} characters")
        if not examples.terms(request.get("query", "")) and not request.get("used_names") and not request.get("tactic_shapes"):
            raise ValueError("supply useful query text, a literal used_name, or a tactic_shape")
    elif not isinstance(request.get("seed_name"), str) or not request["seed_name"].strip() or len(request["seed_name"]) > 512:
        raise ValueError("seed_name is required: use one exact declaration name returned by search_examples (at most 512 characters)")
    return request, limit


def _fingerprint(feedback: Any) -> str:
    registry = feedback.settings.get("fingerprint_registry")
    if not isinstance(registry, str) or not registry:
        raise ValueError("search_extensions requires the host-prepared fingerprint_registry; recreate this capsule on the host")
    return arena.measurement_environment_fingerprint(feedback.row, feedback.project, registry_path=Path(registry))


def _index(feedback: Any, prefix: lean_source.SourcePrefix, fingerprint: str) -> tuple[Path, dict[str, Any]]:
    validate_settings(feedback.settings)
    path = Path(feedback.settings["examples_index"])
    digest = feedback.settings["examples_index_sha256"]
    identity = feedback.settings["examples_index_identity"]
    expected = {"format_version": examples.FORMAT_VERSION, "policy": examples.POLICY,
                "target": feedback.row["name"], "task_signature_sha256": examples.sha256(feedback.row["signature"]),
                "prefix_sha256": prefix.sha256, "environment_fingerprint": fingerprint}
    if any(identity.get(key) != value for key, value in expected.items()):
        raise examples.ExampleSearchError("prepared examples index belongs to a different task, exact prefix or Lean environment; rebuild it on the host")
    if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        raise examples.ExampleSearchError("prepared examples index SHA256 mismatch; rebuild it on the host")
    metadata = examples.inspect_index(path)
    if examples.binding(metadata["identity"]) != identity:
        raise examples.ExampleSearchError("prepared examples index identity mismatch; rebuild it on the host")
    return path, identity


def _raw_records(path: Path, records: list[dict[str, Any]]) -> list[tuple[int, dict[str, Any], dict[str, Any]]]:
    """Recover complete canonical rows for ranking, never from request paths."""
    result = []
    with sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True) as db:
        for record in records[:POOL_LIMIT]:
            if "id" in record:
                rows = db.execute("SELECT id,record FROM examples WHERE id=?", (record["id"],)).fetchall()
            else:
                rows = db.execute("SELECT id,record FROM examples WHERE json_extract(record,'$.name')=? AND json_extract(record,'$.path')=? AND json_extract(record,'$.offset_start')=? LIMIT 2",
                                  (record["name"], record["path"], record["offset_start"])).fetchall()
            if len(rows) != 1:
                raise examples.ExampleSearchError("retrieved example does not identify one exact frozen index row")
            identifier, raw = rows[0]
            raw = json.loads(raw)
            if any(raw.get(key) != record.get(key) for key in ("name", "path", "offset_start", "offset_end")):
                raise examples.ExampleSearchError("retrieved example provenance does not match the frozen index row")
            result.append((identifier, raw, record))
    return result


def _rank(feedback: Any, request: dict[str, Any], rows: list[tuple[int, dict[str, Any], dict[str, Any]]],
          result: dict[str, Any], identity: dict[str, Any]) -> list[tuple[int, dict[str, Any], dict[str, Any]]]:
    from lean_tools import rerank_service_client as transport
    options, automatic = transport.resolve_options()
    if not rows or not automatic or options.get("ranker") != "jev":
        result["reranking"] = {"status": "baseline", "method": "frozen_lexical_pool_order", "provider_called": False}
        return rows
    from lean_tools import example_rerank
    candidates = [example_rerank.index_candidate(identifier, raw) for identifier, raw, _ in rows]
    context = {"task_signature": feedback.row["signature"], "source_sha256": result["source_sha256"],
               "goal": feedback.row["signature"], "hypotheses": [],
               "search_intent": request.get("query", ""), "query": request.get("query", "")}
    binding = example_rerank.make_binding(candidates, context, task_id=feedback.row["name"],
        prefix_sha256=identity["prefix_sha256"], environment_fingerprint=identity["environment_fingerprint"],
        source_sha256=result["source_sha256"], examples_index_sha256=feedback.settings["examples_index_sha256"],
        examples_index_identity=identity)
    ranked = example_rerank.rerank_examples(candidates, context, binding=binding, options=options, automatic=True)
    # The transport validates an exact permutation; retain that invariant here
    # before mapping provider order back to bounded source display records.
    ordered = ranked.get("matches", [])
    if (not isinstance(ordered, list) or len(ordered) != len(candidates)
            or sorted(transport.canonical_json(item) for item in ordered) != sorted(transport.canonical_json(item) for item in candidates)):
        raise ValueError("example reranker changed the exact frozen candidate pool")
    by_id = {row[0]: row for row in rows}
    result["reranking"] = transport.compact_result(ranked, candidates, MAX_LIMIT)
    return [by_id[item["example_id"]] for item in ordered]


def _bounded_sources(rows: list[tuple[int, dict[str, Any], dict[str, Any]]], limit: int) -> tuple[list[dict[str, Any]], list[dict[str, Any]], int]:
    selected, omitted, spent = [], [], 0
    for identifier, raw, evidence in rows:
        if len(selected) >= limit:
            break
        snippet, cost = neighbours._snippet(raw, MAX_SOURCE_CHARS)
        if snippet is None or spent + cost > MAX_TOTAL_SOURCE_CHARS:
            omitted.append({"example_id": identifier, "name": raw["name"], "reason": "complete statement/context or aggregate source budget"})
            continue
        snippet.update(example_id=identifier, callable_verified=False, usage="inspiration_only",
                       availability_note="Source inspiration only; validate premise names in the unchanged exact Lean prefix before using them.")
        for key in ("score", "intent_score", "intent_match_count", "intent_matches_omitted"):
            if key in evidence:
                snippet[key] = evidence[key]
        for key in ("matches", "intent_matches", "paths"):
            if key in evidence:
                snippet[key] = evidence[key][:32]
        selected.append(snippet)
        spent += cost
    return selected, omitted, spent


def _finish(feedback: Any, result: dict[str, Any], started: float) -> dict[str, Any]:
    result["seconds"] = round(time.perf_counter() - started, 6)
    diagnostics = result.get("diagnostics", [])
    if not isinstance(diagnostics, list):
        diagnostics = []
    result["diagnostics"] = [{"code": str(item.get("code", "search_diagnostic"))[:100],
                              "message": str(item.get("message", ""))[:600]}
                             for item in diagnostics[:3] if isinstance(item, dict)]
    if len(diagnostics) > 3:
        result["diagnostics_omitted"] = len(diagnostics) - 3
    arena.record_event(result["tool"], result)
    return result


@bind_feedback_scoring_policy
def call(feedback: Any, name: str, request: Any) -> dict[str, Any]:
    """Dispatch an enabled read-only query; errors carry concrete retry advice."""
    if name not in _TOOLS:
        raise ValueError("unknown search tool")
    started = time.perf_counter()
    result: dict[str, Any] = {"schema_version": 1, "tool": name, "authoritative": False,
                              "checkpoint": None, "matches": [], "diagnostics": []}
    try:
        if feedback.settings.get("search_extensions") is not True:
            raise ValueError("search_extensions is disabled in this capsule; use only tools in tools/list")
        request, limit = _validate(name, request)
        candidate = feedback.candidate_path(request)
        raw = candidate.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        result.update(candidate=str(candidate), source_sha256=digest)
        if request["expected_sha256"] != digest:
            return _finish(feedback, {**result, "status": "source_conflict", "diagnostics": [{"code": "source_conflict", "message": "expected_sha256 does not match the current candidate; read its current hash and retry"}]}, started)
        prefix = lean_source.exact_source_prefix(feedback.row, feedback.project)
        fingerprint = _fingerprint(feedback)
        result.update(environment_fingerprint=fingerprint,
                      prefix={"sha256": prefix.sha256, "kind": prefix.kind, "target_visible": False, "later_declarations_visible": False})
        if name == "suggest_proof":
            goal = request.get("goal")
            if "goal_id" in request:
                handle = lean_goal_state.resolve_goal_handle(feedback, candidate, digest, request["goal_id"], prefix.sha256)
                if handle.get("environment_fingerprint") not in (None, fingerprint):
                    raise lean_goal_state.GoalStateError("goal_id belongs to a different Lean environment; observe goals again with edit_check")
                goal = handle["goal"]
            goal_index = goal.get("index", 0) if goal else 0
            selector = {key: value for key, value in goal.items() if key != "index"} if goal else None
            observed = structural_search.search_candidate(feedback.row, feedback.project, candidate, digest,
                goal=selector, goal_index=goal_index, engine="native", limit=limit,
                native_heartbeats=request.get("native_heartbeats", MAX_NATIVE_HEARTBEATS),
                timeout=min(feedback.timeout, request.get("timeout_seconds", MAX_NATIVE_SECONDS)),
                fingerprint_registry=Path(feedback.settings["fingerprint_registry"]))
            # Lean records are observations rather than a free-form transport.
            # A source-logged marker cannot add arbitrary fields to our reply.
            fields = {"status", "matches", "diagnostics", "backend", "timed_out", "method", "goal", "hypotheses",
                      "suggestions_found", "closed", "native_normalize_goal", "native_heartbeats",
                      "probe_ms", "elaboration_ms", "goal_count", "selected_goal_index",
                      "tactic_start_byte", "tactic_end_byte", "suggested_tactics", "reason"}
            result.update({key: value for key, value in observed.items() if key in fields})
            result.update(engine="native", search_limits={"limit": limit,
                "native_heartbeats": request.get("native_heartbeats", MAX_NATIVE_HEARTBEATS),
                "timeout_seconds": min(feedback.timeout, request.get("timeout_seconds", MAX_NATIVE_SECONDS))},
                goal_selector={**(selector or {"selection": "first_proof_body_tactic_goals_before"}), "index": goal_index})
            if result.get("status") not in {"ok", "empty", "no_goal", "unavailable", "source_conflict", "invalid_request",
                                             "search_exhausted", "native_search_failed"}:
                raise ValueError("native search returned an unsupported status")
            for key in ("backend", "method"):
                if key in result:
                    result[key] = str(result[key])[:100]
            for key in ("timed_out", "closed", "native_normalize_goal"):
                if key in result and type(result[key]) is not bool:
                    raise ValueError("native search returned a malformed " + key)
            for key in ("suggestions_found", "native_heartbeats", "probe_ms", "elaboration_ms", "goal_count",
                        "selected_goal_index", "tactic_start_byte", "tactic_end_byte"):
                if key in result and (type(result[key]) is not int or not 0 <= result[key] < 10 ** 15):
                    raise ValueError("native search returned a malformed " + key)
            if "reason" in result:
                result["reason"] = str(result["reason"])[:600]
            if "suggested_tactics" in result:
                suggestions = result["suggested_tactics"]
                result["suggested_tactics"] = ([{key: value for key, value in item.items()
                    if key in {"tactic_start_byte", "tactic_end_byte", "goal_count"} and type(value) is int}
                    for item in suggestions[:12] if isinstance(item, dict)] if isinstance(suggestions, list) else [])
            matches = result.get("matches")
            if not isinstance(matches, list) or len(matches) > limit or any(not isinstance(item, dict) for item in matches):
                raise ValueError("native search violated the bounded suggestion contract; discard this result and retry")
            kept, spent, omitted = [], 0, 0
            for match in matches:
                cost = len(json.dumps(match, ensure_ascii=False))
                if spent + cost <= MAX_NATIVE_OUTPUT_CHARS:
                    kept.append(match)
                    spent += cost
                else:
                    omitted += 1
            result.update(matches=kept, returned_matches=len(kept), oversized_matches_omitted=omitted)
            hypotheses = result.get("hypotheses", [])
            if (not isinstance(result.get("goal", ""), str) or not isinstance(hypotheses, list)
                    or any(not isinstance(item, str) for item in hypotheses)):
                raise ValueError("native search returned malformed goal context")
            if len(json.dumps(hypotheses, ensure_ascii=False)) + len(result.get("goal", "")) > MAX_NATIVE_OUTPUT_CHARS:
                result.pop("hypotheses", None)
                result.pop("goal", None)
                result["context_omitted"] = "native goal/hypotheses exceed the display budget; inspect the candidate with edit_check"
        else:
            path, identity = _index(feedback, prefix, fingerprint)
            if name == "search_examples":
                found = examples.search(path, request.get("query", ""), used_names=request.get("used_names", []),
                    tactic_shapes=request.get("tactic_shapes", []), limit=POOL_LIMIT,
                    max_source_chars=MAX_SOURCE_CHARS, expected_identity=identity)
                pool = found["matches"]
                result.update(status=found["status"], total_hits=found["total_hits"], ranking=found["ranking"])
            else:
                found = neighbours.neighbours(path, request["seed_name"], request.get("query", ""),
                    candidate_limit=POOL_LIMIT, limit=POOL_LIMIT, max_source_chars=MAX_SOURCE_CHARS,
                    max_total_source_chars=MAX_TOTAL_SOURCE_CHARS, expected_identity=identity)
                pool = found["candidates"]
                result.update(status=found["status"], seed_name=request["seed_name"],
                              edge_precision=found["edge_precision"], algorithm=found["algorithm"],
                              seed_lookup=found["seed_lookup"], total_hits=len(pool))
                if "selected_references" in found:
                    result["selected_references"] = found["selected_references"]
            rows = _raw_records(path, pool)
            rows = _rank(feedback, request, rows, result, identity)
            selected, omitted, spent = _bounded_sources(rows, limit)
            result.update(matches=selected, identity=identity, omitted_sources=omitted,
                          usage="inspiration_only", callable_verified=False,
                          bounds={"limit": limit, "candidate_limit": POOL_LIMIT,
                                  "max_source_chars": MAX_SOURCE_CHARS, "max_total_source_chars": MAX_TOTAL_SOURCE_CHARS},
                          counts={"candidate_chunks": len(pool), "result_chunks": len(selected), "source_characters": spent})
            if hashlib.sha256(path.read_bytes()).hexdigest() != feedback.settings["examples_index_sha256"]:
                raise examples.ExampleSearchError("prepared examples index changed during discovery; discard these examples and recreate the host capsule")
        if candidate.read_bytes() != raw or lean_source.exact_source_prefix(feedback.row, feedback.project).sha256 != prefix.sha256:
            result.update(status="source_conflict", matches=[], diagnostics=[{"code": "source_changed_during_query", "message": "candidate or exact prefix changed during discovery; discard this advice and retry with the current hash"}])
        return _finish(feedback, result, started)
    except (ValueError, OSError, KeyError, TypeError, sqlite3.Error, arena.WorkflowError,
            examples.ExampleSearchError, lean_goal_state.GoalStateError) as error:
        result = {key: result[key] for key in ("schema_version", "tool", "authoritative", "checkpoint",
                  "candidate", "source_sha256", "environment_fingerprint", "prefix") if key in result}
        result.update(status="invalid_request", matches=[], diagnostics=[{"code": "invalid_request", "message": str(error)}])
        return _finish(feedback, result, started)
