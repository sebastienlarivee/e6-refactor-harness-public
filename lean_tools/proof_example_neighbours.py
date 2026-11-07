"""Opt-in, bounded lexical neighbours of a retrieved Lean source declaration.

Reads an existing masked source index only. Edges are literal, unresolved body
tokens; this does not build a semantic dependency graph or discover the seed.
"""
from __future__ import annotations

import json
import heapq
import math
import sqlite3
import time
from pathlib import Path
from typing import Any

from lean_tools import proof_example_search as source
from lean_tools.lean_source import lean_code_mask

REFERENCE_SCAN_LIMIT = 128
QUERY_TERM_LIMIT = 64
EVIDENCE_LIMIT = 32
KEYWORDS = set("by using with fun at in from only match if then else where let have show this exact apply simpa simp cases induction obtain rcases intro intros rintro constructor refine calc do return true false forall exists case generalizing".split()) | set(source.TACTICS)
WEIGHTS = {"name": 3.0, "statement": 1.5, "body": 1.0, "comment": 1.25}


def _bounds(**values: tuple[int, int, int]) -> None:
    for name, (value, low, high) in values.items():
        if type(value) is not int or not low <= value <= high:
            raise source.ExampleSearchError(f"{name} must be an integer in {low}..{high}")


def _intent_scores(db: sqlite3.Connection, query: str, count: int) -> tuple[dict[int, float], list[tuple[str, str]]]:
    scores: dict[int, float] = {}
    wanted = []
    for term in sorted(source.terms(query))[:QUERY_TERM_LIMIT]:
        for field, weight in WEIGHTS.items():
            frequency = db.execute("SELECT COUNT(*) FROM terms WHERE term=? AND field=?", (term, field)).fetchone()[0]
            if not frequency:
                continue
            wanted.append((term, field))
            score = weight * math.log(1 + count / (1 + frequency))
            for (example_id,) in db.execute("SELECT example_id FROM terms WHERE term=? AND field=?", (term, field)):
                scores[example_id] = scores.get(example_id, 0.0) + score
    return scores, wanted


def _intent_evidence(db: sqlite3.Connection, wanted: list[tuple[str, str]], ids: list[int]) -> tuple[dict, dict]:
    evidence = {item: [] for item in ids}
    counts = {item: 0 for item in ids}
    if ids:
        placeholders = ",".join("?" for _ in ids)
        for term, field in wanted:
            for (example_id,) in db.execute(
                    f"SELECT example_id FROM terms WHERE term=? AND field=? AND example_id IN ({placeholders})",
                    [term, field, *ids]):
                counts[example_id] += 1
                if len(evidence[example_id]) < EVIDENCE_LIMIT:
                    evidence[example_id].append({"term": term, "field": field})
    return evidence, counts


def _location(record: dict[str, Any]) -> dict[str, Any]:
    return {key: record.get(key) for key in ("name", "module", "path", "line_start", "line_end", "offset_start", "offset_end",
            "origin", "usage", "callable_verified", "availability", "parse_quality")}


def _snippet(record: dict[str, Any], max_chars: int) -> tuple[dict[str, Any] | None, int]:
    """Never cut a statement or binder context to satisfy a source budget."""
    statement = record["statement"]
    context = record.get("context", [])
    if len(statement) + 4 > max_chars or sum(len(item["source"]) for item in context) > max_chars:
        return None, 0
    snippet = record["source"][:max_chars]
    comments = record.get("leading_comments", "")[:min(2000, max_chars)]
    result = _location(record) | {"kind": record["kind"], "statement": statement, "context": context,
             "source": snippet, "source_complete": len(snippet) == len(record["source"]),
             "source_sha256": source.sha256(record["source"]),
             "snippet_line_start": record["line_start"],
             "snippet_line_end": record["line_start"] + snippet.count("\n"),
             "leading_comments": comments,
             "leading_comments_complete": len(comments) == len(record.get("leading_comments", "")),
             "comment_line_start": record.get("comment_line_start"), "comment_line_end": record.get("comment_line_end"),
             "comment_offset_start": record.get("comment_offset_start"), "comment_offset_end": record.get("comment_offset_end"),
             "tactic_shapes": record.get("tactic_shapes", [])}
    cost = len(snippet) + len(statement) + len(comments) + sum(len(item["source"]) for item in context)
    return result, cost


def neighbours(path: Path, seed_name: str, query: str = "", *, max_references: int = 8,
               per_reference: int = 8, candidate_limit: int = 100, limit: int = 5,
               max_source_chars: int = 8000, max_total_source_chars: int = 64000,
               expected_identity: dict[str, Any] | None = None) -> dict[str, Any]:
    """Return original-intent and rarity views with a shared bounded source set.

    Full/qualified/short seed-name uses are a control alongside shared references.
    At most 128 plausible seed tokens receive frequency lookups, and at most
    max_references are expanded. Per-channel admission uses the original intent;
    candidate_limit bounds the union. Source snippets are round-robin selected
    from rarity, intent, direct, shared views under global result/source budgets.
    There is no positive-score, tactic-only, or semantic-availability filter.
    """
    _bounds(max_references=(max_references, 1, 16), per_reference=(per_reference, 1, 12),
            candidate_limit=(candidate_limit, 1, 100), limit=(limit, 1, 12),
            max_source_chars=(max_source_chars, 256, 32000),
            max_total_source_chars=(max_total_source_chars, 256, 256000))
    if not isinstance(seed_name, str) or not seed_name or len(seed_name) > 512:
        raise source.ExampleSearchError("seed_name must be nonempty and at most 512 characters")
    if not isinstance(query, str) or len(query) > 16000:
        raise source.ExampleSearchError("query must be text of at most 16000 characters")
    started = time.perf_counter()
    try:
        with sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True) as db:
            identity = json.loads(db.execute("SELECT value FROM metadata WHERE key='identity'").fetchone()[0])
            summary = json.loads(db.execute("SELECT value FROM metadata WHERE key='summary'").fetchone()[0])
            binding = source.binding(identity)
            if expected_identity is not None and identity != expected_identity and binding != expected_identity:
                raise source.ExampleSearchError("example-neighbour index does not match expected task/environment/source mask")
            result: dict[str, Any] = {"identity": binding, "seed_name": seed_name, "query": query,
                "edge_precision": "literal unresolved body tokens; suffixes, locals, and field notation are ambiguous",
                "algorithm": "bounded-lexical-source-neighbours-v1", "examples": [], "candidates": [], "views": {},
                "bounds": {"max_references": max_references, "per_reference": per_reference,
                    "candidate_limit": candidate_limit, "limit": limit, "max_source_chars": max_source_chars,
                    "max_total_source_chars": max_total_source_chars, "reference_scan_limit": REFERENCE_SCAN_LIMIT,
                    "query_term_limit": QUERY_TERM_LIMIT, "intent_evidence_limit": EVIDENCE_LIMIT,
                    "expansion_rounds": 1}}
            # Two matches suffice to establish ambiguity; never silently choose.
            found = db.execute("SELECT id,record FROM examples WHERE json_extract(record,'$.name')=? LIMIT 2", (seed_name,)).fetchall()
            if len(found) != 1:
                result.update(status="seed_missing" if not found else "seed_ambiguous",
                    seed_lookup={"match_count_lower_bound": len(found), "exact_name": True,
                                 "matches": [_location(json.loads(raw)) for _, raw in found],
                                 "count_may_be_larger": len(found) == 2},
                    seconds=round(time.perf_counter() - started, 6))
                return result
            seed_id, raw = found[0]
            seed = json.loads(raw)
            seed_snippet, seed_cost = _snippet(seed, max_source_chars)
            if seed_cost > max_total_source_chars:
                seed_snippet, seed_cost = None, 0
            result["seed"] = seed_snippet or (_location(seed) | {"source_omitted": "complete statement/context exceeds source budget"})
            scores, wanted = _intent_scores(db, query, summary["examples"])
            refs, rejected, scanned, eligible_count = [], 0, 0, 0
            for symbol in seed.get("lexical_references", []):
                if (symbol in KEYWORDS or len(symbol) < 3 or ("." not in symbol and "'" in symbol)
                        or ("." not in symbol and "_" not in symbol and not symbol[0].isupper())):
                    rejected += 1
                    continue
                eligible_count += 1
                if scanned >= REFERENCE_SCAN_LIMIT:
                    continue
                scanned += 1
                count = db.execute("SELECT COUNT(*) FROM terms WHERE term=? AND field='symbol'", (symbol,)).fetchone()[0]
                if count >= 2:
                    refs.append({"reference": symbol, "document_frequency": count})
            refs.sort(key=lambda item: (item["document_frequency"], item["reference"]))
            refs = refs[:max_references]
            for rank, item in enumerate(refs, 1):
                item["rarity_rank"] = rank
            parts = seed_name.split(".")
            forms = list(dict.fromkeys([seed_name, ".".join(parts[-2:]), parts[-1]]))
            channels = [{"kind": "shared_dependency", **item, "ambiguity": "unresolved literal seed-body token"} for item in refs]
            channels += [{"kind": "direct_seed_use", "reference": form,
                          "ambiguity": "literal full name" if form == seed_name else "unresolved suffix may name unrelated declarations"}
                         for form in forms]
            admitted: dict[int, list[dict]] = {}
            # Round-robin admission preserves rare channels when total < branch sum.
            branch_ids = []
            for channel in channels:
                channel["total_literal_users"] = db.execute(
                    "SELECT COUNT(*) FROM terms WHERE term=? AND field='symbol'", (channel["reference"],)).fetchone()[0]
                users = (row[0] for row in db.execute("SELECT example_id FROM terms WHERE term=? AND field='symbol'",
                         (channel["reference"],)) if row[0] != seed_id)
                ordered = heapq.nsmallest(per_reference, users, key=lambda item: (-scores.get(item, 0.0), item))
                channel["ranked_candidate_count"] = len(ordered)
                branch_ids.append(ordered)
            for offset in range(per_reference):
                for channel, ids in zip(channels, branch_ids):
                    if offset >= len(ids):
                        continue
                    example_id = ids[offset]
                    if example_id not in admitted and len(admitted) >= candidate_limit:
                        continue
                    edge = {"kind": channel["kind"], "reference": channel["reference"],
                            "ambiguity": channel["ambiguity"], "rarity_rank": channel.get("rarity_rank"),
                            "document_frequency": channel["total_literal_users"]}
                    admitted.setdefault(example_id, []).append(edge)
            evidence, evidence_counts = _intent_evidence(db, wanted, list(admitted))
            records, candidates = {}, []
            for example_id, edges in admitted.items():
                rec = json.loads(db.execute("SELECT record FROM examples WHERE id=?", (example_id,)).fetchone()[0])
                records[example_id] = rec
                score = scores.get(example_id, 0.0) / (1 + .12 * math.log1p(len(rec["body"]) / 400))
                if rec["module"].split(".")[0] in {"Lean", "Lake", "Qq", "Aesop"}:
                    score *= .65
                for edge in edges:
                    edge["path"] = [seed_name, edge["reference"], rec["name"]]
                candidates.append(_location(rec) | {"id": example_id, "intent_score": round(score, 6),
                    "intent_matches": evidence[example_id], "intent_match_count": evidence_counts[example_id],
                    "intent_matches_omitted": max(0, evidence_counts[example_id] - EVIDENCE_LIMIT), "paths": edges,
                    "tactic_shapes": rec.get("tactic_shapes", []),
                    "has_angle_bracket_syntax": "⟨" in lean_code_mask(rec["body"])})
            candidates.sort(key=lambda item: (-item["intent_score"], item["name"], item["id"]))
            direct = [item for item in candidates if any(edge["kind"] == "direct_seed_use" for edge in item["paths"])]
            shared = [item for item in candidates if any(edge["kind"] == "shared_dependency" for edge in item["paths"])]
            rarest = [item for item in shared if any(edge["rarity_rank"] == 1 for edge in item["paths"])]
            views = {"original_intent": candidates, "rarest_dependency": rarest, "direct_seed_uses": direct,
                     "shared_dependencies": shared}
            result["views"] = {name: [item["id"] for item in view[:limit]] for name, view in views.items()}
            chosen, omitted, spent = [], [], seed_cost
            ordered_views = (rarest, candidates, direct, shared)
            seen: set[int] = set()
            for offset in range(limit):
                for view in ordered_views:
                    if offset >= len(view) or len(chosen) >= limit:
                        continue
                    candidate = view[offset]
                    example_id = candidate["id"]
                    if example_id in seen:
                        continue
                    seen.add(example_id)
                    snippet, cost = _snippet(records[example_id], max_source_chars)
                    if snippet is None or spent + cost > max_total_source_chars:
                        omitted.append({"id": example_id, "reason": "complete statement/context or aggregate source budget"})
                        continue
                    chosen.append(snippet | {"id": example_id})
                    spent += cost
            result.update(status="ok" if candidates else "empty", seed_lookup={"exact_name": True, "match_count_lower_bound": 1},
                selected_references=refs, reference_scan={"eligible": eligible_count, "scanned": scanned,
                    "truncated": eligible_count > scanned, "heuristically_rejected": rejected},
                channels=channels, candidates=candidates, examples=chosen, omitted_sources=omitted,
                counts={"candidate_chunks": len(candidates), "result_chunks": len(chosen), "source_characters": spent},
                ordering="original-intent IDF with length/meta normalization; rarity is a separate preserved view",
                seconds=round(time.perf_counter() - started, 6))
            return result
    except (sqlite3.Error, OSError, ValueError, KeyError, TypeError) as error:
        raise source.ExampleSearchError(f"example-neighbour index unavailable: {error}") from error
