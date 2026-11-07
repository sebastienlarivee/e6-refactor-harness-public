"""Host-private, strict-prefix theorem symbol index (never proof or goal data).

The immutable SQLite file contains names and constants used by theorem types.
It is built once from the exact original prefix, independent of any candidate.
"""
from __future__ import annotations

import hashlib
import heapq
import math
import json
import os
import re
import sqlite3
import time
from array import array
from functools import lru_cache
from pathlib import Path
from typing import Any, Callable

FORMAT_VERSION = 1
FAILURE_BACKOFF_SECONDS = 600
BUILD_TIMEOUT_SECONDS = 180
INDEX_MARKER = "__LRH_SIGNATURE_INDEX_V1__"

# Explicit named patterns bind even when the strict prefix opens constructors or
# `[match_pattern]` declarations with these names.
_BUILD = r'''
elab "__COMMAND__" : command => do
  let started ← IO.monoMsNow
  let env ← Lean.getEnv
  let handle ← IO.FS.Handle.mk __PATH__ IO.FS.Mode.write
  let mut examined := 0
  let mut theorems := 0
  for (name@_, info@_) in env.constants.toList do
    examined := examined + 1
    if Lean.wasOriginallyTheorem env name && !name.isInternal && !Lean.isPrivateName name && name.toString != __TARGET__ then
      let symbols := info.type.getUsedConstants |>.map Lean.Name.toString
      handle.putStrLn (Lean.Json.arr #[Lean.toJson name.toString, Lean.toJson symbols]).compress
      theorems := theorems + 1
  handle.flush
  let finished ← IO.monoMsNow
  Lean.logInfo (Lean.toMessageData ("__MARKER__" ++ (Lean.Json.mkObj [("status", Lean.toJson "ok"), ("examined_constants", Lean.toJson examined), ("visible_theorems", Lean.toJson theorems), ("scan_ms", Lean.toJson (finished - started))]).compress))
__COMMAND__
'''


class IndexUnavailable(RuntimeError):
    pass


def identity(prefix_sha256: str, fingerprint: str, target: str) -> dict[str, Any]:
    return {"format_version": FORMAT_VERSION, "prefix_sha256": prefix_sha256,
            "environment_fingerprint": fingerprint, "target": target,
            "tool_sha256": hashlib.sha256(_BUILD.encode()).hexdigest()}


def cache_root(settings: dict[str, Any], project: Path) -> Path:
    configured = settings.get("retrieval_index_cache") or os.environ.get("LEAN_REFACTOR_RETRIEVAL_INDEX_CACHE")
    if configured:
        return Path(configured).resolve()
    # Works without shared experiment state; capsules should supply a host cache.
    return Path(os.environ.get("XDG_CACHE_HOME", str(Path.home() / ".cache"))) / "lean-e6" / "goal-signature-index"


def key_for(material: dict[str, Any]) -> str:
    return hashlib.sha256(json.dumps(material, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def _valid(path: Path, material: dict[str, Any]) -> bool:
    try:
        with sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True) as db:
            stored = db.execute("SELECT value FROM metadata WHERE key='identity'").fetchone()
            return stored is not None and json.loads(stored[0]) == material
    except (OSError, ValueError, sqlite3.Error):
        return False


def _compile_records(records: Path, output: Path, material: dict[str, Any], summary: dict[str, Any]) -> None:
    with sqlite3.connect(output) as db:
        db.executescript("PRAGMA journal_mode=OFF; PRAGMA synchronous=OFF; PRAGMA temp_store=MEMORY; "
                         "CREATE TABLE metadata(key TEXT PRIMARY KEY,value TEXT NOT NULL); "
                         "CREATE TABLE theorems(id INTEGER PRIMARY KEY,name TEXT NOT NULL UNIQUE); "
                         "CREATE TABLE symbols(id INTEGER PRIMARY KEY,name TEXT NOT NULL UNIQUE); "
                         "CREATE TABLE postings(symbol_id INTEGER NOT NULL,theorem_id INTEGER NOT NULL,PRIMARY KEY(symbol_id,theorem_id)) WITHOUT ROWID;")
        symbols: dict[str, int] = {}
        postings: list[tuple[int, int]] = []
        theorem_rows: list[tuple[int, str]] = []
        count = 0
        with records.open(encoding="utf-8") as stream:
            for count, line in enumerate(stream, 1):
                name, used = json.loads(line)
                if not isinstance(name, str) or not isinstance(used, list) or any(not isinstance(s, str) for s in used):
                    raise IndexUnavailable("malformed theorem signature index record")
                theorem_rows.append((count, name))
                for symbol in sorted(set(used)):
                    symbol_id = symbols.setdefault(symbol, len(symbols) + 1)
                    postings.append((symbol_id, count))
                if count % 2000 == 0:
                    db.executemany("INSERT INTO theorems VALUES (?,?)", theorem_rows)
                    db.executemany("INSERT INTO postings VALUES (?,?)", postings)
                    theorem_rows.clear()
                    postings.clear()
        if count != summary["visible_theorems"]:
            raise IndexUnavailable("incomplete theorem signature index export")
        db.executemany("INSERT INTO theorems VALUES (?,?)", theorem_rows)
        db.executemany("INSERT INTO postings VALUES (?,?)", postings)
        db.executemany("INSERT INTO symbols VALUES (?,?)", ((value, key) for key, value in symbols.items()))
        db.execute("INSERT INTO metadata VALUES ('identity',?)", (json.dumps(material, sort_keys=True),))
        db.execute("INSERT INTO metadata VALUES ('summary',?)", (json.dumps(summary, sort_keys=True),))


def ensure_index(root: Path, prefix: str, material: dict[str, Any], project: Path,
                 runner: Callable[[str, Path, int], dict[str, Any]]) -> tuple[Path, dict[str, Any]]:
    root.mkdir(parents=True, exist_ok=True)
    key = key_for(material)
    path = root / f"{key}.sqlite3"
    started = time.perf_counter()
    if _valid(path, material):
        return path, {"key": key, "cache_hit": True, "seconds": round(time.perf_counter() - started, 6)}
    failure_path, lock_path = root / f"{key}.failed.json", root / f"{key}.lock"
    try:
        failure = json.loads(failure_path.read_text())
    except (OSError, ValueError):
        failure = {}
    failed_at = failure.get("failed_at", 0) if isinstance(failure, dict) else 0
    if isinstance(failed_at, (int, float)) and time.time() - failed_at < FAILURE_BACKOFF_SECONDS:
        raise IndexUnavailable("index build is cooling down after a failed build: " + str(failure.get("reason", "unavailable"))[:300])
    try:
        fd = os.open(lock_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    except FileExistsError:
        # A terminated builder must not disable retrieval forever.
        if time.time() - lock_path.stat().st_mtime > BUILD_TIMEOUT_SECONDS * 2 + 120:
            lock_path.unlink(missing_ok=True)
            return ensure_index(root, prefix, material, project, runner)
        raise IndexUnavailable("another process is building this exact prefix index; retry after it finishes")
    os.close(fd)
    export, temporary = root / f"{key}.{os.getpid()}.jsonl", root / f"{key}.{os.getpid()}.tmp"
    try:
        # The fixed prefix-only helper contains no candidate or goal state.
        command = "lrhBuildSignatureIndex" + key[:16]
        source = prefix + _BUILD.replace("__COMMAND__", command).replace("__PATH__", json.dumps(str(export), ensure_ascii=False)).replace("__TARGET__", json.dumps(material["target"], ensure_ascii=False)).replace("__MARKER__", INDEX_MARKER)
        observed = runner(source, project, BUILD_TIMEOUT_SECONDS)
        records = observed.get("records", [])
        if len(records) != 1 or records[0].get("status") != "ok" or observed.get("timed_out"):
            raise IndexUnavailable("Lean signature index build failed: " + json.dumps(observed.get("diagnostics", []), ensure_ascii=False)[:500])
        summary = records[0]
        conversion_started = time.perf_counter()
        _compile_records(export, temporary, material, summary)
        conversion_seconds = time.perf_counter() - conversion_started
        os.replace(temporary, path)
        failure_path.unlink(missing_ok=True)
        return path, {"key": key, "cache_hit": False, "seconds": round(time.perf_counter() - started, 6),
                      "lean_seconds": observed.get("seconds"), "scan_ms": summary.get("scan_ms"),
                      "conversion_seconds": round(conversion_seconds, 6), "bytes": path.stat().st_size}
    except (OSError, ValueError, sqlite3.Error, RuntimeError) as error:
        failure_path.write_text(json.dumps({"failed_at": time.time(), "reason": str(error)[:600]}))
        raise IndexUnavailable(str(error)) from error
    finally:
        export.unlink(missing_ok=True)
        temporary.unlink(missing_ok=True)
        lock_path.unlink(missing_ok=True)


def _rank(path: Path, symbols: list[dict[str, Any]], limit: int) -> dict[str, Any]:
    """Touch postings for query symbols only, sort once, return bounded winners."""
    with sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True) as db:
        summary = json.loads(db.execute("SELECT value FROM metadata WHERE key='summary'").fetchone()[0])
        wanted = []
        for symbol in symbols:
            found = db.execute("SELECT id FROM symbols WHERE name=?", (symbol["name"],)).fetchone()
            if found:
                wanted.append((found[0], symbol["weight"]))
        if not wanted:
            return {**summary, "status": "empty", "total_hits": 0, "matches": []}
        values = ",".join("(?,?)" for _ in wanted)
        query = f"WITH wanted(symbol_id,weight) AS (VALUES {values}), ranked AS (SELECT p.theorem_id AS id,SUM(w.weight) AS score FROM postings p JOIN wanted w USING(symbol_id) GROUP BY p.theorem_id) SELECT t.name,r.score,COUNT(*) OVER() AS total_hits FROM ranked r JOIN theorems t ON t.id=r.id ORDER BY r.score DESC,t.name ASC LIMIT ?"
        rows = db.execute(query, [item for pair in wanted for item in pair] + [limit]).fetchall()
        matches = [{"name": name, "score": score} for name, score, _ in rows]
        return {**summary, "status": "ok" if rows else "empty", "total_hits": rows[0][2] if rows else 0, "matches": matches}


def rank(path: Path, symbols: list[dict[str, Any]], limit: int) -> dict[str, Any]:
    try:
        return _rank(path, symbols, limit)
    except (sqlite3.Error, ValueError, TypeError, KeyError) as error:
        raise IndexUnavailable("signature index read failed: " + str(error)[:400]) from error


def _terms(text: str) -> set[str]:
    # Split Lean names, underscores and camel case without a domain vocabulary.
    separated = re.sub(r"([a-z])([A-Z])", r"\1 \2", text)
    return set(re.findall(r"[^\W_]+", separated.casefold(), flags=re.UNICODE)[:64])


def rank_diverse(path: Path, symbols: list[dict[str, Any]], limit: int, *,
                 search_intent: str = "", name_query: str = "",
                 conclusion: str = "") -> dict[str, Any]:
    """Opt-in deterministic union of independent signals on the existing index.

    No index migration, provider, proof data or benchmark-specific vocabulary is
    needed. Round-robin selection reserves room for distinct signals; duplicates
    merge provenance. ``score`` remains the original overlap score so Lean can
    independently reproduce it when rendering signatures.
    """
    if type(limit) is not int or not 1 <= limit <= 5000:
        raise ValueError("diverse candidate limit must be an integer in 1..5000")
    baseline = rank(path, symbols, limit)
    conclusions = [symbol for symbol in symbols if symbol.get("conclusion", False)]
    focused = rank(path, conclusions, limit) if conclusions else {"matches": []}
    branches: list[tuple[str, list[tuple[str, int]]]] = [
        ("signature_overlap", [(match["name"], match["score"]) for match in baseline["matches"]])]
    weights = {symbol["name"]: symbol["weight"] for symbol in symbols}
    try:
        with sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True) as db:
            names = db.execute("SELECT id,name FROM theorems ORDER BY name").fetchall()
            all_hits: set[str] = set()
            if weights:
                placeholders = ",".join("?" for _ in weights)
                all_hits.update(row[0] for row in db.execute(
                    f"SELECT DISTINCT t.name FROM theorems t JOIN postings p ON t.id=p.theorem_id JOIN symbols s ON s.id=p.symbol_id WHERE s.name IN ({placeholders})",
                    list(weights)))
            # Lexical symbol matching uses the same immutable signature postings.
            symbol_rows = db.execute("SELECT id,name FROM symbols ORDER BY name").fetchall()
            def lexical(text: str, *, explicit_name: bool = False) -> list[tuple[str, int]]:
                terms = _terms(text)
                if not terms:
                    return []
                scores = {identifier: len(terms & _terms(name)) * 4 for identifier, name in names}
                if explicit_name:
                    needle = text.strip().casefold()
                    for identifier, name in names:
                        if needle and needle in name.casefold():
                            scores[identifier] += 32
                matching_symbols = [(identifier, len(terms & _terms(name))) for identifier, name in symbol_rows]
                matching_symbols = [(identifier, score) for identifier, score in matching_symbols if score]
                for identifier, score in matching_symbols:
                    for (theorem_id,) in db.execute("SELECT theorem_id FROM postings WHERE symbol_id=?", (identifier,)):
                        scores[theorem_id] += score
                candidates = [(name, scores[identifier]) for identifier, name in names if scores[identifier]]
                all_hits.update(name for name, _ in candidates)
                return sorted(candidates, key=lambda pair: (-pair[1], pair[0]))[:limit]
            if name_query.strip():
                branches.append(("name_lexical", lexical(name_query, explicit_name=True)))
            if search_intent.strip():
                branches.append(("intent_lexical", lexical(search_intent)))
            if conclusions:
                branches.append(("conclusion_overlap", [(match["name"], match["score"]) for match in focused["matches"]]))
            if conclusion.strip():
                branches.append(("conclusion_lexical", lexical(conclusion)))
            selected: list[str] = []
            sources: dict[str, list[str]] = {}
            signal_scores: dict[str, dict[str, int]] = {}
            for source, rows in branches:
                for name, score in rows:
                    sources.setdefault(name, []).append(source)
                    signal_scores.setdefault(name, {})[source] = score
            for index in range(max((len(rows) for _, rows in branches), default=0)):
                for _, rows in branches:
                    if index < len(rows) and rows[index][0] not in selected:
                        selected.append(rows[index][0])
                        if len(selected) == limit:
                            break
                if len(selected) == limit:
                    break
            matches = []
            theorem_ids = {name: identifier for identifier, name in names}
            symbol_ids = {name: identifier for identifier, name in symbol_rows}
            wanted = [(symbol_ids[name], weight) for name, weight in weights.items() if name in symbol_ids]
            placeholders = ",".join("?" for _ in wanted)
            # The existing primary key is (symbol_id,theorem_id); constraining
            # both keys avoids scanning every posting for each selected name.
            overlap_query = f"SELECT symbol_id FROM postings WHERE symbol_id IN ({placeholders}) AND theorem_id=?"
            wanted_ids = [identifier for identifier, _ in wanted]
            for name in selected:
                used = {row[0] for row in db.execute(overlap_query, wanted_ids + [theorem_ids[name]])} if wanted else set()
                matches.append({"name": name, "score": sum(weight for identifier, weight in wanted if identifier in used),
                                "candidate_sources": sources[name], "signal_scores": signal_scores[name]})
    except (sqlite3.Error, ValueError, TypeError, KeyError) as error:
        raise IndexUnavailable("diverse signature index read failed: " + str(error)[:400]) from error
    return {**baseline, "status": "ok" if matches else "empty", "matches": matches,
            "pool_mode": "diverse", "total_hits": len(all_hits),
            "signature_overlap_total_hits": baseline["total_hits"],
            "pool_total_hits_lower_bound": False,
            "pool_sources": {source: len(rows) for source, rows in branches}}


# Query-only experiment: these data never enter the immutable prefix index.
# The vocabulary describes general mathematical/Lean naming conventions, not
# benchmark tasks. Unknown words remain searchable without a fixed dictionary.
_HYBRID_STOPWORDS = frozenset("a an and are as at be by can close do find first for from goal have if in into is it lemma lemmas let of on or proof prove second seek show so some such than that the then theorem there this to use using via want we where which with".split())
_HYBRID_WORDS = {
    "commutativity": "comm", "commutative": "comm",
    "associativity": "assoc", "associative": "assoc",
    "cardinality": "card", "reversed": "reverse",
    "injectivity": "injective", "surjectivity": "surjective",
    "initialization": "init", "initialize": "init", "initialise": "init",
    "irreducibility": "irreducible",
}
_HYBRID_ACRONYM = re.compile(r"([A-Z]+)([A-Z][a-z])")
_HYBRID_CAMEL = re.compile(r"([a-z0-9])([A-Z])")
_HYBRID_TOKEN = re.compile(r"[^\W_]+", flags=re.UNICODE)
_HYBRID_AUXILIARY = re.compile(r"\._proof_\d|\._auxLemma")
_HYBRID_MATCH = re.compile(r"\.match_\d")


def _hybrid_terms(text: str) -> set[str]:
    separated = _HYBRID_ACRONYM.sub(r"\1 \2", text)
    separated = _HYBRID_CAMEL.sub(r"\1 \2", separated)
    terms = set()
    # Deduplicate before applying the bound: repeated context cannot consume it.
    for word in _HYBRID_TOKEN.findall(separated.casefold()):
        if len(word) < 2 or word.isdigit() or word in _HYBRID_STOPWORDS:
            continue
        word = _HYBRID_WORDS.get(word, word)
        if len(word) > 4 and word.endswith("ies"):
            word = word[:-3] + "y"
        elif len(word) > 4 and word.endswith("s") and not word.endswith(("ss", "is", "us")):
            word = word[:-1]
        terms.add(word)
        if len(terms) == 128:
            break
    return terms


def _hybrid_prior(name: str, *, explicit: bool = False) -> float:
    """Soft corpus prior; exact requests can still retrieve any indexed name."""
    if explicit:
        return 1.0
    prior = 1.0
    if ".sizeOf_spec" in name:
        prior *= 0.025
    elif _HYBRID_AUXILIARY.search(name):
        prior *= 0.12
    elif _HYBRID_MATCH.search(name):
        prior *= 0.4
    # Equations and injectivity lemmas intentionally retain their normal prior.
    if name.startswith(("Lean.Meta.", "Lean.Elab.", "Lean.Parser.", "Aesop.", "Qq.")):
        prior *= 0.3
    elif name.startswith("Lean."):
        prior *= 0.65
    if name.rsplit(".", 1)[-1].startswith("inst"):
        prior *= 0.25
    return prior


def _hybrid_symbol_prior(name: str) -> float:
    leaf = name.rsplit(".", 1)[-1]
    if name.split(".", 1)[0] in {"Eq", "HEq", "Iff", "And", "Or", "Not", "Exists", "True", "False", "Nat", "Int",
                                     "OfNat", "HAdd", "HMul", "HSub", "HDiv", "HPow", "HSMul", "LT", "LE", "GT", "GE"}:
        return 0.12
    if leaf.startswith("inst") or leaf.startswith("dec") or "._proof_" in name:
        return 0.12
    if leaf.startswith("to") and len(leaf) > 2 and leaf[2].isupper():
        return 0.3
    return 1.0


@lru_cache(maxsize=2)
def _hybrid_corpus(path: str, mtime_ns: int, size: int) -> dict[str, Any]:
    """Bounded process cache of statistics derived only from theorem types.

    A changed index stat gets a new cache entry. No theorem bodies, archived
    solutions, target names or query context are retained in this cache.
    """
    del mtime_ns, size
    with sqlite3.connect(Path(path).as_uri() + "?mode=ro", uri=True) as db:
        names = dict(db.execute("SELECT id,name FROM theorems"))
        name_terms: dict[str, array] = {}
        name_lengths: dict[int, int] = {}
        for identifier, name in names.items():
            terms = _hybrid_terms(name)
            name_lengths[identifier] = len(terms)
            for term in terms:
                name_terms.setdefault(term, array("I")).append(identifier)
        symbol_names = dict(db.execute("SELECT id,name FROM symbols"))
        symbol_terms: dict[str, array] = {}
        for identifier, name in symbol_names.items():
            for term in _hybrid_terms(name):
                symbol_terms.setdefault(term, array("I")).append(identifier)
        frequencies = dict(db.execute("SELECT symbol_id,COUNT(*) FROM postings GROUP BY symbol_id"))
        lengths = dict(db.execute("SELECT theorem_id,COUNT(*) FROM postings GROUP BY theorem_id"))
    priors = {identifier: _hybrid_prior(name) for identifier, name in names.items()}
    denominators = {identifier: math.sqrt(1 + lengths.get(identifier, 0) / 12) for identifier in names}
    name_denominators = {identifier: math.sqrt(1 + name_lengths[identifier] / 8) for identifier in names}
    norms = {identifier: priors[identifier] / denominators[identifier] for identifier in names}
    return {"names": names, "name_terms": name_terms, "name_lengths": name_lengths,
            "symbol_names": symbol_names, "symbol_ids": {name: identifier for identifier, name in symbol_names.items()},
            "symbol_terms": symbol_terms, "frequencies": frequencies, "lengths": lengths,
            "priors": priors, "norms": norms, "denominators": denominators, "name_denominators": name_denominators}


def rank_hybrid_v1(path: Path, symbols: list[dict[str, Any]], limit: int, *,
                search_intent: str = "", name_query: str = "",
                conclusion: str = "") -> dict[str, Any]:
    """Experimental broad pool from IDF-normalized complementary branches.

    All admission uses the existing exact-prefix theorem-only corpus. This is
    lexical discovery, not structural matching or semantic equivalence. ``score``
    remains the original overlap score for independent Lean verification;
    normalized scores and candidate admission are separately auditable.
    """
    if type(limit) is not int or not 1 <= limit <= 5000:
        raise ValueError("hybrid candidate limit must be an integer in 1..5000")
    started = time.perf_counter()
    try:
        stat = path.stat()
        cached = _hybrid_corpus(str(path.resolve()), stat.st_mtime_ns, stat.st_size)
        names, frequencies, lengths = cached["names"], cached["frequencies"], cached["lengths"]
        count = len(names)
        weights = {symbol["name"]: symbol["weight"] for symbol in symbols}
        wanted = [(cached["symbol_ids"][s["name"]], s) for s in symbols if s["name"] in cached["symbol_ids"]]
        branch_limit = max(100, min(5000, limit * 4))
        branches: dict[str, list[tuple[int, float]]] = {}
        all_hits: set[int] = set()
        raw_overlap: dict[int, float] = {}
        with sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True) as db:
            summary = json.loads(db.execute("SELECT value FROM metadata WHERE key='summary'").fetchone()[0])

            def finish(source: str, scores: dict[int, float]) -> None:
                all_hits.update(scores)
                branches[source] = heapq.nsmallest(branch_limit,
                    ((identifier, score) for identifier, score in scores.items() if score > 0),
                    key=lambda pair: (-pair[1], names[pair[0]]))

            def exact_symbols(source: str, focused: bool) -> None:
                scores: dict[int, float] = {}
                for identifier, symbol in wanted:
                    if focused and not symbol.get("conclusion", False):
                        continue
                    idf = 1.0 + math.log((count + 1) / (frequencies.get(identifier, 0) + 1))
                    weight = math.sqrt(max(0, float(symbol["weight"]))) * idf * _hybrid_symbol_prior(symbol["name"])
                    if symbol.get("generic", False):
                        weight *= 0.35
                    for (theorem_id,) in db.execute("SELECT theorem_id FROM postings WHERE symbol_id=?", (identifier,)):
                        scores[theorem_id] = scores.get(theorem_id, 0.0) + weight
                        if not focused:
                            raw_overlap[theorem_id] = raw_overlap.get(theorem_id, 0) + weights[symbol["name"]]
                for identifier in scores:
                    scores[identifier] *= cached["norms"][identifier]
                finish(source, scores)

            def lexical(source: str, text: str, *, type_terms: bool = False, explicit: bool = False) -> None:
                terms = _hybrid_terms(text)
                if not terms and not (explicit and text.strip()):
                    return
                scores: dict[int, float] = {}
                matched: dict[int, int] = {}
                postings = cached["symbol_terms"] if type_terms else cached["name_terms"]
                for term in sorted(terms):
                    identifiers = postings.get(term, ())
                    if not identifiers:
                        continue
                    if type_terms:
                        # Upper bound on document frequency is conservative when
                        # many synonymous symbol names occur in the same type.
                        df = min(count, sum(frequencies.get(i, 0) for i in identifiers))
                        idf = 1 + math.log((count + 1) / (df + 1))
                        # MAX per query term prevents long/generated signatures
                        # gaining many points from repeated matching symbols.
                        found: dict[int, float] = {}
                        for symbol_id in identifiers:
                            prior = _hybrid_symbol_prior(cached["symbol_names"][symbol_id])
                            for (theorem_id,) in db.execute("SELECT theorem_id FROM postings WHERE symbol_id=?", (symbol_id,)):
                                found[theorem_id] = max(found.get(theorem_id, 0), prior)
                        for identifier, strength in found.items():
                            scores[identifier] = scores.get(identifier, 0.0) + idf * strength
                            matched[identifier] = matched.get(identifier, 0) + 1
                    else:
                        idf = 1 + math.log((count + 1) / (len(identifiers) + 1))
                        for identifier in identifiers:
                            scores[identifier] = scores.get(identifier, 0.0) + idf
                            matched[identifier] = matched.get(identifier, 0) + 1
                needle = text.strip().casefold() if explicit else ""
                if needle:
                    for identifier, name in names.items():
                        if needle == name.casefold() or needle == name.rsplit(".", 1)[-1].casefold():
                            scores[identifier] = scores.get(identifier, 0.0) + 1000
                        elif needle in name.casefold():
                            scores[identifier] = scores.get(identifier, 0.0) + 30
                for identifier in scores:
                    direct = bool(needle and needle in names[identifier].casefold())
                    coverage = 0.5 + 0.5 * matched.get(identifier, 0) / max(1, len(terms))
                    # Preserve v1's floating-point operation order exactly.
                    denominator = cached["denominators" if type_terms else "name_denominators"][identifier]
                    prior = 1.0 if direct else cached["priors"][identifier]
                    scores[identifier] *= coverage * prior / denominator
                finish(source, scores)

            exact_symbols("signature_idf", False)
            if any(s.get("conclusion", False) for _, s in wanted):
                exact_symbols("conclusion_idf", True)
            if name_query.strip():
                lexical("explicit_name", name_query, explicit=True)
            if search_intent.strip():
                lexical("intent_name", search_intent)
                lexical("intent_type", search_intent, type_terms=True)
            if conclusion.strip():
                lexical("conclusion_name", conclusion)

        # Weighted reciprocal-rank fusion compares ranks rather than unrelated
        # branch units. Each nonempty branch reserves a small admission quota;
        # strong signature candidates retain half the pool when available.
        branch_weights = {"signature_idf": 1.0, "conclusion_idf": 0.65, "explicit_name": 1.8,
                          "intent_name": 1.0, "intent_type": 0.55, "conclusion_name": 0.6}
        fusion: dict[int, float] = {}
        sources: dict[int, dict[str, float]] = {}
        ranks: dict[int, dict[str, int]] = {}
        for source, rows in branches.items():
            for position, (identifier, score) in enumerate(rows, 1):
                fusion[identifier] = fusion.get(identifier, 0.0) + branch_weights[source] / (20 + position)
                sources.setdefault(identifier, {})[source] = round(score, 6)
                ranks.setdefault(identifier, {})[source] = position
        ordered = sorted(fusion, key=lambda i: (-fusion[i], names[i]))
        selected: set[int] = set()
        # A precise full name or suffix is an explicit request, so put it first.
        needle = name_query.strip().casefold()
        direct = [i for i, _ in branches.get("explicit_name", [])
                  if needle and needle in (names[i].casefold(), names[i].rsplit(".", 1)[-1].casefold())]
        selected.update(direct[:limit])
        for source, fraction in (("signature_idf", 0.4), ("intent_name", 0.2), ("intent_type", 0.1),
                                 ("explicit_name", 0.1), ("conclusion_idf", 0.1), ("conclusion_name", 0.1)):
            quota = int(limit * fraction)
            for identifier, _ in branches.get(source, [])[:quota]:
                if len(selected) < limit:
                    selected.add(identifier)
        for identifier in ordered:
            if len(selected) == limit:
                break
            selected.add(identifier)
        direct_set = set(direct)
        final = sorted(selected, key=lambda i: (i not in direct_set, -fusion[i], names[i]))
        matches = [{"name": names[i], "score": raw_overlap.get(i, 0),
                    "candidate_sources": list(sources[i]), "signal_scores": sources[i],
                    "signal_ranks": ranks[i], "hybrid_score": round(fusion[i], 9),
                    "corpus_prior": _hybrid_prior(names[i], explicit=i in direct_set)} for i in final]
        return {**summary, "status": "ok" if matches else "empty", "matches": matches,
                "pool_mode": "hybrid", "pool_version": 1, "total_hits": len(all_hits),
                "signature_overlap_total_hits": len(raw_overlap), "pool_total_hits_lower_bound": False,
                "pool_sources": {source: len(rows) for source, rows in branches.items()},
                "ranking_seconds": round(time.perf_counter() - started, 6),
                "ranking_policy": "idf_length_normalization;term_max;soft_corpus_prior;rrf_with_branch_quotas"}
    except (OSError, sqlite3.Error, ValueError, TypeError, KeyError) as error:
        raise IndexUnavailable("hybrid signature index read failed: " + str(error)[:400]) from error


def rank_hybrid_queries(path: Path, symbols: list[dict[str, Any]], limit: int, *,
                        queries: list[str], name_query: str = "",
                        conclusion: str = "") -> dict[str, Any]:
    """Research-only fusion of explicit, separately auditable subqueries.

    This does not invent a decomposition or treat query text as proof evidence.
    Each query gets its own lexical ranking and quota, while one shared context
    branch preserves goal-symbol candidates without counting them once per query.
    """
    if type(limit) is not int or not 1 <= limit <= 5000:
        raise ValueError("hybrid candidate limit must be an integer in 1..5000")
    if not isinstance(queries, list) or not 1 <= len(queries) <= 8 or any(not isinstance(q, str) or not q.strip() or len(q) > 4000 for q in queries):
        raise ValueError("hybrid queries must contain 1..8 nonempty strings of at most 4000 characters")
    queries = list(dict.fromkeys(q.strip() for q in queries))
    started = time.perf_counter()
    width = min(5000, max(100, limit * 4))
    context = rank_hybrid_v1(path, symbols, width, name_query=name_query, conclusion=conclusion)
    records: dict[str, dict[str, Any]] = {m["name"]: m for m in context["matches"]}
    context_rows = [(m["name"], m["hybrid_score"]) for m in context["matches"]]
    branches = {"context": context_rows}
    query_runs = []
    for position, query in enumerate(queries):
        run = rank_hybrid_v1(path, symbols, width, search_intent=query, conclusion=conclusion)
        lexical = []
        for match in run["matches"]:
            ranks = match["signal_ranks"]
            score = sum(weight / (20 + ranks[source]) for source, weight in (("intent_name", 1.0), ("intent_type", 0.55)) if source in ranks)
            if score:
                lexical.append((match["name"], score))
                records.setdefault(match["name"], match)
        branches[f"query_{position}"] = sorted(lexical, key=lambda row: (-row[1], row[0]))
        query_runs.append({"query": query, "lexical_candidates": len(lexical), "ranking_seconds": run["ranking_seconds"]})
    fusion: dict[str, float] = {}
    provenance: dict[str, dict[str, int]] = {}
    for branch, rows in branches.items():
        weight = 0.7 if branch == "context" else 1.0
        for rank_, (name, _) in enumerate(rows, 1):
            fusion[name] = fusion.get(name, 0) + weight / (20 + rank_)
            provenance.setdefault(name, {})[branch] = rank_
    ordered = sorted(fusion, key=lambda name: (-fusion[name], name))
    selected: set[str] = set()
    quotas = {"context": limit // 4}
    quotas.update({f"query_{i}": (limit - limit // 4) // len(queries) for i in range(len(queries))})
    for branch, rows in branches.items():
        for name, _ in rows[:quotas[branch]]:
            if len(selected) < limit:
                selected.add(name)
    for name in ordered:
        if len(selected) == limit:
            break
        selected.add(name)
    matches = []
    for name in sorted(selected, key=lambda name: (-fusion[name], name)):
        matches.append({**records[name], "query_sources": list(provenance[name]),
                        "query_ranks": provenance[name], "query_fusion_score": round(fusion[name], 9)})
    return {**context, "matches": matches, "pool_mode": "hybrid_queries", "queries": queries,
            "query_runs": query_runs, "query_quotas": quotas,
            "pool_sources": {source: len(rows) for source, rows in branches.items()},
            "total_hits": len(fusion), "pool_total_hits_lower_bound": True,
            "ranking_seconds": round(time.perf_counter() - started, 6)}


def rank_hybrid(path: Path, symbols: list[dict[str, Any]], limit: int, *,
                   search_intent: str = "", name_query: str = "",
                   conclusion: str = "") -> dict[str, Any]:
    """Separate conclusion-dominant experiment; frozen v1 is unaffected.

    Hypothesis-only symbols have a bounded *total possible* normalized weight,
    rather than each unrelated rare hypothesis earning a full IDF contribution.
    Half the admission budget is reserved for conclusion-specific candidates.
    This is a soft bag-of-symbols policy, not hypothesis relevance inference.
    """
    if type(limit) is not int or not 1 <= limit <= 5000:
        raise ValueError("hybrid candidate limit must be an integer in 1..5000")
    started = time.perf_counter()
    try:
        stat = path.stat()
        cached = _hybrid_corpus(str(path.resolve()), stat.st_mtime_ns, stat.st_size)
        count = len(cached["names"])
        goal_total, hypothesis_total = 0.0, 0.0
        for symbol in symbols:
            symbol_id = cached["symbol_ids"].get(symbol["name"])
            if symbol_id is None:
                continue
            idf = 1 + math.log((count + 1) / (cached["frequencies"].get(symbol_id, 0) + 1))
            contribution = math.sqrt(max(0, float(symbol["weight"]))) * idf * _hybrid_symbol_prior(symbol["name"])
            if symbol.get("generic", False):
                contribution *= 0.35
            if symbol.get("conclusion", False):
                goal_total += contribution
            else:
                hypothesis_total += contribution
        scale = min(1.0, 0.35 * goal_total / hypothesis_total) if goal_total and hypothesis_total else 1.0
        adapted = [{**s, "weight": s["weight"] if s.get("conclusion", False) else s["weight"] * scale * scale} for s in symbols]
        width = min(5000, max(100, limit * 4))
        result = rank_hybrid_v1(path, adapted, width, search_intent=search_intent, name_query=name_query, conclusion=conclusion)
        matches = result["matches"]
        by_name = {m["name"]: m for m in matches}
        selected: set[str] = set()
        needle = name_query.strip().casefold()
        direct = [m["name"] for m in matches if needle and needle in (m["name"].casefold(), m["name"].rsplit(".", 1)[-1].casefold())]
        selected.update(direct[:limit])
        quotas = {"conclusion_idf": limit // 2, "signature_idf": limit * 15 // 100,
                  "intent_name": limit * 20 // 100, "intent_type": limit // 10}
        for source, quota in quotas.items():
            branch = sorted((m for m in matches if source in m["signal_ranks"]), key=lambda m: (m["signal_ranks"][source], m["name"]))
            for match in branch[:quota]:
                if len(selected) < limit:
                    selected.add(match["name"])
        for match in matches:
            if len(selected) == limit:
                break
            selected.add(match["name"])
        final = sorted((by_name[name] for name in selected), key=lambda m: (m["name"] not in direct, -m["hybrid_score"], m["name"]))
        # Adapted weights affect discovery only. Restore independently checkable
        # original overlap scores on the selected bounded set.
        raw: dict[str, float] = {}
        if final and symbols:
            wanted = [(cached["symbol_ids"][s["name"]], s["weight"]) for s in symbols if s["name"] in cached["symbol_ids"]]
            if wanted:
                ids = {name: identifier for identifier, name in cached["names"].items() if name in selected}
                values = ",".join("(?,?)" for _ in wanted)
                placeholders = ",".join("?" for _ in ids)
                query = f"WITH wanted(symbol_id,weight) AS (VALUES {values}) SELECT t.name,SUM(w.weight) FROM postings p JOIN wanted w USING(symbol_id) JOIN theorems t ON t.id=p.theorem_id WHERE p.theorem_id IN ({placeholders}) GROUP BY p.theorem_id"
                with sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True) as db:
                    raw = dict(db.execute(query, [v for pair in wanted for v in pair] + list(ids.values())))
        return {**result, "matches": [{**match, "score": raw.get(match["name"], 0)} for match in final],
                "pool_mode": "hybrid", "pool_version": 2,
                "ranking_policy": result["ranking_policy"] + ";conclusion_admission_quota;conditional_hypothesis_mass_cap",
                "context_budget": {"conclusion_weight": round(goal_total, 6), "hypothesis_weight_before": round(hypothesis_total, 6),
                                    "hypothesis_scale": round(scale, 6), "maximum_hypothesis_to_conclusion": 0.35,
                                    "hypothesis_cap_active": bool(goal_total and hypothesis_total)},
                "admission_quotas": quotas, "ranking_seconds": round(time.perf_counter() - started, 6)}
    except (OSError, sqlite3.Error, ValueError, TypeError, KeyError) as error:
        raise IndexUnavailable("hybrid v2 signature index read failed: " + str(error)[:400]) from error
