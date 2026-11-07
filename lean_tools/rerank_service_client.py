"""Finite declaration reranking transport; proof capsules never load provider keys.

Frozen E6 configuration always uses the authenticated host service. Explicit
standalone CLI configuration may use the host Decisions client directly.
"""
from __future__ import annotations

import hashlib
import json
import os
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter
from pathlib import Path
from typing import Any, Mapping, Sequence

URL_ENV = "LEAN_REFACTOR_RERANK_URL"
TOKEN_ENV = "LEAN_REFACTOR_RERANK_TOKEN"
CONFIG_ENV = "LEAN_REFACTOR_RERANK_CONFIG"
MAX_CANDIDATES = 5000
MAX_MESSAGE_BYTES = 16 * 1024 * 1024
MODELS = {"jev": "typesafe/jev-1.13", "openai": "openai/gpt-6-luna-decisions"}
RANKERS = frozenset({"baseline", "lexical", "jev", "openai", "model"})


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False).encode("utf-8")


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value)).hexdigest()


def resolve_options(*, ranker: str | None = None, model: str | None = None) -> tuple[dict[str, Any], bool]:
    """Frozen configuration wins over agent flags and forbids credential fallback."""
    frozen = os.environ.get(CONFIG_ENV)
    if frozen:
        value = json.loads(frozen)
        if not isinstance(value, dict):
            raise ValueError("frozen rerank configuration must be a JSON object")
        options = dict(value)
        if ranker is not None and ranker != options.get("ranker"):
            raise ValueError("ranker differs from the frozen host configuration")
        if model is not None and model != options.get("model"):
            raise ValueError("model differs from the frozen host configuration")
        automatic = True
    elif ranker is not None:
        options, automatic = {"ranker": ranker}, False
        if model is not None:
            options["model"] = model
    elif model is not None:
        raise ValueError("--model requires --ranker model")
    else:
        return {}, False
    selected = options.get("ranker")
    if selected not in RANKERS:
        raise ValueError("unknown reranker in configuration")
    if selected == "model" and not isinstance(options.get("model"), str):
        raise ValueError("ranker model requires an explicit model identifier")
    if not automatic and model is not None and selected != "model":
        raise ValueError("--model requires --ranker model")
    candidate_limit = options.get("candidate_limit", 30)
    if type(candidate_limit) is not int or not 1 <= candidate_limit <= MAX_CANDIDATES:
        raise ValueError(f"candidate_limit must be an integer in 1..{MAX_CANDIDATES}")
    return options, automatic


def search_limit_contract(
    options: Mapping[str, Any], automatic: bool, *, enabled: bool = True,
    result_max: int | None = None, default_limit: int = 30,
) -> dict[str, Any]:
    """Describe the effective pair without changing frozen selector options."""
    candidate_max = options.get("candidate_limit", 30) if automatic else (MAX_CANDIDATES if enabled else None)
    maximum = candidate_max if result_max is None else (
        result_max if candidate_max is None else min(result_max, candidate_max)
    )
    candidate_default = (options.get("candidate_limit", 30) if automatic or "candidate_limit" in options else
                         "max(30, result_limit)" if options else "result_limit")
    return {
        "frozen": automatic,
        "result_limit": {"minimum": 1, "maximum": maximum,
                         "default": default_limit if maximum is None else min(default_limit, maximum)},
        "candidate_limit": {"minimum": 1, "maximum": candidate_max,
                            "default": candidate_default},
        "constraint": "result_limit <= candidate_limit",
    }


class SearchLimitError(ValueError):
    """One joint admission failure with a pair that the same policy accepts."""

    def __init__(self, contract: dict[str, Any], limit: int, candidate_limit: int, *, cli_arguments: bool = True) -> None:
        self.contract = contract
        self.retry = {"limit": limit, "candidate_limit": candidate_limit}
        result_max = contract["result_limit"]["maximum"]
        candidate_max = contract["candidate_limit"]["maximum"]
        result_range = f"1..{result_max}" if result_max is not None else ">=1"
        candidate_range = f"limit..{candidate_max}" if candidate_max is not None else ">=limit"
        frozen = " under the frozen host configuration" if contract["frozen"] else ""
        replacement = (f"--limit {limit} --candidate-limit {candidate_limit}" if cli_arguments else
                       f"limit={limit}, candidate_limit={candidate_limit}")
        super().__init__(
            f"search limit must be an integer in {result_range} and candidate limit must be "
            f"an integer in {candidate_range}{frozen}; use {replacement}"
        )


def resolve_search_limits(
    limit: Any, candidate_limit: Any, *, options: Mapping[str, Any], automatic: bool,
    enabled: bool = True, result_max: int | None = None, default_limit: int = 30,
    cli_arguments: bool = True,
) -> int:
    """Validate requested results and pool together, before Lean/provider work."""
    contract = search_limit_contract(options, automatic, enabled=enabled,
                                     result_max=result_max, default_limit=default_limit)
    pool_limit = candidate_limit if candidate_limit is not None else (
        options.get("candidate_limit", max(30, limit)) if options and type(limit) is int else
        options.get("candidate_limit", 30) if options else limit
    )
    result_maximum = contract["result_limit"]["maximum"]
    candidate_maximum = contract["candidate_limit"]["maximum"]
    valid_result = type(limit) is int and limit >= 1 and (result_maximum is None or limit <= result_maximum)
    valid_pool = (type(pool_limit) is int and type(limit) is int and pool_limit >= limit
                  and (candidate_maximum is None or pool_limit <= candidate_maximum))
    if valid_result and valid_pool:
        return pool_limit
    replacement_limit = max(1, limit) if type(limit) is int else contract["result_limit"]["default"]
    if result_maximum is not None:
        replacement_limit = min(replacement_limit, result_maximum)
    replacement_pool = max(replacement_limit, pool_limit) if type(pool_limit) is int else (
        max(replacement_limit, options.get("candidate_limit", 30)) if options else replacement_limit
    )
    if candidate_maximum is not None:
        replacement_pool = min(replacement_pool, candidate_maximum)
    raise SearchLimitError(contract, replacement_limit, replacement_pool, cli_arguments=cli_arguments)


def load_context(path: Path | None) -> dict[str, Any]:
    value = {} if path is None else json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError("search context file must contain a JSON object")
    allowed = {"goal", "hypotheses", "search_intent", "same_run_context"}
    if set(value) - allowed:
        raise ValueError("search context supports only goal, hypotheses, search_intent and same_run_context")
    if "goal" in value and not isinstance(value["goal"], str):
        raise ValueError("search goal must be text")
    if "hypotheses" in value and (not isinstance(value["hypotheses"], list) or any(not isinstance(item, str) for item in value["hypotheses"])):
        raise ValueError("search hypotheses must be a list of strings")
    for key in ("search_intent", "same_run_context"):
        if key in value and not isinstance(value[key], str):
            raise ValueError(f"{key} must be text")
    return {"goal": "", "hypotheses": [], "search_intent": "", **value}


def make_binding(candidates: Sequence[dict[str, Any]], context: Mapping[str, Any], *, task_id: str, prefix_sha256: str, environment_fingerprint: str, source_sha256: str) -> dict[str, str]:
    return {"task_id": task_id, "prefix_sha256": prefix_sha256,
            "environment_fingerprint": environment_fingerprint, "source_sha256": source_sha256,
            "goal_sha256": digest(context), "pool_sha256": digest(candidates)}


def write_pool(path: Path, candidates: Sequence[dict[str, Any]], context: Mapping[str, Any], binding: Mapping[str, Any], *, reranking: Mapping[str, Any] | None = None) -> None:
    path = path.resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    value = {"schema_version": 1, "binding": binding, "context": context, "candidates": candidates}
    if reranking is not None:
        value["reranking"] = dict(reranking)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def compact_result(result: Mapping[str, Any], pool: Sequence[dict[str, Any]], limit: int, *, include_pool: bool = False) -> dict[str, Any]:
    """Keep model replay and the complete score table out of ordinary shortlist output."""
    if include_pool:
        return {key: value for key, value in result.items() if key != "matches"}
    value = {key: item for key, item in result.items() if key not in {"matches", "calls", "scores"}}
    value["calls"] = [{key: item for key, item in call.items() if key not in {"request", "raw_response", "config"}} for call in result.get("calls", [])]
    selected = {canonical_json(item) for item in result.get("matches", [])[:limit]}
    indexes = {index for index, record in enumerate(pool) if canonical_json(record) in selected}
    value["scores"] = [score for score in result.get("scores", []) if score.get("original_index") in indexes]
    value["metadata"] = {**result.get("metadata", {}), "total_scores": len(result.get("scores", [])), "returned_scores": len(value["scores"])}
    return value


def _fallback(candidates: Sequence[dict[str, Any]], binding: Mapping[str, Any], reason: str) -> dict[str, Any]:
    return {"status": "fallback", "matches": list(candidates), "scores": [], "calls": [],
            "metadata": {"fallback_reason": reason, "transport": "host_service", "binding": dict(binding)}}


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args: Any, **kwargs: Any) -> None:
        return None


def request_service(candidates: Sequence[dict[str, Any]], context: Mapping[str, Any], binding: Mapping[str, Any], *, timeout_seconds: float = 120, operation: str = "declarations") -> dict[str, Any]:
    """Exchange typed records through one of two fixed host ranking routes."""
    if operation not in {"declarations", "examples"}:
        raise ValueError("unsupported rerank operation")
    endpoint, token = os.environ.get(URL_ENV, ""), os.environ.get(TOKEN_ENV, "")
    parsed = urllib.parse.urlparse(endpoint)
    if parsed.scheme != "http" or parsed.hostname != "127.0.0.1" or parsed.path != "/rerank" or parsed.params or parsed.query or parsed.fragment or parsed.username or parsed.password:
        raise ValueError("rerank service must use http://127.0.0.1:<port>/rerank")
    if not parsed.port or not token:
        raise ValueError("rerank service endpoint and authentication token are required")
    maximum = 30 if operation == "examples" else MAX_CANDIDATES
    if len(candidates) > maximum:
        raise ValueError("rerank candidate pool exceeds the finite transport bound")
    if operation == "examples":
        endpoint = urllib.parse.urlunparse(parsed._replace(path="/rerank-examples"))
    data = canonical_json({"candidates": candidates, "context": context, "binding": binding})
    if len(data) > MAX_MESSAGE_BYTES:
        raise ValueError("rerank request exceeds the finite transport byte bound")
    request = urllib.request.Request(endpoint, data=data, headers={"Authorization": "Bearer " + token, "Content-Type": "application/json"}, method="POST")
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), _NoRedirect)
    with opener.open(request, timeout=timeout_seconds) as response:
        raw = response.read(MAX_MESSAGE_BYTES + 1)
    if len(raw) > MAX_MESSAGE_BYTES:
        raise ValueError("rerank response exceeds the finite transport byte bound")
    value = json.loads(raw)
    if not isinstance(value, dict) or value.get("binding") != binding:
        raise ValueError("rerank response binding does not match this source, goal and pool")
    if value.get("status") not in {"ok", "baseline", "fallback"}:
        raise ValueError("rerank response has an invalid status")
    matches = value.get("matches")
    if not isinstance(matches, list) or Counter(canonical_json(item) for item in matches) != Counter(canonical_json(item) for item in candidates):
        raise ValueError("rerank response changed the exact candidate records")
    for field in ("calls", "scores"):
        if not isinstance(value.get(field, []), list) or any(not isinstance(item, dict) for item in value.get(field, [])):
            raise ValueError(f"rerank response has malformed {field}")
    if not isinstance(value.get("metadata", {}), dict):
        raise ValueError("rerank response has malformed metadata")
    return value


def rerank(candidates: Sequence[dict[str, Any]], context: Mapping[str, Any], *, binding: Mapping[str, Any], options: Mapping[str, Any], automatic: bool = False) -> dict[str, Any]:
    """Route capsules exclusively to the host; standalone callers choose a ranker."""
    if automatic or os.environ.get(URL_ENV):
        try:
            return request_service(candidates, context, binding, timeout_seconds=options.get("timeout_seconds", 120))
        except (OSError, ValueError, urllib.error.URLError) as error:
            # The frozen service owns all credentials, cost admission and ledger writes.
            # Its failure never causes a credential-bearing local client to be created.
            return _fallback(candidates, binding, str(error)[:800])
    from lean_tools import decision_rerank
    selected = options.get("ranker", "baseline")
    mode = selected if selected in {"baseline", "lexical"} else "decisions"
    fields = {key: value for key, value in options.items() if key not in {"ranker", "candidate_limit"}}
    fields.update(mode=mode, model=options.get("model") or MODELS.get(selected, MODELS["jev"]))
    try:
        config = decision_rerank.RerankConfig(**fields)
        return decision_rerank.rerank_candidates(candidates, context, config=config)
    except (TypeError, decision_rerank.RerankError) as error:
        raise ValueError(str(error)) from error
