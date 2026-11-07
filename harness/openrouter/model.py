"""Freeze public OpenRouter metadata without credentials or inference.

The settings file is directly consumable by ``--openrouter-config``. Its sibling
evidence file retains the public metadata used to derive conservative ceilings.
Native Codex capabilities are deliberately specified here, rather than copied
from an unrelated OpenAI model's catalog row.
"""
from __future__ import annotations

from collections.abc import Callable, Mapping
import copy
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation
import hashlib
import json
from pathlib import Path
import re
from typing import Any
from urllib.request import Request, urlopen

from .config import CODEX_REASONING_EFFORTS


TARGET_MODEL = "deepseek/deepseek-v4.1-flash-1017"
CANONICAL_MODEL = "deepseek/deepseek-v4.1-flash-20261017"
DEFAULT_PROVIDER = "deepseek"
MODELS_URL = "https://openrouter.ai/api/v1/models"
PROVIDER_ROUTING_SOURCE = "https://openrouter.ai/docs/guides/routing/provider-selection"
REASONING_EFFORTS = ("none", "low", "high", "max")
DEFAULT_OUTPUT_TOKENS = None
PINNED_NATIVE_MODELS = {
    "openai/gpt-6.1-sol": ("model-catalog.json", "gpt-6.1-sol"),
    "openai/gpt-6-luna": ("model-catalog.json", "gpt-6-luna"),
    "openai/gpt-6.1-terra": ("model-catalog-terra61.json", "gpt-6.1-terra"),
}
MILLION = Decimal(1_000_000)
MODEL_SLUG = r"[A-Za-z0-9][A-Za-z0-9._-]*/[A-Za-z0-9][A-Za-z0-9._:-]*"

# This is a native coding instruction, not an identity or model capability claim.
# Codex itself supplies sandbox, shell and MCP tool documentation at runtime.
BASE_INSTRUCTIONS = """You are a coding agent running in the Codex CLI. Work in the supplied workspace to complete the user's task. Follow the repository instructions and use the available native shell and MCP tools. Inspect relevant files before editing, make focused changes, and verify the result with appropriate checks. Use the shell to edit files or invoke an available patch helper. Preserve unrelated user changes. Continue until the requested work is complete, and report the result and any remaining limitation clearly. Do not claim that a command or check succeeded unless its output supports that claim."""


class ModelPreparationError(ValueError):
    """Public metadata cannot support this frozen experiment configuration."""


def _decimal(value: Any, field: str) -> Decimal:
    if isinstance(value, bool) or not isinstance(value, (str, int, float, Decimal)):
        raise ModelPreparationError(f"Invalid {field} price")
    try:
        result = Decimal(str(value))
    except InvalidOperation as error:
        raise ModelPreparationError(f"Invalid {field} price") from error
    if not result.is_finite() or result < 0:
        raise ModelPreparationError(f"Invalid {field} price")
    return result


def _amount(value: Decimal) -> str:
    text = format(value, "f")
    return text.rstrip("0").rstrip(".") if "." in text else text


def _positive_int(value: Any, field: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise ModelPreparationError(f"Invalid {field}")
    return value


def _price_ceiling(pricing: Any) -> tuple[Decimal, Decimal]:
    """Include every time/context override, and reject unbounded charge types.

    Cache partitions are covered by charging every input token at the highest
    prompt/cache rate. Completion covers reasoning tokens as output tokens. A
    Per-request or separate reasoning charges cannot be bounded by these two
    token ceilings. Optional hosted-search/image/audio rates are validated but
    excluded because the relay rejects those modalities and paid hosted tools.
    Unknown pricing keys are rejected so a new charge type cannot slip through.
    """
    if not isinstance(pricing, dict) or not {"prompt", "completion"} <= pricing.keys():
        raise ModelPreparationError("Missing prompt/completion pricing")
    token_keys = {"prompt", "completion", "input_cache_read", "input_cache_write", "input_cache_write_1h"}
    non_token_keys = {"request", "image", "web_search", "internal_reasoning",
                      "audio", "input_audio", "output_audio", "audio_per_second",
                      "input_audio_cache"}
    condition_keys = {"utc_days", "utc_start", "utc_end", "min_tokens", "max_tokens",
                      "min_prompt_tokens", "max_prompt_tokens", "context_length"}
    input_prices: list[Decimal] = []
    output_prices: list[Decimal] = []

    def visit(row: Any, *, override: bool = False) -> None:
        if not isinstance(row, dict):
            raise ModelPreparationError("Malformed pricing override")
        for key, value in row.items():
            if key in token_keys:
                price = _decimal(value, key)
                (output_prices if key == "completion" else input_prices).append(price)
            elif key in non_token_keys:
                price = _decimal(value, key)
                if price != 0 and key in {"request", "internal_reasoning"}:
                    raise ModelPreparationError(f"Non-token {key} charge is unsupported")
            elif key == "discount":
                # Prompt/completion already contain the discounted final rates.
                discount = _decimal(value, key)
                if discount > 1:
                    raise ModelPreparationError("Invalid pricing discount")
            elif key == "overrides":
                if not isinstance(value, list):
                    raise ModelPreparationError("Malformed pricing overrides")
                for nested in value:
                    visit(nested, override=True)
            elif override and key in condition_keys:
                # Conditions never narrow a ceiling: all branches are included.
                continue
            else:
                raise ModelPreparationError(f"Unsupported pricing field: {key}")

    visit(pricing)
    return max(input_prices), max(output_prices)


def fetch_public_json(url: str) -> dict[str, Any]:
    """GET a fixed public metadata URL, without loading any authentication."""
    if url != MODELS_URL and not re.fullmatch(
            rf"https://openrouter[.]ai/api/v1/models/{MODEL_SLUG}/endpoints", url):
        raise ModelPreparationError("Only public OpenRouter metadata URLs are permitted")
    request = Request(url, headers={"Accept": "application/json",
                                   "User-Agent": "lean-e6-public-model-preparation/1"})
    with urlopen(request, timeout=30) as response:
        payload = json.load(response)
    if not isinstance(payload, dict):
        raise ModelPreparationError("Malformed public model metadata")
    return payload


def _reasoning_metadata(row: dict[str, Any]) -> tuple[tuple[str, ...], str]:
    reasoning = row.get("reasoning")
    efforts = reasoning.get("supported_efforts") if isinstance(reasoning, dict) else None
    if (not isinstance(efforts, list) or not efforts
            or any(not isinstance(effort, str) for effort in efforts)
            or len(set(efforts)) != len(efforts)):
        raise ModelPreparationError("Explicit model reasoning metadata is required")
    supported = tuple(effort for effort in CODEX_REASONING_EFFORTS if effort in efforts)
    if not supported or not any(effort != "none" for effort in supported):
        raise ModelPreparationError("Model has no supported Codex reasoning effort")
    # Prefer the experiment's high setting when explicitly supported. Otherwise
    # use an advertised default, never infer a capability or translate efforts.
    default = "high" if "high" in supported else reasoning.get("default_effort")
    if default not in supported:
        raise ModelPreparationError("Model needs a supported explicit default reasoning effort")
    if row.get("id") == TARGET_MODEL and set(efforts) != set(REASONING_EFFORTS):
        raise ModelPreparationError("Pinned DeepSeek reasoning metadata changed")
    return supported, default


def native_model_catalog(settings: Any, output_path: Path | str | None = None) -> dict[str, Any]:
    """Construct a Codex 0.164 catalog using only frozen, offline settings.

    ``settings`` may be the raw JSON mapping or an OpenRouterSettings instance.
    Pinned OpenAI models retain their native instructions, tools and context
    policy. Other models use native JSON shell/MCP calls with a direct tool
    profile. Full Responses is used for the OpenRouter transport in both cases.
    """
    def value(name: str, default: Any = None) -> Any:
        return settings.get(name, default) if isinstance(settings, Mapping) else getattr(settings, name, default)

    model = value("model_id")
    if not isinstance(model, str) or not re.fullmatch(MODEL_SLUG, model):
        raise ModelPreparationError("Native model catalog requires an exact model slug")
    efforts = value("supported_reasoning_efforts")
    default_effort = value("default_reasoning_effort")
    if model == TARGET_MODEL and efforts is None:
        # Retain the original frozen DeepSeek catalog byte identity. Other
        # models must carry explicit metadata in their prepared settings.
        efforts = REASONING_EFFORTS
        default_effort = default_effort or "high"
    if (not isinstance(efforts, (tuple, list)) or not efforts
            or any(not isinstance(effort, str) or effort not in CODEX_REASONING_EFFORTS for effort in efforts)
            or len(set(efforts)) != len(efforts) or default_effort not in efforts):
        raise ModelPreparationError("Native model catalog requires frozen supported/default reasoning efforts")
    context = _positive_int(value("context_length"), "context length")
    display_name = value("model_display_name") or (
        "DeepSeek V4.1 Flash 1017" if model == TARGET_MODEL else model)
    if not isinstance(display_name, str) or not display_name.strip():
        raise ModelPreparationError("Invalid native model display name")
    row = {
        "slug": model,
        "display_name": display_name,
        "description": ("Frozen OpenRouter DeepSeek snapshot with native Codex shell and MCP tools."
                        if model == TARGET_MODEL else "Frozen OpenRouter model with native Codex shell and MCP tools."),
        "default_reasoning_level": default_effort,
        "supported_reasoning_levels": [
            {"effort": effort, "description": f"{effort.capitalize()} reasoning"}
            for effort in efforts],
        "shell_type": "unified_exec",
        "visibility": "list",
        "supported_in_api": True,
        "priority": 1,
        "model_messages": {"instructions_template": BASE_INSTRUCTIONS},
        "include_skills_usage_instructions": False,
        "include_plugin_usage_instructions": False,
        "include_apps_usage_instructions": False,
        "supports_reasoning_summary_parameter": False,
        "default_reasoning_summary": "none",
        "support_verbosity": False,
        "apply_patch_tool_type": None,
        "truncation_policy": {"mode": "tokens", "limit": 10000},
        "context_window": context,
        "max_context_window": context,
        "effective_context_window_percent": 95,
        "experimental_supported_tools": [],
        "input_modalities": ["text"],
        "supports_search_tool": False,
        "supports_experimental_context": False,
        "use_responses_lite": False,
        "supports_reasoning_effort_updates": False,
        "node_repl_disabled": True,
        "tool_mode": "direct",
    }
    if model in PINNED_NATIVE_MODELS:
        # Keep the shipped native Codex 0.164 instruction/tool profile. A renamed
        # OpenRouter slug must not silently replace the benchmark's agent prompt.
        catalog_name, native_slug = PINNED_NATIVE_MODELS[model]
        source = Path(__file__).resolve().parents[2] / "data" / catalog_name
        baseline = json.loads(source.read_text(encoding="utf-8"))
        candidates = [entry for entry in baseline.get("models", []) if entry.get("slug") == native_slug]
        if len(candidates) != 1:
            raise ModelPreparationError("Pinned native model catalog is missing or ambiguous")
        row = copy.deepcopy(candidates[0])
        row["slug"] = model
        row["context_window"] = min(context, row["context_window"])
        row["max_context_window"] = min(context, row["max_context_window"])
        native_efforts = {entry["effort"] for entry in row["supported_reasoning_levels"]}
        if default_effort not in native_efforts:
            raise ModelPreparationError("Requested reasoning effort is absent from the pinned native profile")
        row["supported_reasoning_levels"] = [entry for entry in row["supported_reasoning_levels"] if entry["effort"] in efforts]
        row["default_reasoning_level"] = default_effort
        # OpenRouter's upstream endpoint is full Responses. All other baseline
        # tools/instructions stay intact; Responses-lite is a transport mode.
        row["use_responses_lite"] = False
    result = {"models": [row]}
    if output_path is not None:
        Path(output_path).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return result


def prepare_model(model: str = TARGET_MODEL, provider: str | None = None, *,
                  fetch_json: Callable[[str], dict[str, Any]] | None = None,
                  captured_at: str | None = None,
                  max_output_tokens: int | None = DEFAULT_OUTPUT_TOKENS,
                  budget_usd: str = "3") -> dict[str, Any]:
    """Return ``settings``, native ``catalog``, and public source ``evidence``.

    Models require explicit reasoning, text modality, tools, limits and token
    pricing metadata. All prices are conservative USD per million ceilings for
    one pinned endpoint, including every override regardless of current time.
    """
    if not isinstance(model, str) or not re.fullmatch(MODEL_SLUG, model):
        raise ModelPreparationError("Model must be an exact public catalog slug")
    if provider is None:
        if model != TARGET_MODEL:
            raise ModelPreparationError("An explicit provider endpoint is required for this model")
        provider = DEFAULT_PROVIDER
    if not isinstance(provider, str) or not re.fullmatch(r"[a-z0-9._-]+(?:/[a-z0-9._-]+)*", provider):
        raise ModelPreparationError("Invalid provider endpoint slug")
    output = None if max_output_tokens is None else _positive_int(max_output_tokens, "maximum output tokens")
    budget = _decimal(budget_usd, "budget")
    if budget <= 0 or budget > 3:
        raise ModelPreparationError("Budget must be positive and at most USD 3")
    fetch = fetch_json or fetch_public_json
    models = fetch(MODELS_URL)
    rows = models.get("data")
    if not isinstance(rows, list):
        raise ModelPreparationError("Malformed models catalog")
    matches = [row for row in rows if isinstance(row, dict) and row.get("id") == model]
    if len(matches) != 1:
        raise ModelPreparationError("Exact model ID is unavailable or ambiguous")
    row = matches[0]
    if model == TARGET_MODEL and row.get("canonical_slug") != CANONICAL_MODEL:
        raise ModelPreparationError("Model canonical snapshot changed")
    supported_efforts, default_effort = _reasoning_metadata(row)
    architecture = row.get("architecture")
    if (not isinstance(architecture, dict)
            or not isinstance(architecture.get("input_modalities"), list)
            or "text" not in architecture["input_modalities"]
            or architecture.get("output_modalities") != ["text"]):
        raise ModelPreparationError("Explicit text input and text-only output modalities are required")
    # Native Responses sends reasoning.effort. The separate Chat Completions
    # alias reasoning_effort need not be advertised by this endpoint.
    required_parameters = {"tools", "tool_choice", "reasoning", "max_tokens"}
    model_parameters = row.get("supported_parameters")
    if (not isinstance(model_parameters, list)
            or any(not isinstance(parameter, str) for parameter in model_parameters)
            or not required_parameters <= set(model_parameters)):
        raise ModelPreparationError("Model lacks explicit native tools/reasoning/output limit support")
    # Validate the entire model's advertised charge schema as well as the
    # selected endpoint. Endpoint rates are authoritative for the frozen route.
    _price_ceiling(row.get("pricing"))
    endpoint_url = f"{MODELS_URL}/{model}/endpoints"
    endpoints_payload = fetch(endpoint_url)
    details = endpoints_payload.get("data")
    if not isinstance(details, dict) or details.get("id") != model:
        raise ModelPreparationError("Endpoint model ID changed")
    endpoints = details.get("endpoints")
    if not isinstance(endpoints, list):
        raise ModelPreparationError("Malformed endpoint list")
    # Prefer the requested exact endpoint tag. Provider-name fallback is allowed
    # only if exactly one endpoint has that normalized name; no default model or
    # second provider is silently substituted. Rate ceilings also constrain
    # routing variants (e.g. a provider's publicly offered flex tier).
    matching = [ep for ep in endpoints if isinstance(ep, dict) and ep.get("tag") == provider]
    if not matching:
        normalized = provider.casefold().replace(" ", "-")
        matching = [ep for ep in endpoints if isinstance(ep, dict)
                    and isinstance(ep.get("provider_name"), str)
                    and ep["provider_name"].casefold().replace(" ", "-") == normalized]
    if len(matching) != 1:
        raise ModelPreparationError("Provider must select exactly one advertised endpoint tag or unique provider name")
    provider = matching[0].get("tag")
    if not isinstance(provider, str) or not re.fullmatch(r"[a-z0-9._-]+(?:/[a-z0-9._-]+)*", provider):
        raise ModelPreparationError("Selected endpoint has no valid routing tag")
    endpoint = matching[0]
    if endpoint.get("model_id") != model or endpoint.get("status") != 0:
        raise ModelPreparationError("Selected provider endpoint is unavailable")
    parameters = endpoint.get("supported_parameters")
    choices = endpoint.get("supports_tool_choice")
    if (not isinstance(parameters, list)
            or any(not isinstance(parameter, str) for parameter in parameters)
            or not required_parameters <= set(parameters)
            or not isinstance(choices, dict) or choices.get("auto") is not True):
        raise ModelPreparationError("Selected endpoint lacks native tools/reasoning/output limits")
    context = _positive_int(endpoint.get("context_length"), "endpoint context length")
    model_context = _positive_int(row.get("context_length"), "model context length")
    if context > model_context:
        raise ModelPreparationError("Endpoint context exceeds the verified model context")
    max_completion = _positive_int(endpoint.get("max_completion_tokens"), "endpoint maximum completion tokens")
    if output is None:
        output = min(context, max_completion)
    if output != min(context, max_completion):
        raise ModelPreparationError("Prepared output metadata must equal the endpoint maximum")
    input_price, output_price = _price_ceiling(endpoint.get("pricing"))
    timestamp = captured_at or datetime.now(timezone.utc).isoformat()
    settings = {
        "model_id": model,
        "provider": provider,
        "input_price_per_million": _amount(input_price * MILLION),
        "output_price_per_million": _amount(output_price * MILLION),
        "context_length": context,
        "max_output_tokens": output,
        "budget_usd": _amount(budget),
        "catalog_retrieved_at": timestamp,
        "catalog_source": endpoint_url,
        "supports_parallel_tool_calls": "parallel_tool_calls" in parameters,
    }
    if model != TARGET_MODEL:
        settings.update(supported_reasoning_efforts=list(supported_efforts),
                        default_reasoning_effort=default_effort,
                        model_display_name=row.get("name") or model)
    if model.startswith("anthropic/"):
        settings["automatic_prompt_cache"] = True
    catalog = native_model_catalog(settings)
    if model in PINNED_NATIVE_MODELS:
        settings["supported_reasoning_efforts"] = [entry["effort"] for entry in catalog["models"][0]["supported_reasoning_levels"]]
    routing = {"order": [provider], "only": [provider], "allow_fallbacks": False,
               "require_parameters": True,
               "max_price": {"prompt": settings["input_price_per_million"],
                             "completion": settings["output_price_per_million"],
                             "request": "0", "image": "0"}}
    evidence = {
        "schema_version": 1,
        "retrieved_at": timestamp,
        "sources": {"models": MODELS_URL, "endpoints": endpoint_url,
                    "provider_routing": PROVIDER_ROUTING_SOURCE},
        "model": row,
        "endpoints": details,
        "selected_provider": provider,
        "pricing_policy": "maximum over all base and override token rates; all input/cache partitions use input ceiling; reject request/separate-reasoning charges; optional hosted/multimodal prices excluded because relay prohibits their use",
        "settings": settings,
        "routing": routing,
        "catalog": catalog,
        "native_catalog_target": "codex-cli 0.164.0",
        "native_tool_policy": ("shipped native Codex model instructions/tools, full Responses transport" if model in PINNED_NATIVE_MODELS else "direct JSON native shell and MCP tools; shell editing; no freeform apply_patch or code mode"),
        "input_admission_policy": "run budget_policy selects admission; exact reported charges settle proof ledgers; no local token-cost estimate",
        "output_policy": "run budget_policy selects explicit endpoint output ceiling or legacy native passthrough",
        "prompt_cache_policy": "automatic Anthropic ephemeral cache (default five-minute TTL)" if settings.get("automatic_prompt_cache") else "native provider default",
        "inference_requests": 0,
    }
    return {"settings": settings, "catalog": catalog, "evidence": evidence}


def write_prepared_model(output: Path, prepared: Mapping[str, Any], *,
                         evidence_path: Path | None = None) -> dict[str, str]:
    """Write raw settings and a separate inspectable metadata receipt."""
    output = Path(output)
    evidence_path = Path(evidence_path) if evidence_path is not None else output.with_suffix(".evidence.json")
    if output.resolve() == evidence_path.resolve():
        raise ModelPreparationError("Settings and evidence require different paths")
    output.parent.mkdir(parents=True, exist_ok=True)
    evidence_path.parent.mkdir(parents=True, exist_ok=True)
    settings_bytes = (json.dumps(prepared["settings"], indent=2, ensure_ascii=False) + "\n").encode()
    evidence = dict(prepared["evidence"])
    evidence["settings_sha256"] = hashlib.sha256(settings_bytes).hexdigest()
    output.write_bytes(settings_bytes)
    evidence_path.write_text(json.dumps(evidence, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return {"settings": str(output), "evidence": str(evidence_path),
            "settings_sha256": evidence["settings_sha256"]}


def main(argv=None):
    """Prepare public metadata only; no credentials, inference, or key mutations."""
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", required=True)
    parser.add_argument("--provider", required=True)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--budget", default="3")
    args = parser.parse_args(argv)
    prepared = prepare_model(args.model, args.provider, budget_usd=args.budget)
    result = write_prepared_model(args.output, prepared)
    print(json.dumps(result, sort_keys=True))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
