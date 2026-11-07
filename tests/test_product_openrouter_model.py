"""Public metadata profile preparation uses frozen synthetic catalog data."""
from copy import deepcopy
from decimal import Decimal
import json
from pathlib import Path
import pytest
from harness.openrouter import load_openrouter_settings, native_model_catalog, prepare_model
from harness.openrouter.model import MODELS_URL, ModelPreparationError, _price_ceiling

MODEL = "test/snapshot"

def metadata(model=MODEL):
    pricing = {"prompt": "0.000002", "completion": "0.00001", "input_cache_read": "0.0000001",
               "input_cache_write": "0.0000025", "overrides": [{"min_prompt_tokens": 272000, "prompt": "0.000004", "completion": "0.000015", "input_cache_write": "0.000005"}]}
    parameters = ["tools", "tool_choice", "reasoning", "max_tokens"]
    row = {"id": model, "name": "Synthetic model", "reasoning": {"supported_efforts": ["low", "high", "xhigh"], "default_effort": "high"},
           "architecture": {"input_modalities": ["text"], "output_modalities": ["text"]}, "supported_parameters": parameters,
           "context_length": 1050000, "pricing": pricing}
    endpoint = {"tag": "pinned", "model_id": model, "status": 0, "supported_parameters": parameters,
                "supports_tool_choice": {"auto": True}, "context_length": 1050000, "max_completion_tokens": 128000, "pricing": pricing}
    return row, endpoint

def prepared(model=MODEL):
    row, endpoint = metadata(model)
    calls = []
    def fetch(url):
        calls.append(url)
        return {"data": [row]} if url == MODELS_URL else {"data": {"id": model, "endpoints": [endpoint]}}
    return prepare_model(model, "pinned", fetch_json=fetch, budget_usd="1.5"), calls

def test_default_preparation_uses_full_endpoint_maximum_and_tier_cache_write_ceilings():
    result, calls = prepared()
    settings = load_openrouter_settings(result["settings"])
    assert settings.max_output_tokens == 128000
    assert settings.input_price_per_million == Decimal("5")
    assert settings.output_price_per_million == Decimal("15")
    assert settings.budget_usd == Decimal("1.5")
    assert result["evidence"]["native_catalog_target"] == "codex-cli 0.164.0"
    assert result["evidence"]["inference_requests"] == 0
    assert len(calls) == 2
    assert result["catalog"]["models"][0]["tool_mode"] == "direct"

@pytest.mark.parametrize("model,catalog_file", [
    ("openai/gpt-6.1-sol", "model-catalog.json"),
    ("openai/gpt-6-luna", "model-catalog.json"),
    ("openai/gpt-6.1-terra", "model-catalog-terra61.json"),
])
def test_pinned_model_preserves_native_instructions_and_tools_except_transport_and_slug(model, catalog_file):
    result, _ = prepared(model)
    root = Path(__file__).resolve().parents[1]
    baseline = next(row for row in json.loads((root / "data" / catalog_file).read_text())["models"] if row["slug"] == model.removeprefix("openai/"))
    row = result["catalog"]["models"][0]
    assert row["model_messages"] == baseline["model_messages"]
    assert row["tool_mode"] == baseline["tool_mode"]
    assert row["apply_patch_tool_type"] == baseline["apply_patch_tool_type"]
    assert row["slug"] == model
    assert row["context_window"] == baseline["context_window"]
    assert row["max_context_window"] == baseline["max_context_window"]
    assert row["use_responses_lite"] is False

def test_output_maximum_required_no_arbitrary_default():
    result, _ = prepared()
    del result["settings"]["max_output_tokens"]
    with pytest.raises(ValueError):
        load_openrouter_settings(result["settings"])

def test_unknown_price_dimensions_refused():
    for pricing in ({"prompt": "0", "completion": "0", "request": "0.01"},
                    {"prompt": "0", "completion": "0", "unknown_new_charge": "0.01"}):
        with pytest.raises(ModelPreparationError):
            _price_ceiling(pricing)


def test_anthropic_hour_cache_prices_and_automatic_cache_opt_in():
    assert _price_ceiling({"prompt": "0.000004", "completion": "0.000020",
        "input_cache_write": "0.000005", "input_cache_write_1h": "0.000008",
        "overrides": [{"min_prompt_tokens": 100000, "input_cache_write_1h": "0.000010"}]}) == (Decimal("0.000010"), Decimal("0.000020"))
    result, _ = prepared("anthropic/claude-haiku-5.5")
    assert load_openrouter_settings(result["settings"]).automatic_prompt_cache is True
    assert result["settings"]["automatic_prompt_cache"] is True
    assert result["catalog"]["models"][0]["tool_mode"] == "direct"

def test_caps_above_contest_maximum_refused():
    result, _ = prepared()
    result["settings"]["budget_usd"] = "3.01"
    with pytest.raises(ValueError):
        load_openrouter_settings(result["settings"])

def test_native_catalog_optionally_writes_identical_public_json(tmp_path):
    result, _ = prepared()
    target = tmp_path / "catalog.json"
    catalog = native_model_catalog(load_openrouter_settings(result["settings"]), target)
    assert json.loads(target.read_text()) == catalog


def test_optional_hosted_search_price_does_not_block_text_only_sol_profile():
    assert _price_ceiling({"prompt": "0.000002", "completion": "0.00001", "web_search": "0.01", "image": "0.02"}) == (Decimal("0.000002"), Decimal("0.00001"))


def test_exact_provider_tag_wins_over_descendant_variants():
    row, endpoint = metadata()
    variant = deepcopy(endpoint)
    variant["tag"] = "pinned/flex"
    def fetch(url):
        return {"data": [row]} if url == MODELS_URL else {"data": {"id": MODEL, "endpoints": [endpoint, variant]}}
    result = prepare_model(MODEL, "pinned", fetch_json=fetch)
    assert result["settings"]["provider"] == "pinned"


def test_provider_name_resolution_requires_unique_endpoint():
    row, endpoint = metadata()
    endpoint["provider_name"] = "Synthetic Provider"
    def fetch(url):
        return {"data": [row]} if url == MODELS_URL else {"data": {"id": MODEL, "endpoints": [endpoint]}}
    assert prepare_model(MODEL, "synthetic-provider", fetch_json=fetch)["settings"]["provider"] == "pinned"
    duplicate = deepcopy(endpoint)
    duplicate["tag"] = "pinned/flex"
    def ambiguous(url):
        return {"data": [row]} if url == MODELS_URL else {"data": {"id": MODEL, "endpoints": [endpoint, duplicate]}}
    with pytest.raises(ModelPreparationError):
        prepare_model(MODEL, "synthetic-provider", fetch_json=ambiguous)
