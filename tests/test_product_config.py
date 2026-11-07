from decimal import Decimal
from pathlib import Path
import pytest
from harness.config import RunConfig, runtime_source_hashes, verify_source_hashes


def profile():
    return {"model_id": "test/model", "provider": "Test", "input_price_per_million": "1",
        "output_price_per_million": "2", "context_length": 10000, "max_output_tokens": 1000,
        "supported_reasoning_efforts": ["high"], "default_reasoning_effort": "high"}


def document():
    return {"benchmark": {"input": "original.jsonl", "heartbeats": "reference.json", "env_map": "environment-map.toml"}, "openrouter": profile()}


def test_public_defaults_preserve_reference_rebuild_and_compact_schedule(tmp_path):
    value = RunConfig.from_dict(document(), base=tmp_path)
    spec = value.experiment_spec()
    assert value.budget_usd == Decimal("3")
    assert value.concurrency == 2 and value.optimizer == "compact"
    assert spec.first_pass_reference_rebuild and not spec.first_pass_reprove
    assert spec.stopping_policy == "cost" and spec.max_passes is None
    assert value.workflow_policy == "efficient-v1"
    assert spec.prompt_variant == "control-efficient-v1"
    assert spec.response_policy == "compact-v1" and spec.candidate_batches
    assert value.to_dict()["workflow_policy"] == "efficient-v1"
    assert spec.deterministic_budget_for_pass(1) == 1200
    assert spec.deterministic_budget_for_pass(2) == 1200
    assert spec.deterministic_budget_for_pass(3) == 300
    assert RunConfig.from_dict(value.to_dict()) == value
    dev = document(); dev["run"] = {"profile": "development", "optimizer": "off", "concurrency": 1}
    dev = RunConfig.from_dict(dev, base=tmp_path)
    assert dev.budget_usd == Decimal("1.5") and not dev.experiment_spec().deterministic_refactoring


@pytest.mark.parametrize("overrides", [{"concurrency": 0}, {"concurrency": 3}, {"concurrency": True},
    {"optimizer": "deep"}, {"budget_usd": "3.01"}, {"budget_usd": "NaN"}, {"budget_usd": "0"},
    {"diagnostic_max_passes": 0}])
def test_invalid_public_policy_fails_before_spend(tmp_path, overrides):
    with pytest.raises(ValueError):
        RunConfig.from_dict(document(), base=tmp_path, **overrides)


def test_credentials_are_rejected_and_all_product_source_is_frozen(tmp_path):
    data = document(); data["openrouter"]["api_key"] = "do-not-freeze"
    with pytest.raises(ValueError, match="host-only"):
        RunConfig.from_dict(data, base=tmp_path)
    sources = runtime_source_hashes()
    assert "harness/runner.py" in sources and "harness/openrouter/relay.py" in sources
    assert "harness/optimizer.py" in sources and "e6/run.py" in sources
    verify_source_hashes(sources)
    sources["harness/runner.py"] = "changed"
    with pytest.raises(RuntimeError, match="Frozen harness source"):
        verify_source_hashes(sources)


def test_toml_paths_are_relative_to_configuration_and_overrides_freeze(tmp_path):
    config = tmp_path / "config.toml"
    config.write_text('''schema_version = 1
[benchmark]
input = "original.jsonl"
heartbeats = "heartbeats.json"
env_map = "environments.toml"
[run]
profile = "development"
[openrouter]
model_id = "test/model"
provider = "Test"
input_price_per_million = "1"
output_price_per_million = "2"
context_length = 10000
max_output_tokens = 1000
supported_reasoning_efforts = ["high"]
default_reasoning_effort = "high"
''')
    value = RunConfig.load(config, concurrency=1, selected_proofs=["proof-a"])
    assert value.input_path == tmp_path / "original.jsonl"
    assert value.selected_proofs == ("proof-a",) and value.concurrency == 1
    assert value.to_dict()["budget_usd"] == "1.5"


def test_profile_reference_embeds_capabilities_and_run_owns_cap_without_resume_read(tmp_path):
    import json
    prepared = profile(); prepared["budget_usd"] = "1.5"
    profile_path = tmp_path / "model.json"; profile_path.write_text(json.dumps(prepared))
    data = document(); data["openrouter"] = {"profile": "model.json", "default_reasoning_effort": "high"}
    data["run"] = {"budget_usd": "3"}
    value = RunConfig.from_dict(data, base=tmp_path)
    assert value.openrouter["budget_usd"] == "3" and value.openrouter["context_length"] == 10000
    assert value.model_profile_source["path"] == str(profile_path)
    frozen = value.to_dict()
    profile_path.unlink()
    assert RunConfig.from_dict(frozen) == value


@pytest.mark.parametrize("section,key,value", [("run", "concurreny", 2), ("runtime", "auth_path", "secret"),
    ("benchmark", "input_typo", "a"), ("run", "profile", "unknown"), ("run", "proofs", "all")])
def test_mistyped_nested_settings_are_not_silently_ignored(tmp_path, section, key, value):
    data = document(); data.setdefault(section, {})[key] = value
    with pytest.raises(ValueError):
        RunConfig.from_dict(data, base=tmp_path)


def test_historical_frozen_workflow_requires_its_original_release(tmp_path):
    frozen = RunConfig.from_dict(document(), base=tmp_path).to_dict()
    frozen.pop("workflow_policy")
    with pytest.raises(ValueError, match="original frozen release"):
        RunConfig.from_frozen_dict(frozen)
    frozen["workflow_policy"] = "legacy-v1"
    with pytest.raises(ValueError, match="original frozen release"):
        RunConfig.from_frozen_dict(frozen)



def test_new_frozen_configuration_keeps_explicit_efficient_policy(tmp_path):
    value = RunConfig.from_dict(document(), base=tmp_path)
    assert RunConfig.from_frozen_dict(value.to_dict()) == value
    data = document(); data["run"] = {"workflow_policy": "efficient-v1"}
    assert RunConfig.from_dict(data, base=tmp_path).workflow_policy == "efficient-v1"



@pytest.mark.parametrize("policy", ["legacy-v1", "efficient", "compact-v1", "", None, True, []])
def test_unknown_workflow_policy_is_rejected_for_fresh_and_frozen_configs(tmp_path, policy):
    data = document(); data["run"] = {"workflow_policy": policy}
    with pytest.raises(ValueError, match="workflow_policy"):
        RunConfig.from_dict(data, base=tmp_path)
    frozen = RunConfig.from_dict(document(), base=tmp_path).to_dict()
    frozen["workflow_policy"] = policy
    with pytest.raises(ValueError, match="workflow_policy"):
        RunConfig.from_frozen_dict(frozen)


def test_only_production_prompt_and_compact_presenter_are_frozen():
    sources = runtime_source_hashes()
    assert "lean_tools/feedback_presentation.py" in sources
    prompts = {name for name in sources if name.startswith("prompts/runtime/")}
    assert len(prompts) == 7
    assert all(name.startswith("prompts/runtime/control-efficient-v1/") for name in prompts)



def test_new_local_budget_policy_and_missing_historical_policy_have_distinct_frozen_identities(tmp_path):
    from harness.config import digest
    value = RunConfig.from_dict(document(), base=tmp_path)
    assert value.budget_policy == value.to_dict()["budget_policy"] == "local-actual-cost-v1"
    assert RunConfig.from_frozen_dict(value.to_dict()) == value
    historical = value.to_dict()
    historical.pop("budget_policy")
    identity = digest(historical)
    old = RunConfig.from_frozen_dict(historical)
    assert old.budget_policy == "provider-key-v1"
    assert digest(old.to_dict()) == identity


@pytest.mark.parametrize("policy", ["", None, True, [], "shared"])
def test_invalid_budget_policy_is_rejected(tmp_path, policy):
    data = document(); data["run"] = {"budget_policy": policy}
    with pytest.raises(ValueError, match="budget_policy"):
        RunConfig.from_dict(data, base=tmp_path)


def test_heartbeat_reference_path_is_optional_and_stays_absent_on_resume(tmp_path):
    data = document()
    data["benchmark"].pop("heartbeats")
    value = RunConfig.from_dict(data, base=tmp_path)
    assert value.heartbeat_path is None
    assert value.to_dict()["heartbeat_path"] is None
    assert RunConfig.from_frozen_dict(value.to_dict()) == value
