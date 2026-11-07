"""Opt-in full product integration with real native/Lean edges and synthetic cost."""
import os
from pathlib import Path
import json

import pytest

from tests.support.verify_product_pipeline import KEY, MODEL, ScriptedTransport, fixture_config, verify


@pytest.mark.parametrize("billing_edges", [False, True])
def test_scripted_provider_accepts_endpoint_ceiling_and_preserves_hint_retry(tmp_path, billing_edges):
    transport = ScriptedTransport(tmp_path / "cell", tmp_path / "synthetic.key", billing_edges=billing_edges)
    payload = {"model": MODEL, "provider": {"only": ["scripted"], "allow_fallbacks": False},
        "max_output_tokens": 128000, "tools": [{"type": "custom", "name": "exec"}],
        "input": ["| Verified metric | Measured value | Combined-score contribution |\n"
                  "Approximate combined-score changes with other metrics fixed"]}
    with transport.open_response(payload, api_key=KEY, timeout=1) as response:
        assert response.status == (402 if billing_edges else 200)
    if billing_edges:
        retry = {**payload, "max_output_tokens": 63129}
        with transport.open_response(retry, api_key=KEY, timeout=1) as response:
            assert response.status == 200
        assert transport.observations["provider_hint_retry_preserved_payload"] is True
    assert transport.calls[0]["max_output_tokens"] == 128000


@pytest.mark.parametrize("revision_field", ["revision", "mathlib_revision"])
def test_pipeline_fixture_accepts_cached_snapshot_revision_forms(tmp_path, revision_field):
    requirements = Path(__file__).resolve().parents[1] / "data/environment-requirements.json"
    snapshot = next(spec for spec in json.loads(requirements.read_text())["snapshots"].values()
        if spec["repository"] == "https://github.com/leanprover-community/mathlib4")
    project = tmp_path / "project"
    project.mkdir()
    (project / ".lrh-stage.json").write_text(json.dumps({
        "lean_version": snapshot["lean_version"], revision_field: snapshot["revision"],
    }))
    root = tmp_path / "smoke"
    root.mkdir()
    config, row, _ = fixture_config(root, tmp_path / "codex", project, tmp_path / "elan")
    assert row["version_info"] == [{snapshot["lean_version"]: snapshot["revision"]}]
    assert config.env_map == root / "fixture/environments.toml"
    assert json.loads((root / "fixture/requirements.json").read_text())["snapshots"] == {"synthetic": snapshot}


@pytest.mark.skipif(os.environ.get("HARNESS_RUN_NATIVE_PIPELINE") != "1",
    reason="explicit full product native Codex + cached Lean opt-in")
def test_public_prepare_native_worker_resume_ledger_and_independent_export(tmp_path):
    names = ("HARNESS_SMOKE_CODEX", "HARNESS_SMOKE_PROJECT", "HARNESS_SMOKE_ELAN_HOME", "HARNESS_SMOKE_RUNTIME_ROOT")
    missing = [name for name in names if not os.environ.get(name)]
    if missing:
        pytest.skip("set explicit native paths: " + ", ".join(missing))
    report = verify(tmp_path, *(Path(os.environ[name]).expanduser().resolve() for name in names))
    assert report["status"] == "passed"
    assert report["ledger_request_count"] >= 3
    assert report["external_inference_calls"] == 0
    assert report["host_credential_absent_from_run"] is True
    assert report["workflow"] == {"policy": "efficient-v1", "prompt_variant": "control-efficient-v1",
        "response_policy": "compact-v1", "candidate_batches": True}
    observations = report["tool_observations"]
    assert observations["verified_score_brief_in_native_input"] is True
    assert {"compare_candidates", "score_candidate"} <= observations.keys()
    for name in ("exact_compact_archive", "compare_compact_archive", "score_compact_archive"):
        assert observations[name]["compact_mcp_bytes"] < observations[name]["raw_mcp_bytes"]
