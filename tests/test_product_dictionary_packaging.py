"""Dictionary release inputs and offline driver's isolation; no native calls."""
from copy import deepcopy
from pathlib import Path

import pytest

from e6 import proof
from e6.config import REPO_ROOT, source_paths
from e6.deterministic_support import dictionary_cache
from scripts.build_bundle import source_files
from tests.support import verify_product_dictionary as driver


def test_dictionary_runtime_assets_are_in_the_release_and_frozen_identity():
    required = {REPO_ROOT / path for path in (*dictionary_cache.GENERATOR_FILES,
        "e6/deterministic_support/dictionary_search.py")}
    assert required <= set(source_files())
    assert required <= set(source_paths("control-efficient-v1"))
    assert (dictionary_cache.SUPPORT / "DictionaryCensus.lean.inc").is_file()


@pytest.fixture
def seed_input(tmp_path):
    root = tmp_path / "authenticated-input"
    root.mkdir()
    text = "theorem portable : True := by trivial\n"
    (root / "Task.json").write_text('{"row":{"name":"portable"}}\n')
    (root / "environment-fingerprints.json").write_text('{"entries":{}}\n')
    (root / "Original.lean").write_text(text)
    (root / "source-before.lean").write_text(text)
    config = {"label": "portable", "task_id": "portable", "scoring_policy": "legacy-v1",
        "original_tokens": 100, "original_heartbeats": 100, "primary": "/cached/lean-project",
        "compatibility": [], "elan_home": "/cached/elan", "task_sha256": driver.digest(root / "Task.json"),
        "fingerprint_registry_sha256": driver.digest(root / "environment-fingerprints.json")}
    incumbent = {"source": text, "sha256": proof._digest(text), "tokens": 80, "heartbeats": 70,
        "score": proof._policy(config).score(tokens=80, heartbeats=70, compatibility_pct=100),
        "valid": True, "compatibility_complete": True, "compatibility_pct": 100}
    config["initial_best"] = deepcopy(incumbent)
    for name, value in (("config.json", config), ("incumbent-before.json", incumbent),
            ("origin.json", {"source_sha256": incumbent["sha256"]})):
        proof._write(root / name, value)
    return root


def test_driver_projects_only_authenticated_inputs_and_uses_a_new_root(seed_input, tmp_path):
    original_hashes = {path.name: driver.digest(path) for path in seed_input.iterdir()}
    output = tmp_path / "isolated"
    config, seed, capsule = driver.project_seed(seed_input, output)
    assert Path(config["task"]).parent == output
    assert Path(config["fingerprint_registry"]).parent == output
    assert Path(config["canonical_task"]).parent == output
    assert Path(seed["selected_path"]).parent == capsule
    assert config["primary"] == "/cached/lean-project"
    assert config["initial_best"]["proof_metadata_sha256"] == config["proof_metadata_sha256"]
    assert original_hashes == {path.name: driver.digest(path) for path in seed_input.iterdir()}


def test_driver_rejects_a_source_that_lost_its_authentication(seed_input, tmp_path):
    (seed_input / "source-before.lean").write_text("theorem changed : True := by trivial\n")
    output = tmp_path / "isolated"
    with pytest.raises(AssertionError, match="authentication binding"):
        driver.project_seed(seed_input, output)
    assert not output.exists()


def test_driver_refuses_existing_or_overlapping_outputs(seed_input, tmp_path):
    with pytest.raises(AssertionError, match="fresh nonexistent"):
        driver.fresh_output(seed_input, seed_input, [])
    with pytest.raises(AssertionError, match="overlaps"):
        driver.fresh_output(seed_input, seed_input / "run", [])
    with pytest.raises(AssertionError, match="overlaps"):
        driver.fresh_output(seed_input, tmp_path / "project" / "run", [tmp_path / "project"])
    driver.fresh_output(seed_input, tmp_path / "clean-output", [tmp_path / "project"])
