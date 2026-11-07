"""Explicitly enabled real-native/real-Lean offline integration check."""
import os
from pathlib import Path

import pytest

from tests.support.verify_product_native import verify


@pytest.mark.skipif(os.environ.get("HARNESS_RUN_NATIVE_SMOKE") != "1",
    reason="explicit native Codex + cached Lean opt-in")
def test_scripted_native_shell_lean_mcp_and_compaction(tmp_path):
    names = ("HARNESS_SMOKE_CODEX", "HARNESS_SMOKE_PROJECT", "HARNESS_SMOKE_ELAN_HOME", "HARNESS_SMOKE_RUNTIME_ROOT")
    missing = [name for name in names if not os.environ.get(name)]
    if missing:
        pytest.skip("set explicit native paths: " + ", ".join(missing))
    paths = [Path(os.environ[name]).expanduser().resolve() for name in names]
    report = verify(tmp_path, *paths)
    assert report["status"] == "passed"
    assert report["external_inference_calls"] == 0
    assert report["paid_inference_usd"] == "0"
