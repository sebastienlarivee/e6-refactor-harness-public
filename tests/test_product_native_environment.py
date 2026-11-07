"""Scripted native validation keeps private paths and offline network settings."""
from pathlib import Path
import os
from unittest.mock import patch

from tests.support.verify_product_native import host_environment


def test_native_helper_preserves_private_offline_environment_and_restores_caller(tmp_path):
    private = tmp_path / "private-home"
    original = {"HOME": str(private), "CODEX_HOME": str(private / ".codex"),
        "E6_CODEX_HOME": str(private / ".codex"),
        "HTTPS_PROXY": "http://127.0.0.1:9", "HTTP_PROXY": "http://127.0.0.1:9",
        "ALL_PROXY": "http://127.0.0.1:9", "NO_PROXY": "127.0.0.1,localhost,::1",
        "PIP_NO_INDEX": "1", "UV_OFFLINE": "1", "PYTHONDONTWRITEBYTECODE": "1",
        "OPENROUTER_API_KEY": "synthetic-inaccessible-key", "UNRELATED_SECRET": "synthetic-secret"}
    with patch.dict(os.environ, original, clear=True):
        with host_environment(Path("/explicit/elan"), Path("/explicit/runtime")):
            assert all(os.environ[name] == value for name, value in original.items()
                       if name not in {"OPENROUTER_API_KEY", "UNRELATED_SECRET"})
            assert "OPENROUTER_API_KEY" not in os.environ and "UNRELATED_SECRET" not in os.environ
            assert os.environ["ELAN_HOME"] == "/explicit/elan"
            assert os.environ["E6_RUNTIME_ROOT"] == "/explicit/runtime"
            assert os.environ["LEAN_NUM_THREADS"] == "1"
            assert not private.exists()
        assert dict(os.environ) == original
