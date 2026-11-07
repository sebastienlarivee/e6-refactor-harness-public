from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path


from lean_tools import codex_preflight
from lean_tools import feedback_commands
from lean_tools import feedback_workflow as feedback


def test_shell_fallback_preserves_json_config_and_environment(tmp_path, monkeypatch):
    directory = tmp_path / "space $dollar `tick' quote; $(touch marker)"
    capsule_root = directory / "capsule"
    script_root = directory / "tools"
    capsule_root.mkdir(parents=True)
    script_root.mkdir()
    configuration = feedback.configure_capsule(capsule_root, tmp_path / "project", 120)
    expected = json.loads(configuration.read_text())
    (script_root / "feedback_workflow.py").write_text(
        "import argparse,json,os,sys\n"
        "from pathlib import Path\n"
        "p=argparse.ArgumentParser();p.add_argument('--config',type=Path);a=p.parse_args()\n"
        "print(json.dumps({'request':json.load(sys.stdin),'settings':json.loads(a.config.read_text()),"
        "'broker':os.environ.get('LEAN_REFACTOR_QUICK_BROKER')}))\n"
    )
    monkeypatch.setenv("LEAN_REFACTOR_QUICK_BROKER", "127.0.0.1:43210")
    document = feedback_commands.fallback_document(capsule_root, script_root / "arena_workflow.py", 120)
    commands = re.search(r"```sh\n(.*?)\n```", document, re.DOTALL).group(1).splitlines()
    for mode, command in zip(("quick", "advisory", "exact"), commands, strict=True):
        completed = subprocess.run(["/bin/sh", "-c", command], cwd=tmp_path, text=True, capture_output=True, check=True)
        observed = json.loads(completed.stdout)
        assert observed == {"request": {"mode": mode}, "settings": expected, "broker": "127.0.0.1:43210"}
    assert not (tmp_path / "marker").exists()


def test_offline_preflight_subprocesses_have_no_host_credentials(tmp_path, monkeypatch):
    keys = ("OPENAI_API_KEY", "OPENROUTER_API_KEY", "LRH_SERIAL_MODEL_TOKEN", "E6_BASELINE_CACHE", "E6_SEEDS")
    for key in keys:
        monkeypatch.setenv(key, "host-private-value")
    observed = []

    def run(_command, **kwargs):
        environment = kwargs["env"]
        assert not any(key in environment for key in keys)
        assert Path(environment["CODEX_HOME"]).is_dir()
        observed.append(environment["CODEX_HOME"])
        return subprocess.CompletedProcess(_command, 0, "metadata", "")

    monkeypatch.setattr(codex_preflight.subprocess, "run", run)
    assert codex_preflight._run(["codex", "--version"], tmp_path, codex_preflight.time.monotonic() + 5) == "metadata"
    assert not Path(observed[0]).exists()
    assert all(codex_preflight.os.environ[key] == "host-private-value" for key in keys)
