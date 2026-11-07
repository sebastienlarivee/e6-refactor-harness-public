"""Bounded local CLI/model-metadata/MCP checks; never start a model turn or Lean."""
from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import hashlib
import json
import math
import os
import queue
import re
import subprocess
import sys
import tempfile
import threading
import time
from collections.abc import Iterable
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache
from pathlib import Path
from typing import Any

from lean_tools import process_memory
from lean_tools.feedback_contract import TOOL, TOOL_NAME, enabled_tools, tool_catalog


class PreflightError(RuntimeError):
    def __init__(self, message: str, report: dict[str, Any] | None = None) -> None:
        super().__init__(message)
        self.report = report


def remaining(deadline: float) -> float:
    value = deadline - time.monotonic()
    if value <= 0:
        raise PreflightError("Codex preflight deadline expired")
    return value


def offline_environment(config_home: str) -> dict[str, str]:
    """Run metadata and MCP handshakes without host model credentials or config."""
    excluded = {"OPENAI_API_KEY", "OPENROUTER_API_KEY", "LRH_SERIAL_MODEL_TOKEN", "E6_BASELINE_CACHE", "LEAN_E6_BASELINE_CACHE", "LEAN_REFACTOR_SEED_ARCHIVE"}
    environment = {
        key: value for key, value in os.environ.items()
        if key not in excluded and not key.startswith("E6_SEED")
    }
    environment["CODEX_HOME"] = config_home
    return environment


def _run(command: list[str], cwd: Path, deadline: float, *, input_text: str | None = None) -> str:
    try:
        with tempfile.TemporaryDirectory(prefix="e6-codex-metadata-") as config_home:
            result = subprocess.run(
                command, cwd=cwd, input=input_text, capture_output=True, text=True,
                encoding="utf-8", errors="replace", timeout=remaining(deadline), check=False,
                env=offline_environment(config_home),
            )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise PreflightError(f"{Path(command[0]).name} preflight command failed: {error}") from error
    if result.returncode:
        raise PreflightError(f"{Path(command[0]).name} preflight command exited {result.returncode}: {result.stderr[-2000:]}")
    return result.stdout


@lru_cache(maxsize=32)
def _version_cached(path: str, size: int, mtime_ns: int) -> str:
    del size, mtime_ns  # Cache key follows executable replacement.
    output = _run([path, "--version"], Path(path).parent, time.monotonic() + 5)
    return _parse_version(output, path)


def _parse_version(output: str, path: str) -> str:
    match = re.fullmatch(r"codex-cli (\d+\.\d+\.\d+(?:[^\s]*)?)", output.strip())
    if not match:
        raise PreflightError(f"unrecognized Codex version from {path}: {output[:100]!r}")
    return match[1]


def executable_version(path: Path) -> str:
    try:
        stat = path.stat()
    except OSError as error:
        raise PreflightError(f"cannot inspect Codex executable: {path}") from error
    return _version_cached(str(path.resolve()), stat.st_size, stat.st_mtime_ns)


def version_key(value: str) -> tuple[int, int, int, bool]:
    parts = re.match(r"(\d+)\.(\d+)\.(\d+)(.*)", value)
    if parts is None:
        raise PreflightError(f"unrecognized Codex version: {value}")
    return int(parts[1]), int(parts[2]), int(parts[3]), not bool(parts[4])


def select_executable(candidates: Iterable[Path]) -> Path:
    paths = list(dict.fromkeys(path.resolve() for path in candidates if path.is_file()))
    if not paths:
        raise PreflightError("Codex CLI not found among native explicit or PATH locations")

    def inspect(path: Path) -> tuple[Path, str | None]:
        try:
            return path, executable_version(path)
        except PreflightError:
            return path, None

    with ThreadPoolExecutor(max_workers=min(4, len(paths))) as pool:
        verified = [(path, version) for path, version in pool.map(inspect, paths) if version is not None]
    if not verified:
        raise PreflightError("No installed Codex candidate returned a valid --version")
    return max(verified, key=lambda pair: version_key(pair[1]))[0]


def _config_read(command: list[str], capsule: Path, deadline: float) -> dict[str, Any]:
    """App-server lacks ignore-user-config; give only this parser an empty config home."""
    with tempfile.TemporaryDirectory(prefix="lrh-codex-preflight-") as config_home:
        environment = offline_environment(config_home)
        return _config_read_process(command, capsule, deadline, environment)


def _config_read_process(
    command: list[str], capsule: Path, deadline: float, environment: dict[str, str],
) -> dict[str, Any]:
    """Read effective configuration through this CLI's own app-server parser."""
    process = subprocess.Popen(
        command, cwd=capsule, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL, text=True, encoding="utf-8", errors="replace",
        env=environment,
        creationflags=subprocess.CREATE_NEW_PROCESS_GROUP if os.name == "nt" else 0,
        start_new_session=os.name != "nt",
    )
    process_memory.capture_process_identity(process)
    replies: queue.Queue[str | None] = queue.Queue()
    assert process.stdout is not None and process.stdin is not None

    def read() -> None:
        for line in process.stdout:
            replies.put(line)
        replies.put(None)

    reader = threading.Thread(target=read, daemon=True, name="codex-preflight-config")
    reader.start()

    def request(identity: int, method: str, params: dict[str, Any]) -> dict[str, Any]:
        process.stdin.write(json.dumps({"id": identity, "method": method, "params": params}) + "\n")
        process.stdin.flush()
        while True:
            try:
                line = replies.get(timeout=remaining(deadline))
            except queue.Empty as error:
                raise PreflightError("Codex configuration read timed out") from error
            if line is None:
                raise PreflightError("Codex configuration process exited before replying")
            message = json.loads(line)
            if message.get("id") != identity:
                continue
            if "error" in message:
                raise PreflightError(f"Codex {method} rejected configuration: {message['error']}")
            return message["result"]

    try:
        request(1, "initialize", {"clientInfo": {"name": "lean-refactor-preflight", "version": "1"}, "capabilities": {}})
        process.stdin.write('{"method":"initialized","params":{}}\n')
        process.stdin.flush()
        return request(2, "config/read", {"includeLayers": False, "cwd": str(capsule)})
    finally:
        process.stdin.close()
        try:
            process.wait(timeout=min(2, max(0.01, deadline - time.monotonic())))
        except subprocess.TimeoutExpired:
            from lean_tools import arena_workflow as arena
            arena.terminate_process_tree(process)
            process.wait(timeout=2)
        reader.join(timeout=2)
        process.stdout.close()


def _validate_models(catalog: dict[str, Any], requests: Iterable[tuple[str, str]], *,
                     metadata_source: str = "selected_cli_bundled_catalog") -> list[dict[str, Any]]:
    if not isinstance(catalog, dict) or not isinstance(catalog.get("models"), list):
        raise PreflightError("Model catalog must contain a models list")
    models = {}
    for row in catalog["models"]:
        if not isinstance(row, dict) or not isinstance(row.get("slug"), str) or row["slug"] in models:
            raise PreflightError("Model catalog contains malformed or duplicate model metadata")
        models[row["slug"]] = row
    result = []
    for name, effort in sorted(set(requests)):
        row = models.get(name)
        if row is None:
            if metadata_source == "frozen_external_catalog":
                raise PreflightError(f"Frozen external catalog has no metadata for {name}")
            raise PreflightError(f"Selected CLI has no bundled metadata for {name}; choose an installed compatible CLI")
        supported = [value["effort"] for value in row.get("supported_reasoning_levels", [])]
        if effort not in supported:
            raise PreflightError(f"{name} does not list reasoning effort {effort!r}; supported: {supported}")
        result.append({"model": name, "effort": effort, "supported_efforts": supported,
                       "metadata_source": metadata_source})
    return result


def _offline_provider_args(provider: str, model_catalog: Path | None) -> list[str]:
    """Make external metadata/config parsing independent of keys and network."""
    from lean_tools import codex_provider
    if provider == "openrouter":
        if model_catalog is None:
            raise PreflightError("OpenRouter preflight requires a frozen external model catalog")
        return [
            "-c", 'model_provider="openrouter"',
            "-c", 'model_providers.openrouter.name="OpenRouter offline metadata parser"',
            "-c", 'model_providers.openrouter.base_url="http://127.0.0.1:9/v1"',
            "-c", 'model_providers.openrouter.wire_api="responses"',
            "-c", 'model_providers.openrouter.requires_openai_auth=false',
            "-c", 'model_providers.openrouter.supports_websockets=false',
            "-c", "model_catalog_json=" + json.dumps(str(model_catalog)),
        ]
    arguments = codex_provider.codex_config_args(provider) or ["-c", 'model_provider="openai"']
    if model_catalog is not None:
        arguments += ["-c", "model_catalog_json=" + json.dumps(str(model_catalog))]
    return arguments


def _validate_policy(config: dict[str, Any], capsule: Path, settings: dict[str, Any] | None = None) -> dict[str, Any]:
    from lean_tools import feedback_workflow as feedback
    if settings is None:
        path = capsule / feedback.CONFIG_NAME
        settings = json.loads(path.read_text(encoding="utf-8")) if path.is_file() else {}
    allowed = enabled_tools(settings)
    server = config.get("mcp_servers", {}).get("lean_feedback", {})
    policy = server.get("tools", {}).get(TOOL_NAME, {}).get("approval_mode")
    if (server.get("required") is not True or server.get("enabled_tools") != allowed
            or any(server.get("tools", {}).get(name, {}).get("approval_mode") != "approve" for name in allowed)):
        raise PreflightError("CLI did not retain required=true, the configured capsule allowlist, and approval_mode=approve for every enabled tool")
    if server.get("enabled", True) is not True or set(allowed) & set(server.get("disabled_tools") or []):
        raise PreflightError("A configured capsule tool is disabled by effective CLI configuration")
    if Path(server.get("cwd", "")).resolve() != capsule:
        raise PreflightError("CLI feedback server cwd does not match the fresh capsule")
    expected_args = [str(Path(feedback.__file__).resolve()), "--config", str(capsule / feedback.CONFIG_NAME), "--serve"]
    if Path(server.get("command", "")).resolve() != Path(sys.executable).resolve() or server.get("args") != expected_args:
        raise PreflightError("CLI feedback transport is not the expected local capsule server")
    return {"server": "lean_feedback", "enabled_tools": allowed, "required": True,
            "approval_mode": policy, "policy_source": "installed_cli_config_read",
            "scope": "local capsule edit_check only" if allowed == [TOOL_NAME] else "local capsule configured tools only"}


def _validate_stdio(output: str, settings: dict[str, Any] | None = None) -> dict[str, Any]:
    replies = {row["id"]: row for line in output.splitlines() if (row := json.loads(line)).get("id") in {1, 2}}
    if any(identity not in replies or "error" in replies[identity] for identity in (1, 2)):
        raise PreflightError("Local feedback MCP did not complete initialize and tools/list")
    initialized = replies[1]["result"]
    if (initialized.get("protocolVersion") != "2025-06-18"
            or not isinstance(initialized.get("capabilities", {}).get("tools"), dict)
            or initialized.get("serverInfo", {}).get("name") != "lean-feedback"):
        raise PreflightError("Local feedback MCP initialization metadata did not match")
    tools = replies[2]["result"].get("tools", [])
    allowed = enabled_tools(settings)
    if [tool.get("name") for tool in tools] != allowed:
        raise PreflightError(f"Local feedback MCP must advertise exactly {', '.join(allowed)}")
    schemas = {}
    for actual, expected in zip(tools, tool_catalog(settings), strict=True):
        schema = actual.get("inputSchema", {})
        if schema != expected["inputSchema"]:
            raise PreflightError(f"Local {expected['name']} schema does not match its supported contract")
        schemas[expected["name"]] = hashlib.sha256(json.dumps(schema, sort_keys=True).encode()).hexdigest()
    result = {"protocol_version": initialized.get("protocolVersion"), "server_info": initialized.get("serverInfo"),
              "tools": allowed, "schema_sha256": schemas[TOOL_NAME],
              "operations": ["initialize", "tools/list"], "tool_invocations": 0}
    if len(schemas) > 1:
        result["schema_sha256_by_tool"] = schemas
    return result


def preflight(
    codex: Path, models: Iterable[tuple[str, str]], capsule: Path,
    output: Path | None = None, timeout_seconds: float = 30, *, provider: str = "openai",
    model_catalog: Path | None = None,
) -> dict[str, Any]:
    """Call after configure_capsule, before fingerprints, Lean or broker startup."""
    from lean_tools import feedback_workflow as feedback
    if not math.isfinite(timeout_seconds) or timeout_seconds <= 0:
        raise PreflightError("Codex preflight timeout must be finite and positive")
    started = time.monotonic()
    deadline = started + timeout_seconds
    capsule = capsule.resolve()
    codex = codex.resolve()
    report: dict[str, Any] = {"schema_version": 1, "status": "running", "codex": str(codex),
                              "provider": provider, "model_calls": 0, "lean_calls": 0, "stages": {}}
    stage = "version"
    try:
        report["version"] = _parse_version(_run([str(codex), "--version"], capsule, deadline), str(codex))
        report["stages"][stage] = round(time.monotonic() - started, 6)
        stage = "models"
        stage_started = time.monotonic()
        requests = list(models)
        catalog_path = Path(model_catalog).resolve() if model_catalog is not None else None
        provider_arguments = _offline_provider_args(provider, catalog_path)
        if catalog_path is not None:
            catalog_bytes = catalog_path.read_bytes()
            catalog_hash = hashlib.sha256(catalog_bytes).hexdigest()
            # Check the frozen file itself and the selected CLI's parser output.
            # Neither debug models nor config/read starts a model turn.
            _validate_models(json.loads(catalog_bytes), requests,
                             metadata_source="frozen_external_catalog")
            catalog = json.loads(_run([str(codex), *provider_arguments,
                                      "debug", "models"], capsule, deadline))
            if hashlib.sha256(catalog_path.read_bytes()).hexdigest() != catalog_hash:
                raise PreflightError("Frozen external model catalog changed during preflight")
            report["models"] = _validate_models(catalog, requests,
                                                  metadata_source="frozen_external_catalog")
            for model in report["models"]:
                model["catalog_sha256"] = catalog_hash
            report.update(metadata_source="frozen_external_catalog",
                          model_catalog=str(catalog_path), model_catalog_sha256=catalog_hash)
            report["model_access_note"] = "Frozen external metadata and the selected CLI parser verify local model configuration; live provider compatibility remains untested."
        elif provider == "openai":
            catalog = json.loads(_run([str(codex), "debug", "models", "--bundled"], capsule, deadline))
            report["models"] = _validate_models(catalog, requests)
            report["model_access_note"] = "Bundled metadata verifies client support, not live account entitlement or provider availability."
        else:
            report["models"] = [{"model": name, "effort": effort, "metadata_source": "external_provider_unverified"} for name, effort in requests]
            report["model_access_note"] = "External provider model configuration is unverified."
        report["stages"][stage] = round(time.monotonic() - stage_started, 6)
        stage = "cli_config"
        stage_started = time.monotonic()
        arguments = feedback.codex_config_args(capsule)
        if not arguments:
            raise PreflightError("Fresh capsule has no feedback-config.json")
        settings = json.loads((capsule / feedback.CONFIG_NAME).read_text(encoding="utf-8"))
        config = _config_read([
            str(codex), "app-server", "-c", 'approval_policy="never"',
            *provider_arguments, *arguments,
        ], capsule, deadline)
        effective = config.get("config", {})
        if effective.get("approval_policy") != "never" or effective.get("model_provider") != provider:
            raise PreflightError("CLI did not retain the launch approval policy and model provider")
        report["launch_policy"] = {"approval_policy": "never", "model_provider": provider,
                                   "user_config": "absent in isolated temporary parser home; parent environment/config unchanged"}
        report["mcp_policy"] = _validate_policy(effective, capsule, settings)
        report["stages"][stage] = round(time.monotonic() - stage_started, 6)
        stage = "stdio_schema"
        stage_started = time.monotonic()
        server = config["config"]["mcp_servers"]["lean_feedback"]
        messages = [
            {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-06-18", "capabilities": {}, "clientInfo": {"name": "lean-refactor-preflight", "version": "1"}}},
            {"jsonrpc": "2.0", "method": "notifications/initialized", "params": {}},
            {"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}},
        ]
        text = _run([server["command"], *server["args"]], capsule, deadline,
                    input_text="".join(json.dumps(value) + "\n" for value in messages))
        report["mcp_stdio"] = _validate_stdio(text, settings)
        report["stages"][stage] = round(time.monotonic() - stage_started, 6)
        report["status"] = "passed"
    except (PreflightError, OSError, ValueError, KeyError, TypeError) as error:
        report.update(status="failed", failed_stage=stage, error=str(error))
        raise PreflightError(f"Codex preflight failed at {stage}: {error}", report) from error
    finally:
        report["wall_seconds"] = round(time.monotonic() - started, 6)
        if output is not None:
            try:
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
            except OSError as error:
                report["ledger_write_error"] = str(error)
                if report["status"] != "failed":
                    report.update(status="failed", failed_stage="ledger", error=str(error))
                    raise PreflightError(f"Codex preflight report could not be written: {error}", report) from error
    return report
