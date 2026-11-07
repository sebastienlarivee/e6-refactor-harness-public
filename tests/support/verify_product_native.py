"""Exercise pinned native Codex, HTTP Responses, shell and real Lean MCP offline.

Only a loopback scripted provider and fresh synthetic theorems are used. No
account authentication, model credentials or external inference are loaded.
All environment and executable paths are explicit; provisioned projects stay
read-only inside the same bubblewrap boundary used by production proof passes.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from dataclasses import replace
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import hashlib
import os
from pathlib import Path
import re
import shlex
import signal
import subprocess
import sys
import threading
import time
from typing import Any

REPO = Path(__file__).resolve().parents[2]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

FINAL = "HARNESS_NATIVE_SCRIPTED_COMPLETED"
SHELL = "HARNESS_NATIVE_SHELL_VERIFIED"
SUMMARY = "HARNESS_NATIVE_COMPACTION_SUMMARY"
TOOL = "HARNESS_NATIVE_TOOL_OUTPUT"
ORIGINAL = "by\n  have h : True := True.intro\n  exact h"
CHANGED = "by\n  exact True.intro"
INVALID = "by\n  exact Nat.zero"


def require(value: Any, explanation: str) -> None:
    if not value:
        raise AssertionError(explanation)


def tool_inventory(tools: list[dict]) -> dict[str, str]:
    result = {}
    for tool in tools:
        if tool.get("type") == "namespace":
            result.update(tool_inventory(tool.get("tools", [])))
        elif tool.get("name"):
            result[tool["name"]] = tool.get("type", "")
    return result


def request_tools(payload: dict) -> list[dict]:
    return [*payload.get("tools", []), *(tool for item in payload.get("input", [])
        if isinstance(item, dict) and item.get("type") == "additional_tools"
        for tool in item.get("tools", []))]


def message(text: str, sequence: int) -> dict:
    return {"type": "message", "id": f"msg_scripted_{sequence}", "role": "assistant",
        "status": "completed", "content": [{"type": "output_text", "text": text, "annotations": []}]}


def tool_call(tools: list[dict], name: str, arguments: Any, sequence: int, *, custom=False) -> dict:
    item = {"type": "custom_tool_call" if custom else "function_call", "id": f"item_scripted_{sequence}",
        "call_id": f"call_scripted_{sequence}", "name": name,
        "input" if custom else "arguments": arguments if custom else json.dumps(arguments)}
    namespace = next((tool.get("name") for tool in tools if tool.get("type") == "namespace"
        and any(child.get("name") == name for child in tool.get("tools", []))), None)
    if namespace:
        item["namespace"] = namespace
    return item


def sse_result(item: dict, sequence: int, *, input_tokens=10) -> bytes:
    response = {"id": f"scripted_response_{sequence}", "object": "response", "status": "completed",
        "output": [item], "usage": {"input_tokens": input_tokens, "output_tokens": 5,
        "total_tokens": input_tokens + 5, "input_tokens_details": {"cached_tokens": 0},
        "output_tokens_details": {"reasoning_tokens": 0}}}
    events = [{"type": "response.created", "response": {**response, "status": "in_progress", "output": []}},
        {"type": "response.output_item.added", "output_index": 0, "item": item},
        {"type": "response.output_item.done", "output_index": 0, "item": item},
        {"type": "response.completed", "response": response}]
    return b"".join(("data: " + json.dumps(event) + "\n\n").encode() for event in events)


def decoded_objects(value: Any):
    """Decode MCP results even when the CLI wraps them in text content blocks."""
    if isinstance(value, str):
        decoder = json.JSONDecoder()
        for index, character in enumerate(value):
            if character not in "{[":
                continue
            try:
                decoded, _ = decoder.raw_decode(value[index:])
            except ValueError:
                continue
            yield from decoded_objects(decoded)
    elif isinstance(value, dict):
        yield value
        for child in value.values():
            yield from decoded_objects(child)
    elif isinstance(value, list):
        for child in value:
            yield from decoded_objects(child)


class ScriptedProvider:
    def __init__(self, capsule: Path, forbidden: Path, *, compaction=False):
        self.capsule, self.forbidden, self.compaction = capsule, forbidden, compaction
        self.calls: list[dict] = []
        self.stages = [
            ("shell", None),
            ("changed_quick", {"mode": "quick", "body": CHANGED}),
            ("changed_exact", {"mode": "exact"}),
            ("invalid_quick", {"mode": "quick", "body": INVALID}),
        ]
        self.next_stage, self.pending = 0, None
        self.results: dict[str, dict] = {}
        self.errors: list[str] = []

    def _exec(self, tools, code, sequence):
        require(tool_inventory(tools).get("exec") == "custom", "native code-mode exec tool absent")
        return tool_call(tools, "exec", code, sequence, custom=True)

    def response(self, payload: dict) -> bytes:
        sequence = len(self.calls) + 1
        require(sequence <= 16, "unexpected repeated native provider requests")
        tools = request_tools(payload)
        inventory = tool_inventory(tools)
        inputs = json.dumps(payload.get("input", []))
        outputs = [item.get("output", "") for item in payload.get("input", []) if isinstance(item, dict)
            and item.get("type") in {"function_call_output", "custom_tool_call_output"}]
        latest = outputs[-1] if outputs else ""
        compact = "CONTEXT CHECKPOINT COMPACTION" in inputs
        self.calls.append({"kind": "compaction" if compact else "response", "model": payload.get("model"),
            "reasoning_effort": payload.get("reasoning", {}).get("effort"), "tools": sorted(inventory),
            "tool_output_seen": TOOL in json.dumps(outputs), "summary_seen": SUMMARY in inputs})
        if self.compaction:
            if sequence == 1:
                item = self._exec(tools, f"text({json.dumps(TOOL)});", sequence)
            else:
                item = message(SUMMARY if compact else FINAL, sequence)
            return sse_result(item, sequence, input_tokens=12000 if sequence == 1 else 100)
        if self.pending:
            wire = latest if isinstance(latest, str) else json.dumps(latest)
            cell = re.search(r"Script running with cell ID\s+([\w-]+)", wire)
            if cell:
                return sse_result(tool_call(tools, "wait", {"cell_id": cell[1], "yield_time_ms": 1000,
                    "max_tokens": 3000}, sequence), sequence)
            if self.pending == "shell":
                require(SHELL in wire, "native shell command did not return its marker")
                self.results["shell"] = {"marker_seen": True}
            else:
                results = [value for value in decoded_objects(latest)
                    if "source_sha256" in value and "valid" in value and "status" in value]
                require(results, f"{self.pending} omitted a structured source-bound feedback result: {wire[:1000]}")
                result = results[-1]
                self.results[self.pending] = result
                if self.pending == "invalid_quick":
                    require(result["valid"] is False and not result.get("checkpoint"), "invalid proof produced a checkpoint")
                else:
                    require(result["valid"] is True, f"{self.pending} did not compile successfully: {result}")
                    if self.pending == "changed_exact":
                        require(result.get("heartbeat_status") == "exact" and type(result.get("heartbeat")) is int,
                            "exact MCP feedback omitted measured heartbeats")
            self.pending = None
        if self.next_stage >= len(self.stages):
            return sse_result(message(FINAL, sequence), sequence)
        label, arguments = self.stages[self.next_stage]
        self.next_stage += 1
        self.pending = label
        if label == "shell":
            marker = self.capsule / "shell-marker.txt"
            command = ('set -eu; test "${LRH_SERIAL_MODEL_TOKEN+x}" != x; '
                'test "${OPENAI_API_KEY+x}" != x; test "${OPENROUTER_API_KEY+x}" != x; '
                'test "${LEAN_NUM_THREADS:-}" = 1; test "${OMP_NUM_THREADS:-}" = 1; '
                f'test ! -r {shlex.quote(str(self.forbidden))}; '
                f'printf "%s\\n" {shlex.quote(SHELL)} > {shlex.quote(str(marker))}; cat {shlex.quote(str(marker))}')
            args = {"cmd": command, "max_output_tokens": 1000, "yield_time_ms": 1000}
            item = self._exec(tools, "text(await tools.exec_command(" + json.dumps(args) + "));", sequence)
        else:
            arguments["expected_sha256"] = hashlib.sha256((self.capsule / "Candidate.lean").read_bytes()).hexdigest()
            name = next((name for name in inventory if "lean_feedback" in name and "edit_check" in name), None)
            if name and inventory[name] == "function":
                item = tool_call(tools, name, arguments, sequence)
            else:
                code = 'const tool = ALL_TOOLS.find(t => t.name.includes("lean_feedback") && t.name.endsWith("edit_check")); '
                code += 'if (!tool) throw new Error("real Lean feedback MCP absent"); '
                code += "text(await tools[tool.name](" + json.dumps(arguments) + "));"
                item = self._exec(tools, code, sequence)
        return sse_result(item, sequence)


@contextmanager
def scripted_http(provider: ScriptedProvider):
    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *_args):
            pass

        def do_POST(self):
            try:
                require(self.path == "/v1/responses", "native provider used an unexpected endpoint")
                require(not self.headers.get("Content-Encoding"), "scripted requests must be uncompressed JSON")
                length = int(self.headers["Content-Length"])
                require(0 < length < 16 * 1024 * 1024, "unexpected request size")
                payload = json.loads(self.rfile.read(length))
                body = provider.response(payload)
                self.send_response(200)
                self.send_header("Content-Type", "text/event-stream")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            except Exception as error:
                provider.errors.append(f"{type(error).__name__}: {error}")
                self.send_error(500, "scripted provider assertion failed")

    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        yield f"http://127.0.0.1:{server.server_port}/v1"
    finally:
        server.shutdown()
        thread.join(timeout=5)
        server.server_close()


@contextmanager
def host_environment(elan_home: Path, runtime_root: Path):
    previous = dict(os.environ)
    allowed = {"PATH", "LANG", "LC_ALL", "TERM", "SHELL", "HOME", "CODEX_HOME", "E6_CODEX_HOME",
        "HTTP_PROXY", "HTTPS_PROXY", "ALL_PROXY", "NO_PROXY",
        "http_proxy", "https_proxy", "all_proxy", "no_proxy",
        "PIP_NO_INDEX", "UV_OFFLINE", "HF_HUB_OFFLINE", "TRANSFORMERS_OFFLINE",
        "PYTHONDONTWRITEBYTECODE"}
    clean = {key: value for key, value in previous.items() if key in allowed}
    clean.update(ELAN_HOME=str(elan_home), E6_RUNTIME_ROOT=str(runtime_root),
        PATH=f"{elan_home / 'bin'}:{runtime_root / 'bin'}:/usr/local/bin:/usr/bin:/bin",
        LEAN_NUM_THREADS="1", OMP_NUM_THREADS="1")
    os.environ.clear()
    os.environ.update(clean)
    try:
        yield
    finally:
        os.environ.clear()
        os.environ.update(previous)


def native_pass(root: Path, codex: Path, project: Path, *, compaction=False, timeout_seconds=120) -> dict:
    from e6 import run as runner
    from e6.experiment import DEFAULT_SPEC
    from e6.isolation import wrap_command
    capsule = root / ("compaction-capsule" if compaction else "capsule")
    require(capsule.is_dir(), "synthetic capsule was not prepared")
    forbidden = root / "forbidden-host" / "auth.json"
    forbidden.parent.mkdir(exist_ok=True)
    forbidden.write_text('{"synthetic_auth_sentinel":"forbidden"}\n', encoding="utf-8")
    config = {"codex": str(codex), "primary": str(project), "root": str(root), "compatibility": [],
        "model_catalog": str(REPO / "data/model-catalog.json"),
        "experiment_spec": replace(DEFAULT_SPEC, first_pass_reprove=False, first_pass_reference_rebuild=False).to_dict()}
    provider = ScriptedProvider(capsule, forbidden, compaction=compaction)
    environment = {key: value for key, value in os.environ.items()
        if key in {"PATH", "LANG", "LC_ALL", "TERM", "SHELL", "ELAN_HOME", "LEAN_NUM_THREADS", "OMP_NUM_THREADS"}}
    environment[runner.TOKEN_ENV] = "synthetic-loopback-token-only"
    with scripted_http(provider) as url:
        argv = runner.command(config, capsule, url)
        if compaction:
            argv[-1:-1] = ["-c", "model_auto_compact_token_limit=10000"]
        argv, environment = wrap_command(config, capsule, argv, runner.writable_roots(config, capsule), environment)
        with (root / ("compaction-events.jsonl" if compaction else "native-events.jsonl")).open("w") as output, \
             (root / ("compaction-stderr.log" if compaction else "native-stderr.log")).open("w") as errors:
            process = subprocess.Popen(argv, cwd=capsule, env=environment, stdin=subprocess.PIPE,
                stdout=output, stderr=errors, text=True, start_new_session=True)
            try:
                process.communicate("Execute the local scripted smoke sequence.", timeout=timeout_seconds)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.communicate(timeout=5)
                raise AssertionError("native smoke exceeded its finite wall allowance")
    result = {"returncode": process.returncode, "calls": provider.calls, "results": provider.results,
        "provider_errors": provider.errors, "compaction": compaction}
    (root / ("compaction-result.json" if compaction else "native-result.json")).write_text(json.dumps(result, indent=2) + "\n")
    require(not provider.errors, f"scripted provider rejected requests: {provider.errors}")
    require(process.returncode == 0, f"native Codex failed; see {root}")
    require(provider.calls, "native Codex never contacted the loopback provider")
    require((capsule / "codex-final.txt").read_text().strip() == FINAL, "native turn omitted its final marker")
    require(not (Path(environment["CODEX_HOME"]) / "auth.json").exists(), "native pass created account auth")
    require(all(not set(call["tools"]).intersection({"spawn_agent", "send_message", "wait_agent"})
        for call in provider.calls), "native pass exposed agent delegation")
    if compaction:
        require([call["kind"] for call in provider.calls] == ["response", "compaction", "response"],
            "native local compaction did not use the provider and resume")
        require(provider.calls[1]["tool_output_seen"] and provider.calls[2]["summary_seen"],
            "native compaction lost preceding tool output or its summary")
    else:
        require(set(provider.results) == {name for name, _ in provider.stages}, "native smoke skipped a tool stage")
        require((capsule / "shell-marker.txt").read_text().strip() == SHELL, "native shell marker missing")
    return result


def verify(root: Path, codex: Path, project: Path, elan_home: Path, runtime_root: Path,
           *, compaction=True, timeout_seconds=120) -> dict:
    from lean_tools import arena_workflow as arena, feedback_workflow as feedback
    from lean_tools.evaluation import evaluate_candidate_fresh
    require(not root.exists() or (root.is_dir() and not any(root.iterdir())), "use a fresh empty artifact root")
    require(not root.is_relative_to(REPO), "use an artifact root outside the source tree")
    require((project / "lean-toolchain").is_file() and (project / "lake-manifest.json").is_file(),
        "provide an existing cached Lean project")
    require((elan_home / "bin/elan").is_file(), "provide an existing native ELAN_HOME")
    root.mkdir(parents=True, exist_ok=True)
    report = {"schema_version": 1, "kind": "scripted-native-product-smoke", "status": "running",
        "root": str(root), "project": str(project), "codex": str(codex), "account_auth_loaded": False,
        "external_inference_calls": 0, "paid_inference_usd": "0", "synthetic_usage_only": True,
        "environment_rebuilds": 0, "benchmark_proofs_generated": False}
    started = time.monotonic()
    try:
        with host_environment(elan_home, runtime_root):
            version = subprocess.run([str(codex), "--version"], text=True, capture_output=True, check=True).stdout.strip()
            require(version == "codex-cli 0.164.0", f"expected pinned native Codex 0.164.0, got {version}")
            report["codex_version"] = version
            capsule = root / "capsule"
            capsule.mkdir()
            row = {"name": "harnessNativeSmoke", "header": "import Mathlib.Util.CountHeartbeats\n\n",
                "contexts": [], "signature": "theorem harnessNativeSmoke : True",
                "src": "theorem harnessNativeSmoke : True := " + ORIGINAL}
            task, candidate, registry = capsule / "Task.json", capsule / "Candidate.lean", capsule / "environment-fingerprints.json"
            arena.write_json_atomic(task, {"schema_version": 1, "row": row})
            candidate.write_text(arena.render_candidate_scaffold(row), encoding="utf-8")
            arena.write_environment_fingerprint_registry(row, [project], registry)
            fingerprint = arena.measurement_environment_fingerprint(row, project, registry_path=registry)
            baseline = evaluate_candidate_fresh(task, candidate, project,
                timeout_seconds=timeout_seconds, environment_fingerprint=fingerprint)
            require(baseline.valid and type(baseline.heartbeat) is int, "cached original Lean proof failed")
            feedback.configure_capsule(capsule, project, timeout_seconds)
            report["baseline"] = {"valid": baseline.valid, "heartbeat": baseline.heartbeat,
                "source_sha256": arena.sha256_file(candidate)}
            report["native"] = native_pass(root, codex, project, timeout_seconds=timeout_seconds)
            checked = report["native"]["results"]
            checkpoint = Path(checked["changed_quick"]["checkpoint"])
            require(arena.sha256_file(checkpoint) == checked["changed_quick"]["source_sha256"],
                "native checkpoint bytes differ from the measured source")
            host = evaluate_candidate_fresh(task, checkpoint, project,
                timeout_seconds=timeout_seconds, environment_fingerprint=baseline.environment_fingerprint)
            require(host.valid and type(host.heartbeat) is int, "host remeasurement rejected native checkpoint")
            require(checked["changed_exact"]["source_sha256"] == checked["changed_quick"]["source_sha256"],
                "exact feedback measured a different source")
            require(arena.sha256_file(candidate) == checked["invalid_quick"]["source_sha256"],
                "invalid draft feedback differs from submitted bytes")
            report["host_verified_changed_checkpoint"] = {"valid": host.valid, "heartbeat": host.heartbeat,
                "source_sha256": arena.sha256_file(checkpoint)}
            if compaction:
                (root / "compaction-capsule").mkdir()
                report["compaction"] = native_pass(root, codex, project, compaction=True, timeout_seconds=timeout_seconds)
        report["status"] = "passed"
        return report
    except BaseException as error:
        report.update(status="failed", error={"type": type(error).__name__, "message": str(error)})
        raise
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        (root / "report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--codex", type=Path, required=True)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--elan-home", type=Path, required=True)
    parser.add_argument("--runtime-root", type=Path, required=True)
    parser.add_argument("--without-compaction", action="store_true")
    parser.add_argument("--timeout-seconds", type=int, default=120)
    args = parser.parse_args()
    require(args.timeout_seconds > 0, "timeout-seconds must be positive")
    report = verify(*(path.expanduser().resolve() for path in
        (args.root, args.codex, args.project, args.elan_home, args.runtime_root)),
        compaction=not args.without_compaction, timeout_seconds=args.timeout_seconds)
    print(json.dumps({key: report[key] for key in ("status", "root", "paid_inference_usd", "elapsed_seconds")}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
