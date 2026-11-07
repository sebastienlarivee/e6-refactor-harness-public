"""Run the public preparation, native product worker and export with synthetic billing.

Only the host OpenRouter transport constructor is replaced. The real local HTTP
relay, durable SQLite ledger, Codex CLI, Lean broker/MCP tools, host finalizer and
independent export validator all run normally. No external inference is possible
through the finite scripted transport; the fixture key is synthetic and host-only.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from decimal import Decimal
import io
import json
import os
from pathlib import Path
import re
import shlex
import sys
import time
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[2]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from tests.support.verify_product_native import (
    INVALID, ORIGINAL, decoded_objects, host_environment, message, request_tools, require,
    tool_call, tool_inventory,
)

FINAL = "HARNESS_PRODUCT_PIPELINE_COMPLETED"
SHELL = "HARNESS_PRODUCT_ORIGINAL_RESTORED"
KEY = "synthetic-product-pipeline-host-only-credential"
COST = Decimal("0.0001")
MODEL = "openai/gpt-6.1-sol"


def feedback_result(latest, tool):
    """Find a complete tool receipt inside native text/MCP envelopes."""
    results = [value for value in decoded_objects(latest)
        if ("base_source_sha256" in value and "alternatives" in value
            if tool == "compare_candidates" else
            "valid" in value and "source_sha256" in value and "status" in value
            and (tool != "score_candidate" or value.get("tool") == tool))]
    require(results, f"native {tool} omitted its source-bound result")
    return results[-1]


def check_compact_archive(result):
    """Prove native delivery retained a smaller view and its complete raw receipt."""
    import hashlib
    from lean_tools.feedback_response import mcp_response, serialized_bytes
    require(result.get("response_presentation", {}).get("policy") == "compact-v1",
        "native feedback did not use its frozen compact presentation policy")
    path = Path(result["full_response_path"])
    encoded = path.read_bytes()
    require(path.name == hashlib.sha256(encoded).hexdigest() + ".json",
        "compact result did not link its content-addressed full receipt")
    raw = json.loads(encoded)["result"]
    require(json.loads(Path(raw["feedback_request"]["result_path"]).read_text()) == raw,
        "full compact archive differs from the unshortened request journal")
    require(serialized_bytes(mcp_response(result)) < serialized_bytes(mcp_response(raw)),
        "compact native envelope did not shrink")
    require(raw.get("feedback_request", {}).get("request_id") == result.get("feedback_request", {}).get("request_id"),
        "compact native result lost its request binding")
    return {"full_response_path": str(path), "raw_mcp_bytes": serialized_bytes(mcp_response(raw)),
        "compact_mcp_bytes": serialized_bytes(mcp_response(result))}


class Response:
    status = 200
    headers = {"Content-Type": "text/event-stream"}

    def __init__(self, raw, status=200):
        self.source = io.BytesIO(raw)
        self.status = status

    def read(self, size=-1):
        return self.source.read(size)


def charged_result(item, sequence, *, model=MODEL, unpriced=False):
    response = {"id": f"gen-scripted-product-{sequence:04d}", "object": "response",
        "status": "completed", "model": model, "provider": "scripted",
        "output": [item], "usage": {"input_tokens": 10, "output_tokens": 5,
        "total_tokens": 15, "cost": str(COST),
        "input_tokens_details": {"cached_tokens": 0},
        "output_tokens_details": {"reasoning_tokens": 0}}}
    if unpriced:
        response["usage"].pop("cost")
    events = [{"type": "response.created", "response": {**response, "status": "in_progress", "output": []}},
        {"type": "response.output_item.added", "output_index": 0, "item": item},
        {"type": "response.output_item.done", "output_index": 0, "item": item},
        {"type": "response.completed", "response": response}]
    return b"".join(("data: " + json.dumps(event) + "\n\n").encode() for event in events)


class ScriptedTransport:
    """Finite Responses provider substituted only inside the host test process."""

    def __init__(self, cell: Path, key_path: Path, *, model=MODEL, billing_edges=False):
        self.capsule, self.key_path = cell / "pass-001", key_path
        self.calls, self.observations = [], {}
        self.stage = "shell"
        self.model, self.billing_edges = model, billing_edges
        self.rejected_payload = None

    def _feedback_call(self, tools, inventory, name, arguments, sequence):
        native_name = next((value for value in inventory if value == name
            or ("lean_feedback" in value and value.endswith(name))), None)
        if native_name and inventory[native_name] == "function":
            return tool_call(tools, native_name, arguments, sequence)
        require(inventory.get("exec") == "custom", "native code-mode exec tool missing")
        code = 'const tool = ALL_TOOLS.find(t => t.name.includes("lean_feedback") && t.name.endsWith(' + json.dumps(name) + ')); '
        code += 'if (!tool) throw new Error("real Lean feedback MCP absent"); '
        code += "text(await tools[tool.name](" + json.dumps(arguments) + "));"
        return tool_call(tools, "exec", code, sequence, custom=True)

    def _exact_result(self, latest):
        result = feedback_result(latest, "edit_check")
        require(result["valid"] is True and result.get("heartbeat_status") == "exact",
            "native original reconstruction failed real exact Lean checking")
        require(result["source_sha256"] == self.observations["shell"]["source_sha256"],
            "Lean MCP measured different source bytes")
        self.observations["exact"] = result
        self.observations["exact_compact_archive"] = check_compact_archive(result)

    @contextmanager
    def open_response(self, payload, *, api_key, timeout):
        self.observations["last_tool_inventory"] = tool_inventory(request_tools(payload))
        require(api_key == KEY, "worker did not load the explicit synthetic host key")
        require(payload["model"] == self.model, "relay changed the frozen model")
        require(payload["provider"]["only"] == ["scripted"] and payload["provider"]["allow_fallbacks"] is False,
            "relay failed to pin provider routing")
        if self.model.startswith("anthropic/"):
            require(payload.get("cache_control") == {"type": "ephemeral"}, "Anthropic automatic caching was not enabled")
        if self.billing_edges and len(self.calls) == 1:
            require(payload == {**self.rejected_payload, "max_output_tokens": 63129},
                "provider rejection retry changed native history, tools or reasoning")
            self.observations["provider_hint_retry_preserved_payload"] = True
        else:
            require(payload.get("max_output_tokens") == 128000,
                "local-actual-cost relay did not use the frozen endpoint output ceiling")
        require(timeout > 0, "transport timeout must be finite and positive")
        require(len(self.calls) < 16, "unexpected repeated native product requests")
        sequence = len(self.calls) + 1
        tools = request_tools(payload)
        inventory = tool_inventory(tools)
        if sequence == 1:
            initial = json.dumps(payload.get("input", []))
            require("| Verified metric | Measured value | Combined-score contribution |" in initial
                and "Approximate combined-score changes with other metrics fixed" in initial,
                "native initial prompt omitted its verified score brief")
            self.observations["verified_score_brief_in_native_input"] = True
        self.calls.append({"sequence": sequence, "model": payload["model"],
            "max_output_tokens": payload.get("max_output_tokens"), "tool_names": sorted(inventory),
            "synthetic_reported_cost_usd": str(COST)})
        if self.billing_edges and sequence == 1:
            self.rejected_payload = payload
            self.calls[-1]["synthetic_reported_cost_usd"] = "0"
            self.calls[-1]["credit_rejection"] = True
            rejection = {"error": {"code": 402, "message":
                "This request requires more credits, or fewer max_tokens. You requested up to 65536 tokens, "
                "but can only afford 63129. To increase, visit https://openrouter.ai/workspaces/default/keys/abc123 "
                "and adjust the key's total limit", "metadata": {"provider_name": None,
                    "limit_source": "openrouter_key_limit", "remedy_hint": "Review the proof key limit."}}}
            yield Response(json.dumps(rejection).encode(), status=402)
            return
        outputs = [item.get("output", "") for item in payload.get("input", []) if isinstance(item, dict)
            and item.get("type") in {"function_call_output", "custom_tool_call_output"}]
        latest = outputs[-1] if outputs else ""
        wire = latest if isinstance(latest, str) else json.dumps(latest)
        cell = re.search(r"Script running with cell ID\s+([\w-]+)", wire)
        if cell:
            item = tool_call(tools, "wait", {"cell_id": cell[1], "yield_time_ms": 1000,
                "max_tokens": 3000}, sequence)
        elif self.stage == "shell":
            command = ('set -eu; test "${OPENROUTER_API_KEY+x}" != x; '
                'test "${LRH_SERIAL_MODEL_TOKEN+x}" != x; '
                f'test ! -r {shlex.quote(str(self.key_path))}; '
                'test -r Original.lean; cp Original.lean Candidate.lean; '
                f'printf "%s\\n" {shlex.quote(SHELL)}')
            arguments = {"cmd": command, "max_output_tokens": 1000, "yield_time_ms": 1000}
            if inventory.get("exec") == "custom":
                item = tool_call(tools, "exec", "text(await tools.exec_command(" + json.dumps(arguments) + "));",
                    sequence, custom=True)
            else:
                require(inventory.get("exec_command") == "function", "native shell tool missing")
                item = tool_call(tools, "exec_command", arguments, sequence)
            self.stage = "exact"
        elif self.stage == "exact":
            from harness.config import file_hash
            require(SHELL in wire, "native shell failed to restore the supplied original")
            self.observations["shell"] = {"original_restored": True,
                "source_sha256": file_hash(self.capsule / "Candidate.lean")}
            arguments = {"mode": "exact", "expected_sha256": file_hash(self.capsule / "Candidate.lean")}
            item = self._feedback_call(tools, inventory, "edit_check", arguments, sequence)
            self.stage = "compare"
        elif self.stage == "compare":
            self._exact_result(latest)
            arguments = {"expected_sha256": self.observations["shell"]["source_sha256"],
                "alternatives": [{"label": "original", "body": ORIGINAL},
                    {"label": "invalid", "body": INVALID}]}
            item = self._feedback_call(tools, inventory, "compare_candidates", arguments, sequence)
            self.stage = "score"
        elif self.stage == "score":
            from harness.config import file_hash
            result = feedback_result(latest, "compare_candidates")
            require(result["base_source_sha256"] == self.observations["shell"]["source_sha256"],
                "batch comparison used different draft bytes")
            alternatives = {row["label"]: row for row in result["alternatives"]}
            require(set(alternatives) == {"original", "invalid"}, "batch comparison dropped an alternative")
            require(alternatives["original"]["status"] == "valid_scored"
                and alternatives["original"]["compatibility_status"] == "complete"
                and alternatives["original"]["score"] is not None,
                "batch comparison did not completely score the original")
            require(alternatives["invalid"]["valid"] is False and not alternatives["invalid"].get("checkpoint"),
                "invalid batch alternative received a checkpoint")
            require(file_hash(self.capsule / "Candidate.lean") == result["base_source_sha256"],
                "batch comparison mutated the editable draft")
            self.observations["compare_candidates"] = result
            self.observations["compare_compact_archive"] = check_compact_archive(result)
            arguments = {"expected_sha256": result["base_source_sha256"]}
            item = self._feedback_call(tools, inventory, "score_candidate", arguments, sequence)
            self.stage = "final"
        elif self.stage == "final":
            from harness.config import file_hash
            result = feedback_result(latest, "score_candidate")
            require(result["valid"] is True and result["status"] == "valid_scored"
                and result["compatibility_status"] == "complete" and result["score"] is not None,
                "single-candidate tool did not produce a complete advisory score")
            require(result["base_source_sha256"] == file_hash(self.capsule / "Candidate.lean")
                == self.observations["shell"]["source_sha256"], "single-candidate scoring mutated the draft")
            self.observations["score_candidate"] = result
            self.observations["score_compact_archive"] = check_compact_archive(result)
            item = message(FINAL, sequence)
            self.stage = "completed"
        else:
            raise AssertionError("native worker repeated a completed scripted turn")
        unpriced = self.billing_edges and sequence == 2
        if unpriced:
            self.calls[-1]["synthetic_reported_cost_usd"] = None
        yield Response(charged_result(item, sequence, model=self.model, unpriced=unpriced))

    def get_generation(self, *_args, **_kwargs):
        if self.billing_edges:
            return {}  # Missing bill remains unknown even after read-only reconciliation.
        raise AssertionError("complete synthetic usage receipts must not require external reconciliation")


def fixture_config(root, codex, project, elan_home, *, model=MODEL, optimizer="off"):
    """Create a new public-format toy row bound to an existing pinned snapshot."""
    from harness.config import RunConfig, file_hash
    from lean_tools.lean_source import local_proof_tokens
    directory = root / "fixture"
    directory.mkdir()
    stage = json.loads((project / ".lrh-stage.json").read_text())
    revision = stage.get("revision", stage.get("mathlib_revision"))
    requirements = json.loads((REPO / "data/environment-requirements.json").read_text())
    matches = [spec for spec in requirements["snapshots"].values()
        if spec["lean_version"] == stage["lean_version"] and spec["revision"] == revision]
    require(matches and all(spec == matches[0] for spec in matches), "explicit project lacks an unambiguous shipped snapshot identity")
    snapshot = matches[0]
    row = {"name": "harnessProductPipelineSmoke", "header": "import Mathlib.Util.CountHeartbeats\n\n",
        "contexts": [], "signature": "theorem harnessProductPipelineSmoke : True",
        "src": "theorem harnessProductPipelineSmoke : True := " + ORIGINAL,
        "source": "Mathlib", "proof_length": len(local_proof_tokens(ORIGINAL, "arena-v1")),
        "url": snapshot["repository"], "version_info": [{snapshot["lean_version"]: snapshot["revision"]}]}
    benchmark = directory / "original.jsonl"
    benchmark.write_text(json.dumps(row) + "\n")
    heartbeats = directory / "heartbeats.jsonl"
    heartbeats.write_text(json.dumps({"name": row["name"], "heartbeat": 5}) + "\n")
    requirement_path = directory / "requirements.json"
    requirement_path.write_text(json.dumps({"schema_version": 1, "snapshots": {"synthetic": snapshot}, "tasks": {}}, indent=2) + "\n")
    env_map = directory / "environments.toml"
    env_map.write_text('schema_version = 1\nrequirements = "requirements.json"\n'
        f'elan_home = {json.dumps(str(elan_home))}\n[paths]\nsynthetic = {json.dumps(str(project))}\n')
    profile = {"model_id": model, "provider": "scripted", "input_price_per_million": "1",
        "output_price_per_million": "1", "context_length": 1050000, "max_output_tokens": 128000,
        "supported_reasoning_efforts": ["high"], "default_reasoning_effort": "high"}
    if model.startswith("anthropic/"):
        profile["automatic_prompt_cache"] = True
    document = {"schema_version": 1, "input": str(benchmark), "heartbeats": str(heartbeats),
        "env_map": str(env_map), "concurrency": 1, "optimizer": optimizer, "budget_usd": "0.50",
        "diagnostic_max_passes": 1, "runtime": {"codex": str(codex), "elan_home": str(elan_home)},
        "openrouter": profile}
    config_path = directory / "run.json"
    config_path.write_text(json.dumps(document, indent=2) + "\n")
    return RunConfig.from_dict(document), row, {str(path.name): file_hash(path)
        for path in (benchmark, heartbeats, requirement_path, env_map, config_path)}


def verify(root: Path, codex: Path, project: Path, elan_home: Path, runtime_root: Path, *, model=MODEL,
           billing_edges=False, optimizer="off"):
    from harness import runner
    from harness.export import export_run
    from harness.openrouter import relay as relay_module
    from harness.openrouter.ledger import read_openrouter_receipt
    from harness.config import file_hash
    require(not root.exists() or (root.is_dir() and not any(root.iterdir())), "use a fresh empty artifact root")
    require(not root.is_relative_to(REPO), "artifact root must be outside the source checkout")
    root.mkdir(parents=True, exist_ok=True)
    report = {"schema_version": 1, "kind": "scripted-full-product-native-pipeline", "status": "running",
        "root": str(root), "external_inference_calls": 0, "paid_inference_usd": "0",
        "billing_receipts_are_synthetic": True, "account_auth_loaded": False,
        "model": model, "billing_edges": billing_edges, "optimizer": optimizer, "phases": []}
    started = time.monotonic()
    try:
        with host_environment(elan_home, runtime_root):
            config, row, fixture_hashes = fixture_config(root, codex, project, elan_home,
                model=model, optimizer=optimizer)
            report["fixture_hashes"] = fixture_hashes
            spec = config.experiment_spec()
            report["workflow"] = {"policy": config.workflow_policy,
                "prompt_variant": spec.prompt_variant, "response_policy": spec.response_policy,
                "candidate_batches": spec.candidate_batches}
            require(spec.prompt_variant == "control-efficient-v1" and spec.candidate_batches is True,
                "efficient workflow omitted its coupled prompt or batch capability")
            run_root = root / "run"
            snapshot = runner.prepare_run(config, run_root, doctor=True)
            report["phases"].append("public_prepare_with_real_doctor")
            require(len(snapshot["proofs"]) == 1, "synthetic benchmark resolved multiple proofs")
            metadata = snapshot["proofs"][0]
            cell = runner.proof_root(run_root, metadata)
            key = root / "host-only" / "synthetic-inference.key"
            key.parent.mkdir()
            key.write_text(KEY + "\n")
            key.chmod(0o600)
            transport = ScriptedTransport(cell, key, model=model, billing_edges=billing_edges)
            # The constructor patch is the only test seam; production relay and
            # all native subprocesses remain the actual product implementation.
            with patch.object(relay_module, "OpenRouterTransport", lambda: transport):
                code = runner.run_proof(run_root, metadata["label"], credentials=key)
                report["native_calls"] = transport.calls
                report["tool_observations"] = transport.observations
                require(code == 0, f"product worker failed; inspect {cell}")
                require(transport.stage == "completed", "native product turn skipped a scripted stage")
                report["phases"].append("native_compact_exact_batch_score_and_verified_score_brief")
                state = runner.read(cell / "state.json")
                require(state["status"] == "diagnostic_pass_cap" and len(state["passes"]) == 1,
                    "product did not honor the frozen one-pass diagnostic boundary")
                require(state["passes"][0]["validation_healthy"] is True, "host finalization was unhealthy")
                if optimizer == "compact":
                    transaction = runner.read(cell / "optimizer-boundaries/pass-001/transaction.json")
                    require(transaction["stage"] == "committed", "optimizer transaction was not committed")
                    optimization = transaction["report"]
                    require(optimization["model_calls"] == 0 and optimization["cost_usd"] == 0,
                        "deterministic optimizer used inference")
                    require(optimization["effective_budget_seconds"] == 1200,
                        "first optimizer pass did not receive its agreed allowance")
                    require(not optimization["errors"] and optimization["improved"],
                        "real optimizer failed to improve the deliberately redundant toy proof")
                    report["optimizer_report"] = optimization
                    report["phases"].append("real_optimizer_improvement_and_committed_promotion")
                report["phases"].append("real_native_product_worker_and_host_finalize")
                receipt_before = read_openrouter_receipt(cell / "billing/openrouter.sqlite")
                expected_cost = sum((Decimal(call["synthetic_reported_cost_usd"])
                    for call in transport.calls if call["synthetic_reported_cost_usd"] is not None), Decimal(0))
                require(Decimal(receipt_before["budget"]["spent_usd"]) == expected_cost,
                    "durable ledger did not settle every synthetic provider receipt")
                require(not receipt_before["budget"]["active_requests"], "product left unsettled liability")
                require(receipt_before["budget"]["unknown_requests"] == int(billing_edges),
                    "missing receipt was dropped, fabricated as zero, or unexpectedly introduced")
                if billing_edges:
                    require(transport.observations.get("provider_hint_retry_preserved_payload") is True,
                        "missing provider hint retry evidence")
                    report["phases"].append("provider_hint_retry_and_missing_cost_kept_native_context")
                prior_calls = len(transport.calls)
                require(runner.run_proof(run_root, metadata["label"], credentials=key, resume=True) == 0,
                    "completed diagnostic product resume failed")
                receipt_after = read_openrouter_receipt(cell / "billing/openrouter.sqlite")
                require(receipt_before["sha256"] == receipt_after["sha256"] and len(transport.calls) == prior_calls,
                    "resume created a fresh ledger identity, charge or native turn")
                report["phases"].append("resume_preserved_ledger_without_new_inference")
            output = root / "submission.jsonl"
            exported = export_run(run_root, output)
            require(exported["status"] == "exported" and not exported["failures"], "independent product export failed")
            rows = [json.loads(line) for line in output.read_text().splitlines()]
            expected_source = row["src"]
            if optimizer == "compact":
                from lean_tools import arena_workflow as arena
                expected_source, _ = arena.extract_candidate_declaration(row, transaction["output"]["source"])
            require(len(rows) == 1 and rows[0]["name"] == row["name"] and rows[0]["proof"] == expected_source,
                "export omitted the complete verified declaration")
            require(exported["proofs"][0]["selection"] == "verified_incumbent",
                "product export fell back instead of independently validating its incumbent")
            cost = exported["proofs"][0]["cost"]
            require(Decimal(cost["reported_settled_cost_usd"]) == expected_cost,
                "export cost provenance differs from the durable proof ledger")
            require(cost["actual_cost_usd"] is None if billing_edges else Decimal(cost["actual_cost_usd"]) == expected_cost,
                "export presented an incomplete cost total as complete")
            report["phases"].append("independent_real_lean_export_and_cost_provenance")
            for path in run_root.rglob("*"):
                if path.is_file() and not path.is_symlink():
                    require(KEY.encode() not in path.read_bytes(), f"host credential appeared in run artifact {path}")
            report.update(status="passed", run_identity=snapshot["identity"], proof_budget_identity=runner.proof_identity(snapshot, metadata),
                label=metadata["label"], native_calls=transport.calls, tool_observations=transport.observations,
                synthetic_receipt_total_usd=str(expected_cost), ledger_receipt_sha256=receipt_after["sha256"],
                ledger_request_count=len(receipt_after["requests"]), export_report=str(output) + ".report.json",
                submission_sha256=file_hash(output), host_credential_absent_from_run=True)
            return report
    except BaseException as error:
        report.update(status="failed", error={"type": type(error).__name__, "message": str(error)})
        raise
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        (root / "report.json").write_text(json.dumps(report, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("root", "codex", "project", "elan-home", "runtime-root"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--model", default=MODEL, choices=(MODEL, "openai/gpt-6-luna", "openai/gpt-6.1-terra", "anthropic/claude-haiku-5.5"))
    parser.add_argument("--billing-edges", action="store_true",
        help="Inject an uncharged provider output hint and a missing itemized receipt")
    parser.add_argument("--optimizer", choices=("off", "compact"), default="off")
    args = parser.parse_args()
    report = verify(*(path.expanduser().resolve() for path in
        (args.root, args.codex, args.project, args.elan_home, args.runtime_root)),
        model=args.model, billing_edges=args.billing_edges, optimizer=args.optimizer)
    print(json.dumps({key: report[key] for key in
        ("status", "root", "paid_inference_usd", "synthetic_receipt_total_usd", "ledger_request_count", "elapsed_seconds")}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
