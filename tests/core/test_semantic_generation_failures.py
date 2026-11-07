"""Semantic compiler caps survive discovery, compaction and health adapters."""
from dataclasses import replace
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from e6 import deterministic, deterministic_candidates, deterministic_native, proof
from e6.deterministic_support import semantic_search
from e6.experiment import DEFAULT_SPEC


@pytest.fixture
def semantic_flow(tmp_path, monkeypatch):
    signature = "theorem target (p : Prop) (h : p) : p"
    source = signature + " := by exact h"
    task = tmp_path / "Task.json"
    task.write_text(json.dumps({"schema_version": 1, "row": {
        "name": "target", "header": "import Lean\n", "contexts": [],
        "signature": signature, "src": source}}))
    config = {**replace(DEFAULT_SPEC, deterministic_refactoring=True,
                        deterministic_policy="compact").proof_settings(),
              "task": str(task), "primary": str(tmp_path / "project"), "root": str(tmp_path / "run")}
    cleanup = {"id": "cleanup", "family": "test", "source": "cleanup"}
    monkeypatch.setattr(deterministic_candidates, "generate", lambda *a, **k: [cleanup])
    monkeypatch.setattr(deterministic_native, "generate", lambda *a, **k: [])
    monkeypatch.setattr(semantic_search, "configure_native_environment", lambda **k: {})
    monkeypatch.setattr(semantic_search.lean_launch, "workspace_guard", lambda *a: {"compiler": "stub"})
    now = [1000.0]
    monkeypatch.setattr(deterministic.time, "monotonic", lambda: now[0])
    directory = tmp_path / "generation"

    def collect(phase, failure, *, expired=False):
        calls = []

        def run(path, project, deadline, log, **kwargs):
            stage = "helper" if path.name == semantic_search.MODULE_NAME + ".lean" else "capture"
            calls.append(stage)
            if stage == phase:
                if expired:
                    now[0] = 1401.0
                if isinstance(failure, BaseException):
                    raise failure
                log.write_text("compiler diagnostic mentions timeout" if failure == "compiler" else "")
                return {"command": ["lean", str(path)],
                        "returncode": -9 if failure == "timeout" else 1 if failure == "compiler" else 0,
                        "timed_out": failure == "timeout", "seconds": 19.25, "queue_wait_seconds": 2.5}
            Path(kwargs["lean_args"][-1]).write_bytes(b"compiled stub helper")
            return {"returncode": 0, "timed_out": False}

        monkeypatch.setattr(deterministic_native, "_run", run)
        records = []
        candidates = deterministic._generators(config, source, signature, directory, 1400.0, 16, records)
        assert candidates == [cleanup]
        assert calls == (["helper"] if phase == "helper" else ["helper", "capture"])
        receipt = json.loads((directory / "semantic-compact/semantic-search-proposals.json").read_text())
        assert receipt["status"] == "failed" and receipt["candidate_count"] == 0
        assert receipt["partial_candidates_discarded"] is True
        return records[-1], deterministic._compact({"status": "completed", "generator_records": records})

    return collect


@pytest.mark.parametrize("phase", ["helper", "capture"])
@pytest.mark.parametrize("failure,expired,kind", [
    ("timeout", False, "resource_limit"), ("timeout", True, "budget"),
    ("compiler", False, "infrastructure"), ("compiler", True, "infrastructure"),
    ("missing_output", False, "infrastructure"),
])
def test_compiler_result_classification_survives_real_semantic_flow(semantic_flow, phase, failure, expired, kind):
    record, report = semantic_flow(phase, failure, expired=expired)
    assert record["generator"] == "semantic_compact" and record["status"] == "failed"
    assert record["failure_kind"] == kind
    run = record["error"]["lean_run"]
    assert run["timed_out"] is (failure == "timeout")
    assert run["returncode"] == (-9 if failure == "timeout" else 1 if failure == "compiler" else 0)
    assert run["seconds"] == 19.25 and run["queue_wait_seconds"] == 2.5
    assert run["log_path"].endswith("build.log" if phase == "helper" else "semantic-search.log")
    key = {"resource_limit": "generator_resource_limits", "budget": "generator_budget_stops",
           "infrastructure": "generator_failures"}[kind]
    assert report["health_counts"][key] == 1
    assert sum(report["health_counts"][name] for name in (
        "generator_resource_limits", "generator_budget_stops", "generator_failures")) == 1
    assert report["health_status"] == ("degraded" if kind == "infrastructure" else "limited")


@pytest.mark.parametrize("phase", ["helper", "capture"])
@pytest.mark.parametrize("expired", [False, True])
def test_typed_deadline_without_a_run_keeps_timeout_evidence(semantic_flow, phase, expired):
    record, report = semantic_flow(phase, TimeoutError("discovery deadline expired"), expired=expired)
    assert record["failure_kind"] == ("budget" if expired else "resource_limit")
    assert record["error"]["lean_run"]["timed_out"] is True
    assert report["health_counts"]["generator_failures"] == 0


def test_error_without_a_run_remains_infrastructure(semantic_flow):
    record, report = semantic_flow("capture", ValueError("compiler protocol mentions timeout"))
    assert record["failure_kind"] == "infrastructure"
    assert "lean_run" not in record["error"]
    assert report["health_counts"]["generator_failures"] == 1


def test_existing_typed_lean_result_survives_semantic_and_compact_wrappers(semantic_flow):
    result = SimpleNamespace(command=["lean", "capture.lean"], returncode=-9, seconds=21.0,
                             timed_out=True, log_path="capture.log", queue_wait_seconds=3.0)
    record, _ = semantic_flow("capture", proof.arena.LeanTimeoutError("compile watchdog", result))
    assert record["failure_kind"] == "resource_limit"
    assert record["error"]["lean_run"] == {**vars(result), "output_tail": ""}
