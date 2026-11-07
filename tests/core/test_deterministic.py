"""Host deterministic search keeps promotion evidence separate from native health."""
from dataclasses import replace
import os
from pathlib import Path
import signal
import stat
import sys
import time
from types import SimpleNamespace

import pytest

from e6 import deterministic, proof
from e6.experiment import DEFAULT_SPEC
from e6.runtime import scoped_environment
from .test_proof import config, manifest


@pytest.fixture
def search(tmp_path, monkeypatch, manifest):
    settings = config(tmp_path)
    settings.update(replace(DEFAULT_SPEC, deterministic_refactoring=True,
        deterministic_budget_seconds=5, deterministic_max_candidates=8,
        deterministic_rounds=2).proof_settings())
    capsule = tmp_path / "pass-001"
    capsule.mkdir()
    (capsule / "Selected.lean").write_text(settings["initial_best"]["source"])
    proof._write(capsule / "selection.json", {**settings["initial_best"], "validation_healthy": True})
    monkeypatch.setattr(proof.arena, "load_task", lambda _path: ({}, {
        "name": settings["task_id"], "signature": "theorem Task.st : True"}))
    monkeypatch.setattr(proof.arena, "extract_candidate_declaration", lambda _row, source: (source, source))
    state = {"sources": [], "generated": [], "checks": [], "candidates": []}

    def generate(_config, source, _signature, _directory, _deadline, _maximum, records):
        state["generated"].append(source)
        values = state["candidates"](source) if callable(state["candidates"]) else state["candidates"]
        records.append({"generator": "test", "parent_sha256": proof._digest(source), "count": len(values)})
        return [{"id": str(index), "family": "test", "source": value} for index, value in enumerate(values)]

    def check(_config, candidate, project, *, quick=False, timeout_seconds):
        source = candidate.read_text()
        state["checks"].append((source, str(project), quick, timeout_seconds))
        state["sources"].append(source)
        tokens, beats = {"better": (130, 600), "best": (80, 100),
                         "no_gain": (200, 800), "bad": (1, 0), "partial": (1, 0),
                         "same": (200, 800)}.get(source, (200, 800))
        return {"valid": source != "bad" and not (source == "partial" and quick),
                "measurement_mode": "exact", "axiom_status": "measured", "axioms": [],
                "length": {"candidate_tokens": tokens},
                "heartbeat": {"candidate": beats, "local_reference": settings["original_heartbeats"]}}

    def launch(_config, directory, _deadline):
        with scoped_environment(deterministic._environment(_config, directory)), proof._host_validation_cache(_config):
            deterministic._search(_config, deterministic._read(directory / "incumbent-before.json"),
                directory, deterministic._read(directory / "request.json"))
        return {"returncode": 0, "timed_out": False}

    monkeypatch.setattr(deterministic, "_generators", generate)
    monkeypatch.setattr(deterministic, "_launch_worker", launch)
    monkeypatch.setattr(proof, "_check", check)
    return settings, capsule, state, launch


def run_search(search):
    settings, capsule, _, _ = search
    return deterministic.optimize(settings, capsule, settings["initial_best"])


def detailed(capsule):
    return deterministic._read(capsule.parent / "deterministic" / capsule.name / "report.json")


def test_accepts_strict_improvement_after_exact_and_all_versions_without_changing_native_selection(search):
    settings, capsule, state, _ = search
    before = {name: (capsule / name).read_bytes() for name in ("Selected.lean", "selection.json")}
    state["candidates"] = ["better", "better", "bad", "no_gain"]
    best, report = run_search(search)
    assert best["source"] == "better" and best["score"] > settings["initial_best"]["score"]
    proof._verify_incumbent(settings, best)
    assert best["compatibility_complete"] and best["compatibility_pct"] == 100
    assert len(best["compatibility"]) == 1 + len(settings["compatibility"])
    assert report["model_calls"] == report["cost_usd"] == 0
    assert report["evaluated_candidates"] == 3 and report["accepted_candidates"] == 1
    assert [check[2] for check in state["checks"][:3]] == [False, True, True]
    assert all(0 < check[3] <= 5 for check in state["checks"])
    assert all((capsule / name).read_bytes() == original for name, original in before.items())
    assert Path(best["selected_path"]).read_text() == best["source"]
    assert not stat.S_IMODE(Path(best["selected_path"]).stat().st_mode) & 0o222
    receipt = detailed(capsule)
    assert receipt["before"]["sha256"] == settings["initial_best"]["sha256"]
    assert receipt["after"]["sha256"] == best["sha256"]
    assert receipt["selection_before_sha256"] == proof.arena.sha256_file(capsule / "selection.json")
    assert "validation_healthy" not in receipt


def test_contract_accepts_root_precreated_agent_selection_only(search):
    settings, capsule, state, _ = search
    directory = capsule.parent / "deterministic" / capsule.name
    directory.mkdir(parents=True)
    raw = (capsule / "selection.json").read_bytes()
    (directory / "agent-selection.json").write_bytes(raw)
    state["candidates"] = ["better"]
    best, report = run_search(search)
    assert best["source"] == "better" and report["status"] == "completed"
    assert (directory / "agent-selection.json").read_bytes() == raw


@pytest.mark.parametrize("candidate, status", [("bad", "primary_invalid"), ("same", "no_improvement"),
                                               ("partial", "compatibility_failed")])
def test_invalid_equal_and_incompatible_candidates_retain_verified_incumbent(search, candidate, status):
    settings, capsule, state, _ = search
    state["candidates"] = [candidate]
    best, report = run_search(search)
    assert best["source"] == settings["initial_best"]["source"] and not report["improved"]
    assert detailed(capsule)["candidate_records"][0]["status"] == status
    if candidate == "partial":
        # Even an enormous optimistic gain must pass every supplied version.
        assert len(state["checks"]) == 1 + len(settings["compatibility"])


def test_invalid_incumbent_never_generates_or_launches(search, monkeypatch):
    settings, capsule, state, _ = search
    incumbent = {**settings["initial_best"], "sha256": "wrong"}
    monkeypatch.setattr(deterministic, "_launch_worker", lambda *_args: pytest.fail("launched unverified source"))
    best, report = deterministic.optimize(settings, capsule, incumbent)
    assert best == incumbent and report["status"] == "infrastructure_failure"
    assert not state["checks"] and not state["generated"]
    assert not (capsule.parent / "deterministic").exists()


def test_rounds_regenerate_only_from_latest_accepted_source_and_deduplicate_globally(search):
    settings, capsule, state, _ = search
    state["candidates"] = lambda source: ["better", "bad"] if source == "previous" else ["better", "best"]
    best, report = run_search(search)
    assert best["source"] == "best" and state["generated"] == ["previous", "better"]
    assert report["accepted_candidates"] == 2
    assert sum(source == "better" and not quick for source, _, quick, _ in state["checks"]) == 1


def test_no_gain_batches_continue_cached_inventory_and_global_limit(search):
    settings, capsule, state, _ = search
    settings.update(replace(DEFAULT_SPEC, deterministic_refactoring=True,
        deterministic_budget_seconds=5, deterministic_max_candidates=4,
        deterministic_rounds=2).proof_settings())
    state["candidates"] = ["one", "two", "better", "best", "too-late"]
    best, report = run_search(search)
    assert best["source"] == "best"
    assert report["evaluated_candidates"] == 4 and report["rounds_completed"] == 2
    assert state["generated"] == ["previous"] and "too-late" not in state["sources"]


def test_infrastructure_failure_preserves_last_complete_improvement(search, monkeypatch):
    settings, capsule, state, _ = search
    state["candidates"] = ["better", "best"]
    check = proof._check

    def fail_best(*args, **kwargs):
        if args[1].read_text() == "best":
            raise TimeoutError("gate stalled")
        return check(*args, **kwargs)

    monkeypatch.setattr(proof, "_check", fail_best)
    best, report = run_search(search)
    assert best["source"] == "better" and report["accepted_candidates"] == 1
    failures = [item for item in detailed(capsule)["candidate_records"] if item.get("error_kind") == "infrastructure"]
    assert failures and "gate stalled" in failures[0]["error"]["message"]


def test_missing_exact_audit_cannot_promote(search, monkeypatch):
    _, capsule, state, _ = search
    state["candidates"] = ["better"]
    check = proof._check

    def missing_audit(*args, **kwargs):
        result = check(*args, **kwargs)
        result.pop("axiom_status")
        return result

    monkeypatch.setattr(proof, "_check", missing_audit)
    best, report = run_search(search)
    assert best["source"] == "previous" and not report["improved"]
    assert detailed(capsule)["candidate_records"][0]["error_kind"] == "infrastructure"


def test_each_request_has_shorter_optimizer_watchdog_than_native_model_checks(search):
    settings, _, state, _ = search
    settings.update(replace(DEFAULT_SPEC, deterministic_refactoring=True,
        deterministic_budget_seconds=200, deterministic_max_candidates=8,
        deterministic_rounds=2).proof_settings())
    state["candidates"] = ["better"]
    _, report = run_search(search)
    assert {check[3] for check in state["checks"]} == {90}
    assert report["candidate_timeout_seconds"] == 90
    assert settings["check_timeout_seconds"] == DEFAULT_SPEC.check_timeout_seconds


def test_native_control_fallback_is_required_when_primary_reference_is_missing(search, monkeypatch):
    _, _, state, _ = search
    state["candidates"] = ["better"]
    check, calls = proof._check, []

    def absent_reference(*args, **kwargs):
        result = check(*args, **kwargs)
        result["heartbeat"]["local_reference"] = None
        return result

    monkeypatch.setattr(proof, "_check", absent_reference)
    monkeypatch.setattr(proof, "_native_control_evidence", lambda config, row, primary: calls.append(primary) or {"verified": True})
    best, _ = run_search(search)
    assert best["source"] == "better" and calls
    assert best["native_control_evidence"] == {"verified": True}


def test_boundary_is_idempotent_for_original_and_already_promoted_source(search, monkeypatch):
    settings, capsule, state, _ = search
    state["candidates"] = ["better"]
    best, report = run_search(search)
    monkeypatch.setattr(deterministic, "_launch_worker", lambda *_args: pytest.fail("repeated deterministic boundary"))
    repeated, reused = run_search(search)
    assert repeated == best and reused["reused"] and reused["binding_sha256"] == report["binding_sha256"]
    # The host promotion hook may repoint selected_path to its own Selected.lean.
    promoted = {**best, "selected_path": str(capsule / "Selected.lean")}
    repeated, reused = deterministic.optimize(settings, capsule, promoted)
    assert repeated == best and reused["reused"]


def test_mismatched_source_config_or_checkpoint_receipt_cannot_be_reused(search, monkeypatch):
    settings, capsule, state, _ = search
    state["candidates"] = ["better"]
    best, _ = run_search(search)
    monkeypatch.setattr(deterministic, "_launch_worker", lambda *_args: pytest.fail("repeated deterministic boundary"))
    changed = {**settings, "host-note": "different frozen config"}
    retained, report = deterministic.optimize(changed, capsule, settings["initial_best"])
    assert retained["source"] == "previous" and report["status"] == "infrastructure_failure"
    directory = capsule.parent / "deterministic" / capsule.name
    checkpoint = deterministic._read(directory / "checkpoint.json")
    checkpoint["binding_sha256"] = "unbound"
    proof._write(directory / "checkpoint.json", checkpoint)
    retained, report = run_search(search)
    assert retained["source"] == "previous" and report["status"] == "infrastructure_failure"


def test_interrupted_boundary_consumes_checkpoint_instead_of_restarting(search, monkeypatch):
    settings, capsule, state, _ = search
    state["candidates"] = ["better"]
    best, _ = run_search(search)
    directory = capsule.parent / "deterministic" / capsule.name
    (directory / "report.json").unlink()
    monkeypatch.setattr(deterministic, "_launch_worker", lambda *_args: pytest.fail("restarted interrupted boundary"))
    recovered, report = run_search(search)
    assert recovered == best and report["status"] == "interrupted" and report["reused"]


def test_worker_wall_deadline_kills_hung_generator_and_preserves_complete_checkpoint(search, monkeypatch):
    settings, capsule, state, direct_launch = search
    settings.update(replace(DEFAULT_SPEC, deterministic_refactoring=True,
        deterministic_budget_seconds=1, deterministic_max_candidates=8,
        deterministic_rounds=2).proof_settings())
    state["candidates"] = ["better"]
    # The fixture launches the actual worker logic in-process; after it commits
    # a full win, launch an owned sleeping child to exercise the outer watchdog.
    real_launch = _REAL_LAUNCH

    def stall_after_checkpoint(config, directory, deadline):
        direct_launch(config, directory, deadline)
        monkeypatch.setattr(deterministic, "_worker_command", lambda _directory: [
            sys.executable, "-c", "import time; time.sleep(30)"])
        return real_launch(config, directory, deadline)

    monkeypatch.setattr(deterministic, "_launch_worker", stall_after_checkpoint)
    started = time.monotonic()
    best, report = run_search(search)
    assert time.monotonic() - started < 5
    assert best["source"] == "better" and report["status"] == "timed_out"
    assert detailed(capsule)["worker"]["timed_out"]
    assert report["accepted_candidates"] == 1 and report["model_calls"] == 0


_REAL_LAUNCH = deterministic._launch_worker


@pytest.mark.parametrize("interrupt_at", ["wait", "spawn"])
def test_keyboard_interrupt_cleans_registered_worker_before_propagating(search, monkeypatch, interrupt_at):
    settings, capsule, _, _ = search
    directory = capsule.parent / "interrupt-test"
    directory.mkdir()
    events = []

    class Child:
        pid = 123456
        returncode = None

        def poll(self):
            return self.returncode

        def wait(self, **kwargs):
            if self.returncode is None:
                raise KeyboardInterrupt("interrupted during wait")
            return self.returncode

    child = Child()

    def spawn(*args, **kwargs):
        events.append("spawned")
        if interrupt_at == "spawn":
            os.kill(os.getpid(), signal.SIGINT)
        return child

    def terminate(process):
        assert process is child
        events.append("cleaned")
        child.returncode = -9

    monkeypatch.setattr(deterministic.subprocess, "Popen", spawn)
    monkeypatch.setattr(deterministic.process_memory, "capture_process_identity",
                        lambda process: events.append("registered"))
    monkeypatch.setattr(proof.arena, "terminate_process_tree", terminate)
    with pytest.raises(KeyboardInterrupt):
        _REAL_LAUNCH(settings, directory, time.monotonic() + 5)
    assert events == ["spawned", "registered", "cleaned"]


def test_roundrobin_generator_order_and_environment_excludes_credentials(search, monkeypatch):
    settings, capsule, _, _ = search
    from e6 import deterministic_candidates, deterministic_native
    monkeypatch.setattr(deterministic_candidates, "generate", lambda *_args, **_kwargs: [
        {"source": "p1"}, {"source": "p2"}, {"source": "p3"}])
    monkeypatch.setattr(deterministic_native, "generate", lambda *_args, **_kwargs: [
        {"source": "n1"}, {"source": "n2"}])
    records = []
    values = _REAL_GENERATORS(settings, "previous", "signature", capsule.parent / "native-test",
                              time.monotonic() + 5, 8, records)
    assert [item["source"] for item in values] == ["p1", "n1", "p2", "n2", "p3"]
    assert [item["generator"] for item in records] == ["pure", "native"]
    monkeypatch.setenv("OPENAI_API_KEY", "private")
    monkeypatch.setenv("LEAN_REFACTOR_BROKER_TOKEN", "private")
    monkeypatch.setenv("LEAN_REFACTOR_LEAN_GATE", str(capsule.parent / "panel-gate"))
    monkeypatch.setenv("LEAN_NUM_THREADS", "2")
    environment = deterministic._environment(settings, capsule.parent / "deterministic" / capsule.name)
    assert "OPENAI_API_KEY" not in environment and "LEAN_REFACTOR_BROKER_TOKEN" not in environment
    assert environment["LEAN_REFACTOR_LEAN_GATE"].endswith("panel-gate")
    assert environment["LEAN_NUM_THREADS"] == "2"
    assert environment["LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE"] == "request"
    assert environment["LEAN_REFACTOR_EVALUATION_CACHE"].endswith("host-final-validation-cache")


_REAL_GENERATORS = deterministic._generators
