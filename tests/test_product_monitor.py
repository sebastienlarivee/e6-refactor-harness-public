"""Operator snapshots distinguish proof completion from a usable submission."""
import hashlib
import json
import os
from pathlib import Path

import pytest

from scripts import monitor


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value))


@pytest.fixture
def run(tmp_path):
    root = tmp_path / "run"
    snapshot = {"identity": "frozen", "config": {"budget_usd": "2.90",
        "openrouter": {"model_id": "openai/gpt-6.1-sol", "default_reasoning_effort": "high"}},
        "proofs": [{"label": "proof-a1b2c3", "task_id": "Nat.example_theorem"}]}
    state = {"status": "completed", "elapsed_seconds": 12}
    write(root / "resolved-config.json", snapshot)
    write(root / "state.json", state)
    write(root / "proofs/proof-a1b2c3/state.json", {"status": "budget_reached", "passes": [],
        "budget": {"spent_usd": "2.90", "limit_usd": "2.90", "unknown_requests": 0,
                   "cost_reporting_complete": True}})
    return root, snapshot, state


def export_report(root, snapshot, *, name="submission.jsonl", **overrides):
    output = root / name
    output.write_text('{"name":"Nat.example_theorem","proof":"theorem example : True := by trivial"}\n')
    report = {"status": "exported", "roots": [str(root)], "run_identities": [snapshot["identity"]],
        "output": str(output), "output_sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
        "failures": [], "cost_status": "settled_or_not_started", **overrides}
    write(Path(str(output) + ".report.json"), report)
    return output


def test_completed_proofs_without_export_are_pending_and_names_are_readable(run, capsys):
    root, _, _ = run
    before = {path: (path.read_bytes(), path.stat().st_mtime_ns) for path in root.rglob("*") if path.is_file()}
    assert monitor.main(["--root", str(root)]) == 0
    text = capsys.readouterr().out
    assert "proofs completed; export pending" in text
    assert "Nat.example_theorem" in text and "proof-a1b2c3" not in text
    assert "Retry export without inference:" in text
    assert before == {path: (path.read_bytes(), path.stat().st_mtime_ns) for path in root.rglob("*") if path.is_file()}


def test_live_export_and_abandoned_export_have_distinct_status(run, monkeypatch):
    root, snapshot, state = run
    write(root / "submission-status.json", {"run_identity": snapshot["identity"], "status": "exporting",
        "pid": os.getpid(), "process_start_tick": 123})
    monkeypatch.setattr(monitor, "process_start_tick", lambda _: 123)
    assert monitor.submission_status(root, snapshot, state)[0] == "exporting"
    monkeypatch.setattr(monitor, "process_start_tick", lambda _: 456)  # Reused PID is not the exporter.
    phase, messages = monitor.submission_status(root, snapshot, state)
    assert phase == "export interrupted"
    assert any("Retry export without inference:" in line for line in messages)


def test_failed_export_is_reported_and_manual_fresh_export_restores_readiness(run, capsys):
    root, snapshot, _ = run
    write(root / "submission-status.json", {"run_identity": snapshot["identity"], "status": "export_failed",
        "error": "compiler failed"})
    write(root / "submission.jsonl.report.json", {"roots": [str(root)], "status": "failed", "error": "compiler failed"})
    monitor.main(["--root", str(root)])
    failed = capsys.readouterr().out
    assert "export failed" in failed and "compiler failed" in failed
    output = export_report(root, snapshot, name="submission-retry.jsonl", status="exported_with_failures",
        failures=[{"stage": "incumbent"}], cost_status="unresolved")
    monitor.main(["--root", str(root)])
    ready = capsys.readouterr().out
    assert "submission ready" in ready and str(output) in ready
    assert "review original fallbacks" in ready and "Export cost status: unresolved" in ready
    assert "Retry export without inference:" not in ready


def test_missing_or_changed_artifact_is_never_ready(run):
    root, snapshot, state = run
    output = export_report(root, snapshot)
    output.write_text("changed after export")
    assert monitor.submission_status(root, snapshot, state)[0] == "export incomplete"
    output.unlink()
    assert monitor.submission_status(root, snapshot, state)[0] == "export incomplete"


def test_export_report_from_different_run_cannot_claim_readiness(run):
    root, snapshot, state = run
    export_report(root, snapshot, run_identities=["other-run"])
    assert monitor.submission_status(root, snapshot, state)[0] == "proofs completed; export pending"


@pytest.mark.parametrize(("total", "completed"), [(60, 12), (4, 1)])
def test_preflight_counts_completed_receipts_for_selected_proofs(tmp_path, capsys, total, completed):
    proofs = [{"label": f"proof-{index}", "task_id": f"example_{index}"} for index in range(total)]
    write(tmp_path / "benchmark/benchmark.json", {"row_count": 60, "proofs": proofs})
    for proof in proofs[:completed]:
        write(tmp_path / "baselines" / f"{proof['label']}.json", {
            **proof, "kind": "per-run-original-baseline", "evidence": {"status": "passed"},
        })
    malformed = proofs[completed]["label"]
    (tmp_path / "baselines" / f"{malformed}.json").write_text('{"kind":')
    incomplete = proofs[completed + 1]
    write(tmp_path / "baselines" / f"{incomplete['label']}.json", {
        **incomplete, "kind": "per-run-original-baseline",
    })
    write(tmp_path / "baselines/proof-other.json", {
        "label": "proof-other", "task_id": "other", "kind": "per-run-original-baseline",
        "evidence": {"status": "passed"},
    })

    assert monitor.main(["--root", str(tmp_path)]) == 1
    assert f"Original proofs checked: {completed}/{total}" in capsys.readouterr().out


def test_preflight_without_resolved_proof_selection_has_generic_status(tmp_path, capsys):
    assert monitor.main(["--root", str(tmp_path)]) == 1
    text = capsys.readouterr().out
    assert "No frozen run snapshot yet" in text
    assert "Original proofs checked" not in text


def test_failed_preflight_and_root_recovery_errors_are_visible(tmp_path, run, capsys):
    root = tmp_path / "failed-preflight"
    write(root / "benchmark/benchmark.json", {
        "proofs": [{"label": "proof-a1b2c3", "task_id": "Nat.example_theorem"}],
    })
    write(root / "doctor.json", {"status": "failed"})
    assert monitor.main(["--root", str(root)]) == 1
    text = capsys.readouterr().out
    assert "Preflight failed" in text and "fresh --output directory; --resume is unavailable" in text
    assert "Original proofs checked: 0/1" in text
    root, _, state = run
    state.update(status="needs_attention", recovery_error={"message": "Automatic receipt recovery failed"},
                 worker_returncodes={"proof-a1b2c3": 1})
    write(root / "state.json", state)
    monitor.main(["--root", str(root)])
    text = capsys.readouterr().out
    assert "Automatic receipt recovery failed" in text
    assert "Nat.example_theorem: worker exited with code 1" in text
