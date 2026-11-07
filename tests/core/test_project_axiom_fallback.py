"""Private-name discovery must audit the artifact that supplied the heartbeat count."""
import json
from pathlib import Path

import pytest

from lean_tools import arena_workflow as arena


@pytest.fixture
def fallback(tmp_path, monkeypatch):
    support = tmp_path / "support"
    support.mkdir()
    monkeypatch.setattr(arena, "evaluation_scratch_parent", lambda: tmp_path)
    monkeypatch.setattr(arena, "project_measurement_helper_lean_args", lambda _: [])
    monkeypatch.setattr(arena, "cached_project_measurement_helper", lambda *_: support)
    monkeypatch.setattr(arena, "project_compile_harness", lambda *_a, **_k: "module\n-- measured original\n")
    monkeypatch.setattr(arena, "project_source_has_module_header", lambda *_: True)
    monkeypatch.setattr(arena, "archive_failed_lean_run", lambda result, *_a, **_k: (result, result.output))
    state = {"probe_heartbeats": 7033, "original_axioms": ["propext"], "probe_axioms": ["Classical.choice"],
        "target": "_private.ArenaProjectMeasured.0.Task.target", "calls": [], "public": False}

    def run(source, _project, _timeout, *, lean_args=None, lean_path_prefixes=()):
        state["calls"].append((source.parent.name, source.name))
        if source.name == "ArenaProjectMeasured.lean":
            artifact = Path(lean_args[lean_args.index("-o") + 1])
            if source.parent.name == "measured":
                assert source.read_text() == "module\n-- measured original\n"
                artifact.write_text(json.dumps({"kind": "original", "axioms": state["original_axioms"]}))
                state.update(measured_source=source, measured_olean=artifact, original_bytes=artifact.read_bytes())
                return arena.LeanRun(["lean", str(source)], 0, 2, "LRH_HEARTBEATS 7032\n", queue_wait_seconds=1)
            assert source.parent.name == "resolve"
            assert artifact != state["measured_olean"]
            assert source.name == state["measured_source"].name
            assert state["measured_olean"].read_bytes() == state["original_bytes"]
            assert state["measured_source"].read_text() == "module\n-- measured original\n"
            artifact.write_text(json.dumps({"kind": "probe", "axioms": state["probe_axioms"]}))
            state["probe_olean"] = artifact
            heartbeat = "" if state["probe_heartbeats"] is None else f"LRH_HEARTBEATS {state['probe_heartbeats']}\n"
            return arena.LeanRun(["lean", str(source)], 0, 3,
                heartbeat + f"LRH_AUDIT_TARGET {state['target']}\n", queue_wait_seconds=2)
        assert source.name == "Audit.lean"
        if state["public"]:
            return arena.LeanRun(["lean", str(source)], 0, 1, "'Task.target' depends on axioms: [propext]")
        if "mkPrivateNameCore" not in source.read_text():
            return arena.LeanRun(["lean", str(source)], 1, 1, "error: unknown constant 'Task.target'")
        imported = next(root / "ArenaProjectMeasured.olean" for root in lean_path_prefixes
            if (root / "ArenaProjectMeasured.olean").exists())
        assert imported == state["measured_olean"]
        assert imported.read_bytes() == state["original_bytes"]
        assert state["probe_olean"].parent not in lean_path_prefixes
        state["audited_kind"] = json.loads(imported.read_text())["kind"]
        if state.get("audit_fails"):
            return arena.LeanRun(["lean", str(source)], 1, 4, "error: original private declaration unavailable")
        axioms = json.loads(imported.read_text())["axioms"]
        return arena.LeanRun(["lean", str(source)], 0, 4,
            f"'{state['target']}' depends on axioms: [{', '.join(axioms)}]")

    monkeypatch.setattr(arena, "run_lean", run)
    return state


def evaluate(tmp_path):
    return arena.evaluate_project_declaration({"name": "Task.target"}, "theorem Task.target : True := by trivial",
        tmp_path, 600, "f" * 64)


@pytest.mark.parametrize("probe_heartbeats", [7032, 7033, 9000, None])
def test_probe_never_replaces_measured_artifact_or_heartbeat(tmp_path, fallback, probe_heartbeats):
    fallback["probe_heartbeats"] = probe_heartbeats
    measured, audit, heartbeat, axioms = evaluate(tmp_path)
    assert heartbeat == 7032 and measured.output == "LRH_HEARTBEATS 7032\n"
    assert Path(measured.command[1]).parent.name == "measured"
    assert measured.seconds == 5 and measured.queue_wait_seconds == 3
    assert audit.seconds == 5
    assert axioms == ["propext"] and fallback["audited_kind"] == "original"
    assert fallback["calls"] == [("measured", "ArenaProjectMeasured.lean"), ("audit", "Audit.lean"),
        ("resolve", "ArenaProjectMeasured.lean"), ("audit", "Audit.lean")]


@pytest.mark.parametrize("axiom", ["sorryAx", "unapprovedAxiom"])
def test_disallowed_original_axioms_fail_even_when_probe_artifact_is_clean(tmp_path, fallback, axiom):
    fallback["original_axioms"] = [axiom]
    fallback["probe_axioms"] = ["propext"]
    with pytest.raises(arena.WorkflowError, match="sorryAx|unexpected axiom"):
        evaluate(tmp_path)
    assert fallback["audited_kind"] == "original"


def test_original_artifact_audit_failure_is_not_ignored(tmp_path, fallback):
    fallback["audit_fails"] = True
    with pytest.raises(arena.LeanCompileError, match="resolved project axiom audit"):
        evaluate(tmp_path)


@pytest.mark.parametrize("target", ["Other.target", "_private.ArenaProjectMeasured.0.Other.target"])
def test_probe_target_must_remain_bound_to_original_declaration(tmp_path, fallback, target):
    fallback["target"] = target
    with pytest.raises(arena.WorkflowError, match="source-bound project axiom target"):
        evaluate(tmp_path)


def test_successful_public_audit_does_not_compile_a_probe(tmp_path, fallback):
    fallback["public"] = True
    measured, audit, heartbeat, axioms = evaluate(tmp_path)
    assert heartbeat == 7032 and measured.seconds == 2 and audit.seconds == 1
    assert axioms == ["propext"]
    assert fallback["calls"] == [("measured", "ArenaProjectMeasured.lean"), ("audit", "Audit.lean")]
