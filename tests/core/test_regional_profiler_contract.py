from __future__ import annotations

import io
import json
import time

import pytest

from lean_tools import feedback_workflow as feedback
from lean_tools import lean_source, regional_profiler as profiler


@pytest.fixture
def service(tmp_path):
    row = {
        "name": "demo", "header": "import Lean\n\n", "contexts": [],
        "signature": "theorem demo : True",
        "src": "theorem demo : True := by\n  have hα : True := by trivial\n  exact hα",
        "proof_length": 2,
    }
    task = tmp_path / "Task.json"
    task.write_text(json.dumps({"schema_version": 1, "row": row}), encoding="utf-8")
    candidate = tmp_path / "Candidate.lean"
    candidate.write_text(lean_source.render_candidate_scaffold(row), encoding="utf-8")
    return feedback.Feedback({
        "task": str(task), "candidate": str(candidate), "project_root": str(tmp_path),
        "regional_profiler": True,
    })


def test_native_mcp_lists_profiler_field_guidance_and_direct_selector_shape(service):
    output = io.StringIO()
    feedback.serve(service, io.StringIO('{"id":1,"method":"tools/list"}\n'), output)
    tools = json.loads(output.getvalue())["result"]["tools"]
    schema = next(tool for tool in tools if tool["name"] == "profile_proof")["inputSchema"]
    properties = schema["properties"]
    for name in ("expected_sha256", "candidate", "checkpoint_id", "regions"):
        assert properties[name]["description"].strip()
    selector = properties["regions"]["items"]
    for name in ("text", "start_byte", "end_byte"):
        assert selector["properties"][name]["description"].strip()
    assert schema["required"] == ["expected_sha256"]
    assert selector["additionalProperties"] is False
    assert "selector" not in selector["properties"]
    assert selector["oneOf"] == [
        {"required": ["text"]}, {"required": ["start_byte", "end_byte"]},
    ]


def test_profiler_rejects_candidate_and_checkpoint_together():
    request = {"expected_sha256": "a" * 64}
    assert profiler._request(request) == profiler._request({**request, "candidate": "Candidate.lean"})
    assert profiler._request(request) == profiler._request({**request, "checkpoint_id": "saved.lean"})
    with pytest.raises(feedback.arena.WorkflowError, match="omit candidate"):
        profiler._request({**request, "candidate": "Candidate.lean", "checkpoint_id": "saved.lean"})


def test_profile_hash_binds_selected_checkpoint_instead_of_current_draft(service, monkeypatch):
    current = service.candidate.read_bytes()
    checkpoint_source = current.decode("utf-8").replace("exact hα", "exact True.intro")
    checkpoint = service.root / "saved.lean"
    checkpoint.write_text(checkpoint_source, encoding="utf-8")
    monkeypatch.setattr(service, "resolve_checkpoint", lambda _identity: (checkpoint, checkpoint_source, {}))
    current_hash = feedback.arena.sha256_bytes(current)
    checkpoint_hash = feedback.arena.sha256_bytes(checkpoint_source.encode("utf-8"))
    deadline = time.perf_counter() + 10

    assert profiler._freeze(service, {"expected_sha256": current_hash}, deadline) == (
        current, current.decode("utf-8"), service.candidate, "current",
    )
    selected = {"checkpoint_id": checkpoint.name, "expected_sha256": checkpoint_hash}
    assert profiler._freeze(service, selected, deadline) == (
        checkpoint_source.encode("utf-8"), checkpoint_source, checkpoint, "checkpoint",
    )
    with pytest.raises(feedback.EditRequestError) as conflict:
        profiler._freeze(service, {**selected, "expected_sha256": current_hash}, deadline)
    assert conflict.value.details["code"] == "source_conflict"
    assert conflict.value.details["selected_source_sha256"] == checkpoint_hash
    assert conflict.value.details["current_candidate_sha256"] == current_hash
    assert service.candidate.read_bytes() == current


def test_menu_selectors_are_direct_full_source_utf8_spans(service):
    source = service.candidate.read_text(encoding="utf-8")
    raw = source.encode("utf-8")
    tactic = "exact hα"
    start = raw.index(tactic.encode("utf-8"))
    end = start + len(tactic.encode("utf-8"))
    assert start != source.index(tactic)  # Earlier Unicode makes character offsets differ.
    prefix = b"instrumentation\n"
    output = "\n".join(json.dumps({"data": message}) for message in (
        f"token MENU {start + len(prefix)} {end + len(prefix)} 0",
        "token MENU_STATE false 1",
    ))
    menu = profiler._region_menu(output, "token", len(prefix), raw, prefix + raw)
    assert menu["source_sha256"] == feedback.arena.sha256_bytes(raw)
    selector = menu["regions"][0]["selector"]
    candidate = lean_source.snapshot_candidate(service.row, source, service.candidate)
    selected = profiler._selections({"regions": [selector]}, source, candidate)
    assert selected[0]["start_byte"] == start
    assert selected[0]["end_byte"] == end
    with pytest.raises(feedback.arena.WorkflowError, match="directly into regions"):
        profiler._selections({"regions": [{"selector": selector}]}, source, candidate)
    with pytest.raises(feedback.arena.WorkflowError, match="UTF-8 character boundaries"):
        profiler._selections({"regions": [{**selector, "end_byte": end - 1}]}, source, candidate)


def _events(*messages):
    return "\n".join(json.dumps({"data": "token " + message}) for message in messages)


def test_repeated_nested_regions_keep_observed_totals_and_singletons_without_remainder():
    raw = b"outer(inner) sibling"
    regions = [{"id": "outer"}, {"id": "inner"}, {"id": "sibling"}]
    result = profiler._region_results(_events(
        "MATCH 0 0 12", "MATCH 1 6 11", "MATCH 2 13 20",
        "REGION inner 3 30", "REGION outer 10 100", "REGION inner 5 50",
        "REGION outer 20 200", "REGION sibling 7 70", "COMMAND 100 1000",
    ), "token", regions, 0, raw, raw)
    assert result["complete"] is result["accounting_complete"] is False
    assert result["measurement_outcome"] == "repeated_region_events"
    assert result["unattributed"] is None
    assert result["useful_region_observations"] == ["outer", "inner", "sibling"]
    outer, inner, singleton = result["regions"]
    assert inner["parent_id"] == "outer"
    assert outer["observed_completed_invocations"] == 2
    assert outer["observed_raw_heartbeats"] == {"total": 30, "min": 10, "max": 20}
    assert outer["observed_elapsed_nanoseconds"] == {"total": 300, "min": 100, "max": 200}
    assert outer["raw_heartbeats"] == 30
    assert outer["elapsed_nanoseconds"] == 300
    assert singleton["observed_completed_invocations"] == 1
    assert singleton["observed_raw_heartbeats"] == {"total": 7, "min": 7, "max": 7}
    assert singleton["original_span"]["mapping_confidence"] == "exact_original_parsed_syntax"
    assert result["declaration_command"]["raw_heartbeats"] == 100
    assert "backtracking" in result["observation_semantics"]
    assert "no claim" in result["accounting_scope"]


def test_missing_completion_is_unknown_not_zero_and_retains_successful_sibling():
    raw = b"first second"
    result = profiler._region_results(_events(
        "MATCH 0 0 5", "MATCH 1 6 12", "REGION first 0 0", "COMMAND 10 100",
    ), "token", [{"id": "first"}, {"id": "second"}], 0, raw, raw)
    assert result["complete"] is result["accounting_complete"] is False
    assert result["unattributed"] is None
    assert result["missing_regions"] == ["second"]
    assert result["useful_region_observations"] == ["first"]
    assert result["regions"][0]["observed_raw_heartbeats"] == {"total": 0, "min": 0, "max": 0}
    second = result["regions"][1]
    assert second["observed_completed_invocations"] == 0
    assert second["observed_raw_heartbeats"] == {"total": None, "min": None, "max": None}
    assert second["raw_heartbeats"] is None


@pytest.mark.parametrize("command,complete", [("COMMAND 20 200", True), ("COMMAND 2 20", False)])
def test_singletons_keep_existing_containment_checks(command, complete):
    raw = b"tactic"
    result = profiler._region_results(_events(
        "MATCH 0 0 6", "REGION selected 5 50", command,
    ), "token", [{"id": "selected"}], 0, raw, raw)
    assert result["complete"] is result["accounting_complete"] is complete
    assert result["regions"][0]["raw_heartbeats"] == 5
    assert (result["unattributed"] is not None) is complete
    if complete:
        assert result["unattributed"]["raw_heartbeats"] == 15
    else:
        assert result["measurement_outcome"] == "containment_mismatch"


@pytest.mark.parametrize("event", ["REGION selected -1 2", "REGION selected 2 -1", "COMMAND -1 2"])
def test_negative_observations_are_rejected(event):
    with pytest.raises(ValueError, match="negative"):
        profiler._region_results(_events("MATCH 0 0 6", event), "token", [{"id": "selected"}], 0, b"tactic", b"tactic")


@pytest.mark.parametrize("profile_timeout", [False, True])
def test_profile_retains_observations_but_never_complete_after_timeout(service, monkeypatch, profile_timeout):
    source = service.candidate.read_text(encoding="utf-8")
    original = source.encode("utf-8")
    start = original.index(b"exact h")
    end = start + len("exact hα".encode("utf-8"))
    selected = {"id": "selected", "start_byte": start, "end_byte": end}
    launch = profiler.lean_launch.LaunchEnvironment("/cached/lean", {}, {"guard_hash": "guard", "toolchain": "cached", "status": "hit"})
    monkeypatch.setattr(profiler, "_prepare_launch", lambda *_: launch)
    monkeypatch.setattr(profiler, "_compiler_identity", lambda *_: {})
    monkeypatch.setattr(profiler, "_cache_evidence", lambda *_: None)
    token_seen = []

    def instrument(_prefix, _declaration, _candidate, _regions, token):
        token_seen.append(token)
        return source, 0

    def run(*_args, purpose, **_kwargs):
        output = ""
        if purpose == "profile":
            messages = [f"MATCH 0 {start} {end}", "REGION selected 2 20"]
            if not profile_timeout:
                messages.append("REGION selected 4 40")
            output = _events(*messages, "COMMAND 20 200")
            output = output.replace("token ", token_seen[0] + " ")
        return feedback.arena.LeanRun(["fake"], 0, .01, output, timed_out=profile_timeout and purpose == "profile")

    monkeypatch.setattr(profiler, "_instrument", instrument)
    monkeypatch.setattr(profiler, "_run", run)
    result = profiler.profile_proof(service, {"expected_sha256": profiler._sha(original), "regions": [selected]})
    assert result["status"] == ("timeout" if profile_timeout else "partial")
    assert result["outcome"] == ("profile_timeout" if profile_timeout else "repeated_region_events")
    assert result["authoritative"] is False
    assert result["valid"] is True
    assert result["complete"] is result["accounting_complete"] is False
    assert result["unattributed"] is None
    assert result["regions"][0]["observed_completed_invocations"] == (1 if profile_timeout else 2)
    if profile_timeout:
        assert result["measurement_outcome"] == "profile_process_incomplete"
        assert result["declaration_command"]["inclusive"] is False
    assert service.candidate.read_bytes() == original
    assert "score" not in result


def test_native_parse_budget_is_independent_of_process_budget_and_reported_in_capability(service):
    parsing = profiler.native_wall_time.DEFAULT_MAX_PARSE_SECONDS
    for process_budget in (1, 30):
        regional = profiler._budgets(process_budget, 30, "regions")
        native = profiler._budgets(process_budget, 30, "wall_time")
        assert regional["native_parse_seconds"] == 0
        assert native["native_parse_seconds"] == parsing
        assert native["pre_parse_stage_seconds"] == regional["total_stage_seconds"]
        assert native["total_stage_seconds"] == regional["total_stage_seconds"] + parsing
        assert native["profile_process_seconds"] == native["source_validation_process_seconds"] == process_budget
    capability = profiler.profiler_capability(service.row, service.project)
    assert capability["native_parse_seconds"] == parsing
    assert capability["max_default_stage_seconds_by_mode"] == {"regions": 100, "wall_time": 100 + parsing}
    assert capability["max_default_stage_seconds"] == 100 + parsing


def test_native_parsing_has_a_separate_reported_stage(service, monkeypatch):
    launch = profiler.lean_launch.LaunchEnvironment("/cached/lean", {}, {})
    monkeypatch.setattr(profiler, "_prepare_launch", lambda *_: launch)
    monkeypatch.setattr(profiler, "_compiler_identity", lambda *_: {})
    monkeypatch.setattr(profiler, "_cache_evidence", lambda *_: None)

    def run(path, *_args, purpose, **_kwargs):
        if purpose == "profile":
            (path.parent / "native-wall-time.json").write_text("{}")
        return feedback.arena.LeanRun(["fake"], 0, .01, "")

    parsed = []

    def parse(path, top_n):
        parsed.append((path, top_n))
        return {"complete": True, "hotspots": []}

    monkeypatch.setattr(profiler, "_run", run)
    monkeypatch.setattr(profiler, "_wall_time", parse)
    result = profiler.profile_proof(service, {"expected_sha256": profiler._sha(service.candidate.read_bytes()), "mode": "wall_time"})
    assert result["status"] == "profiled"
    assert len(parsed) == 1
    assert result["budgets"]["native_parse_seconds"] == profiler.native_wall_time.DEFAULT_MAX_PARSE_SECONDS
    timings = result["timings"]
    assert "native_parse" in timings["stage_wall_seconds"]
    assert timings["native_parse_seconds"] == timings["stage_wall_seconds"]["native_parse"]
    assert timings["source_validation_process_seconds"] == timings["profile_process_seconds"] == .01


@pytest.mark.parametrize("prefix", ["import Lean\nnamespace Demo\n", "module\nimport Lean\nset_option maxRecDepth 100 in\n"])
def test_native_trace_options_are_scoped_to_candidate_and_prefix_is_exact(prefix, tmp_path):
    declaration = "theorem candidate : True := by exact True.intro"
    profile_path = tmp_path / "native.json"
    source, arguments = profiler._native_instrument(prefix, declaration, profile_path)
    assert source.startswith(prefix)
    assert source[len(prefix):] == "\nset_option Elab.async false in\nset_option trace.profiler true in\n" + declaration + "\n"
    assert "-Dtrace.profiler=true" not in arguments
    assert "-Dtrace.profiler.threshold=0" in arguments
    assert "-Dtrace.profiler.output=" + str(profile_path) in arguments
    if prefix.startswith("module"):
        assert source.startswith("module\n")
