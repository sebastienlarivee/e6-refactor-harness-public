"""Presentation-only prefix provenance checks; no Lean process or inference."""
from __future__ import annotations

import copy
from dataclasses import replace
import hashlib
import json
from pathlib import Path

import pytest

from lean_tools import diagnostic_presentation as diagnostics
from lean_tools import feedback_presentation as presentation
from lean_tools import feedback_response as response
from lean_tools import feedback_workflow as workflow
from tests.core.test_feedback_transport_integration import service


def _warning(line=0, message=None, **extra):
    return {"severity": "warning", "line": line, "character": 0,
            "message": message or "unused variable `prefix`\n" + "prefix explanation 🙂 " * 80, **extra}


def _fixture(tmp_path, raw=None, *, prefix=None, candidate_source=None, declaration=None):
    prefix = prefix if prefix is not None else "-- frozen prefix 🙂\n" * 16
    declaration = declaration or "theorem candidate : True := by\n  trivial"
    candidate_source = candidate_source or declaration + "\n"
    candidate = candidate_source.encode("utf-8")
    digest = hashlib.sha256(candidate).hexdigest()
    snapshot = tmp_path / ".feedback" / "sources" / (digest + ".lean")
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    snapshot.write_bytes(candidate)
    generated = prefix + declaration + "\n"
    source_map = diagnostics.SourceMap.for_declaration(candidate_source, generated, declaration)
    raw = raw if raw is not None else [_warning(line) for line in range(12)]
    shown = diagnostics.present_diagnostics(raw, source_map, source=generated)
    artifact = diagnostics.archive_diagnostics(raw, shown, source=generated, candidate_path=snapshot,
                                               candidate_bytes=candidate, source_map=source_map)
    result = {"schema_version": 1, "mode": "quick", "status": "invalid", "valid": False,
              "source_sha256": digest, "snapshot_path": str(snapshot), "diagnostics_path": str(artifact),
              **{key: shown[key] for key in ("diagnostics", "diagnostics_compacted", "diagnostics_truncation")},
              "tokens": 5, "heartbeat": None, "goals": "h : True\n⊢ True",
              "goal_handles": [{"goal_id": "g", "goal": {"line": 1, "column": 1, "index": 0}}]}
    context = presentation.ImmutablePrefixContext(digest, candidate_source, declaration, prefix,
                                                  "project-source-prefix")
    return result, context


def _present(raw, context, tmp_path):
    return presentation.present_result(raw, artifact_dir=tmp_path / "responses", policy="compact-v1",
                                       tool="edit_check", prefix_context=context)


def _rewrite_artifact(raw, mutate):
    old = Path(raw["diagnostics_path"])
    artifact = json.loads(old.read_bytes())
    mutate(artifact)
    encoded = (json.dumps(artifact, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    path = old.with_name(raw["source_sha256"] + "-" + hashlib.sha256(encoded).hexdigest() + ".json")
    path.write_bytes(encoded)
    raw["diagnostics_path"] = str(path)


def test_true_prefix_groups_have_explicit_counts_bound_provenance_and_exact_archive(tmp_path):
    raw, context = _fixture(tmp_path)
    before = copy.deepcopy(raw)
    artifact_bytes = Path(raw["diagnostics_path"]).read_bytes()
    compact = _present(raw, context, tmp_path)
    assert compact["diagnostics"] == []
    summary = compact["response_presentation"]["immutable_prefix_warnings"]
    assert summary["diagnostic_groups"] == 1
    assert summary["warning_occurrences"] == 12  # Includes all four locations omitted inline.
    assert summary["prefix_kind"] == "project-source-prefix"
    assert summary["prefix_sha256"] == hashlib.sha256(context.prefix_text.encode()).hexdigest()
    assert summary["generated_source_sha256"] == json.loads(artifact_bytes)["generated_source_sha256"]
    assert "full_response_path" in summary["full_text"] and "diagnostics_path" in summary["full_text"]
    assert raw == before and Path(raw["diagnostics_path"]).read_bytes() == artifact_bytes
    archived = json.loads(Path(compact["full_response_path"]).read_bytes())
    assert archived == {"schema_version": 1, "result": before}
    assert archived["result"]["diagnostics"][0]["message"] == before["diagnostics"][0]["message"]
    for key in ("valid", "status", "source_sha256", "tokens", "heartbeat", "goals", "goal_handles"):
        assert compact[key] == raw[key]
    for wrap in (lambda value: value, response.mcp_response):
        assert response.serialized_bytes(wrap(compact)) < response.serialized_bytes(wrap(raw))
    assert _present(compact, context, tmp_path) is compact
    assert _present(raw, context, tmp_path) == compact
    assert len(list((tmp_path / "responses").iterdir())) == 1


def test_candidate_warnings_errors_prefix_errors_information_and_actions_stay_exact(tmp_path):
    raw_diagnostics = [*_fixture_raw_prefix(),
        _warning(16, "candidate warning " + "candidate detail " * 100),
        {**_warning(16), "severity": "error", "message": "candidate error"},
        {**_warning(0), "severity": "error", "message": "prefix error"},
        {**_warning(1), "severity": "information", "message": "prefix information"},
        _warning(2, "Try this: exact h")]
    raw, context = _fixture(tmp_path, raw_diagnostics)
    compact = _present(raw, context, tmp_path)
    expected = [item for item in raw["diagnostics"] if item.get("warning_family") != "unused-variable"]
    assert compact["diagnostics"] == expected
    assert compact["valid"] is False and compact["goals"] == raw["goals"]


def _fixture_raw_prefix():
    return [_warning(0), _warning(1)]


@pytest.mark.parametrize("unreliable", [
    [_warning(0), _warning(16)],  # Mixed group with an editable candidate occurrence.
    [_warning(16)],  # Point exactly at the prefix/candidate boundary.
    [_warning(16, end_line=17, end_character=0)],
    [_warning(0), _warning(1, end_line=17, end_character=0)],
    [_warning(0), _warning(1, range={"start": {"line": 1}, "end": {"line": 17}})],
    [_warning(0), _warning(1, future_origin={"scope": "candidate"})],
    [_warning(-1)],
    [{"severity": "warning", "message": "unlocated warning"}],
])
def test_mixed_boundary_unfamiliar_span_or_unlocated_warning_groups_survive(tmp_path, unreliable):
    raw, context = _fixture(tmp_path, unreliable)
    compact = _present(raw, context, tmp_path)
    assert compact["diagnostics"] == raw["diagnostics"]
    assert "immutable_prefix_warnings" not in compact.get("response_presentation", {})


@pytest.mark.parametrize("change", [
    lambda a: a.update(schema_version=2),
    lambda a: a.update(future_required_metadata={"origin": "unknown"}),
    lambda a: a.update(generated_source_sha256="0" * 64),
    lambda a: a.update(candidate_source_sha256="0" * 64),
    lambda a: a.update(service_diagnostics_omitted=True),
    lambda a: a.update(position_encoding="future"),
    lambda a: a.update(generated_source="different source"),
    lambda a: a.pop("raw_diagnostics"),
])
def test_unknown_or_mismatched_artifact_evidence_keeps_warnings(tmp_path, change):
    raw, context = _fixture(tmp_path)
    _rewrite_artifact(raw, change)
    compact = _present(raw, context, tmp_path)
    assert compact["diagnostics"] == raw["diagnostics"]


@pytest.mark.parametrize("damage", ["missing", "malformed", "non_addressed", "modified", "unknown_inline"])
def test_unavailable_tampered_or_unrecognized_diagnostics_never_break_delivery(tmp_path, damage):
    raw, context = _fixture(tmp_path)
    path = Path(raw["diagnostics_path"])
    if damage == "missing":
        path.unlink()
    elif damage == "malformed":
        path.write_text("not JSON")
    elif damage == "non_addressed":
        other = path.with_name("not-content-addressed.json")
        other.write_bytes(path.read_bytes())
        raw["diagnostics_path"] = str(other)
    elif damage == "modified":
        path.write_bytes(path.read_bytes() + b" ")
    else:
        raw["diagnostics"][0]["new_required_action"] = "Read this diagnostic"
    compact = _present(raw, context, tmp_path)
    assert compact["diagnostics"] == raw["diagnostics"]


def test_source_and_prefix_must_match_exactly_and_no_context_means_no_summary(tmp_path):
    raw, context = _fixture(tmp_path)
    for invalid in (None, replace(context, source_sha256="0" * 64),
                    replace(context, prefix_text=context.prefix_text + "\n"),
                    replace(context, prefix_kind="future-prefix")):
        assert _present(raw, invalid, tmp_path)["diagnostics"] == raw["diagnostics"]


def test_small_summary_never_grows_the_receipt_or_publishes_unused_archive(tmp_path):
    raw, context = _fixture(tmp_path, [_warning(0, "short")])
    raw = {key: raw[key] for key in ("schema_version", "mode", "status", "valid", "source_sha256",
                                    "diagnostics_path", "diagnostics")}
    assert _present(raw, context, tmp_path) is raw
    assert not (tmp_path / "responses").exists()


def test_legacy_keeps_exact_identity_even_with_valid_context(tmp_path):
    raw, context = _fixture(tmp_path)
    assert presentation.present_result(raw, artifact_dir=tmp_path / "responses", tool="edit_check",
                                        prefix_context=context) is raw
    assert not (tmp_path / "responses").exists()


def test_delivery_factory_binds_snapshot_under_capsule_and_leaves_journal_raw(service, monkeypatch):
    settings = {**service.settings, "response_policy": "compact-v1"}
    service = workflow.Feedback(settings)
    candidate = service.candidate.read_text()
    prefix = workflow.lean_source.exact_source_prefix(service.row, service.project)
    declaration, _ = workflow.lean_source.extract_candidate_declaration(service.row, candidate)
    raw, _context = _fixture(service.root, [_warning(0)], prefix=prefix.text,
                             candidate_source=candidate, declaration=declaration)
    snapshot = Path(raw["snapshot_path"])
    generated = prefix.text + declaration.rstrip() + "\n"
    source_map = diagnostics.SourceMap.for_declaration(candidate, generated, declaration)
    shown = diagnostics.present_diagnostics([_warning(0)], source_map, source=generated)
    raw.update({key: shown[key] for key in ("diagnostics", "diagnostics_compacted", "diagnostics_truncation")})
    raw["diagnostics_path"] = str(diagnostics.archive_diagnostics([_warning(0)], shown, source=generated,
        candidate_path=snapshot, candidate_bytes=snapshot.read_bytes(), source_map=source_map))
    raw["candidate"] = str(service.candidate)
    context = presentation.prefix_context_for_result(raw, row=service.row, project_root=service.project,
                                                     capsule_root=service.root)
    assert context is not None
    assert context.source_sha256 == raw["source_sha256"] and context.prefix_text == prefix.text
    outside = service.root / "outside.lean"
    outside.write_bytes(snapshot.read_bytes())
    for replacement in ({**raw, "snapshot_path": str(outside)}, {**raw, "source_sha256": "0" * 64}):
        assert presentation.prefix_context_for_result(replacement, row=service.row,
            project_root=service.project, capsule_root=service.root) is None
    monkeypatch.setattr(service, "check", lambda _request: raw)
    compact = service.call("edit_check", {})
    assert compact["diagnostics"] == []
    journal = json.loads(next(service.request_journal.directory.glob("*.result.json")).read_bytes())
    assert journal["diagnostics"] == raw["diagnostics"]
    assert "response_presentation" not in journal
    assert json.loads(Path(compact["full_response_path"]).read_bytes())["result"] == journal
