from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import argparse
import hashlib
import json
import os
import re
import sys
import tempfile
import time
import uuid
from pathlib import Path
from typing import Any


from lean_tools import arena_workflow as arena
from lean_tools import lean_source
from lean_tools import check_budget
from lean_tools.lean_source import SourceDocument as PreparedDocument
from lean_tools import diagnostic_presentation as presentation
from lean_tools import persistent_quick_workflow as persistent
class GoalStateError(RuntimeError):
    pass


def _goal_handle_path(feedback: Any, candidate: Path, digest: str) -> Path:
    root = Path(getattr(feedback, "root", candidate.parent))
    return root / ".feedback" / "goal-handles" / f"{digest}.json"


def _source_revision_path(candidate: Path) -> Path:
    key = hashlib.sha256(str(candidate.resolve()).encode()).hexdigest()
    return candidate.parent / ".feedback" / "source-revisions" / f"{key}.txt"


def invalidate_source_revision(candidate: Path) -> None:
    """Invalidate a tracked draft before an atomic edit/restore replaces it."""
    path = _source_revision_path(candidate)
    if not path.exists():
        return
    temporary = path.with_suffix(f".{uuid.uuid4().hex}.tmp")
    try:
        temporary.write_text(uuid.uuid4().hex, encoding="ascii")
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def source_revision(candidate: Path) -> str:
    """A restored identical draft is a new observation lifetime.

    The explicit token changes on harness writes, even when an inode/timestamp
    is recycled after a fast edit and identical restore. File metadata also
    detects ordinary external edits. Immutable state caches remain reusable.
    """
    path = _source_revision_path(candidate)
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists():
        temporary = path.with_suffix(f".{uuid.uuid4().hex}.tmp")
        try:
            temporary.write_text(uuid.uuid4().hex, encoding="ascii")
            try:
                os.link(temporary, path)
            except FileExistsError:
                pass
        finally:
            temporary.unlink(missing_ok=True)
    stat = candidate.stat()
    material = [str(candidate.resolve()), stat.st_ino, stat.st_size,
                stat.st_mtime_ns, stat.st_ctime_ns, path.read_text(encoding="ascii")]
    return hashlib.sha256(json.dumps(material).encode()).hexdigest()


def attach_goal_handles(feedback: Any, snapshot_path: Path, source_sha256: str,
                        goal_payload: dict[str, Any]) -> dict[str, Any]:
    """Register already observed goals, without asking Lean to elaborate again.

    A handle identifies a candidate snapshot, legal prefix, cursor and one goal.
    It never transfers a goal observation to a different source or task.
    """
    goals = goal_payload.get("goals")
    position = goal_payload.get("position", {}).get("candidate")
    if not isinstance(goals, list) or not goals or not isinstance(position, dict):
        return {}
    raw = snapshot_path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != source_sha256:
        raise GoalStateError("goal observation does not match the candidate snapshot")
    text = lean_source.candidate_text_from_bytes(raw)
    snapshot = lean_source.snapshot_candidate(feedback.row, text, snapshot_path)
    offset, column = candidate_position_to_offset(text, position["line"], position.get("column"))
    if not snapshot.declaration_start <= offset < snapshot.declaration_start + len(snapshot.declaration):
        raise GoalStateError("observed goal position is outside the target declaration")
    prefix = lean_source.exact_source_prefix(feedback.row, feedback.project)
    generated_digest = hashlib.sha256((prefix.text + snapshot.declaration.rstrip() + "\n").encode("utf-8")).hexdigest()
    observed_digest = goal_payload.get("source_sha256")
    if isinstance(observed_digest, str) and re.fullmatch(r"[0-9a-f]{64}", observed_digest) and observed_digest != generated_digest:
        raise GoalStateError("goal observation belongs to a different generated source or legal prefix")
    fingerprint = goal_payload.get("environment_fingerprint")
    registry = getattr(feedback, "settings", {}).get("fingerprint_registry")
    if fingerprint is None and registry:
        # A capsule already provisions this guarded registry. Never compute a
        # fingerprint or build anything merely to attach display handles.
        fingerprint = arena.environment_fingerprint_registry_entry(feedback.row, feedback.project, Path(registry), validate_guard=True)["fingerprint"]
    binding = {"source_sha256": source_sha256, "prefix_sha256": prefix.sha256,
               "task": feedback.row["name"], "task_signature": feedback.row["signature"],
               "project_root": str(Path(feedback.project).resolve()), "environment_fingerprint": fingerprint}
    path = _goal_handle_path(feedback, snapshot_path, source_sha256)
    additions = {}
    public = []
    residual = goal_payload.get("phase") == "residual"
    if residual and (not isinstance(fingerprint, str) or not isinstance(goal_payload.get("source_revision"), str)):
        raise GoalStateError("residual handles require a frozen environment and draft revision")
    for ordinal, goal in enumerate(goals):
        if not isinstance(goal, dict) or not isinstance(goal.get("target"), str):
            continue
        index = goal.get("index", ordinal)
        if type(index) is not int or index < 0:
            continue
        observed_position = goal.get("position", position) if residual else position
        _, observed_column = candidate_position_to_offset(text, observed_position["line"], observed_position.get("column"))
        selector = {"line": observed_position["line"], "column": observed_column, "index": index}
        material = {**binding, "goal": selector, "target": goal["target"],
                    "case_name": goal.get("case_name")}
        if residual:
            context = goal.get("context")
            if not isinstance(context, dict) or context.get("target") != goal["target"]:
                raise GoalStateError("residual handle has no complete actual goal context")
            material.update(phase="residual", occurrence=goal["occurrence"],
                            source_revision=goal_payload["source_revision"],
                            candidate_path=goal_payload["candidate_path"],
                            context_sha256=hashlib.sha256(json.dumps(context, sort_keys=True, ensure_ascii=False).encode()).hexdigest(),
                            record_sha256=hashlib.sha256(json.dumps(goal["record"], sort_keys=True, ensure_ascii=False).encode()).hexdigest())
        identifier = "goal-" + hashlib.sha256(json.dumps(material, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
        additions[identifier] = {**material, "goal_count": goal.get("goal_count", goal_payload.get("goal_count", len(goals))),
                                  "context_origin": goal_payload.get("context_origin", "interactive")}
        if residual:
            additions[identifier]["context"] = context
            additions[identifier]["record"] = goal["record"]
        public.append({"goal_id": identifier, "goal": selector,
                       "case_name": goal.get("case_name"),
                       **({"phase": "residual", "occurrence": goal["occurrence"]} if residual else {})})
    if not public:
        return {}
    with arena.exclusive_file_lock(path.with_suffix(".lock"), timeout_seconds=10,
                                   request={"purpose": "goal-handles", "source_sha256": source_sha256}):
        try:
            previous = json.loads(path.read_text(encoding="utf-8"))
            old_binding = previous.get("binding", {})
            same_context = all(old_binding.get(key) == value for key, value in binding.items() if key != "environment_fingerprint")
            compatible_environment = old_binding.get("environment_fingerprint") in (None, fingerprint) or fingerprint is None
            registered = previous.get("handles", {}) if same_context and compatible_environment else {}
            if not isinstance(registered, dict):
                registered = {}
        except (OSError, ValueError, AttributeError):
            registered = {}
        if residual:
            registered = {key: value for key, value in registered.items()
                          if not isinstance(value, dict) or value.get("phase") != "residual"
                          or (value.get("source_revision") == goal_payload["source_revision"]
                              and value.get("candidate_path") == goal_payload["candidate_path"])}
        registered.update(additions)
        temporary = path.with_suffix(f".{time.time_ns()}.tmp")
        try:
            temporary.write_text(json.dumps({"binding": binding, "handles": registered}, ensure_ascii=False), encoding="utf-8")
            temporary.replace(path)
        finally:
            temporary.unlink(missing_ok=True)
    return {"goal_handles": public, "default_goal_id": public[0]["goal_id"]}


def known_goal_handles(feedback: Any, candidate: Path, source_sha256: str) -> dict[str, Any]:
    """Return selectors already observed for this exact snapshot; no Lean call."""
    try:
        saved = json.loads(_goal_handle_path(feedback, candidate, source_sha256).read_text(encoding="utf-8"))
        binding = saved["binding"]
        if (binding["source_sha256"] != source_sha256 or binding["task"] != feedback.row["name"]
                or binding["task_signature"] != feedback.row["signature"]
                or binding["project_root"] != str(Path(feedback.project).resolve())):
            return {}
        public = [{"goal_id": identifier, "goal": value["goal"], "case_name": value.get("case_name")}
                  for identifier, value in sorted(saved["handles"].items(), key=lambda item: (item[1]["goal"]["line"], item[1]["goal"]["column"], item[1]["goal"]["index"], item[0]))
                  if value.get("phase") != "residual"]
        return {"goal_handles": public, "default_goal_id": public[0]["goal_id"]} if public else {}
    except (OSError, ValueError, KeyError, TypeError):
        return {}


def resolve_goal_handle(feedback: Any, candidate: Path, digest: str, identifier: str,
                        prefix_sha256: str) -> dict[str, Any]:
    try:
        saved = json.loads(_goal_handle_path(feedback, candidate, digest).read_text(encoding="utf-8"))
        handle = saved["handles"][identifier]
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise GoalStateError("unknown goal_id for this snapshot; use goal_handles from edit_check or omit the selector to find a live tactic") from error
    if (not isinstance(handle, dict) or not isinstance(handle.get("goal"), dict)
            or not isinstance(handle.get("target"), str) or type(handle.get("goal_count")) is not int):
        raise GoalStateError("malformed stored goal_id; observe goals again")
    if (handle.get("source_sha256") != digest or handle.get("prefix_sha256") != prefix_sha256
            or handle.get("task") != feedback.row["name"]
            or handle.get("task_signature") != feedback.row["signature"]
            or handle.get("project_root") != str(Path(feedback.project).resolve())):
        raise GoalStateError("goal_id belongs to a different source, task or legal prefix; observe goals again")
    if handle.get("phase") == "residual":
        if (handle.get("candidate_path") != str(candidate.resolve())
                or handle.get("source_revision") != source_revision(candidate)):
            raise GoalStateError("goal_id expired after a draft edit or restore; request unfinished_cases again")
        context = handle.get("context")
        if (not isinstance(context, dict) or
                hashlib.sha256(json.dumps(context, sort_keys=True, ensure_ascii=False).encode()).hexdigest() != handle.get("context_sha256")):
            raise GoalStateError("stored residual goal context does not match its handle")
        if hashlib.sha256(json.dumps(handle.get("record"), sort_keys=True, ensure_ascii=False).encode()).hexdigest() != handle.get("record_sha256"):
            raise GoalStateError("stored residual retrieval record does not match its handle")
    return handle


def _line_bounds(text: str, line: int) -> tuple[int, int]:
    """Return code-point offsets for a one-based line, excluding its newline."""
    if line < 1:
        raise GoalStateError("line must be at least 1")
    starts = [0]
    starts.extend(match.end() for match in re.finditer(r"\n", text))
    if line > len(starts):
        raise GoalStateError(
            f"line {line} is outside the candidate (which has {len(starts)} lines)"
        )
    start = starts[line - 1]
    end = text.find("\n", start)
    if end < 0:
        end = len(text)
    if end > start and text[end - 1] == "\r":
        end -= 1
    return start, end


def candidate_position_to_offset(
    text: str, line: int, column: int | None
) -> tuple[int, int]:
    """Map a human one-based line/column to a code-point offset.

    When the column is omitted, select the first non-whitespace character on the
    requested line. Tabs count as one displayed source character here; conversion
    to LSP's UTF-16 character units happens separately.
    """
    start, end = _line_bounds(text, line)
    line_text = text[start:end]
    if column is None:
        leading = len(line_text) - len(line_text.lstrip())
        column = leading + 1
    if column < 1 or column > len(line_text) + 1:
        raise GoalStateError(
            f"column {column} is outside line {line} "
            f"(valid range: 1..{len(line_text) + 1})"
        )
    return start + column - 1, column


def offset_to_human_position(text: str, offset: int) -> dict[str, int]:
    if offset < 0 or offset > len(text):
        raise GoalStateError("source offset is outside the document")
    line = text.count("\n", 0, offset) + 1
    previous_newline = text.rfind("\n", 0, offset)
    column = offset - (previous_newline + 1) + 1
    return {"line": line, "column": column}


def offset_to_lsp_position(text: str, offset: int) -> dict[str, int]:
    human = offset_to_human_position(text, offset)
    line_start = text.rfind("\n", 0, offset) + 1
    character = len(text[line_start:offset].encode("utf-16-le")) // 2
    return {"line": human["line"] - 1, "character": character}


def lsp_position_to_offset(text: str, line: int, character: int) -> int:
    if line < 0 or character < 0:
        raise GoalStateError("negative LSP position")
    start, end = _line_bounds(text, line + 1)
    units = 0
    for index, value in enumerate(text[start:end]):
        if units == character:
            return start + index
        units += len(value.encode("utf-16-le")) // 2
        if units > character:
            raise GoalStateError("LSP character splits a UTF-16 surrogate pair")
    if units == character:
        return end
    raise GoalStateError("LSP character is outside the source line")


def tagged_text_to_string(value: Any) -> str:
    """Strip Lean widget tags while preserving their displayed text."""
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    if isinstance(value, list):
        return "".join(tagged_text_to_string(item) for item in value)
    if not isinstance(value, dict):
        return str(value)
    text = value.get("text")
    if isinstance(text, str):
        return text
    append = value.get("append")
    if isinstance(append, list):
        return "".join(tagged_text_to_string(item) for item in append)
    tag = value.get("tag")
    if isinstance(tag, list) and tag:
        return tagged_text_to_string(tag[-1])
    # This should only be reached if Lean adds a new TaggedText constructor.
    return "".join(tagged_text_to_string(item) for item in value.values())


def normalize_interactive_goals(value: Any) -> list[dict[str, Any]]:
    if value is None:
        return []
    if not isinstance(value, dict) or not isinstance(value.get("goals"), list):
        raise GoalStateError("Lean returned an unrecognized interactive-goal payload")
    normalized: list[dict[str, Any]] = []
    for index, raw_goal in enumerate(value["goals"]):
        if not isinstance(raw_goal, dict):
            raise GoalStateError("Lean returned a malformed interactive goal")
        raw_hypotheses = raw_goal.get("hyps", [])
        if not isinstance(raw_hypotheses, list):
            raise GoalStateError("Lean returned malformed goal hypotheses")
        hypotheses: list[dict[str, Any]] = []
        for raw_hypothesis in raw_hypotheses:
            if not isinstance(raw_hypothesis, dict):
                raise GoalStateError("Lean returned a malformed hypothesis")
            names = raw_hypothesis.get("names", [])
            if not isinstance(names, list) or not all(
                isinstance(name, str) for name in names
            ):
                raise GoalStateError("Lean returned malformed hypothesis names")
            value_text = (
                tagged_text_to_string(raw_hypothesis["val"])
                if "val" in raw_hypothesis
                else None
            )
            hypotheses.append(
                {
                    "names": names,
                    "type": tagged_text_to_string(raw_hypothesis.get("type")),
                    "value": value_text,
                    "is_instance": bool(raw_hypothesis.get("isInstance", False)),
                    "is_type": bool(raw_hypothesis.get("isType", False)),
                }
            )
        normalized.append(
            {
                "index": index,
                "case_name": raw_goal.get("userName"),
                "goal_prefix": str(raw_goal.get("goalPrefix", "⊢ ")),
                "target": tagged_text_to_string(raw_goal.get("type")),
                "hypotheses": hypotheses,
            }
        )
    return normalized


def render_goals(goals: list[dict[str, Any]]) -> str:
    rendered: list[str] = []
    for goal in goals:
        lines: list[str] = []
        case_name = goal.get("case_name")
        if isinstance(case_name, str) and case_name:
            lines.append(f"case {case_name}")
        for hypothesis in goal["hypotheses"]:
            names = " ".join(hypothesis["names"])
            if hypothesis["value"] is None:
                lines.append(f"{names} : {hypothesis['type']}".lstrip())
            else:
                lines.append(
                    f"{names} : {hypothesis['type']} := {hypothesis['value']}".lstrip()
                )
        lines.append(f"{goal['goal_prefix']}{goal['target']}")
        rendered.append("\n".join(lines))
    return "\n\n".join(rendered) if rendered else "no goals"


def prepare_document(
    task_path: Path, candidate_path: Path, project_root: Path
) -> PreparedDocument:
    try:
        return lean_source.prepare_document(task_path, candidate_path, project_root)
    except lean_source.SourceDocumentError as error:
        raise GoalStateError(str(error)) from error


def map_candidate_position(
    document: PreparedDocument, line: int, column: int | None
) -> tuple[dict[str, int], dict[str, int]]:
    candidate_offset, resolved_column = candidate_position_to_offset(
        document.candidate_text, line, column
    )
    declaration_end = document.candidate_declaration_start + len(document.declaration)
    if not document.candidate_declaration_start <= candidate_offset <= declaration_end:
        raise GoalStateError(
            "the requested cursor is outside the target declaration; "
            "choose a line in the theorem proof"
        )
    try:
        managed_offset = document.source_map().candidate_to_generated(candidate_offset)
    except presentation.PositionError as error:
        raise GoalStateError(str(error)) from error
    return (
        {"line": line, "column": resolved_column},
        offset_to_lsp_position(document.source, managed_offset),
    )


def map_diagnostic(
    diagnostic: persistent.Diagnostic, document: PreparedDocument
) -> dict[str, Any]:
    return presentation.map_diagnostic(diagnostic.as_json(), document.source_map())


def relevant_diagnostics(
    diagnostics: list[persistent.Diagnostic], document: PreparedDocument
) -> tuple[list[dict[str, Any]], int]:
    """Keep all warnings/errors plus useful information attached to the candidate.

    Project-prefix LSP documents can emit one informational ``Goals accomplished!``
    diagnostic for every earlier declaration. They add no goal-state information and
    can dwarf the actual response, so they are suppressed even at the target.
    """
    mapped = [map_diagnostic(diagnostic, document) for diagnostic in diagnostics]
    relevant: list[dict[str, Any]] = []
    for diagnostic in mapped:
        severity = diagnostic["severity"]
        location = diagnostic.get("location")
        in_candidate = (
            isinstance(location, dict) and location.get("scope") == "candidate"
        )
        accomplished = diagnostic["message"].strip() == "Goals accomplished!"
        if (
            severity in {"error", "warning"}
            or presentation.ACTIONABLE.search(diagnostic["message"])
            or (in_candidate and not accomplished)
        ):
            relevant.append(diagnostic)
    compact, _compacted = presentation.compact_diagnostics(relevant)
    return compact, len(mapped) - len(compact)


class GoalStateSession(persistent.LeanLspSession):
    """Persistent Lean LSP session with the structured infoview-goal RPC."""


def query_goal_state(
    task_path: Path,
    candidate_path: Path,
    project_root: Path,
    *,
    line: int,
    column: int | None,
    timeout_seconds: int,
) -> dict[str, Any]:
    timeout_seconds = check_budget.remaining(timeout_seconds)
    if timeout_seconds <= 0:
        raise GoalStateError("timeout must be positive")
    started = time.perf_counter()
    deadline = time.monotonic() + timeout_seconds
    compile_scope = arena.lean_timeout_scope() == "compile"
    document = prepare_document(task_path, candidate_path, project_root)
    candidate_position, lsp_position = map_candidate_position(document, line, column)
    source_sha256 = arena.sha256_bytes(document.source.encode("utf-8"))
    document_version: int | None = None
    reused_source = False
    service_omitted = 0
    if arena.persistent_quick_matches_project(document.project_root):
        response = persistent.feedback_request(
            document.source,
            timeout_seconds if compile_scope else persistent._remaining_seconds(deadline),
            operation="goals",
            position=lsp_position,
            target_start_line=document.source.count(
                "\n", 0, document.document_declaration_start
            ),
        )
        raw_goals = response["goals"]
        diagnostics = [
            persistent.Diagnostic(**item) for item in response["diagnostics"]
        ]
        startup_seconds = response["startup_seconds"]
        elaboration_seconds = response["elaboration_seconds"]
        document_version = response["document_version"]
        reused_source = response["reused_source"]
        service_omitted = response.get("diagnostics_omitted", 0)
        backend = "resident"
    else:
        backend = "lsp"
        with (
            arena.resource_gate.permit_from_environment(
                "lean",
                priority=0,
                timeout_seconds=None if compile_scope else max(0.0, deadline - time.monotonic()),
                metadata={
                    "purpose": "goal-state",
                    "project_root": str(document.project_root),
                },
            ),
            tempfile.TemporaryDirectory(
                prefix="lrh-goal-", dir=arena.evaluation_scratch_parent()
            ) as temporary,
        ):
            work_root = Path(temporary).resolve()
            managed_path = work_root / "ManagedGoal.lean"
            managed_path.write_text(document.source, encoding="utf-8")
            session = GoalStateSession(
                document.project_root,
                managed_path,
                work_root / "lean-lsp.stderr.log",
                timeout_seconds,
            )
            session.request_deadline = (time.monotonic() + timeout_seconds if compile_scope else deadline)
            try:
                session.start()
                elaboration_seconds, diagnostics = session.open_document(
                    document.source
                )
                setup_errors = [
                    item.message
                    for item in diagnostics
                    if persistent.is_infrastructure_message(item.message)
                ]
                if setup_errors:
                    raise GoalStateError(
                        "Lean setup infrastructure failure: " + "\n".join(setup_errors)
                    )
                raw_goals = session.interactive_goals(lsp_position)
                startup_seconds = session.startup_seconds
                document_version = session.version
            finally:
                session.request_deadline = None
                session.close()
    goals = normalize_interactive_goals(raw_goals)
    normalized_diagnostics, diagnostics_omitted = relevant_diagnostics(
        diagnostics, document
    )
    raw_diagnostics = [item.as_json() for item in diagnostics]
    details_path = presentation.archive_diagnostics(
        raw_diagnostics,
        {
            "diagnostics": normalized_diagnostics,
            "mapped_diagnostics": [
                map_diagnostic(item, document) for item in diagnostics
            ],
            "diagnostics_compacted": diagnostics_omitted,
            "raw_goals": raw_goals,
            "goals": goals,
        },
        source=document.source,
        candidate_path=document.candidate_path,
        source_map=document.source_map(),
        service_omitted=service_omitted,
    )
    return {
        "schema_version": 1,
        "ok": True,
        "task": document.task_name,
        "candidate": str(document.candidate_path),
        "project_root": str(document.project_root),
        "document_kind": document.document_kind,
        "backend": backend,
        "source_sha256": source_sha256,
        "document_version": document_version,
        "reused_source": reused_source,
        "position": {
            "candidate": candidate_position,
            "lsp": lsp_position,
        },
        "valid": not any(
            diagnostic["severity"] == "error" for diagnostic in normalized_diagnostics
        ),
        "goal_state_available": raw_goals is not None,
        "goals": goals,
        "rendered": render_goals(goals),
        "diagnostics": normalized_diagnostics,
        "details_path": str(details_path),
        "diagnostics_omitted": diagnostics_omitted + service_omitted,
        "timing": {
            "startup_seconds": (
                round(startup_seconds, 6) if startup_seconds is not None else None
            ),
            "elaboration_seconds": round(elaboration_seconds, 6),
            "total_seconds": round(time.perf_counter() - started, 6),
        },
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Return Lean goals and hypotheses at a Candidate.lean cursor as JSON"
        )
    )
    parser.add_argument("--task", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--project-root", type=Path, required=True)
    parser.add_argument(
        "--line", type=int, required=True, help="one-based line in Candidate.lean"
    )
    parser.add_argument(
        "--column",
        type=int,
        help=(
            "one-based Unicode column in Candidate.lean; defaults to the first "
            "non-whitespace character"
        ),
    )
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--pretty", action="store_true")
    return parser


def write_json(value: dict[str, Any], *, pretty: bool) -> None:
    encoded = json.dumps(
        value,
        ensure_ascii=False,
        indent=2 if pretty else None,
        separators=None if pretty else (",", ":"),
    ).encode("utf-8")
    sys.stdout.buffer.write(encoded + b"\n")


def main() -> int:
    args = build_parser().parse_args()
    try:
        result = query_goal_state(
            args.task,
            args.candidate,
            args.project_root,
            line=args.line,
            column=args.column,
            timeout_seconds=args.timeout,
        )
    except (
        GoalStateError,
        arena.WorkflowError,
        persistent.PersistentQuickError,
        arena.resource_gate.ResourceGateError,
        OSError,
        ValueError,
    ) as error:
        write_json(
            {
                "schema_version": 1,
                "ok": False,
                "error": {
                    "type": type(error).__name__,
                    "message": str(error),
                },
            },
            pretty=args.pretty,
        )
        return 2
    write_json(result, pretty=args.pretty)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
