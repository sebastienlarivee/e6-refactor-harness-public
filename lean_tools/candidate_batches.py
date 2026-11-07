"""Bounded candidate comparisons against one frozen capsule draft.

The comparisons are advisory to the normal host selector. No model is called,
the editable candidate is never written, and every exact-valid alternative is
retained even when its optimistic score cannot improve the comparison floor.
"""
from __future__ import annotations

import math
from copy import deepcopy
import json
import os
from pathlib import Path
import re
import time
from typing import Any, TYPE_CHECKING
import uuid

from lean_tools import arena_workflow as arena
from lean_tools import lean_source
from lean_tools.feedback_workflow import EditRequestError, bind_feedback_scoring_policy, edit_source, immutable_text
from lean_tools.feedback_contract import score_capability
from lean_tools.scoring import OriginalDenominatorScorePolicy, incumbent_score_delta, score_breakdown

if TYPE_CHECKING:
    from lean_tools.feedback_workflow import Feedback

MAX_ALTERNATIVES = 4
INTAKE_CHARACTERS = 262144
_DIAGNOSTIC_CHARACTERS = 1200
_DIAGNOSTIC_LINES = 12
_DIAGNOSTIC_OMITTED = "... [diagnostic text omitted]"
_DIAGNOSTIC_HEADER = re.compile(r"^[ \t]*(?:.*?:\d+:\d+:[ \t]*)?(?P<severity>error(?:\([^\n)]+\))?|warning|info(?:rmation)?):", re.I)
_GOAL_LINE = re.compile(r"^[ \t]*⊢(?:\s|$)")
_CASE_LINE = re.compile(r"^[ \t]*case(?:\s|$)")
TOOL = {
    "name": "compare_candidates",
    "description": (
        "Compare 2–4 complete Lean proof alternatives against the same frozen source. "
        "Requires the full candidate file's SHA256. Each uniquely labelled alternative "
        "provides body or unique-match edits. The draft stays untouched. Every alternative "
        "gets primary validation; exact-valid proofs retain immutable checkpoints. "
        "Exact token/heartbeat/axiom checks and necessary compatibility checks produce "
        "advisory combined scores using the original denominators. Strict optimistic "
        "losers may omit compatibility and score. Partial proofs never receive scores. "
        "All variants run; compact results link to full on-disk details."
    ),
    "inputSchema": {
        "type": "object",
        "properties": {
            "candidate": {"type": "string"},
            "expected_sha256": {"type": "string", "pattern": "^[0-9a-f]{64}$"},
            "alternatives": {
                "type": "array", "minItems": 2, "maxItems": MAX_ALTERNATIVES,
                "items": {
                    "type": "object",
                    "properties": {
                        "label": {"type": "string", "pattern": "^[A-Za-z0-9._-]{1,64}$"},
                        "body": {"type": "string"},
                        "edits": {
                            "type": "array", "minItems": 1,
                            "items": {
                                "type": "object",
                                "properties": {"old": {"type": "string", "minLength": 1}, "new": {"type": "string"}},
                                "required": ["old", "new"], "additionalProperties": False,
                            },
                        },
                    },
                    "required": ["label"], "additionalProperties": False,
                    "oneOf": [{"required": ["body"]}, {"required": ["edits"]}],
                },
            },
        },
        "required": ["expected_sha256", "alternatives"],
        "additionalProperties": False,
    },
}

SCORE_TOOL = {
    "name": "score_candidate",
    "description": (
        "Get one candidate's complete advisory score without editing the draft. Requires "
        "expected_sha256 of the full current candidate. Optionally provide body, literal "
        "source_text, unique-match edits, or checkpoint_id as the starting source. Reuses "
        "batch quick/exact validation, allowed-axiom audit, immutable checkpoints and every "
        "configured compatibility environment. No optimistic pruning. Partial or incomplete "
        "measurements never receive a score; host selection remains authoritative."
    ),
    "inputSchema": {
        "type": "object",
        "properties": {
            "candidate": {"type": "string"},
            "expected_sha256": {"type": "string", "pattern": "^[0-9a-f]{64}$"},
            "body": {"type": "string"},
            "source_text": {"type": "string", "description": "Literal Lean text, never a path."},
            "source": {"type": "string", "description": "Legacy alias for source_text."},
            "checkpoint_id": {"type": "string"},
            "edits": TOOL["inputSchema"]["properties"]["alternatives"]["items"]["properties"]["edits"],
        },
        "required": ["expected_sha256"], "additionalProperties": False,
    },
}


def _immutable_source(path: Path, source: str) -> None:
    """Publish a complete UTF-8 file atomically, and never replace an existing file."""
    immutable_text(path, source)


def _unchanged(path: Path, digest: str) -> None:
    if arena.sha256_file(path) != digest:
        raise arena.WorkflowError("evaluated snapshot changed; no checkpoint was saved")


def _request(feedback: Feedback, request: dict[str, Any], *, single: bool = False) -> tuple[Path, list[dict[str, Any]], OriginalDenominatorScorePolicy, list[Path], float | None]:
    if not single and feedback.settings.get("candidate_batches") is not True:
        raise arena.WorkflowError("candidate batch comparisons are not enabled")
    if single and not score_capability(feedback.settings):
        raise arena.WorkflowError("complete candidate scoring requires frozen original metrics and compatibility roots")
    if not isinstance(request, dict) or set(request) - {"candidate", "expected_sha256", "alternatives"}:
        raise arena.WorkflowError("provide candidate, expected_sha256, and alternatives only")
    digest = request.get("expected_sha256")
    if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
        raise arena.WorkflowError("expected_sha256 must be the 64-character SHA256 of the full candidate file")
    alternatives = request.get("alternatives")
    if not isinstance(alternatives, list) or not (1 if single else 2) <= len(alternatives) <= (1 if single else MAX_ALTERNATIVES):
        raise arena.WorkflowError("provide one candidate" if single else "provide 2–4 alternatives")
    labels = set()
    for alternative in alternatives:
        if not isinstance(alternative, dict):
            raise arena.WorkflowError("each alternative must be an object with a unique label")
        label = alternative.get("label")
        if not isinstance(label, str) or re.fullmatch(r"[A-Za-z0-9._-]{1,64}", label) is None or label in labels:
            raise arena.WorkflowError("alternative labels must be unique ASCII names of 1–64 characters")
        labels.add(label)
    try:
        policy = OriginalDenominatorScorePolicy(feedback.settings["original_tokens"], feedback.settings["original_heartbeats"], feedback.scoring_policy)
    except (KeyError, ValueError) as error:
        raise arena.WorkflowError("candidate comparisons require positive original_tokens and original_heartbeats") from error
    supplied_roots = feedback.settings.get("compatibility_roots", [])
    if not isinstance(supplied_roots, list) or not all(isinstance(root, str) and root for root in supplied_roots):
        raise arena.WorkflowError("compatibility_roots must be an array of paths")
    roots = []
    for supplied in supplied_roots:
        root = Path(supplied).resolve()
        if root != feedback.project and root not in roots:
            roots.append(root)
    floor = feedback.settings.get("incumbent_score")
    if floor is not None:
        if isinstance(floor, bool) or not isinstance(floor, (int, float)) or not math.isfinite(floor) or floor > 100:
            raise arena.WorkflowError("incumbent_score must be finite and at most 100")
        floor = float(floor)
    return feedback.candidate_path(request), alternatives, policy, roots, floor


@bind_feedback_scoring_policy
def _evaluate(feedback: Feedback, snapshot: Path, digest: str, project: Path, *, quick: bool) -> arena.Evaluation:
    _unchanged(snapshot, digest)
    registry = feedback.settings.get("fingerprint_registry")
    evaluation = arena.evaluate_candidate(
        feedback.task, snapshot, project, timeout_seconds=feedback.quick_timeout if quick else feedback.timeout,
        quick=quick, fingerprint_registry=Path(registry) if registry else None,
    )
    _unchanged(snapshot, digest)
    if evaluation.valid is not True:
        raise arena.WorkflowError("evaluator did not confirm complete candidate validity")
    return evaluation


def _exact_metrics(evaluation: arena.Evaluation) -> tuple[int, int]:
    if (evaluation.axiom_audit_seconds is None or not isinstance(evaluation.axioms, list)
            or any(not isinstance(axiom, str) or axiom not in arena.ALLOWED_AXIOMS for axiom in evaluation.axioms)):
        raise arena.WorkflowError("candidate lacks an exact allowed-axiom audit")
    tokens, heartbeats = evaluation.candidate_local_tokens, evaluation.heartbeat
    if type(tokens) is not int or tokens < 0 or type(heartbeats) is not int or heartbeats < 0:
        raise arena.WorkflowError("candidate lacks exact token and heartbeat measurements")
    return tokens, heartbeats


def _failure_preview(output: str) -> str:
    """Keep literal error/goal excerpts within the existing brief-response bounds."""
    lines = arena.lean_error_context(output).splitlines()
    text = "\n".join(lines)
    if len(text) <= _DIAGNOSTIC_CHARACTERS and len(lines) <= _DIAGNOSTIC_LINES:
        return text

    # A later error's goal keeps its own header; warning examples are not goals.
    goal, goal_header, is_error = None, 0, True
    for index, line in enumerate(lines):
        header = _DIAGNOSTIC_HEADER.match(line)
        if header is not None:
            goal_header = index
            is_error = header["severity"].lower().startswith("error")
        if is_error and _GOAL_LINE.match(line):
            goal = index
            break
    if goal is None:
        head = "\n".join(lines[:_DIAGNOSTIC_LINES - 1])
        return head[:_DIAGNOSTIC_CHARACTERS - len(_DIAGNOSTIC_OMITTED) - 1].rstrip() + "\n" + _DIAGNOSTIC_OMITTED

    # Only contiguous indented lines belong to the displayed target. Blank lines,
    # cases, goals and new diagnostics are boundaries, not target continuations.
    goal_end = goal + 1
    while goal_end < len(lines):
        line = lines[goal_end]
        if (not line.strip() or not line[0].isspace()
                or _DIAGNOSTIC_HEADER.match(line) or _GOAL_LINE.match(line) or _CASE_LINE.match(line)):
            break
        goal_end += 1

    def shorten(line: str, limit: int) -> str:
        return line if len(line) <= limit else line[:limit - len(_DIAGNOSTIC_OMITTED)] + _DIAGNOSTIC_OMITTED

    selected = {index: shorten(lines[index], _DIAGNOSTIC_CHARACTERS // 5) for index in {0, goal_header}}
    case = next((i for i in range(goal - 1, goal_header, -1) if _CASE_LINE.match(lines[i])), None)
    if case is not None:
        selected[case] = shorten(lines[case], _DIAGNOSTIC_CHARACTERS // 5)
    selected[goal] = lines[goal]

    def render() -> str:
        excerpt, previous = [], -1
        for index in sorted(selected):
            if index > previous + 1:
                excerpt.append(_DIAGNOSTIC_OMITTED)
            excerpt.append(selected[index])
            previous = index
        if previous < len(lines) - 1:
            excerpt.append(_DIAGNOSTIC_OMITTED)
        return "\n".join(excerpt)

    def fits(excerpt: str) -> bool:
        return len(excerpt) <= _DIAGNOSTIC_CHARACTERS and len(excerpt.splitlines()) <= _DIAGNOSTIC_LINES

    excerpt = render()
    if len(excerpt) > _DIAGNOSTIC_CHARACTERS:
        allowance = _DIAGNOSTIC_CHARACTERS - len(excerpt) + len(lines[goal])
        selected[goal] = shorten(lines[goal], allowance)
    else:
        for index in range(goal + 1, goal_end):
            selected[index] = lines[index]
            if not fits(render()):
                del selected[index]
                break
    # Prefer nearby locals after reserving space for the target and its wrapping.
    for index in range(goal - 1, max(goal_header, goal - 5), -1):
        if index in selected:
            continue
        selected[index] = lines[index]
        if not fits(render()):
            del selected[index]
    return render()


def _failure_diagnostic(summary: dict[str, Any], error: Exception) -> None:
    if isinstance(error, EditRequestError):
        summary.update(error.details)
        if error.details.get("current_snapshot_sha256"):
            summary["source_sha256"] = error.details["current_snapshot_sha256"]
    if isinstance(error, (arena.LeanCompileError, arena.LeanTimeoutError)):
        output = error.result.output.strip()
        excerpt = _failure_preview(output)
        summary["diagnostic"] = {"severity": "error", "message": excerpt or str(error).partition("\n")[0][:_DIAGNOSTIC_CHARACTERS],
                                 "truncated": excerpt != output}
        if error.result.log_path:
            summary["diagnostics_path"] = error.result.log_path


def _failure(summary: dict[str, Any], details: dict[str, Any], error: Exception, *, phase: str) -> None:
    if isinstance(error, (arena.LeanTimeoutError, arena.CacheLockTimeout, TimeoutError)):
        status, valid = "timeout", None
    elif isinstance(error, arena.LeanCompileError) or phase == "edit":
        status, valid = "invalid", False
    elif isinstance(error, arena.WorkflowError):
        status, valid = "provisional" if "lacks exact" in str(error) or "lacks an exact" in str(error) else "check_failed", None
    else:
        status, valid = "infrastructure_error", None
    summary.update(status=status, valid=valid, error=str(error).splitlines()[0][:240], score=None, checkpoint=None)
    details.update(error=str(error), failure_phase=phase)
    _failure_diagnostic(summary, error)
    if isinstance(error, (arena.LeanCompileError, arena.LeanTimeoutError)):
        details["lean_run"] = {"output": error.result.output, "log_path": error.result.log_path,
                               "returncode": error.result.returncode, "timed_out": error.result.timed_out}


def _checkpoint(feedback: Feedback, snapshot: Path, digest: str, evaluation: arena.Evaluation, staging: Path) -> str:
    _unchanged(snapshot, digest)
    # Reuse normal naming/intake, but publish its staged copy atomically so host
    # selection cannot observe a partially copied checkpoint.
    staged = arena.checkpoint_candidate(snapshot, evaluation, staging)
    _unchanged(staged, digest)
    destination = feedback.checkpoint_directory() / staged.name
    _immutable_source(destination, staged.read_bytes().decode("utf-8"))
    _unchanged(destination, digest)
    receipt = staged.with_suffix(".json")
    if not receipt.is_file():
        raise arena.WorkflowError("checkpoint validation receipt unavailable")
    arena.write_json_atomic(destination.with_suffix(".json"), json.loads(receipt.read_text(encoding="utf-8")))
    return str(destination.resolve())


def _run_candidates(feedback: Feedback, request: dict[str, Any], *, single: bool = False, force_complete: bool = False) -> dict[str, Any]:
    """Evaluate all alternatives without editing the capsule's candidate file."""
    started = time.perf_counter()
    candidate, alternatives, policy, roots, initial_floor = _request(feedback, request, single=single)
    incumbent_metrics = deepcopy(feedback.settings.get("incumbent_metrics"))
    incumbent_source_sha256 = feedback.settings.get("incumbent_source_sha256")
    with arena.exclusive_file_lock(candidate.with_suffix(".edit.lock"),
            None if os.environ.get("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE") == "compile" else feedback.timeout):
        current = candidate.read_bytes()
        digest = arena.sha256_bytes(current)
        if digest != request["expected_sha256"]:
            raise EditRequestError("source conflict: expected_sha256 does not match current candidate",
                code="source_conflict", current_snapshot_sha256=digest)
        base = current.decode("utf-8")
        batch = feedback.root / ".feedback" / "batches" / uuid.uuid4().hex
        _immutable_source(batch / f"base-{digest}.lean", base)

    summaries, full, eligible = [], [], []
    for index, alternative in enumerate(alternatives):
        summary = {"label": alternative["label"], "status": "pending", "valid": None,
                   "source_sha256": None, "tokens": None, "heartbeats": None,
                   "compatibility_pct": None, "compatibility_status": "not_run",
                   "score": None, "score_breakdown": None, "incumbent_delta": None,
                   "checkpoint": None, "checkpoint_id": None,
                   "details_path": str(batch / "results.json"), "details_index": index}
        details: dict[str, Any] = {"request": alternative}
        summaries.append(summary)
        full.append(details)
        phase = "edit"
        try:
            allowed = {"label", "body", "source_text", "source", "edits"} if single else {"label", "body", "edits"}
            mutations = [key for key in ("body", "source_text", "source", "edits") if key in alternative]
            if set(alternative) - allowed or len(mutations) > 1 or (not single and len(mutations) != 1):
                raise arena.WorkflowError("provide only one source mutation" if single else "each alternative must provide exactly one of body or edits")
            if "edits" in alternative:
                edits = alternative["edits"]
                if not isinstance(edits, list) or not edits:
                    raise arena.WorkflowError("alternative edits must be a nonempty list")
                old = [edit.get("old") for edit in edits if isinstance(edit, dict)]
                if any(not isinstance(value, str) for value in old) or len(old) != len(edits) or len(set(old)) != len(old):
                    raise arena.WorkflowError("alternative edits must contain unique old strings")
                if any(set(edit) != {"old", "new"} for edit in edits):
                    raise arena.WorkflowError("each edit must provide old and new only")
            source = edit_source(feedback.row, base, {key: value for key, value in alternative.items() if key != "label"})
            declaration, _ = arena.extract_candidate_declaration(feedback.row, lean_source.candidate_text_from_bytes(source.encode("utf-8")))
            if len(declaration) > INTAKE_CHARACTERS:
                raise arena.WorkflowError(f"submitted declaration exceeds the contest's {INTAKE_CHARACTERS}-character intake limit")
            source_digest = arena.sha256_bytes(source.encode("utf-8"))
            snapshot = batch / f"{index}-{source_digest}.lean"
            _immutable_source(snapshot, source)
            summary["source_sha256"] = source_digest
            details["snapshot"] = str(snapshot)
            summary["snapshot_path"] = str(snapshot)
            phase = "quick_primary"
            quick = _evaluate(feedback, snapshot, source_digest, feedback.project, quick=True)
            details["quick_primary"] = arena.evaluation_payload(quick)
            phase = "exact_primary"
            exact = _evaluate(feedback, snapshot, source_digest, feedback.project, quick=False)
            details["exact_primary"] = arena.evaluation_payload(exact)
            tokens, heartbeats = _exact_metrics(exact)
            optimistic = policy.score(tokens=tokens, heartbeats=heartbeats, compatibility_pct=100.0)
            summary.update(status="valid", valid=True, tokens=tokens, heartbeats=heartbeats, optimistic_score=optimistic)
            phase = "checkpoint"
            summary["checkpoint"] = _checkpoint(feedback, snapshot, source_digest, exact, batch / "checkpoint-staging" / str(index))
            summary["checkpoint_id"] = Path(summary["checkpoint"]).name
            summary["checkpoint_validation"] = "exact"
            summary["checkpoint_receipt_path"] = str(Path(summary["checkpoint"]).with_suffix(".json"))
            eligible.append((optimistic, index, snapshot, source_digest, exact))
        except (arena.WorkflowError, OSError, RuntimeError, ValueError, TypeError, TimeoutError) as error:
            _failure(summary, details, error, phase=phase)
            if isinstance(error, (arena.LeanCompileError, arena.LeanTimeoutError)) and error.result.diagnostics_path:
                feedback.present_artifact(error.result.diagnostics_path, source, summary, details)
                if summary.get("diagnostics"):
                    summary.pop("diagnostic", None)

    # Compare highest upper bounds first, while still measuring every primary.
    # Newly scored valid alternatives can tighten the advisory incumbent floor.
    floor = initial_floor
    for optimistic, index, snapshot, source_digest, exact in sorted(eligible, key=lambda item: (-item[0], item[1])):
        summary, details = summaries[index], full[index]
        phase = "compatibility"
        try:
            if not force_complete and floor is not None and optimistic < floor:
                summary.update(status="valid_pruned", compatibility_status="skipped_optimistic_bound", pruning_floor=floor)
            else:
                compatibility = [{"environment": str(feedback.project), "passed": True}]
                details["compatibility"] = compatibility
                for project in roots:
                    try:
                        check = _evaluate(feedback, snapshot, source_digest, project, quick=True)
                        compatibility.append({"environment": str(project), "passed": True, "evaluation": arena.evaluation_payload(check)})
                    except arena.LeanCompileError as error:
                        _unchanged(snapshot, source_digest)
                        compatibility.append({"environment": str(project), "passed": False, "error": str(error),
                                              "log_path": error.result.log_path, "output": error.result.output})
                        failure: dict[str, Any] = {"environment": str(project)}
                        _failure_diagnostic(failure, error)
                        summary.setdefault("compatibility_failures", []).append(failure)
                pct = 100.0 * sum(item["passed"] for item in compatibility) / len(compatibility)
                score = policy.score(tokens=summary["tokens"], heartbeats=summary["heartbeats"], compatibility_pct=pct)
                breakdown = score_breakdown(policy, tokens=summary["tokens"], heartbeats=summary["heartbeats"],
                                            compatibility_pct=pct)
                delta = incumbent_score_delta(policy, tokens=summary["tokens"], heartbeats=summary["heartbeats"],
                    compatibility_pct=pct, incumbent_score=initial_floor, incumbent_metrics=incumbent_metrics,
                    incumbent_source_sha256=incumbent_source_sha256,
                    environment_fingerprint=exact.environment_fingerprint,
                    compatibility_environments=[str(feedback.project), *(str(root) for root in roots)])
                summary.update(status="valid_scored", compatibility_status="complete", compatibility_pct=pct,
                               score=score, score_breakdown=breakdown, incumbent_delta=delta)
                floor = max(floor, score) if floor is not None else score
        except (arena.WorkflowError, OSError, RuntimeError, ValueError, TypeError, TimeoutError) as error:
            # Missing compatibility evidence never becomes a compatibility fail
            # or a score. The prior immutable exact-valid checkpoint remains
            # reusable even if a later compatibility scratch is corrupted.
            summary.update(status="valid_unscored", valid=True, score=None,
                           compatibility_status="incomplete", error=str(error).splitlines()[0][:240])
            details.update(error=str(error), failure_phase=phase)
            _failure_diagnostic(summary, error)

    ranking = sorted((item for item in summaries if item["score"] is not None),
                     key=lambda item: (-item["score"], item["tokens"], item["heartbeats"], item["label"]))
    result = {"schema_version": 1, "status": "completed", "authoritative": False,
              "candidate": str(candidate), "base_source_sha256": digest,
              "original_tokens": policy.original_tokens, "original_heartbeats": policy.original_heartbeats,
              "incumbent_score": initial_floor, "alternatives": summaries,
              "ranking": [item["label"] for item in ranking],
              "best_label": ranking[0]["label"] if ranking else None,
              "wall_seconds": round(time.perf_counter() - started, 6),
              "details_path": str(batch / "results.json")}
    arena.write_json_atomic(Path(result["details_path"]), {"summary": result, "alternatives": full,
        "scoring_note": "Advisory comparison only. Normal host selection revalidates every retained candidate.",
        "compatibility_environments": [str(feedback.project), *(str(root) for root in roots)]})
    if not single:
        arena.record_event("compare_candidates", result)
    return result


@bind_feedback_scoring_policy
def compare_candidates(feedback: Feedback, request: dict[str, Any]) -> dict[str, Any]:
    return _run_candidates(feedback, request)


@bind_feedback_scoring_policy
def score_candidate(feedback: Feedback, request: dict[str, Any]) -> dict[str, Any]:
    """Run one source through the existing complete batch path, without pruning."""
    allowed = {"candidate", "expected_sha256", "body", "source_text", "source", "edits", "checkpoint_id"}
    if not isinstance(request, dict) or set(request) - allowed:
        raise arena.WorkflowError("score_candidate accepts candidate, expected_sha256 and one source mutation only")
    alternative = {"label": "candidate", **{key: request[key] for key in ("body", "source_text", "source", "edits") if key in request}}
    if "checkpoint_id" in request:
        guarded_request = {key: request[key] for key in ("candidate", "expected_sha256") if key in request}
        candidate, *_ = _request(feedback, guarded_request | {"alternatives": [alternative]}, single=True)
        with arena.exclusive_file_lock(candidate.with_suffix(".edit.lock"),
                None if os.environ.get("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE") == "compile" else feedback.timeout):
            destination_digest = arena.sha256_file(candidate)
            if destination_digest != request["expected_sha256"]:
                raise EditRequestError("source conflict: expected_sha256 does not match current candidate",
                    code="source_conflict", current_snapshot_sha256=destination_digest)
            _, source, _ = feedback.resolve_checkpoint(request["checkpoint_id"])
            source = edit_source(feedback.row, source,
                {key: value for key, value in alternative.items() if key != "label"},
                destination_sha256=destination_digest)
        alternative = {"label": "candidate", "source_text": source}
    result = _run_candidates(feedback, {key: request[key] for key in ("candidate", "expected_sha256") if key in request}
        | {"alternatives": [alternative]}, single=True, force_complete=True)
    response = {key: value for key, value in result.items() if key not in {"alternatives", "ranking", "best_label", "status"}}
    response.update(result["alternatives"][0], tool=SCORE_TOOL["name"])
    # The single response is one compact row; full batch evidence remains on disk.
    artifact = Path(result["details_path"])
    full = json.loads(artifact.read_text(encoding="utf-8"))
    full["batch_summary"] = result
    full["summary"] = response
    arena.write_json_atomic(artifact, full)
    arena.record_event("score_candidate", response)
    return response
