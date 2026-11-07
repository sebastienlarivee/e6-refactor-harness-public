"""One-call edits, source-bound feedback and checkpoints; optional stdio MCP transport.

The server has no model dependency and only exposes the configured task/capsule.
Authoritative validation continues to use arena_workflow's evaluator and caches.
"""

from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))
if __name__ == "__main__":
    _sys.modules["lean_tools.feedback_workflow"] = _sys.modules[__name__]

import argparse
import contextlib
import json
import os
import queue
import re
import sys
import tempfile
import threading
import time
from dataclasses import dataclass
from copy import deepcopy
from functools import wraps
from pathlib import Path
from typing import Any, TextIO

from lean_tools import arena_workflow as arena
from lean_tools import lean_source
from lean_tools.measurement_policy import (
    LEGACY_POLICY, SCORING_POLICY_ENV, resolve_scoring_policy, scoring_policy_context,
)
from lean_tools import diagnostic_presentation as presentation
from lean_tools.feedback_requests import AdmittedRequest, RequestJournal
from lean_tools import feedback_response
from lean_tools.feedback_contract import TOOL, TOOL_NAME, enabled_tools, feature_flags, score_capability, tool_catalog
from lean_tools import feedback_presentation
from lean_tools import check_budget
MAX_REQUEST_BYTES = 2 * 1024 * 1024
# Includes the executing call. Bounded admission keeps control messages readable
# even when the single execution worker is occupied by a long Lean invocation.
MAX_PENDING_REQUESTS = 8
CONFIG_NAME = "feedback-config.json"
EXCERPT_CHARACTERS = 1200


class EditRequestError(arena.WorkflowError):
    """A request failure with enough source-bound detail to repair the edit."""

    def __init__(self, message: str, **details: Any) -> None:
        super().__init__(message)
        self.details = details


def _source_excerpt(source: str, old: str = "") -> dict[str, Any]:
    """Show a bounded, line-numbered neighborhood without echoing a whole proof."""
    lines = source.splitlines()
    needle = old.splitlines()[0].strip() if old else ""
    fallback = next((index + 1 for index, line in enumerate(lines) if line.startswith(arena.TARGET_BEGIN.strip())), 0)
    anchor = next((index for index, line in enumerate(lines) if needle and needle in line), fallback)
    start, end = max(0, anchor - 3), min(len(lines), anchor + 9)
    rendered = "\n".join(f"{index + 1}: {lines[index]}" for index in range(start, end))
    return {"start_line": start + 1, "end_line": end, "text": rendered[:EXCERPT_CHARACTERS],
            "truncated": len(rendered) > EXCERPT_CHARACTERS or end < len(lines)}


def atomic_text(path: Path, source: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=path.name + ".", dir=path.parent)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
            stream.write(source)
        if path.suffix == ".lean":
            from lean_tools import lean_goal_state
            lean_goal_state.invalidate_source_revision(path)
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def immutable_text(path: Path, source: str) -> None:
    """Publish complete bytes once; a content-address collision is an error."""
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=".snapshot-", dir=path.parent)
    encoded = source.encode("utf-8")
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(encoded)
        try:
            os.link(temporary, path)
        except FileExistsError:
            if path.is_symlink() or path.read_bytes() != encoded:
                raise arena.WorkflowError("immutable artifact already exists with different source")
    finally:
        Path(temporary).unlink(missing_ok=True)


def configure_capsule(
    capsule: Path, project_root: Path, timeout_seconds: int = 600, *,
    candidate_batches: bool = False, goal_retrieval: bool = False,
    search_extensions: bool = False, unfinished_cases: bool = False, regional_profiler: bool = False,
    compatibility_roots: tuple[Path, ...] | list[Path] = (),
    original_tokens: int | None = None, original_heartbeats: int | None = None,
    incumbent_score: float | None = None,
    incumbent_metrics: dict[str, Any] | None = None, incumbent_source_sha256: str | None = None,
    retrieval_index: Path | None = None, retrieval_index_sha256: str | None = None,
    retrieval_pool_mode: str = "overlap",
    examples_index: Path | None = None, examples_index_sha256: str | None = None,
    examples_index_identity: dict[str, Any] | None = None,
    scoring_policy: str = LEGACY_POLICY,
    response_policy: str = "legacy",
) -> Path:
    if not isinstance(scoring_policy, str):
        raise ValueError("scoring_policy must be a supported version string")
    scoring_policy = resolve_scoring_policy(scoring_policy)
    if not isinstance(response_policy, str) or response_policy not in {"legacy", "compact-v1"}:
        raise ValueError("Unsupported response_policy")
    flags = feature_flags({"candidate_batches": candidate_batches, "goal_retrieval": goal_retrieval,
                           "search_extensions": search_extensions, "unfinished_cases": unfinished_cases,
                           "regional_profiler": regional_profiler})
    config = capsule / CONFIG_NAME
    settings = {
        "task": str((capsule / "Task.json").resolve()),
        "candidate": str((capsule / "Candidate.lean").resolve()),
        "project_root": str(project_root.resolve()),
        "fingerprint_registry": str((capsule / "environment-fingerprints.json").resolve()),
        "checkpoint_dir": str((capsule / "valid-candidates").resolve()),
        "timeout_seconds": timeout_seconds,
    }
    # Keep historical generic configuration bytes free of new default fields.
    if scoring_policy != LEGACY_POLICY:
        settings["scoring_policy"] = scoring_policy
    if response_policy != "legacy":
        settings["response_policy"] = response_policy
    # Absent flags retain the legacy disabled-feature semantics.
    settings.update({name: True for name, enabled in flags.items() if enabled})
    if not isinstance(retrieval_pool_mode, str) or retrieval_pool_mode not in {"overlap", "diverse", "hybrid"}:
        raise ValueError("retrieval_pool_mode must be overlap, diverse or hybrid")
    if retrieval_pool_mode != "overlap":
        if not goal_retrieval:
            raise ValueError("a nondefault retrieval_pool_mode requires goal_retrieval")
        settings["retrieval_pool_mode"] = retrieval_pool_mode
    if candidate_batches or original_tokens is not None or original_heartbeats is not None or compatibility_roots:
        settings.update(compatibility_roots=[str(root.resolve()) for root in compatibility_roots],
                        original_tokens=original_tokens, original_heartbeats=original_heartbeats,
                        incumbent_score=incumbent_score)
    if incumbent_metrics is not None or incumbent_source_sha256 is not None:
        from lean_tools.scoring import OriginalDenominatorScorePolicy, validate_incumbent_metrics
        receipt = validate_incumbent_metrics(
            OriginalDenominatorScorePolicy(original_tokens, original_heartbeats, scoring_policy), incumbent_metrics,
            incumbent_source_sha256=incumbent_source_sha256,
            compatibility_environments=[str(project_root.resolve()), *(str(root.resolve()) for root in compatibility_roots)])
        if receipt["score"] != incumbent_score:
            raise ValueError("incumbent metrics disagree with frozen scalar score")
        settings.update(incumbent_metrics=receipt, incumbent_source_sha256=incumbent_source_sha256)
    if retrieval_index is not None or retrieval_index_sha256 is not None:
        if (not goal_retrieval or retrieval_index is None
                or not isinstance(retrieval_index_sha256, str)
                or len(retrieval_index_sha256) != 64
                or any(char not in "0123456789abcdef" for char in retrieval_index_sha256)):
            raise ValueError("A prepared retrieval index requires an enabled tool, file and SHA256")
        settings.update(retrieval_index=str(retrieval_index.resolve()),
                        retrieval_index_sha256=retrieval_index_sha256)
    if search_extensions or any(value is not None for value in
                                (examples_index, examples_index_sha256, examples_index_identity)):
        from lean_tools.search_extensions import validate_settings
        settings.update(examples_index=str(examples_index.resolve()) if examples_index is not None else None,
                        examples_index_sha256=examples_index_sha256,
                        examples_index_identity=examples_index_identity)
        validate_settings(settings)
    if regional_profiler:
        from lean_tools.regional_profiler import profiler_capability
        _, row = arena.load_task(capsule / "Task.json")
        settings["profiler_capability"] = profiler_capability(row, project_root)
    settings["enabled_tools"] = enabled_tools(settings)
    atomic_text(
        config,
        json.dumps(settings, indent=2) + "\n",
    )
    return config


def codex_config_args(capsule: Path) -> list[str]:
    from lean_tools import persistent_quick_workflow as persistent
    config = capsule / CONFIG_NAME
    if not config.is_file():
        return []
    settings = json.loads(config.read_text(encoding="utf-8"))
    scoring_policy = resolve_scoring_policy(settings.get("scoring_policy", LEGACY_POLICY))
    allowed_tools = enabled_tools(settings)
    tool_timeout = 4 * settings["timeout_seconds"] + 30
    if feature_flags(settings)["candidate_batches"]:
        # Four alternatives can each need quick primary, exact compile/audit/
        # heartbeat work and every compatibility version. Per-Lean limits and
        # queue behavior remain unchanged; the transport permits the whole batch.
        tool_timeout = 4 * (5 + len(settings.get("compatibility_roots", []))) * settings["timeout_seconds"] + 30
    elif score_capability(settings):
        tool_timeout = (5 + len(settings["compatibility_roots"])) * settings["timeout_seconds"] + 30
    values = {
        "command": str(Path(sys.executable).resolve()),
        "args": [
            str(Path(__file__).resolve()),
            "--config",
            str(config.resolve()),
            "--serve",
        ],
        "cwd": str(capsule.resolve()),
        f"env.{SCORING_POLICY_ENV}": scoring_policy,
        # Codex's MCP launcher filters its inherited environment. Forward only harness
        # variables by name; never put loopback authentication tokens in command logs.
        "env_vars": sorted(
            {
                *(key for key in os.environ if key.startswith("LEAN_REFACTOR_") and key != SCORING_POLICY_ENV),
                # E5 builds its launch command before starting the broker. Codex resolves
                # these names at subprocess launch, after the endpoint becomes available.
                arena.PERSISTENT_QUICK_ENDPOINT_ENV,
                arena.PERSISTENT_QUICK_TOKEN_ENV,
                arena.PERSISTENT_QUICK_PROJECT_ROOT_ENV,
                persistent.FEEDBACK_SUPPORT_ENV,
                # The host starts the finite rerank service after prompt/config
                # preparation; forward names so the MCP child sees launch-time values.
                "LEAN_REFACTOR_RERANK_URL",
                "LEAN_REFACTOR_RERANK_TOKEN",
                "LEAN_REFACTOR_RERANK_CONFIG",
                "LEAN_REFACTOR_LEAN_PRIORITY",
                # Native Codex filters MCP inheritance independently of its
                # shell environment. HOME is a fresh capsule, so Lean must use
                # the host's explicitly mounted, pinned native installation.
                "ELAN_HOME",
                "PATH",
                "E6_ENVIRONMENTS_ROOT",
                "E6_RUNTIME_ROOT",
            }
        ),
        "startup_timeout_sec": 20,
        "tool_timeout_sec": tool_timeout,
        # This invocation authorizes only the capsule-scoped local feedback tool.
        # See https://learn.chatgpt.com/docs/extend/mcp?surface=cli.
        "enabled_tools": allowed_tools,
        "required": True,
        **{f"tools.{name}.approval_mode": "approve" for name in allowed_tools},
    }
    result: list[str] = [
        "-c", f"shell_environment_policy.set.{SCORING_POLICY_ENV}={json.dumps(scoring_policy)}"
    ]
    for key, value in values.items():
        result.extend(["-c", f"mcp_servers.lean_feedback.{key}={json.dumps(value)}"])
    return result


def edit_source(
    row: dict[str, Any], current: str, request: dict[str, Any], *,
    destination_sha256: str | None = None,
) -> str:
    """Stage edits on a base; rejection hashes identify the unchanged destination."""
    current_digest = arena.sha256_bytes(current.encode("utf-8"))
    destination_digest = current_digest if destination_sha256 is None else destination_sha256
    expected = request.get("expected_sha256")
    if expected is not None and expected != destination_digest:
        raise EditRequestError(
            "source conflict: expected_sha256 does not match current candidate",
            code="source_conflict", current_snapshot_sha256=destination_digest,
        )
    choices = [key for key in ("body", "source_text", "source", "edits") if key in request]
    if len(choices) > 1:
        raise arena.WorkflowError("provide only one of body, source_text (legacy source), or edits")
    source = current
    if "body" in request:
        if not isinstance(request["body"], str):
            raise arena.WorkflowError("body must be a string")
        source = (
            arena.render_environment(row)
            + arena.TARGET_BEGIN
            + row["signature"]
            + " :=\n"
            + request["body"].strip()
            + "\n"
            + arena.TARGET_END
        )
    elif "source_text" in request or "source" in request:
        source = request.get("source_text", request.get("source"))
        if isinstance(source, str) and "\n" not in source and source.strip().endswith(".lean"):
            raise arena.WorkflowError("source_text contains literal Lean text; use checkpoint_id to load a saved checkpoint")
    elif "edits" in request:
        if not isinstance(request["edits"], list):
            raise arena.WorkflowError("edits must be a list")
        for index, edit in enumerate(request["edits"]):
            if (
                not isinstance(edit, dict)
                or not isinstance(edit.get("old"), str)
                or not edit["old"]
                or not isinstance(edit.get("new"), str)
            ):
                raise EditRequestError("each edit needs nonempty old and string new",
                    code="invalid_edit", failed_edit_index=index, match_count=None,
                    current_snapshot_sha256=destination_digest, base_source_sha256=current_digest,
                    excerpt=_source_excerpt(source),
                    excerpt_source_sha256=arena.sha256_bytes(source.encode("utf-8")))
            matches = source.count(edit["old"])
            if matches != 1:
                raise EditRequestError(
                    f"edit {index} old text matched {matches} times; expected exactly one match",
                    code="edit_match_count", failed_edit_index=index, match_count=matches,
                    current_snapshot_sha256=destination_digest, base_source_sha256=current_digest,
                    excerpt=_source_excerpt(source, edit["old"]),
                    excerpt_source_sha256=arena.sha256_bytes(source.encode("utf-8")),
                )
            source = source.replace(edit["old"], edit["new"], 1)
    if not isinstance(source, str) or len(source.encode("utf-8")) > MAX_REQUEST_BYTES:
        raise arena.WorkflowError("source_text must be a string of at most 2 MiB")
    arena.extract_candidate_declaration(row, lean_source.candidate_text_from_bytes(source.encode("utf-8")))
    return source


@dataclass(frozen=True)
class CandidateSnapshot:
    """The immutable source identity evaluated and accepted by this request."""

    candidate: Path
    path: Path
    source: str
    sha256: str


def bind_feedback_scoring_policy(operation):
    """Bind direct helper calls as well as MCP dispatch to their capsule policy."""
    @wraps(operation)
    def bound(feedback, *args, **kwargs):
        policy = getattr(feedback, "scoring_policy", feedback.settings.get("scoring_policy", LEGACY_POLICY))
        with scoring_policy_context(policy):
            return operation(feedback, *args, **kwargs)
    return bound


class Feedback:
    def __init__(self, settings: dict[str, Any]) -> None:
        settings = deepcopy(settings)
        # Persisted settings without this field always mean historical semantics,
        # even if the hosting process currently measures another experiment.
        policy = settings.get("scoring_policy", LEGACY_POLICY)
        if not isinstance(policy, str):
            raise ValueError("scoring_policy must be a supported version string")
        self._scoring_policy = resolve_scoring_policy(policy)
        settings["scoring_policy"] = self.scoring_policy
        response_policy = settings.get("response_policy", "legacy")
        if not isinstance(response_policy, str) or response_policy not in {"legacy", "compact-v1"}:
            raise ValueError("Unsupported response_policy")
        incumbent_metrics = settings.get("incumbent_metrics")
        if isinstance(incumbent_metrics, dict) and incumbent_metrics.get("scoring_policy", LEGACY_POLICY) != self.scoring_policy:
            raise ValueError("incumbent metrics use a different scoring policy")
        feature_flags(settings)
        score_capability(settings)
        if settings.get("search_extensions") is True:
            from lean_tools.search_extensions import validate_settings
            validate_settings(settings)
        self.settings = settings
        self.task = Path(settings["task"]).resolve()
        self.candidate = Path(settings["candidate"]).resolve()
        self.project = Path(settings["project_root"]).resolve()
        self.root = self.candidate.parent
        self.request_journal = RequestJournal(self.root)
        self.timeout = int(settings.get("timeout_seconds", 600))
        if self.timeout <= 0:
            raise ValueError("timeout_seconds must be positive")
        self.quick_timeout = min(check_budget.DEFAULT_QUICK_SECONDS, self.timeout)
        _, self.row = arena.load_task(self.task)

    @property
    def scoring_policy(self) -> str:
        return self._scoring_policy

    @bind_feedback_scoring_policy
    def call(self, name: str, request: dict[str, Any]) -> dict[str, Any]:
        """Route only tools enabled in this capsule's immutable configuration."""
        if name not in enabled_tools(self.settings):
            raise ValueError("unknown tool")
        candidate = None
        if isinstance(request, dict):
            with contextlib.suppress(arena.WorkflowError, OSError, RuntimeError):
                candidate = self.candidate_path(request)
        result = self.request_journal.call(
            name, request, lambda: self._call(name, request), candidate=candidate)
        policy = self.settings.get("response_policy", "legacy")
        prefix_context = (feedback_presentation.prefix_context_for_result(
            result, row=self.row, project_root=self.project, capsule_root=self.root)
            if policy == "compact-v1" and name == TOOL_NAME else None)
        result = feedback_presentation.present_result(
            result, artifact_dir=self.root / ".feedback" / "responses",
            policy=policy, tool=name, prefix_context=prefix_context)
        return feedback_response.bound_result(result, artifact_dir=self.root / ".feedback" / "responses")

    def _call(self, name: str, request: dict[str, Any]) -> dict[str, Any]:
        try:
            if name == TOOL_NAME:
                return self.check(request)
            if name in {"compare_candidates", "score_candidate"}:
                from lean_tools import candidate_batches
                operation = (candidate_batches.compare_candidates if name == "compare_candidates"
                             else candidate_batches.score_candidate)
                return operation(self, request)
            if name == "retrieve_lemmas":
                from lean_tools import goal_retrieval
                return goal_retrieval.retrieve_lemmas(self, request)
            if name == "unfinished_cases":
                from lean_tools import unfinished_cases
                return unfinished_cases.unfinished_cases(self, request)
            if name == "profile_proof":
                from lean_tools import regional_profiler
                return regional_profiler.profile_proof(self, request)
            if name in {"suggest_proof", "search_examples", "example_neighbours"}:
                from lean_tools import search_extensions
                return search_extensions.call(self, name, request)
        except FileNotFoundError as error:
            # A missing selected draft is a repairable input error. Missing
            # infrastructure must not be mislabeled as a bad candidate.
            path = self.candidate_path(request) if isinstance(request, dict) else None
            missing_candidate = (path is not None and error.filename is not None
                                 and Path(error.filename).resolve() == path)
            result = {"schema_version": 1, "status": "invalid_request" if missing_candidate else "infrastructure_error",
                      "valid": None, "checkpoint": None,
                      "code": "candidate_missing" if missing_candidate else "resource_missing",
                      "error": f"candidate file does not exist: {path.name}" if missing_candidate else str(error)}
            if path is not None:
                result["candidate"] = str(path)
            arena.record_event(name, result)
            return result
        except (arena.WorkflowError, check_budget.DeadlineExpired) as error:
            if isinstance(error, (arena.CacheLockTimeout, arena.LeanTimeoutError, check_budget.DeadlineExpired)):
                return {"schema_version": 1, "status": "timeout", "valid": None, "checkpoint": None,
                        "error": str(error), "failure_kind": getattr(error, "code", "queue_timeout"),
                        "retry_hint": "The check is inconclusive. Retry explicitly with timeout_seconds up to the capsule maximum if more time is justified."}
            details = error.details if isinstance(error, EditRequestError) else {}
            result = {"schema_version": 1, "status": "source_conflict" if details.get("code") == "source_conflict" else "invalid_request",
                      "valid": None, "checkpoint": None, "error": str(error), **details}
            if details.get("current_snapshot_sha256"):
                result["source_sha256"] = details["current_snapshot_sha256"]
            if details.get("selected_source_path") and details.get("selected_source_sha256"):
                result["candidate"] = details["selected_source_path"]
                result["source_sha256"] = details["selected_source_sha256"]
            if isinstance(request, dict):
                try:
                    path = self.candidate_path(request)
                    result.setdefault("candidate", str(path))
                    result.setdefault("source_sha256", arena.sha256_file(path))
                    if not details.get("selected_source_path"):
                        result.setdefault("current_snapshot_sha256", result["source_sha256"])
                except (arena.WorkflowError, OSError):
                    pass
            arena.record_event(name, result)
            return result
        raise ValueError("unknown tool")

    def candidate_path(self, request: dict[str, Any]) -> Path:
        name = request.get("candidate", self.candidate.name)
        if (
            not isinstance(name, str)
            or "/" in name or "\\" in name
            or Path(name).name != name
            or not name.endswith(".lean")
        ):
            raise arena.WorkflowError(
                "candidate must be a .lean filename in this capsule"
            )
        path = (self.root / name).resolve()
        if path.parent != self.root:
            raise arena.WorkflowError("candidate escaped its capsule")
        return path

    def checkpoint_directory(self) -> Path:
        directory = Path(self.settings.get("checkpoint_dir", self.root / "valid-candidates"))
        resolved = directory.resolve()
        if not resolved.is_relative_to(self.root) or directory.is_symlink():
            raise arena.WorkflowError("checkpoint directory must stay inside this capsule")
        return resolved

    @bind_feedback_scoring_policy
    def resolve_checkpoint(self, checkpoint_id: Any) -> tuple[Path, str, dict[str, Any]]:
        """Resolve an ID through its receipt; a filename alone is never evidence."""
        if (not isinstance(checkpoint_id, str)
                or re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]{0,127}\.lean", checkpoint_id) is None):
            raise arena.WorkflowError("checkpoint_id must be a saved checkpoint basename, not a path")
        directory = self.checkpoint_directory()
        path = directory / checkpoint_id
        receipt_path = path.with_suffix(".json")
        if path.is_symlink() or receipt_path.is_symlink() or path.resolve().parent != directory:
            raise arena.WorkflowError("checkpoint_id must identify a regular file in this capsule's checkpoint directory")
        try:
            raw = path.read_bytes()
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        except (OSError, ValueError) as error:
            raise arena.WorkflowError("checkpoint or validation receipt unavailable; check the source before using it") from error
        digest = arena.sha256_bytes(raw)
        if (not isinstance(receipt, dict) or receipt.get("schema_version") != 1
                or receipt.get("source_sha256") != digest or receipt.get("valid") is not True
                or receipt.get("task_id") != self.row["name"]
                or not isinstance(receipt.get("validation"), str)
                or receipt["validation"] not in {"quick", "exact"}):
            raise arena.WorkflowError("checkpoint validation receipt does not match this source and task")
        evaluation = receipt.get("evaluation")
        if (not isinstance(evaluation, dict) or evaluation.get("valid") is not True
                or evaluation.get("task_id") != self.row["name"]
                or evaluation.get("source_sha256") != digest
                or evaluation.get("measurement_mode") != receipt["validation"]):
            raise arena.WorkflowError("checkpoint validation receipt lacks matching evaluation evidence")
        if evaluation.get("scoring_policy", LEGACY_POLICY) != self.scoring_policy:
            raise arena.WorkflowError("checkpoint scoring policy does not match this capsule")
        length, heartbeat = evaluation.get("length"), evaluation.get("heartbeat")
        if (not isinstance(length, dict) or not isinstance(heartbeat, dict)
                or length.get("candidate_tokens") != receipt.get("candidate_local_tokens")
                or heartbeat.get("candidate") != receipt.get("heartbeat")):
            raise arena.WorkflowError("checkpoint receipt metrics do not match its evaluation evidence")
        if receipt["validation"] == "exact":
            axioms = evaluation.get("axioms")
            if (evaluation.get("axiom_status") != "measured" or not isinstance(axioms, list)
                    or any(not isinstance(axiom, str) or axiom not in arena.ALLOWED_AXIOMS for axiom in axioms)
                    or type(receipt.get("candidate_local_tokens")) is not int
                    or receipt["candidate_local_tokens"] < 0
                    or type(receipt.get("heartbeat")) is not int or receipt["heartbeat"] < 0):
                raise arena.WorkflowError("exact checkpoint receipt lacks exact metrics and allowed-axiom evidence")
        try:
            source = raw.decode("utf-8")
        except UnicodeDecodeError as error:
            raise arena.WorkflowError("checkpoint source is not UTF-8") from error
        arena.extract_candidate_declaration(self.row, lean_source.candidate_text_from_bytes(raw))
        return path, source, receipt

    def checkpoint_operation(self, request: dict[str, Any]) -> dict[str, Any]:
        operation = request["operation"]
        if not isinstance(operation, str) or operation not in {"clone", "promote", "restore"}:
            raise arena.WorkflowError("operation must be check, clone, promote, or restore")
        if "mode" in request or "goal" in request:
            raise arena.WorkflowError("checkpoint copy operations do not evaluate; omit mode and goal, then use edit_check to validate")
        if operation != "clone" and any(key in request for key in ("body", "source_text", "source", "edits")):
            raise arena.WorkflowError("promote and restore copy a verified checkpoint unchanged; use clone to edit it")
        checkpoint, source, receipt = self.resolve_checkpoint(request.get("checkpoint_id"))
        if operation == "promote":
            candidate = self.candidate_path(request)
            if candidate != self.candidate:
                raise arena.WorkflowError("promote targets the configured main candidate")
        else:
            candidate = self.candidate_path(request)
        if operation == "clone" and ("candidate" not in request or candidate == self.candidate):
            raise arena.WorkflowError("clone requires a separate capsule candidate filename")
        with arena.exclusive_file_lock(candidate.with_suffix(".edit.lock"),
                None if os.environ.get("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE") == "compile" else self.timeout):
            current = candidate.read_bytes().decode("utf-8") if candidate.exists() else ""
            current_digest = arena.sha256_bytes(current.encode("utf-8"))
            expected = request.get("expected_sha256")
            if (candidate.exists() and expected is None) or (expected is not None and expected != current_digest):
                raise EditRequestError("checkpoint write requires expected_sha256 matching the current destination",
                    code="source_conflict", current_snapshot_sha256=current_digest)
            changes = {key: request[key] for key in ("body", "source_text", "source", "edits") if key in request}
            source = edit_source(self.row, source, changes, destination_sha256=current_digest)
            atomic_text(candidate, source)
        digest = arena.sha256_bytes(source.encode("utf-8"))
        return {"schema_version": 1, "status": "cloned" if operation == "clone" else "restored" if operation == "restore" else "promoted",
                "operation": operation, "candidate": str(candidate), "source_sha256": digest,
                "valid": None, "evaluation_status": "not_run", "checkpoint": str(checkpoint),
                "checkpoint_id": checkpoint.name, "checkpoint_source_sha256": receipt["source_sha256"],
                "checkpoint_validation": receipt["validation"], "source_matches_checkpoint": digest == receipt["source_sha256"],
                "validation_note": "Copied source only; host selection still validates retained candidates."}

    def present_artifact(
        self, path: str, source: str, result: dict[str, Any], full: dict[str, Any]
    ) -> None:
        """Remap cached observations to this snapshot, without changing its verdict."""
        try:
            artifact = json.loads(Path(path).read_text(encoding="utf-8"))
            if not isinstance(artifact, dict):
                raise TypeError("diagnostic artifact is not an object")
            generated_path = artifact.get("generated_source_path")
            generated = (
                Path(generated_path).read_bytes().decode("utf-8")
                if generated_path else artifact["generated_source"]
            )
            raw = artifact["raw_diagnostics"]
            if not isinstance(generated, str) or not isinstance(raw, list) or not all(isinstance(item, dict) for item in raw):
                raise ValueError("diagnostic artifact omitted source or diagnostics")
            if arena.sha256_bytes(generated.encode("utf-8")) != artifact["generated_source_sha256"]:
                raise ValueError("diagnostic source hash mismatch")
            normalized_source = lean_source.candidate_text_from_bytes(source.encode("utf-8"))
            declaration, _ = arena.extract_candidate_declaration(self.row, normalized_source)
            encoding = artifact.get("position_encoding", "utf-16")
            if generated_path and arena.sha256_bytes(source.encode("utf-8")) != artifact["candidate_source_sha256"]:
                raise ValueError("diagnostic candidate source hash mismatch")
            try:
                source_map = presentation.SourceMap.for_declaration(normalized_source, generated, declaration)
            except presentation.PositionError:
                if not generated_path:
                    raise
                source_map = None  # Separate audit/helper files contain no candidate declaration.
            shown = presentation.present_diagnostics(raw, source_map, source=generated, position_encoding=encoding)
            full["diagnostic_presentation"] = shown
            result["diagnostics"] = shown["diagnostics"]
            result["diagnostics_compacted"] = shown["diagnostics_compacted"]
            result["diagnostics_truncation"] = shown["diagnostics_truncation"]
            result["diagnostics_path"] = path
            if generated_path:
                result["generated_source_path"] = generated_path
                result["compiler_log_path"] = artifact.get("compiler_log_path")
        except (OSError, ValueError, KeyError, TypeError) as error:
            result["diagnostics_note"] = f"diagnostic artifact unavailable: {error}"

    def prepare_snapshot(self, request: dict[str, Any]) -> CandidateSnapshot:
        """Apply a capsule edit under its lock, then release an immutable snapshot."""
        candidate = self.candidate_path(request)
        # Only hold the edit lock while reading/updating the draft. Evaluation uses an
        # immutable copy, so another child can work without corrupting its checkpoint.
        with arena.exclusive_file_lock(
            candidate.with_suffix(".edit.lock"),
            None if os.environ.get("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE") == "compile" else self.timeout
        ):
            current = (
                candidate.read_bytes().decode("utf-8")
                if candidate.exists()
                else arena.render_candidate_scaffold(self.row)
            )
            expected = request.get("expected_sha256")
            current_digest = arena.sha256_bytes(current.encode("utf-8"))
            if expected is not None and expected != current_digest:
                raise EditRequestError("source conflict: expected_sha256 does not match current candidate",
                    code="source_conflict", current_snapshot_sha256=current_digest)
            if "checkpoint_id" in request:
                _, base, _ = self.resolve_checkpoint(request["checkpoint_id"])
                source = edit_source(self.row, base,
                    {key: value for key, value in request.items() if key != "expected_sha256"},
                    destination_sha256=current_digest)
            else:
                source = edit_source(self.row, current, request)
            digest = arena.sha256_bytes(source.encode("utf-8"))
            snapshot = self.root / ".feedback" / "sources" / f"{digest}.lean"
            immutable_text(snapshot, source)
            if not candidate.exists() or candidate.read_bytes() != source.encode("utf-8"):
                atomic_text(candidate, source)
        return CandidateSnapshot(candidate, snapshot, source, digest)

    @bind_feedback_scoring_policy
    def observe_snapshot(
        self, submission: CandidateSnapshot, result: dict[str, Any], full: dict[str, Any]
    ) -> None:
        """Collect advisory feedback; observation cannot accept a checkpoint."""
        source = lean_source.candidate_text_from_bytes(submission.source.encode("utf-8"))
        digest = submission.sha256
        from lean_tools import advisory_feedback
        declaration, _ = arena.extract_candidate_declaration(self.row, source)
        registry = self.settings.get("fingerprint_registry")
        fingerprint = arena.measurement_environment_fingerprint(
            self.row,
            self.project,
            registry_path=Path(registry) if registry else None,
        )
        full["advisory"] = advisory_feedback.observe(
            self.row,
            declaration,
            self.project,
            self.timeout,
            fingerprint=fingerprint,
        )
        result.update(full["advisory"])
        # Keep submitted source identity separate from instrumented source.
        result["measurement_source_sha256"] = result["source_sha256"]
        result["source_sha256"] = digest
        result["checkpoint"] = None
        if full["advisory"].get("diagnostics"):
            try:
                measured_source = advisory_feedback.source_for_measurement(
                    self.row, declaration, self.project
                )
                if arena.sha256_bytes(measured_source.encode("utf-8")) != result["measurement_source_sha256"]:
                    raise ValueError("diagnostic measurement source hash mismatch")
                source_map = presentation.SourceMap.for_declaration(
                    source, measured_source, declaration
                )
                shown = presentation.present_diagnostics(
                    full["advisory"]["diagnostics"], source_map
                )
                full["advisory_generated_source"] = measured_source
                full["advisory_presentation"] = shown
                result["diagnostics"] = shown["diagnostics"]
                result["diagnostics_compacted"] = shown["diagnostics_compacted"]
                result["diagnostics_truncation"] = shown["diagnostics_truncation"]
            except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
                result["diagnostics_note"] = f"diagnostic presentation unavailable: {error}"

    @bind_feedback_scoring_policy
    def evaluate_snapshot(
        self, submission: CandidateSnapshot, mode: str,
        result: dict[str, Any], full: dict[str, Any],
    ) -> None:
        """Evaluate the frozen source and let the evaluator accept its checkpoint."""
        source, digest, snapshot = submission.source, submission.sha256, submission.path
        registry = (
            Path(self.settings["fingerprint_registry"])
            if self.settings.get("fingerprint_registry")
            else None
        )
        evaluation = arena.evaluate_candidate(
            self.task,
            snapshot,
            self.project,
            timeout_seconds=self.timeout,
            quick=mode == "quick",
            fingerprint_registry=registry,
        )
        full["evaluation"] = arena.evaluation_payload(evaluation)
        result["cache"] = full["evaluation"]["cache"]
        result["timing"] = full["evaluation"]["timing"]
        if evaluation.diagnostics_path:
            self.present_artifact(evaluation.diagnostics_path, source, result, full)
        if arena.sha256_file(snapshot) != digest:
            raise arena.WorkflowError(
                "evaluated snapshot changed; no checkpoint was saved"
            )
        check_budget.stage("checkpoint", source_sha256=digest)
        checkpoints = self.checkpoint_directory()
        checkpoint = arena.checkpoint_candidate(
            snapshot, evaluation, checkpoints
        )
        receipt_path = checkpoint.with_suffix(".json")
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        result.update(
            status="valid",
            valid=True,
            tokens=evaluation.candidate_local_tokens,
            heartbeat=evaluation.heartbeat,
            heartbeat_status="exact" if mode == "exact" else "not_run",
            checkpoint=str(checkpoint),
            checkpoint_id=checkpoint.name,
            checkpoint_validation=receipt["validation"],
            checkpoint_receipt_path=str(receipt_path),
        )
        cache_root = arena.evaluation_cache_root()
        if mode == "quick" and cache_root is not None:
            declaration, _ = arena.extract_candidate_declaration(
                self.row, lean_source.candidate_text_from_bytes(source.encode("utf-8"))
            )
            exact_key = arena.evaluation_cache_key(
                self.task,
                self.row,
                declaration,
                evaluation.environment_fingerprint,
                "exact",
            )
            cached_exact = arena.cached_evaluation(
                arena.evaluation_cache_path(cache_root, "exact", exact_key),
                snapshot,
            )
            if cached_exact is not None:
                full["cached_exact"] = arena.evaluation_payload(cached_exact)
                result.update(
                    heartbeat=cached_exact.heartbeat,
                    heartbeat_status="cached_exact",
                )

    @bind_feedback_scoring_policy
    def check(self, request: dict[str, Any]) -> dict[str, Any]:
        if not isinstance(request, dict):
            raise arena.WorkflowError("tool arguments must be an object")
        if request.get("operation", "check") != "check" or request.get("mode", "quick") != "quick":
            if "timeout_seconds" in request:
                raise arena.WorkflowError("timeout_seconds is available only for quick checks")
            return self._check(request)
        timeout = self.quick_request_timeout(request)
        with check_budget.scope(timeout, started=self.request_journal.admitted_monotonic,
                                observe=self.request_journal.update_stage):
            check_budget.stage("source_lock")
            return self._check(request)

    def quick_request_timeout(self, request: dict[str, Any]) -> float:
        try:
            return check_budget.validate_seconds(request.get("timeout_seconds", self.quick_timeout),
                                                 maximum=min(check_budget.MAX_QUICK_SECONDS, self.timeout))
        except ValueError as error:
            raise arena.WorkflowError(str(error)) from error

    def _check(self, request: dict[str, Any]) -> dict[str, Any]:
        if not isinstance(request, dict):
            raise arena.WorkflowError("tool arguments must be an object")
        if set(request) - {"candidate", "body", "source_text", "source", "expected_sha256", "mode", "edits", "goal", "operation", "checkpoint_id", "timeout_seconds"}:
            raise arena.WorkflowError("unknown edit_check argument; use body, source_text, edits, or checkpoint_id")
        if request.get("operation", "check") != "check":
            return self.checkpoint_operation(request)
        started = time.perf_counter()
        mode = request.get("mode", "quick")
        if not isinstance(mode, str) or mode not in {"quick", "exact", "advisory"}:
            raise arena.WorkflowError("mode must be quick, advisory, or exact")
        submission = self.prepare_snapshot(request)
        candidate, snapshot = submission.candidate, submission.path
        source, digest = submission.source, submission.sha256
        result: dict[str, Any] = {
            "schema_version": 1,
            "candidate": str(candidate),
            "source_sha256": digest,
            "snapshot_path": str(snapshot),
            "mode": mode,
        }
        if check_budget.current() is not None:
            result.update(timeout_seconds=check_budget.current().seconds, timeout_scope="quick_request",
                          cleanup_grace_seconds=check_budget.CLEANUP_GRACE_SECONDS)
        full: dict[str, Any] = {}
        try:
            if mode == "advisory":
                self.observe_snapshot(submission, result, full)
            else:
                self.evaluate_snapshot(submission, mode, result, full)
        except (arena.WorkflowError, check_budget.DeadlineExpired) as error:
            result.update(
                status=(
                    "timeout"
                    if isinstance(
                        error, (arena.CacheLockTimeout, arena.LeanTimeoutError, check_budget.DeadlineExpired)
                    )
                    else "invalid"
                    if isinstance(error, arena.LeanCompileError)
                    else "check_failed"
                ),
                valid=None,
                error=str(error),
            )
            if result["status"] == "invalid":
                result["valid"] = False
            full["error"] = str(error)
            result["failure_kind"] = getattr(error, "code", "operation_timeout" if result["status"] == "timeout" else "evaluation_error")
            failure_details = getattr(error, "failure_details", None)
            if failure_details:
                full["failure_details"] = failure_details
            if result["status"] == "timeout":
                result["timeout_stage"] = ((failure_details or {}).get("failure_phase")
                                           or (check_budget.current().stage if check_budget.current() is not None else None))
            if result["status"] == "timeout":
                result["retry_hint"] = "The check is inconclusive; no automatic cold replay occurred. Retry explicitly with a larger timeout_seconds (up to the capsule maximum) if justified."
            if isinstance(error, (arena.LeanCompileError, arena.LeanTimeoutError)):
                full["lean_run"] = {
                    "output": error.result.output,
                    "log_path": error.result.log_path,
                    "returncode": error.result.returncode,
                    "timed_out": error.result.timed_out,
                }
                if error.result.log_path:
                    result["diagnostics_path"] = error.result.log_path
                    if error.result.command == ["persistent-lean-lsp"]:
                        self.present_artifact(error.result.log_path, source, result, full)
                if error.result.diagnostics_path:
                    self.present_artifact(error.result.diagnostics_path, source, result, full)
        except (OSError, RuntimeError) as error:
            result.update(status="infrastructure_error", valid=None, error=str(error))
            full["error"] = str(error)
        budget_expired = check_budget.current() is not None and check_budget.current().deadline <= time.monotonic()
        if (request.get("goal") is not None and not budget_expired
                and result.get("status") in {"valid", "invalid"}):
            tools_root = Path(__file__).resolve().parent
            if str(tools_root) not in sys.path:
                sys.path.insert(0, str(tools_root))
            from lean_tools import lean_goal_state
            try:
                check_budget.stage("goal_diagnostics")
                goal = request["goal"]
                full["goals"] = lean_goal_state.query_goal_state(
                    self.task,
                    snapshot,
                    self.project,
                    line=goal["line"],
                    column=goal.get("column"),
                    timeout_seconds=self.timeout,
                )
                result["goals"] = full["goals"]["rendered"]
                result["goal_position"] = full["goals"]["position"]["candidate"]
                result["goal_diagnostics"] = full["goals"]["diagnostics"]
                result["goal_details_path"] = full["goals"].get("details_path")
                result.update(lean_goal_state.attach_goal_handles(self, snapshot, digest, full["goals"]))
            except (RuntimeError, OSError, ValueError, KeyError, TypeError) as error:
                result["goal_error"] = str(error)
        elif self.settings.get("goal_retrieval") is True or self.settings.get("search_extensions") is True:
            from lean_tools import lean_goal_state
            result.update(lean_goal_state.known_goal_handles(self, snapshot, digest))
        if (self.settings.get("unfinished_cases") is True and result.get("status") == "invalid"
                and (check_budget.current() is None or check_budget.current().deadline > time.monotonic())):
            from lean_tools import unfinished_cases
            check_budget.stage("residual_diagnostics")
            result["unfinished_cases"] = unfinished_cases.failure_feedback(self, submission, result, full)
        diagnostics = result.get("diagnostics")
        if isinstance(diagnostics, list):
            error_text = result.get("error")
            if diagnostics and isinstance(error_text, str) and error_text:
                full.setdefault("error", error_text)
                result["error"] = error_text.splitlines()[0]
            if result.get("goal_diagnostics") == diagnostics:
                # The complete goal observation remains in full["goals"].
                del result["goal_diagnostics"]
                result["goal_diagnostics_ref"] = "diagnostics"
        result["wall_seconds"] = round(time.perf_counter() - started, 6)
        log = (
            self.root / ".feedback" / "results" / f"{time.time_ns()}-{digest[:12]}.json"
        )
        result["details_path"] = str(log)
        atomic_text(
            log,
            json.dumps({"summary": result, **full}, ensure_ascii=False, indent=2)
            + "\n",
        )
        arena.record_event("edit_check", result)
        return result





def _execution_error(feedback: Feedback, error: BaseException) -> dict[str, Any]:
    value: dict[str, Any] = {"schema_version": 1, "status": "infrastructure_error",
                             "valid": None, "error": str(error)}
    journal = feedback.request_journal
    if journal.last_request_id:
        value["feedback_request"] = {
            "request_id": journal.last_request_id,
            "request_path": str(journal.directory / f"{journal.last_request_id}.json"),
        }
    return value


class _MCPWriter:
    def __init__(self, stream: TextIO, journal: RequestJournal):
        self.stream = stream
        self.journal = journal
        self.lock = threading.Lock()
        self.failure: BaseException | None = None

    def send(self, response: dict[str, Any], *, request_id: str | None = None) -> None:
        with self.lock:
            if self.failure is not None:
                raise self.failure
            try:
                self.stream.write(feedback_response.json_text(response) + "\n")
                self.stream.flush()
            except (OSError, ValueError) as error:
                self.failure = error
                self.journal.transport_outcome(request_id, "write_failed", error=error)
                raise
            else:
                self.journal.transport_outcome(request_id, "written")

    def progress(self, token: str | int | None, admission: AdmittedRequest, stage: int) -> None:
        if token is not None:
            # MCP progress is opt-in via request metadata. It does not establish
            # whether a client displays the message or a model receives it.
            message = ("Queued Lean feedback request " if stage == 0 else "Starting Lean feedback request ")
            self.send({"jsonrpc": "2.0", "method": "notifications/progress", "params": {
                "progressToken": token, "progress": stage,
                "message": message + admission.request_id}})


@dataclass
class _QueuedCall:
    identity: str | int
    name: str
    arguments: Any
    admission: AdmittedRequest
    progress_token: str | int | None


def serve(feedback: Feedback, input_stream: TextIO, output_stream: TextIO) -> None:
    """Read/admit independently; execute FIFO with exactly one source/Lean worker.

    Normal EOF drains accepted calls. Output failure lets an executing call
    finish; unstarted admissions are interrupted on abnormal shutdown.
    The reader is a daemon so broken output cannot strand serve() on stdin.read.
    """
    journal = feedback.request_journal
    writer = _MCPWriter(output_stream, journal)
    waiting: queue.Queue[_QueuedCall] = queue.Queue(maxsize=MAX_PENDING_REQUESTS)
    pending: dict[str | int, _QueuedCall] = {}
    state_lock = threading.Lock()
    stopped, reader_done = threading.Event(), threading.Event()
    reader_errors: list[BaseException] = []

    def read_requests():
        try:
            while not stopped.is_set() and writer.failure is None:
                line = input_stream.readline(MAX_REQUEST_BYTES + 1)
                if not line or stopped.is_set() or writer.failure is not None:
                    break
                identity = None
                error_code = -32600
                try:
                    if len(line.encode("utf-8")) > MAX_REQUEST_BYTES:
                        while not line.endswith("\n") and line:
                            line = input_stream.readline(MAX_REQUEST_BYTES + 1)
                        raise ValueError("request exceeds 2 MiB")
                    error_code = -32700
                    request = json.loads(line)
                    error_code = -32600
                    if not isinstance(request, dict):
                        raise TypeError("request must be an object")
                    proposed_id = request.get("id")
                    if proposed_id is None:
                        continue
                    if (type(proposed_id) not in {str, int}
                            or len(str(proposed_id).encode("utf-8")) > 1024):
                        raise ValueError("request id must be a string or integer of at most 1024 UTF-8 bytes")
                    identity = proposed_id
                    with state_lock:
                        if identity in pending:
                            raise ValueError("request id is already pending")
                    method = request.get("method")
                    if method == "initialize":
                        result = {
                            "protocolVersion": "2025-06-18", "capabilities": {"tools": {}},
                            "serverInfo": {"name": "lean-feedback", "version": "1.0.0"},
                        }
                    elif method == "ping":
                        result = {}
                    elif method == "tools/list":
                        result = {"tools": tool_catalog(feedback.settings)}
                    elif method == "tools/call":
                        error_code = -32602
                        params = request.get("params", {})
                        if not isinstance(params, dict):
                            raise ValueError("params must be an object")
                        if params.get("name") not in enabled_tools(feedback.settings):
                            raise ValueError("unknown tool")
                        meta = params.get("_meta", {})
                        if not isinstance(meta, dict):
                            raise ValueError("request _meta must be an object")
                        progress_token = meta.get("progressToken")
                        if "progressToken" in meta and (
                                type(progress_token) not in {str, int}
                                or len(str(progress_token).encode("utf-8")) > 1024):
                            raise ValueError("progressToken must be a string or integer of at most 1024 UTF-8 bytes")
                        with state_lock:
                            if stopped.is_set() or writer.failure is not None:
                                break
                            if len(pending) >= MAX_PENDING_REQUESTS:
                                error_code = -32000
                                raise ValueError(f"feedback queue is full ({MAX_PENDING_REQUESTS} pending calls); request was not accepted; inspect existing requests before retrying")
                            if progress_token is not None and any(
                                    item.progress_token == progress_token for item in pending.values()):
                                raise ValueError("progressToken is already pending")
                            arguments = params.get("arguments", {})
                            admission = journal.admit(params["name"], arguments, identity=identity,
                                pending_ahead=len(pending), requested_candidate=(
                                    arguments.get("candidate", feedback.candidate.name)
                                    if isinstance(arguments, dict) else None),
                                budget_seconds=(feedback.quick_request_timeout(arguments)
                                    if params["name"] == TOOL_NAME and isinstance(arguments, dict)
                                    and arguments.get("mode", "quick") == "quick"
                                    and arguments.get("operation", "check") == "check" else None))
                            call = _QueuedCall(identity, params["name"], arguments, admission, progress_token)
                            try:
                                writer.progress(progress_token, admission, 0)
                            except BaseException as error:
                                journal.interrupt_queued(admission, error)
                                raise
                            pending[identity] = call
                            waiting.put_nowait(call)
                        continue
                    else:
                        error_code = -32601
                        raise ValueError("unknown method")
                    reply = {"jsonrpc": "2.0", "id": identity, "result": result}
                except (ValueError, TypeError, OSError, arena.WorkflowError) as error:
                    message = presentation.utf8_excerpt(str(error), 4096)[0]
                    reply = {"jsonrpc": "2.0", "id": identity,
                             "error": {"code": error_code, "message": message}}
                writer.send(reply)
        except BaseException as error:
            reader_errors.append(error)
        finally:
            reader_done.set()

    original_stdout = sys.stdout
    # This is a dedicated stdio server: stdout belongs to the protocol for its
    # entire lifetime. Capture output_stream before redirecting; reader and
    # helper-thread incidental prints then cannot cross into the protocol.
    diagnostic_stdout = sys.stderr
    sys.stdout = diagnostic_stdout
    reader = threading.Thread(target=read_requests, name="lean-feedback-reader", daemon=True)
    shutdown_error: BaseException | None = None
    try:
        reader.start()
        while True:
            if writer.failure is not None:
                raise writer.failure
            if reader_errors:
                raise reader_errors[0]
            try:
                call = waiting.get(timeout=0.05)
            except queue.Empty:
                if reader_done.is_set() and not reader_errors and writer.failure is None:
                    break
                continue
            try:
                if writer.failure is not None:
                    raise writer.failure
                if reader_errors:
                    raise reader_errors[0]
                with journal.rpc_request(call.identity, admission=call.admission):
                    writer.progress(call.progress_token, call.admission, 1)
                    try:
                        value = feedback.call(call.name, call.arguments)
                    except (RuntimeError, ValueError, TypeError, KeyError, OSError) as error:
                        if not call.admission.claimed:
                            journal.interrupt_queued(call.admission, error, failed=True)
                        value = _execution_error(feedback, error)
                    value = feedback_response.bound_result(
                        value, artifact_dir=feedback.root / ".feedback" / "responses",
                        envelope=lambda item: feedback_response.mcp_response(item, call.identity),
                        max_response_bytes=feedback_response.RESPONSE_BYTE_LIMIT - 1)
                    writer.send(feedback_response.mcp_response(value, call.identity),
                                request_id=journal.last_request_id)
            finally:
                with state_lock:
                    pending.pop(call.identity, None)
                if not call.admission.claimed:
                    journal.interrupt_queued(call.admission, writer.failure or RuntimeError("request did not start"))
    except BaseException as error:
        shutdown_error = error
        raise
    finally:
        stopped.set()
        try:
            with state_lock:
                while True:
                    try:
                        call = waiting.get_nowait()
                    except queue.Empty:
                        break
                    pending.pop(call.identity, None)
                    journal.interrupt_queued(call.admission, shutdown_error or RuntimeError("feedback server stopped"))
        finally:
            if reader_done.is_set():
                reader.join()
            if sys.stdout is diagnostic_stdout:
                sys.stdout = original_stdout


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--serve", action="store_true")
    parser.add_argument("--tool", default=TOOL_NAME, help="Configured tool to invoke in JSON-stdin mode")
    args = parser.parse_args()
    feedback = Feedback(json.loads(args.config.read_text(encoding="utf-8")))
    if args.serve:
        serve(feedback, sys.stdin, sys.stdout)
    else:
        if args.tool not in enabled_tools(feedback.settings):
            parser.error("unknown tool")
        request = sys.stdin.read(MAX_REQUEST_BYTES + 1)
        if len(request.encode("utf-8")) > MAX_REQUEST_BYTES:
            parser.error("request exceeds 2 MiB")
        try:
            value = feedback.call(args.tool, json.loads(request or "{}"))
        except (RuntimeError, ValueError, TypeError, KeyError, OSError) as error:
            value = _execution_error(feedback, error)
            try:
                value = feedback_response.bound_result(
                    value, artifact_dir=feedback.root / ".feedback" / "responses")
            except (OSError, ValueError) as persistence_error:
                # A failed archive must not print an unbounded chained traceback.
                value["error"] = presentation.utf8_excerpt(str(error), 4096)[0]
                value["error_details_unavailable"] = True
                value["persistence_error"] = presentation.utf8_excerpt(str(persistence_error), 512)[0]
            print(feedback_response.json_text(value))
            return 1
        print(feedback_response.json_text(value))
    return 0


if __name__ == "__main__":
    sys.stdin.reconfigure(encoding="utf-8")
    sys.stdout.reconfigure(encoding="utf-8")
    raise SystemExit(main())
