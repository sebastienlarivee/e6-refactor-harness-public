from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import argparse
import json
import math
import re
import sys
import tempfile
import time
from collections import Counter
from collections.abc import Sequence
from contextlib import ExitStack
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any


from lean_tools import arena_workflow as arena
from lean_tools import lean_source
from lean_tools import diagnostic_presentation as presentation
from lean_tools import persistent_quick_workflow as persistent
SCHEMA_VERSION = 1
SUGGESTION_MARKER = "__LRH_SUGGEST__"
DEFAULT_TIMEOUT_SECONDS = 600
MAX_LSP_ATTEMPT_SECONDS = 120
MAX_SUMMARY_BYTES = 65_536
MAX_SUMMARY_ENVIRONMENTS = 8
MAX_SUMMARY_RESULTS = 32
MAX_DIAGNOSTIC_PREVIEWS = 2
MAX_DIAGNOSTIC_MESSAGE_CHARS = 500
MAX_SUGGESTION_PREVIEWS = 3
MAX_SUGGESTION_CHARS = 1_500
SETUP_FILE_FAILURE_PATTERN = re.compile(
    r"(?is)\blake(?:\.exe)?\s+setup-file\b.*?\b(?:failed|exited)\b"
)
MODULE_DEPENDENCY_FAILURE_PATTERN = re.compile(
    r"(?is)(?:\bcannot\s+[`'\"]?import(?:\s+all)?[`'\"]?\s+the\s+module\b|"
    r"\bunknown module prefix\b|\bobject file\b[^\r\n]*\.olean\b"
    r"[^\r\n]*\bdoes not exist\b|\bfailed to load (?:the )?module\b|"
    r"\bmodule\s+[`'\"]?[^\r\n]+?\bhas not been built\b)"
)


@dataclass(frozen=True)
class TacticProbe:
    name: str
    tactic: str


DEFAULT_CAPABILITY_PROBES = (
    TacticProbe("exact?", "exact?"),
    TacticProbe("apply?", "apply?"),
    TacticProbe("rw?", "rw?"),
    TacticProbe("simp?", "simp?"),
    TacticProbe("simpa?", "simpa?"),
    TacticProbe("dsimp?", "dsimp?"),
    TacticProbe("grind", "grind"),
    TacticProbe("grind?", "grind?"),
    TacticProbe("omega", "omega"),
    TacticProbe("aesop", "aesop"),
    TacticProbe("aesop?", "aesop?"),
    TacticProbe("library_search", "library_search"),
    TacticProbe("linarith", "linarith"),
    TacticProbe("nlinarith", "nlinarith"),
    TacticProbe("ring", "ring"),
    TacticProbe("norm_num", "norm_num"),
    TacticProbe("tauto", "tauto"),
    TacticProbe("itauto", "itauto"),
)

DEFAULT_SUGGESTION_TACTICS = (
    "exact?",
    "apply?",
    "rw?",
    "simp?",
    "simpa?",
    "dsimp?",
    "grind?",
)


class ContextToolError(RuntimeError):
    pass


@dataclass(frozen=True)
class CompileWatchdog:
    """A per-operation allowance; discovery batches have no E6 aggregate cap."""
    seconds: float


def discovery_deadline(timeout_seconds: float) -> float | CompileWatchdog:
    if not math.isfinite(timeout_seconds) or timeout_seconds <= 0:
        raise ContextToolError("discovery timeout must be positive and finite")
    if arena.lean_timeout_scope() == "compile":
        return CompileWatchdog(timeout_seconds)
    return time.monotonic() + timeout_seconds


def discovery_remaining(deadline: float | CompileWatchdog) -> float:
    if isinstance(deadline, CompileWatchdog):
        return deadline.seconds
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise ContextToolError("discovery deadline expired")
    return remaining


def checked_environment_guard(
    row: dict[str, Any],
    project_root: Path,
    deadline: float,
    expected: str | None = None,
) -> str:
    discovery_remaining(deadline)
    guard = arena.environment_fingerprint_guard_sha256(row, project_root)
    if expected is not None and guard != expected:
        raise ContextToolError("discovery environment changed during the request")
    discovery_remaining(deadline)
    return guard


@dataclass(frozen=True)
class SourceObservation:
    seconds: float
    diagnostics: tuple[dict[str, Any], ...]
    backend: str = "lsp"
    fallback_reason: str | None = None
    source_sha256: str | None = None
    document_version: int | None = None
    reused_source: bool = False
    diagnostics_omitted: int = 0
    batch_failure_reason: str | None = None

    @property
    def errors(self) -> tuple[dict[str, Any], ...]:
        return tuple(
            item for item in self.diagnostics if item.get("severity") == "error"
        )


def infrastructure_diagnostics(
    diagnostics: Sequence[dict[str, Any]],
) -> list[dict[str, Any]]:
    failures: list[dict[str, Any]] = []
    for item in diagnostics:
        message = str(item.get("message", ""))
        setup_failed = SETUP_FILE_FAILURE_PATTERN.search(message) is not None
        dependency_failed = (
            MODULE_DEPENDENCY_FAILURE_PATTERN.search(message) is not None
        )
        if (
            setup_failed
            or dependency_failed
            or persistent.is_infrastructure_message(message)
        ):
            failures.append(item)
    return failures


def infrastructure_summary(diagnostics: Sequence[dict[str, Any]]) -> str:
    messages = [
        re.sub(r"\s+", " ", str(item.get("message", ""))).strip()
        for item in infrastructure_diagnostics(diagnostics)
    ]
    return "; ".join(messages[:3])[:2_000]


def capability_probe_declaration(tactic: str) -> str:
    """Return a disposable declaration that tests tactic syntax on ``True``."""
    return f"example : True := by\n  first | ({tactic}; all_goals trivial) | trivial\n"


def target_prefix(row: dict[str, Any], project_root: Path) -> str:
    """Return the shared evaluator prefix immediately before the target."""
    try:
        return lean_source.exact_source_prefix(row, project_root).text
    except lean_source.SourceDocumentError as error:
        raise ContextToolError(str(error)) from error


def source_for_declaration(
    row: dict[str, Any], declaration: str, project_root: Path
) -> str:
    return lean_source.quick_compile_harness(row, declaration, project_root)


def capability_probe_source(
    row: dict[str, Any], tactic: str, project_root: Path
) -> str:
    return target_prefix(row, project_root) + capability_probe_declaration(tactic)


def suggestion_declaration(
    row: dict[str, Any], tactic: str, candidate_text: str | None
) -> str:
    if candidate_text is None:
        return f"{row['signature']} := by\n  {tactic}"
    occurrences = candidate_text.count(SUGGESTION_MARKER)
    if occurrences != 1:
        raise ContextToolError(
            "suggestion candidate must contain exactly one "
            f"{SUGGESTION_MARKER} marker; found {occurrences}"
        )
    replaced = candidate_text.replace(SUGGESTION_MARKER, tactic)
    try:
        declaration, _body = arena.extract_candidate_declaration(row, replaced)
    except arena.WorkflowError as error:
        raise ContextToolError(str(error)) from error
    return declaration


def observe_sources(
    project_root: Path,
    sources: Sequence[str],
    timeout_seconds: float,
    *,
    deadline: float | None = None,
) -> list[SourceObservation]:
    """Elaborate variants with LSP, safely falling back to isolated cold Lean.

    Keep completed observations when a later source fails. Cold fallback retries
    only the failed and remaining sources, sharing the original batch deadline.
    """
    if not sources:
        return []
    deadline = discovery_deadline(timeout_seconds) if deadline is None else deadline
    compile_scope = arena.lean_timeout_scope() == "compile"
    observations: list[SourceObservation] = []
    resident_failure: str | None = None
    if arena.persistent_quick_matches_project(project_root):
        try:
            for source in sources:
                response = persistent.feedback_request(
                    source, discovery_remaining(deadline), operation="observe"
                )
                values = tuple(response["diagnostics"])
                if infrastructure_diagnostics(values):
                    raise persistent.PersistentQuickError(
                        "Lean resident setup/module infrastructure diagnostic: "
                        + infrastructure_summary(values)
                    )
                observations.append(
                    SourceObservation(
                        seconds=response["wall_seconds"],
                        diagnostics=values,
                        backend="resident",
                        diagnostics_omitted=response.get("diagnostics_omitted", 0),
                        source_sha256=arena.sha256_bytes(source.encode("utf-8")),
                        document_version=response["document_version"],
                        reused_source=response["reused_source"],
                    )
                )
            return observations
        except (persistent.PersistentQuickError, TimeoutError) as error:
            resident_failure = str(error)
    with tempfile.TemporaryDirectory(
        prefix="lrh-context-", dir=arena.evaluation_scratch_parent()
    ) as temporary:
        work_root = Path(temporary)
        document_path = work_root / "ContextProbe.lean"
        stderr_path = work_root / "lean-lsp.stderr.log"
        document_path.write_text(sources[len(observations)], encoding="utf-8")
        try:
            if resident_failure is not None:
                raise persistent.PersistentQuickError(resident_failure)
            with ExitStack() as stack:
                stack.enter_context(
                    arena.resource_gate.permit_from_environment(
                        "lean",
                        priority=0,
                        timeout_seconds=None if compile_scope else max(0.0, deadline - time.monotonic()),
                        metadata={
                            "purpose": "context-probe",
                            "project_root": str(project_root.resolve()),
                        },
                    )
                )
                session = persistent.LeanLspSession(
                    project_root.resolve(),
                    document_path,
                    stderr_path,
                    discovery_remaining(deadline) if compile_scope else min(
                        discovery_remaining(deadline), MAX_LSP_ATTEMPT_SECONDS
                    ),
                )
                session.request_deadline = (time.monotonic() + discovery_remaining(deadline)
                    if compile_scope else min(deadline, time.monotonic() + MAX_LSP_ATTEMPT_SECONDS))
                stack.enter_context(session)
                for index, source in enumerate(sources):
                    session.request_deadline = (time.monotonic() + discovery_remaining(deadline)
                        if compile_scope else min(deadline, time.monotonic() + MAX_LSP_ATTEMPT_SECONDS))
                    seconds, diagnostics = (
                        session.open_document(source)
                        if index == 0
                        else session.change_document(source)
                    )
                    diagnostic_values = tuple(item.as_json() for item in diagnostics)
                    if infrastructure_diagnostics(diagnostic_values):
                        raise persistent.PersistentQuickError(
                            "Lean LSP setup/module infrastructure diagnostic: "
                            + infrastructure_summary(diagnostic_values)
                        )
                    observations.append(
                        SourceObservation(
                            seconds=seconds,
                            diagnostics=diagnostic_values,
                            source_sha256=arena.sha256_bytes(source.encode("utf-8")),
                            document_version=getattr(session, "version", None),
                        )
                    )
                session.request_deadline = None
        except (persistent.PersistentQuickError, TimeoutError) as error:
            detail = ""
            if stderr_path.is_file():
                detail = stderr_path.read_text(
                    encoding="utf-8", errors="replace"
                ).strip()
            reason = str(error)
            if detail:
                reason += "\n" + detail[-2_000:]
            observations = [
                replace(item, batch_failure_reason=reason) for item in observations
            ]
            for source in sources[len(observations) :]:
                document_path.write_text(source, encoding="utf-8")
                try:
                    cold = persistent.run_cold_lean(
                        document_path,
                        project_root.resolve(),
                        work_root,
                        discovery_remaining(deadline),
                    )
                except (persistent.PersistentQuickError, TimeoutError) as cold_error:
                    raise ContextToolError(
                        "Lean LSP probe failed and cold Lean fallback also failed: "
                        f"LSP: {reason}; cold: {cold_error}"
                    ) from cold_error
                diagnostics = [
                    item.as_json()
                    for item in persistent.cold_json_diagnostics(cold.output)
                ]
                if infrastructure_diagnostics(diagnostics):
                    raise ContextToolError(
                        "cold Lean setup infrastructure failure: "
                        + infrastructure_summary(diagnostics)
                    )
                if cold.returncode != 0 and not any(
                    item.get("severity") == "error" for item in diagnostics
                ):
                    diagnostics.append(
                        persistent.Diagnostic(
                            "error",
                            None,
                            None,
                            "Lean exited with status "
                            f"{cold.returncode}: "
                            f"{arena.compact_lean_diagnostic(cold.output, 2_000)}",
                        ).as_json()
                    )
                if infrastructure_diagnostics(diagnostics):
                    raise ContextToolError(
                        "Lean LSP probe failed and cold Lean fallback reported a "
                        "setup/module infrastructure failure: "
                        + infrastructure_summary(diagnostics)
                    )
                observations.append(
                    SourceObservation(
                        seconds=cold.seconds,
                        diagnostics=tuple(diagnostics),
                        backend="cold",
                        fallback_reason=reason,
                        source_sha256=arena.sha256_bytes(source.encode("utf-8")),
                    )
                )
        return observations


def compact_diagnostics(
    observation: SourceObservation,
    limit: int = 30,
    *,
    source: str | None = None,
    source_map: presentation.SourceMap | None = None,
) -> tuple[list[dict[str, Any]], bool]:
    shown = presentation.present_diagnostics(
        observation.diagnostics,
        source_map,
        source=source,
        information_limit=limit,
        position_encoding="unicode" if observation.backend == "cold" else "utf-16",
    )
    return shown["diagnostics"], (shown["diagnostics_compacted"] > 0
                                   or shown["diagnostics_truncation"]["messages_truncated"] > 0)


def diagnostic_report(
    observation: SourceObservation,
    source: str,
    source_map: presentation.SourceMap | None = None,
    candidate_path: Path | None = None,
) -> dict[str, Any]:
    shown = presentation.present_diagnostics(
        observation.diagnostics,
        source_map,
        source=source,
        position_encoding="unicode" if observation.backend == "cold" else "utf-16",
    )
    path = presentation.archive_diagnostics(
        observation.diagnostics,
        shown,
        source=source,
        source_map=source_map,
        candidate_path=candidate_path,
        service_omitted=observation.diagnostics_omitted,
    )
    return {
        "diagnostics": shown["diagnostics"],
        "diagnostic_counts": dict(Counter(
            str(item.get("severity", "unknown")) for item in observation.diagnostics
        )),
        "diagnostics_truncated": (shown["diagnostics_compacted"] > 0
                                  or shown["diagnostics_truncation"]["messages_truncated"] > 0),
        "diagnostics_compacted": shown["diagnostics_compacted"],
        "diagnostics_truncation": shown["diagnostics_truncation"],
        "diagnostics_path": str(path),
        "service_diagnostics_omitted": observation.diagnostics_omitted,
    }


def common_fallback_reason(observations: Sequence[SourceObservation]) -> str | None:
    reasons = list(
        dict.fromkeys(
            observation.fallback_reason or observation.batch_failure_reason
            for observation in observations
            if observation.fallback_reason or observation.batch_failure_reason
        )
    )
    if len(reasons) > 1:
        raise ContextToolError("inconsistent fallback reasons within one environment")
    return reasons[0] if reasons else None


def task_version_label(
    row: dict[str, Any], index: int, lean_version: str | None = None
) -> str | None:
    version_info = row.get("version_info")
    if not isinstance(version_info, list):
        return None
    labels = [
        next(iter(value))
        for value in version_info
        if isinstance(value, dict)
        and len(value) == 1
        and isinstance(next(iter(value)), str)
    ]
    if lean_version is not None:
        match = re.search(r"\bversion\s+([0-9]+(?:\.[0-9]+)+)", lean_version)
        if match is not None:
            detected = "v" + match.group(1)
            if detected in labels:
                return detected
    if index >= len(version_info):
        return None
    value = version_info[index]
    if not isinstance(value, dict) or len(value) != 1:
        return None
    label = next(iter(value))
    return label if isinstance(label, str) else None


def environment_identity(
    row: dict[str, Any],
    project_root: Path,
    index: int,
    timeout_seconds: float,
    fingerprint_registry: Path | None = None,
) -> dict[str, Any]:
    try:
        if fingerprint_registry is not None:
            entry = arena.environment_fingerprint_registry_entry(
                row,
                project_root,
                fingerprint_registry,
                validate_guard=True,
            )
            lean_version = str(entry["lean_version"])
        else:
            lean_version = arena.recorded_lean_version(project_root, timeout_seconds)
    except arena.WorkflowError as error:
        raise ContextToolError(str(error)) from error
    version_label = task_version_label(row, index, lean_version)
    primary_label = task_version_label(row, 0)
    is_primary = (
        version_label == primary_label
        if version_label is not None and primary_label is not None
        else index == 0
    )
    return {
        "project_root": str(project_root.resolve()),
        "role": "primary" if is_primary else "compatibility",
        "task_version": version_label,
        "lean_version": lean_version,
    }


def _capability_environment_report_uncached(
    row: dict[str, Any],
    project_root: Path,
    probes: Sequence[TacticProbe],
    timeout_seconds: float,
    index: int = 0,
    fingerprint_registry: Path | None = None,
    *,
    deadline: float | None = None,
    environment_guard: str | None = None,
) -> dict[str, Any]:
    deadline = discovery_deadline(timeout_seconds) if deadline is None else deadline
    guard = checked_environment_guard(row, project_root, deadline, environment_guard)
    sources = []
    for probe in probes:
        discovery_remaining(deadline)
        sources.append(capability_probe_source(row, probe.tactic, project_root))
    observations = observe_sources(
        project_root, sources, discovery_remaining(deadline), deadline=deadline
    )
    checked_environment_guard(row, project_root, deadline, guard)
    tactics: list[dict[str, Any]] = []
    for probe, source, observation in zip(probes, sources, observations, strict=True):
        discovery_remaining(deadline)
        tactics.append(
            {
                "name": probe.name,
                "tactic": probe.tactic,
                "available": tactic_is_recognized(observation),
                "backend": observation.backend,
                "fallback_reason": observation.fallback_reason,
                "batch_failure_reason": observation.batch_failure_reason,
                "environment_guard_sha256": guard,
                "source_sha256": observation.source_sha256,
                "document_version": observation.document_version,
                "reused_source": observation.reused_source,
                "seconds": round(observation.seconds, 6),
                **diagnostic_report(observation, source),
            }
        )
    identity = environment_identity(
        row, project_root, index, discovery_remaining(deadline), fingerprint_registry
    )
    checked_environment_guard(row, project_root, deadline, guard)
    return {
        **identity,
        "environment_guard_sha256": guard,
        "fallback_reason": common_fallback_reason(observations),
        "tactics": tactics,
    }


def capability_environment_report(
    row: dict[str, Any],
    project_root: Path,
    probes: Sequence[TacticProbe],
    timeout_seconds: float,
    index: int = 0,
    fingerprint_registry: Path | None = None,
    *,
    deadline: float | None = None,
) -> dict[str, Any]:
    """Share one deadline across guard work, cache admission, probes and identity."""
    deadline = discovery_deadline(timeout_seconds) if deadline is None else deadline
    guard = checked_environment_guard(row, project_root, deadline)
    root = arena.evaluation_cache_root()
    if root is None:
        return _capability_environment_report_uncached(
            row,
            project_root,
            probes,
            discovery_remaining(deadline),
            index,
            fingerprint_registry,
            deadline=deadline,
            environment_guard=guard,
        )
    if fingerprint_registry is not None:
        arena.environment_fingerprint_registry_entry(
            row, project_root, fingerprint_registry, validate_guard=True
        )
    sources = []
    for probe in probes:
        discovery_remaining(deadline)
        sources.append(capability_probe_source(row, probe.tactic, project_root))
    key = arena.sha256_bytes(
        json.dumps(
            {
                "schema_version": 1,
                "environment_guard": guard,
                "source_sha256": [
                    arena.sha256_bytes(source.encode("utf-8")) for source in sources
                ],
                "probes": [(probe.name, probe.tactic) for probe in probes],
                "tool_sha256": arena.sha256_file(Path(__file__)),
                "service_sha256": arena.sha256_file(Path(persistent.__file__)),
                "index": index,
            },
            sort_keys=True,
        ).encode("utf-8")
    )
    path = root / "capabilities" / key[:2] / f"{key}.json"

    def read_cached() -> dict[str, Any] | None:
        try:
            saved = json.loads(path.read_text(encoding="utf-8"))
            if saved.get("cache_key") == key and isinstance(saved.get("report"), dict):
                return {**saved["report"], "cache_status": "hit", "cache_key": key}
        except (OSError, ValueError, AttributeError):
            pass
        return None

    cached = read_cached()
    if cached is not None:
        checked_environment_guard(row, project_root, deadline, guard)
        return cached
    path.parent.mkdir(parents=True, exist_ok=True)
    with arena.exclusive_file_lock(
        path.with_suffix(".lock"), None if arena.lean_timeout_scope() == "compile" else discovery_remaining(deadline)
    ):
        checked_environment_guard(row, project_root, deadline, guard)
        cached = read_cached()
        if cached is not None:
            discovery_remaining(deadline)
            return cached
        report = _capability_environment_report_uncached(
            row,
            project_root,
            probes,
            discovery_remaining(deadline),
            index,
            fingerprint_registry,
            deadline=deadline,
            environment_guard=guard,
        )
        checked_environment_guard(row, project_root, deadline, guard)
        # A recovered infrastructure failure remains explicit and is not fossilized.
        # Ordinary unknown-tactic diagnostics are deterministic capability outcomes.
        if report.get("fallback_reason") is None:
            arena.write_json_atomic(path, {"cache_key": key, "report": report})
        discovery_remaining(deadline)
        return {**report, "cache_status": "miss", "cache_key": key}


def capability_report(
    task_path: Path,
    project_roots: Sequence[Path],
    probes: Sequence[TacticProbe] = DEFAULT_CAPABILITY_PROBES,
    timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS,
    fingerprint_registry: Path | None = None,
) -> dict[str, Any]:
    deadline = discovery_deadline(timeout_seconds)
    _document, row = arena.load_task(task_path)
    environments = [
        capability_environment_report(
            row,
            root,
            probes,
            discovery_remaining(deadline),
            index=index,
            fingerprint_registry=fingerprint_registry,
            deadline=deadline,
        )
        for index, root in enumerate(project_roots)
    ]
    portable = [
        probe.name
        for probe in probes
        if all(
            next(
                tactic
                for tactic in environment["tactics"]
                if tactic["name"] == probe.name
            )["available"]
            for environment in environments
        )
    ]
    return {
        "schema_version": SCHEMA_VERSION,
        "command": "capabilities",
        "task": row["name"],
        "source_kind": "project" if arena.is_project_resident(row) else "standalone",
        "portable_tactics": portable,
        "environments": environments,
    }


TRY_THIS_PATTERN = re.compile(r"(?ims)\bTry (?:this|these):\s*(.+?)(?=\n\s*\n|\Z)")
UNAVAILABLE_PATTERN = re.compile(
    r"(?i)(unknown tactic|unexpected (?:identifier|token)|"
    r"expected (?:tactic|term), got|no parser)"
)


def extract_try_suggestions(diagnostics: Sequence[dict[str, Any]]) -> list[str]:
    suggestions: list[str] = []
    for diagnostic in diagnostics:
        message = diagnostic.get("message")
        if not isinstance(message, str):
            continue
        for match in TRY_THIS_PATTERN.finditer(message):
            suggestion = match.group(1).strip()
            suggestion = re.sub(r"^\[apply\]\s*", "", suggestion)
            if suggestion and suggestion not in suggestions:
                suggestions.append(suggestion)
    return suggestions


def tactic_is_recognized(observation: SourceObservation) -> bool:
    return not infrastructure_diagnostics(observation.diagnostics) and not any(
        UNAVAILABLE_PATTERN.search(str(item.get("message", "")))
        for item in observation.errors
    )


def suggestion_environment_report(
    row: dict[str, Any],
    project_root: Path,
    tactics: Sequence[str],
    candidate_text: str | None,
    timeout_seconds: int,
    index: int = 0,
    fingerprint_registry: Path | None = None,
    candidate_path: Path | None = None,
) -> dict[str, Any]:
    guard = arena.environment_fingerprint_guard_sha256(row, project_root)
    declarations = [
        suggestion_declaration(row, tactic, candidate_text) for tactic in tactics
    ]
    sources = [
        source_for_declaration(row, declaration, project_root)
        for declaration in declarations
    ]
    observations = observe_sources(project_root, sources, timeout_seconds)
    results: list[dict[str, Any]] = []
    for tactic, declaration, source, observation in zip(
        tactics, declarations, sources, observations, strict=True
    ):
        source_map = (
            presentation.SourceMap.for_replacement(
                candidate_text, source, declaration, SUGGESTION_MARKER, tactic
            )
            if candidate_text is not None
            else None
        )
        results.append(
            {
                "tactic": tactic,
                "recognized": tactic_is_recognized(observation),
                "solved": not observation.errors,
                "suggestions": extract_try_suggestions(observation.diagnostics),
                "backend": observation.backend,
                "fallback_reason": observation.fallback_reason,
                "batch_failure_reason": observation.batch_failure_reason,
                "environment_guard_sha256": guard,
                "source_sha256": observation.source_sha256,
                "document_version": observation.document_version,
                "reused_source": observation.reused_source,
                "seconds": round(observation.seconds, 6),
                **diagnostic_report(observation, source, source_map, candidate_path),
            }
        )
    identity = environment_identity(
        row, project_root, index, timeout_seconds, fingerprint_registry
    )
    if arena.environment_fingerprint_guard_sha256(row, project_root) != guard:
        raise ContextToolError("discovery environment changed during the request")
    return {
        **identity,
        "environment_guard_sha256": guard,
        "fallback_reason": common_fallback_reason(observations),
        "results": results,
    }


def suggestion_report(
    task_path: Path,
    project_roots: Sequence[Path],
    tactics: Sequence[str] = DEFAULT_SUGGESTION_TACTICS,
    candidate_path: Path | None = None,
    timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS,
    fingerprint_registry: Path | None = None,
) -> dict[str, Any]:
    _document, row = arena.load_task(task_path)
    candidate_text = (
        candidate_path.read_text(encoding="utf-8")
        if candidate_path is not None
        else None
    )
    environments = [
        suggestion_environment_report(
            row,
            root,
            tactics,
            candidate_text,
            timeout_seconds,
            index=index,
            fingerprint_registry=fingerprint_registry,
            candidate_path=candidate_path,
        )
        for index, root in enumerate(project_roots)
    ]
    portable = [
        tactic
        for tactic in tactics
        if all(
            next(
                result
                for result in environment["results"]
                if result["tactic"] == tactic
            )["recognized"]
            for environment in environments
        )
    ]
    solved_everywhere = [
        tactic
        for tactic in tactics
        if all(
            next(
                result
                for result in environment["results"]
                if result["tactic"] == tactic
            )["solved"]
            for environment in environments
        )
    ]
    return {
        "schema_version": SCHEMA_VERSION,
        "command": "suggest",
        "task": row["name"],
        "goal": "marker" if candidate_path is not None else "theorem-entry",
        "candidate": (
            str(candidate_path.resolve()) if candidate_path is not None else None
        ),
        "portable_tactics": portable,
        "solved_in_every_environment": solved_everywhere,
        "environments": environments,
    }


def archive_report(
    report: dict[str, Any], output_path: Path | None = None
) -> Path:
    """Persist the full report before publishing a summary that points to it."""
    if output_path is None:
        candidate = report.get("candidate")
        directory = presentation.artifact_directory(
            Path(candidate) if candidate else None
        ).parent / "discovery"
        digest = arena.sha256_bytes(
            json.dumps(report, ensure_ascii=False, sort_keys=True).encode("utf-8")
        )
        output_path = directory / f"{report['command']}-{digest}.json"
    output_path = output_path.resolve()
    arena.write_json_atomic(output_path, report)
    return output_path


def _summary_text(
    target: dict[str, Any], key: str, value: Any, limit: int = 500
) -> None:
    if not isinstance(value, str):
        target[key] = value
        return
    target[key] = value[:limit]
    if len(value) > limit:
        target[key + "_omitted_chars"] = len(value) - limit


def _summary_result(item: dict[str, Any], command: str) -> dict[str, Any]:
    """Keep outcomes and bounded useful previews; source and logs live in artifacts."""
    summary: dict[str, Any] = {}
    for key in ("name", "tactic"):
        if key in item:
            _summary_text(summary, key, item[key], 160)
    for key in (
        "available", "recognized", "solved", "backend", "seconds",
        "diagnostics_path", "source_sha256", "document_version", "reused_source",
        "service_diagnostics_omitted",
    ):
        if key in item:
            summary[key] = item[key]
    diagnostics = item.get("diagnostics", [])
    counts: Counter[str] = Counter()
    for diagnostic in diagnostics:
        counts[str(diagnostic.get("severity", "unknown"))] += diagnostic.get("count", 1)
    summary["diagnostic_counts"] = item.get("diagnostic_counts", dict(counts))
    failures = [value for value in diagnostics if value.get("severity") == "error"]
    previews: list[dict[str, Any]] = []
    for diagnostic in failures[:MAX_DIAGNOSTIC_PREVIEWS]:
        preview = {"severity": "error"}
        location = diagnostic.get("location")
        if isinstance(location, dict):
            preview["location"] = {
                key: location[key] for key in ("scope", "line", "column", "column_encoding")
                if key in location
            }
        for key in ("line", "character"):
            if key in diagnostic:
                preview[key] = diagnostic[key]
        _summary_text(
            preview, "message", str(diagnostic.get("message", "")),
            MAX_DIAGNOSTIC_MESSAGE_CHARS,
        )
        previews.append(preview)
    summary["diagnostics"] = previews
    summary["diagnostic_previews_omitted"] = max(0, len(failures) - len(previews))
    if command == "suggest":
        suggestions = item.get("suggestions", [])
        # Never publish a partial tactic as a ready-to-use suggestion.
        shown = [value for value in suggestions if len(value) <= MAX_SUGGESTION_CHARS]
        summary["suggestions"] = shown[:MAX_SUGGESTION_PREVIEWS]
        summary["suggestions_omitted"] = len(suggestions) - len(summary["suggestions"])
    return summary


def compact_cli_report(report: dict[str, Any], report_path: Path) -> dict[str, Any]:
    """Bound stdout as valid JSON while retaining version and availability facts.

    Detailed APIs and --full-output retain their previous shape. A content-addressed
    full report and each source-bound diagnostics artifact support selective reads.
    """
    summary: dict[str, Any] = {
        "schema_version": report["schema_version"],
        "command": report["command"],
        "output_detail": "summary",
        "report_path": str(report_path),
    }
    for key in ("task", "source_kind", "goal", "candidate"):
        if key in report:
            _summary_text(summary, key, report[key], 1_024)
    for key in ("portable_tactics", "solved_in_every_environment"):
        if key in report:
            values = report[key]
            summary[key] = [value for value in values if len(value) <= 160][:MAX_SUMMARY_RESULTS]
            summary[key + "_omitted"] = len(values) - len(summary[key])
    summary["summary_limits"] = {
        "output_bytes": MAX_SUMMARY_BYTES,
        "diagnostics_per_result": MAX_DIAGNOSTIC_PREVIEWS,
        "diagnostic_message_chars": MAX_DIAGNOSTIC_MESSAGE_CHARS,
        "suggestions_per_result": MAX_SUGGESTION_PREVIEWS,
        "suggestion_chars": MAX_SUGGESTION_CHARS,
    }
    environments = report.get("environments", [])
    summary["environments"] = []
    summary["environments_omitted"] = max(0, len(environments) - MAX_SUMMARY_ENVIRONMENTS)
    results_key = "tactics" if report["command"] == "capabilities" else "results"
    for environment in environments[:MAX_SUMMARY_ENVIRONMENTS]:
        shown: dict[str, Any] = {}
        for key in (
            "project_root", "role", "task_version", "lean_version",
            "environment_guard_sha256", "cache_status", "cache_key", "fallback_reason",
        ):
            if key in environment:
                _summary_text(shown, key, environment[key], 1_024 if key == "project_root" else 500)
        results = environment[results_key]
        shown[results_key] = [
            _summary_result(item, report["command"])
            for item in results[:MAX_SUMMARY_RESULTS]
        ]
        shown[results_key + "_omitted"] = max(0, len(results) - MAX_SUMMARY_RESULTS)
        summary["environments"].append(shown)

    def encoded_size() -> int:
        return len(json.dumps(summary, ensure_ascii=False, indent=2).encode("utf-8")) + 1

    # Prefer the complete outcome matrix to large previews. This also bounds
    # explicit custom sweeps without inserting omission text inside JSON.
    for field in ("diagnostics", "suggestions"):
        for environment in reversed(summary["environments"]):
            for item in reversed(environment[results_key]):
                if encoded_size() <= MAX_SUMMARY_BYTES:
                    return summary
                values = item.get(field, [])
                if values:
                    item[field] = []
                    omitted_key = (
                        "diagnostic_previews_omitted" if field == "diagnostics"
                        else "suggestions_omitted"
                    )
                    item[omitted_key] = item.get(omitted_key, 0) + len(values)
    for environment in reversed(summary["environments"]):
        while environment[results_key] and encoded_size() > MAX_SUMMARY_BYTES:
            environment[results_key].pop()
            environment[results_key + "_omitted"] += 1
    while summary["environments"] and encoded_size() > MAX_SUMMARY_BYTES:
        summary["environments"].pop()
        summary["environments_omitted"] += 1
    return summary


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        description=(
            "Probe tactics and run suggestion tactics in the exact Arena target "
            "context without modifying a staged project."
        )
    )
    subparsers = result.add_subparsers(dest="command", required=True)

    capabilities = subparsers.add_parser(
        "capabilities", help="report tactics available in every supplied environment"
    )
    capabilities.add_argument("--task", type=Path, required=True)
    capabilities.add_argument(
        "--project-root", type=Path, action="append", required=True
    )
    capabilities.add_argument(
        "--tactic",
        action="append",
        help="override the default probe set; may be repeated",
    )
    capabilities.add_argument(
        "--timeout",
        type=int,
        default=DEFAULT_TIMEOUT_SECONDS,
        help="total seconds across all environments, cache waits, probes and identity checks",
    )
    capabilities.add_argument("--fingerprint-registry", type=Path)
    capabilities.add_argument(
        "--output", type=Path, help="save the complete report at this path"
    )
    capabilities.add_argument(
        "--full-output", action="store_true",
        help="include the complete report on stdout instead of its bounded summary",
    )

    suggest = subparsers.add_parser(
        "suggest", help="run suggestion tactics at theorem entry or a candidate marker"
    )
    suggest.add_argument("--task", type=Path, required=True)
    suggest.add_argument("--project-root", type=Path, action="append", required=True)
    suggest.add_argument(
        "--candidate",
        type=Path,
        help=(
            "candidate scaffold containing exactly one " + SUGGESTION_MARKER + " marker"
        ),
    )
    suggest.add_argument(
        "--tactic",
        action="append",
        help="override the default suggestion sweep; may be repeated",
    )
    suggest.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT_SECONDS)
    suggest.add_argument("--fingerprint-registry", type=Path)
    suggest.add_argument(
        "--output", type=Path, help="save the complete report at this path"
    )
    suggest.add_argument(
        "--full-output", action="store_true",
        help="include the complete report on stdout instead of its bounded summary",
    )
    return result


def main(argv: Sequence[str] | None = None) -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    args = parser().parse_args(argv)
    try:
        if args.timeout <= 0:
            raise ContextToolError("--timeout must be positive")
        roots = [root.resolve() for root in args.project_root]
        missing = [str(root) for root in roots if not root.is_dir()]
        if missing:
            raise ContextToolError("project root does not exist: " + ", ".join(missing))
        if args.command == "capabilities":
            probes = (
                tuple(TacticProbe(value, value) for value in args.tactic)
                if args.tactic
                else DEFAULT_CAPABILITY_PROBES
            )
            report = capability_report(
                args.task.resolve(),
                roots,
                probes,
                args.timeout,
                args.fingerprint_registry,
            )
        else:
            tactics = tuple(args.tactic) if args.tactic else DEFAULT_SUGGESTION_TACTICS
            report = suggestion_report(
                args.task.resolve(),
                roots,
                tactics,
                args.candidate.resolve() if args.candidate else None,
                args.timeout,
                args.fingerprint_registry,
            )
        report_path = archive_report(report, args.output)
        output = report if args.full_output else compact_cli_report(report, report_path)
        print(json.dumps(output, ensure_ascii=False, indent=2))
        return 0
    except (
        OSError,
        json.JSONDecodeError,
        arena.WorkflowError,
        ContextToolError,
        arena.resource_gate.ResourceGateError,
        ValueError,
    ) as error:
        print(
            json.dumps(
                {
                    "schema_version": SCHEMA_VERSION,
                    "command": getattr(args, "command", None),
                    "error": str(error),
                },
                ensure_ascii=False,
                indent=2,
            ),
            file=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
