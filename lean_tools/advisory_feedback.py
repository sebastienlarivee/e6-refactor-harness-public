"""Source-bound warm heartbeat observations; never authoritative selection results.

Setup may explicitly prepare the existing cached module helper before starting a
broker. Observation never starts Lean, builds a helper, or falls back to cold exact
measurement when the configured resident service cannot handle a source.
"""

from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import json
import os
from pathlib import Path
from typing import Any

from lean_tools import arena_workflow as arena
from lean_tools import persistent_quick_workflow as persistent
def prepare_support(
    row: dict[str, Any],
    project_root: Path,
    timeout_seconds: int,
    fingerprint: str | None = None,
) -> Path | None:
    """Explicit broker setup: reuse/build the existing exact-measurement helper."""
    if not arena.is_project_resident(row):
        return None
    fingerprint = fingerprint or arena.measurement_environment_fingerprint(
        row, project_root
    )
    support = arena.cached_project_measurement_helper(
        project_root,
        timeout_seconds,
        fingerprint,
        arena.project_measurement_helper_lean_args(project_root),
    )
    if support is None:
        raise arena.WorkflowError(
            "project advisory feedback requires an evaluation cache for its measurement helper"
        )
    return support


def source_for_measurement(
    row: dict[str, Any], declaration: str, project_root: Path
) -> str:
    """Measure the whole synchronous command, separate from submitted source."""
    arena.validate_declaration(row, declaration)
    if arena.is_project_resident(row):
        return arena.project_compile_harness(row, declaration, project_root, exact=True)
    return (
        arena.render_environment(row)
        + "set_option Elab.async false in\n"
        + "set_option maxHeartbeats 1000000000 in\n"
        + "#count_heartbeats in\n"
        + declaration.rstrip()
        + "\n"
    )


def _has_support(project_root: Path, fingerprint: str) -> bool:
    root = arena.evaluation_cache_root()
    if root is None:
        return False
    lean_args = arena.project_measurement_helper_lean_args(project_root)
    legacy_key = arena.measurement_helper_cache_key(fingerprint, lean_args)
    build_args = arena.measurement_helper_compile_args(lean_args)
    task_key = arena.measurement_helper_cache_key(fingerprint, build_args)
    task_paths = {
        (root / "helpers" / key[:2] / key).resolve(): key
        for key in (legacy_key, task_key)
    }
    try:
        configured = json.loads(os.environ.get(persistent.FEEDBACK_SUPPORT_ENV, "[]"))
        if not isinstance(configured, list) or not all(
            isinstance(item, str) for item in configured
        ):
            return False
        for item in configured:
            support = Path(item).resolve()
            key, cache_fingerprint, guard = task_paths.get(support), fingerprint, None
            if key is None:
                marker = json.loads((support / "ready.json").read_text(encoding="utf-8"))
                if not isinstance(marker, dict):
                    continue
                if marker.get("cache_scope") == "task":
                    # A broker's task cache is separate from each fresh capsule's
                    # cache. Its explicitly provisioned helper still binds the
                    # same measured import prefix, helper options, and files.
                    key = marker.get("key")
                    if (key not in {legacy_key, task_key}
                            or marker.get("environment_fingerprint") != fingerprint
                            or marker.get("origin_task_fingerprint") != fingerprint
                            or marker.get("build_guard") is not None
                            or support.name != key or support.parent.name != key[:2]
                            or support.parent.parent.name != "helpers"):
                        continue
                elif marker.get("cache_scope") == "shared-build":
                    cache_fingerprint = marker.get("environment_fingerprint")
                    if not isinstance(cache_fingerprint, str):
                        continue
                    key = arena.measurement_helper_cache_key(cache_fingerprint, build_args)
                    expected = project_root.resolve() / ".lake/lrh-measurement-helpers" / key[:2] / key
                    guard = arena.shared_measurement_helper_guard(project_root)
                    if support != expected or guard is None:
                        continue
                else:
                    continue
            if arena.measurement_helper_is_ready(
                support / "LrhMeasurement.lean", support / "LrhMeasurement.olean",
                support / "ready.json", key, cache_fingerprint, guard,
            ):
                return True
    except (OSError, ValueError, TypeError):
        return False
    return False


def observe(
    row: dict[str, Any],
    declaration: str,
    project_root: Path,
    timeout_seconds: int,
    fingerprint: str | None = None,
) -> dict[str, Any]:
    """Return advisory counts and diagnostics, with explicit unsupported outcomes.

    Warm counts are never entered in the evaluator's exact cache and must not be used
    to prune the exact-validation candidate set. The usual exact evaluator remains the
    sole final score/axiom authority. Infrastructure and count failures are distinct
    from a candidate's Lean diagnostics.
    """
    fingerprint = fingerprint or arena.measurement_environment_fingerprint(
        row, project_root
    )
    source = source_for_measurement(row, declaration, project_root)
    result: dict[str, Any] = {
        "schema_version": 1,
        "ok": False,
        "measurement_mode": "advisory",
        "authoritative": False,
        "task": row["name"],
        "project_root": str(project_root.resolve()),
        "environment_fingerprint": fingerprint,
        "source_sha256": arena.sha256_bytes(source.encode("utf-8")),
        "declaration_sha256": arena.sha256_bytes(declaration.encode("utf-8")),
        "heartbeat": None,
        "valid": None,
        "diagnostics": [],
    }
    if not arena.persistent_quick_matches_project(project_root):
        return {
            **result,
            "status": "unsupported",
            "error": "no resident service for this project root",
        }
    if arena.is_project_resident(row) and not _has_support(project_root, fingerprint):
        return {
            **result,
            "status": "unsupported",
            "error": "resident service was not provisioned with the matching cached measurement helper",
        }
    target_start_line = source.count("\n", 0, source.rfind(declaration.rstrip()))
    try:
        response = persistent.feedback_request(
            source,
            timeout_seconds,
            operation="observe",
            target_start_line=target_start_line,
        )
    except persistent.PersistentQuickError as error:
        return {**result, "status": "infrastructure_failure", "error": str(error)}
    result.update(
        ok=True,
        status="completed" if response["valid"] else "invalid",
        valid=response["valid"],
        diagnostics=response["diagnostics"],
        diagnostics_omitted=response.get("diagnostics_omitted", 0),
        diagnostics_truncated=response.get("diagnostics_truncated", False),
        document_version=response["document_version"],
        reused_source=response["reused_source"],
        backend="resident",
        timing={
            key: response.get(key)
            for key in (
                "startup_seconds",
                "elaboration_seconds",
                "queue_wait_seconds",
                "lsp_seconds",
                "wall_seconds",
            )
        },
    )
    if response["valid"]:
        output = "\n".join(item["message"] for item in response["diagnostics"])
        parser = (
            arena.parse_project_heartbeat_count
            if arena.is_project_resident(row)
            else arena.parse_exact_heartbeat_count
        )
        try:
            result["heartbeat"] = parser(output)
        except arena.WorkflowError as error:
            result.update(status="count_unavailable", error=str(error))
    return result
