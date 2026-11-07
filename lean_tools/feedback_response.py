"""Bound model-facing JSON while retaining complete, content-addressed receipts.

The response limit counts serialized UTF-8 bytes of the *whole* supplied
envelope, including JSON strings containing JSON. It is not a character, token,
or diagnostic-content limit. Callers must use the same serializer on delivery.
"""

from __future__ import annotations

import hashlib
import json
import os
import tempfile
from collections.abc import Callable
from pathlib import Path
from typing import Any

from lean_tools.diagnostic_presentation import utf8_excerpt


RESPONSE_BYTE_LIMIT = 64 * 1024
_ERROR_STATUSES = {
    "infrastructure_error", "timeout", "check_failed", "unavailable",
    "source_conflict", "invalid_request",
}
_ESSENTIAL_FIELDS = {
    "schema_version", "tool", "status", "valid", "authoritative", "candidate",
    "source_sha256", "current_snapshot_sha256", "base_source_sha256",
    "selected_source_sha256", "checkpoint", "checkpoint_id",
    "checkpoint_source_sha256", "checkpoint_validation", "source_matches_checkpoint",
    "score", "score_breakdown", "scoring_policy", "tokens", "heartbeats", "heartbeat", "heartbeat_status",
    "original_tokens", "original_heartbeats",
    "compatibility_pct", "compatibility_status", "incumbent_score", "incumbent_delta",
    "evaluation_status", "goal_handles", "default_goal_id", "goal_id", "goal",
    "goal_position", "phase", "occurrence", "index", "line", "column", "location",
    "generated_position", "diagnostics_path", "details_path", "goal_details_path",
    "full_response_path", "alternatives", "ranking", "best_label", "label",
    "unfinished_cases", "cases", "total_cases", "omitted", "response_truncation",
    "feedback_request", "request_id", "request_path", "result_path", "arguments_sha256",
    "response_presentation",
}


def json_text(value: Any) -> str:
    """The serializer used for both budget checks and transport output."""
    return json.dumps(value, ensure_ascii=False)


def serialized_bytes(value: Any) -> int:
    return len(json_text(value).encode("utf-8"))


def mcp_response(value: dict[str, Any], identity: Any = None) -> dict[str, Any]:
    """Build the actual JSON-RPC/MCP envelope, with its nested JSON text."""
    return {
        "jsonrpc": "2.0", "id": identity,
        "result": {
            "content": [{"type": "text", "text": json_text(value)}],
            "isError": value.get("status") in _ERROR_STATUSES,
        },
    }


def _essential(key: str) -> bool:
    return key in _ESSENTIAL_FIELDS or key.endswith(("_sha256", "_path", "_fingerprint"))


def _field_priority(key: Any) -> int:
    if isinstance(key, str) and key in {"feedback_request", "full_response_path", "response_presentation"}:
        return 0
    if isinstance(key, str) and key in _ESSENTIAL_FIELDS:
        return 1
    return 2 if isinstance(key, str) and _essential(key) else 3


def _artifact_directory(directory: Path) -> Path:
    """Reject pre-existing symlink escapes in the capsule artifact directory.

    The caller supplies the fixed capsule path, never a result-provided path.
    Artifact creation is not a sandbox against a concurrent filesystem attacker;
    capsule writers must not rename its parents while publishing receipts.
    """
    directory = Path(os.path.abspath(directory))
    for parent in (directory, *directory.parents):
        if parent.is_symlink():
            raise ValueError("response artifact directory must not contain symlinks")
    directory.mkdir(parents=True, exist_ok=True)
    for parent in (directory, *directory.parents):
        if parent.is_symlink():
            raise ValueError("response artifact directory must not contain symlinks")
    return directory


def _archive(value: dict[str, Any], directory: Path) -> Path:
    encoded = (json_text({"schema_version": 1, "result": value}) + "\n").encode("utf-8")
    path = _artifact_directory(directory) / (hashlib.sha256(encoded).hexdigest() + ".json")
    descriptor, temporary = tempfile.mkstemp(prefix=".response-", suffix=".json", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(encoded)
            stream.flush()
            os.fsync(stream.fileno())
        try:
            os.link(temporary, path)
        except FileExistsError:
            if path.is_symlink() or path.read_bytes() != encoded:
                raise ValueError("full response artifact has different content")
        # Publish before callers remove model-facing fields. Directory fsync is
        # available on POSIX; Windows does not expose directory descriptors.
        if os.name != "nt":
            directory_fd = os.open(path.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
    finally:
        Path(temporary).unlink(missing_ok=True)
    return path


def archive_result(value: dict[str, Any], directory: Path) -> Path:
    """Durably publish a complete immutable receipt for presentation policies."""
    if not isinstance(value, dict):
        raise TypeError("feedback result must be an object")
    return _archive(value, directory)


def _archived_origin(value: dict[str, Any], directory: Path) -> Path | None:
    """Verify a previous boundary's content-addressed original in this capsule.

    A result-provided path alone must never cause a shortened response to claim
    an unrelated full artifact. This verifies both the immutable filename and
    the common receipt wrapper without following symlinks outside the capsule.
    """
    truncation = value.get("response_truncation")
    presentation = value.get("response_presentation")
    if not ((isinstance(truncation, dict) and truncation.get("schema_version") == 1)
            or (isinstance(presentation, dict) and presentation.get("policy") == "compact-v1")):
        return None
    path_text = value.get("full_response_path")
    if not isinstance(path_text, str):
        return None
    path = Path(path_text)
    if path.parent != directory or path.is_symlink() or not path.is_file():
        return None
    encoded = path.read_bytes()
    if path.name != hashlib.sha256(encoded).hexdigest() + ".json":
        return None
    try:
        receipt = json.loads(encoded)
    except (ValueError, UnicodeError):
        return None
    if (not isinstance(receipt, dict) or receipt.get("schema_version") != 1
            or not isinstance(receipt.get("result"), dict)):
        return None
    return path


class _Compactor:
    def __init__(self, string_bytes: int, items: int) -> None:
        self.string_bytes, self.items = string_bytes, items
        self.nodes = 0
        self.stats: dict[str, Any] = {
            "strings_truncated": 0, "truncated_string_utf8_bytes_omitted": 0,
            "list_items_omitted": 0, "object_fields_omitted": 0,
            "subtrees_omitted": 0, "affected_fields": [],
        }

    def note(self, path: str) -> None:
        if len(self.stats["affected_fields"]) < 8:
            self.stats["affected_fields"].append(utf8_excerpt(path, 160)[0])

    def compact(self, value: Any, key: str = "", path: str = "$", depth: int = 0) -> Any:
        self.nodes += 1
        if depth > 16 or self.nodes > 4096:
            self.stats["subtrees_omitted"] += 1
            self.note(path)
            return None
        if isinstance(value, str):
            # Valid filesystem paths, source hashes and opaque goal/checkpoint
            # identities survive the aggressive display-text reduction stages.
            limit = max(4096, self.string_bytes) if _essential(key) else self.string_bytes
            excerpt, kept = utf8_excerpt(value, limit)
            original = len(value.encode("utf-8"))
            if kept < original:
                self.stats["strings_truncated"] += 1
                self.stats["truncated_string_utf8_bytes_omitted"] += original - kept
                self.note(path)
            return excerpt
        if isinstance(value, dict):
            keys = sorted(value, key=_field_priority)
            kept_keys = [item for item in keys if isinstance(item, str) and len(item.encode("utf-8")) <= 256][:64]
            omitted = len(value) - len(kept_keys)
            if omitted:
                self.stats["object_fields_omitted"] += omitted
                self.note(path)
            return {item: self.compact(value[item], item, f"{path}.{item}", depth + 1) for item in kept_keys}
        if isinstance(value, (list, tuple)):
            limit = max(64, self.items) if key == "goal_handles" else max(16, self.items) if key == "cases" else self.items
            if len(value) > limit:
                self.stats["list_items_omitted"] += len(value) - limit
                self.note(path)
            return [self.compact(item, "", f"{path}[{index}]", depth + 1) for index, item in enumerate(value[:limit])]
        return value


def bound_result(
    value: dict[str, Any], *, artifact_dir: Path,
    envelope: Callable[[dict[str, Any]], Any] | None = None,
    max_response_bytes: int = RESPONSE_BYTE_LIMIT,
) -> dict[str, Any]:
    """Return an exact-budget result, archiving the unabridged original first.

    The default envelope is a JSON-RPC MCP response with a null id, making direct
    ``Feedback.call`` and CLI results conservative too. At the native boundary,
    pass ``lambda result: mcp_response(result, actual_request_id)``. An envelope
    whose fixed overhead alone exceeds the limit is rejected: silently changing
    a JSON-RPC request id would break correlation.

    No in-place mutation occurs. Source/score/checkpoint/goal essentials and real
    artifact paths receive priority; all omissions are recoverable from the full
    receipt. Pathological oversized identity fields are bounded like other text.
    """
    if not isinstance(value, dict):
        raise TypeError("feedback result must be an object")
    if max_response_bytes < 2048:
        raise ValueError("response budget must be at least 2048 bytes")
    wrap = envelope or mcp_response
    original_size = serialized_bytes(wrap(value))
    if original_size <= max_response_bytes:
        return value
    if serialized_bytes(wrap({})) >= max_response_bytes - 1024:
        raise ValueError("response envelope exceeds the byte budget")
    # A second boundary check (with the actual request id) must keep the first
    # complete receipt, rather than replace it with an already shortened result.
    previous = value.get("response_truncation")
    directory = _artifact_directory(Path(artifact_dir))
    origin = _archived_origin(value, directory)
    reuse = origin is not None
    path = origin if reuse else _archive(value, directory)
    base_metadata = {
        "schema_version": 1,
        "budget_scope": "serialized_json_utf8_including_envelope",
        "max_response_bytes": max_response_bytes,
        "original_serialized_response_utf8_bytes": max(original_size, previous.get("original_serialized_response_utf8_bytes", 0)) if reuse and isinstance(previous, dict) else original_size,
        "note": "Inline excerpts only; inspect full_response_path for the complete response.",
    }
    for string_bytes, items in ((8192, 64), (4096, 32), (2048, 16), (1024, 8), (512, 4), (256, 2), (128, 1)):
        compactor = _Compactor(string_bytes, items)
        result = compactor.compact({key: item for key, item in value.items() if key != "response_truncation"})
        result["full_response_path"] = str(path)
        result["response_truncation"] = {**base_metadata, **compactor.stats}
        if serialized_bytes(wrap(result)) <= max_response_bytes:
            return result
    # An unusually large set of identities/paths can itself exceed the cap.
    # Preserve the common root receipt, then admit remaining essential fields
    # only when the complete envelope still fits. The full artifact is exact.
    compactor = _Compactor(128, 1)
    result = {"full_response_path": str(path), "response_truncation": {
        **base_metadata, "essential_fields_omitted": [],
    }}
    ordered = ["schema_version", "status", "valid", "feedback_request", "response_presentation", "candidate", "source_sha256",
               "current_snapshot_sha256", "base_source_sha256", "score", "tokens",
               "heartbeats", "heartbeat", "heartbeat_status", "checkpoint", "checkpoint_id", "checkpoint_source_sha256",
               "default_goal_id", "goal_handles", "unfinished_cases", "feedback_request"]
    ordered.extend(key for key in value if isinstance(key, str) and len(key.encode("utf-8")) <= 256
                   and key not in ordered and _essential(key)
                   and key not in {"full_response_path", "response_truncation"})
    for key in ordered:
        if key not in value:
            continue
        result[key] = compactor.compact(value[key], key, f"$.{key}")
        if serialized_bytes(wrap(result)) > max_response_bytes - 1024:
            del result[key]
            omitted = result["response_truncation"]["essential_fields_omitted"]
            if len(omitted) < 8:
                omitted.append(utf8_excerpt(key, 160)[0])
    result["response_truncation"].update(compactor.stats)
    result["response_truncation"]["object_fields_omitted"] += len(value) - sum(key in value for key in result)
    if serialized_bytes(wrap(result)) > max_response_bytes:
        # Samples are descriptive conveniences, so they give way before receipt
        # identities when an unusually small caller budget is used.
        result["response_truncation"]["affected_fields"] = []
        result["response_truncation"]["essential_fields_omitted_count"] = len(result["response_truncation"]["essential_fields_omitted"])
        result["response_truncation"]["essential_fields_omitted"] = []
    for key in reversed(tuple(result)):
        if serialized_bytes(wrap(result)) <= max_response_bytes:
            break
        if key not in {"full_response_path", "response_truncation"}:
            del result[key]
            result["response_truncation"]["object_fields_omitted"] += 1
    if serialized_bytes(wrap(result)) > max_response_bytes:
        raise ValueError("response artifact path and envelope exceed the byte budget")
    return result
