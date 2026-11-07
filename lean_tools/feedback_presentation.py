"""Opt-in receipt presentation, independent of evaluation and journal semantics.

``compact-v1`` removes recognized host bookkeeping and exact duplicates. It
can summarize source-bound warnings wholly in the unchanged source prefix when
the caller supplies validated prefix context. Full receipts remain archived.
Unknown tools, schemas and diagnostic shapes pass through; goals, region menus,
measurements and candidate diagnostics stay inline. The transport byte bound
still runs *after* this presentation policy.
"""

from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any

from lean_tools import feedback_response as response
from lean_tools import diagnostic_presentation as diagnostics


POLICIES = frozenset({"legacy", "compact-v1"})
_TOOLS = {"edit_check", "score_candidate", "compare_candidates", "profile_proof"}
_CACHE_KEYS = {"status", "hit", "source_mode"}
_TIMING_KEYS = {"measurement_source", "axiom_audit_shares_compile", "phase_note",
                "request_wall_seconds", "measurement_compile_seconds", "measurement_axiom_audit_seconds"}
_TRUNCATION_KEYS = {"message_utf8_byte_limit", "total_message_utf8_byte_limit", "inline_json_utf8_byte_limit",
                    "inline_json_utf8_bytes", "inline_message_utf8_bytes", "original_message_utf8_bytes",
                    "omitted_message_utf8_bytes", "messages_truncated", "diagnostics_omitted"}
_CAPABILITY_KEYS = {"schema_version", "available", "supported_modes", "outcome", "reason", "prefix_sha256",
                    "source_form", "default_timeout_seconds", "max_timeout_seconds", "timeout_scope",
                    "shared_queue_wait_seconds", "max_default_stage_seconds", "max_top_n", "instrumentation_revision"}
_PROFILE_TIMING_KEYS = {"stage_wall_seconds", "other_wall_seconds", "queue_wait_seconds", "queue_wait_complete",
                        "stage_queue_wait_seconds", "source_validation_process_seconds", "profile_process_seconds", "note"}
_PROFILE_BUDGET_KEYS = {"timeout_scope", "setup_seconds", "maximum_process_seconds", "source_validation_process_seconds",
                        "profile_process_seconds", "shared_queue_wait_seconds", "total_stage_seconds", "note"}
_DIAGNOSTIC_ARTIFACT_KEYS = {"schema_version", "generated_source", "generated_source_sha256", "candidate",
                             "candidate_source_sha256", "raw_diagnostics", "service_diagnostics_omitted",
                             "diagnostics", "diagnostics_compacted", "diagnostics_truncation", "mapped_diagnostics",
                             "position_encoding"}


@dataclass(frozen=True)
class ImmutablePrefixContext:
    """Trusted source inputs, kept outside raw receipts and the request journal."""

    source_sha256: str
    candidate_source: str
    declaration: str
    prefix_text: str
    prefix_kind: str


def prefix_context_for_result(value: dict[str, Any], *, row: dict[str, Any],
                              project_root: Path, capsule_root: Path) -> ImmutablePrefixContext | None:
    """Validate a saved snapshot and obtain the evaluator's exact frozen prefix.

    This is optional presentation evidence, not a compilation or cache lookup.
    Any unavailable or unfamiliar evidence leaves every diagnostic inline.
    Never read the mutable candidate path as a substitute for its snapshot.
    """
    from lean_tools import lean_source

    if (not isinstance(value.get("diagnostics"), list)
            or not any(isinstance(item, dict) and item.get("severity") == "warning"
                       and isinstance(item.get("location"), dict)
                       and item["location"].get("scope") == "generated" for item in value["diagnostics"])
            or not isinstance(value.get("snapshot_path"), str)
            or not isinstance(value.get("source_sha256"), str)
            or any(key in value for key in ("response_presentation", "response_truncation", "full_response_path"))):
        return None
    try:
        snapshot = Path(value["snapshot_path"]).resolve()
        snapshot.relative_to(Path(capsule_root).resolve() / ".feedback" / "sources")
        candidate = snapshot.read_bytes()
        if hashlib.sha256(candidate).hexdigest() != value["source_sha256"]:
            return None
        source = lean_source.candidate_text_from_bytes(candidate)
        declaration, _ = lean_source.extract_candidate_declaration(row, source)
        prefix = lean_source.exact_source_prefix(row, Path(project_root))
        return ImmutablePrefixContext(value["source_sha256"], source, declaration, prefix.text, prefix.kind)
    except (OSError, ValueError, KeyError, TypeError, RuntimeError):
        return None


def _prefix_warning_groups(value: dict[str, Any], context: ImmutablePrefixContext | None,
                           ) -> tuple[list[int], dict[str, Any]] | None:
    """Prove group origins from a complete source-bound diagnostic artifact.

    ``scope=generated`` alone proves nothing: helpers, suffixes and instrumented
    files also use it. Verify the content-addressed artifact, candidate binding,
    complete generated text, remapping and *all* members of a warning group.
    Unknown span/range metadata is deliberately not interpreted as a point.
    """
    if (not isinstance(context, ImmutablePrefixContext)
            or value.get("source_sha256") != context.source_sha256
            or not isinstance(value.get("diagnostics_path"), str)
            or not isinstance(value.get("diagnostics"), list)
            or not context.prefix_text
            or context.prefix_kind not in {"project-source-prefix", "supplied-environment-prefix"}):
        return None
    try:
        path = Path(value["diagnostics_path"])
        encoded = path.read_bytes()
        if path.name != context.source_sha256 + "-" + hashlib.sha256(encoded).hexdigest() + ".json":
            return None
        artifact = json.loads(encoded)
        if (not _known_mapping(artifact, _DIAGNOSTIC_ARTIFACT_KEYS)
                or type(artifact.get("schema_version")) is not int or artifact["schema_version"] != 1
                or artifact.get("candidate_source_sha256") != context.source_sha256
                or type(artifact.get("service_diagnostics_omitted")) is not int
                or artifact["service_diagnostics_omitted"] < 0):
            return None
        generated = artifact.get("generated_source")
        if (not isinstance(generated, str)
                or hashlib.sha256(generated.encode("utf-8")).hexdigest() != artifact.get("generated_source_sha256")
                or generated != context.prefix_text + context.declaration.rstrip() + "\n"):
            return None
        raw = artifact.get("raw_diagnostics")
        if not isinstance(raw, list) or not all(isinstance(item, dict) for item in raw):
            return None
        encoding = artifact.get("position_encoding", "utf-16")
        if encoding not in ("utf-16", "unicode"):
            return None
        source_map = diagnostics.SourceMap.for_declaration(context.candidate_source, generated, context.declaration)
        if source_map.generated_start != len(context.prefix_text):
            return None
        shown = diagnostics.present_diagnostics(raw, source_map, source=generated, position_encoding=encoding)
        if shown["diagnostics"] != value["diagnostics"]:
            return None
        # Keep groups intact if their representative or any omitted member has
        # unfamiliar metadata, candidate origin, a boundary point or a span.
        groups: dict[str, list[tuple[dict[str, Any], dict[str, Any]]]] = {}
        for original, mapped in zip(raw, shown["mapped_diagnostics"]):
            if mapped["severity"] == "warning" and not diagnostics.ACTIONABLE.search(mapped["message"]):
                groups.setdefault(diagnostics.warning_family(mapped["message"]), []).append((original, mapped))
        selected, occurrences = [], 0
        for index, item in enumerate(value["diagnostics"]):
            if item.get("severity") != "warning" or diagnostics.ACTIONABLE.search(item.get("message", "")):
                continue
            members = groups.get(diagnostics.warning_family(item["message"]), [])
            if not members or item.get("count", 1) != len(members):
                continue
            eligible = True
            for original, mapped in members:
                if (original.keys() != {"severity", "message", "line", "character"}
                        or not isinstance(original["message"], str)
                        or type(original["line"]) is not int or type(original["character"]) is not int
                        or (mapped.get("location") or {}).get("scope") != "generated"):
                    eligible = False
                    break
                offset = diagnostics.source_offset(generated, original["line"], original["character"], encoding)
                if not 0 <= offset < len(context.prefix_text):
                    eligible = False
                    break
            if eligible:
                selected.append(index)
                occurrences += len(members)
        if not selected:
            return None
        return selected, {"diagnostic_groups": len(selected), "warning_occurrences": occurrences,
                          "prefix_kind": context.prefix_kind,
                          "prefix_sha256": hashlib.sha256(context.prefix_text.encode("utf-8")).hexdigest(),
                          "generated_source_sha256": artifact["generated_source_sha256"],
                          "full_text": "full_response_path; original observations in diagnostics_path"}
    except (OSError, ValueError, KeyError, TypeError, RuntimeError):
        return None


def _known_mapping(value: Any, keys: set[str]) -> bool:
    return isinstance(value, dict) and bool(value) and value.keys() <= keys


def _number(value: Any) -> bool:
    return type(value) in {int, float}


def _budget_shape(value: Any) -> bool:
    return (_known_mapping(value, _PROFILE_BUDGET_KEYS)
            and all(isinstance(item, str) if key in {"timeout_scope", "note"} else _number(item)
                    for key, item in value.items()))


def _profile_timing_shape(value: Any) -> bool:
    if not _known_mapping(value, _PROFILE_TIMING_KEYS):
        return False
    for key, item in value.items():
        if key in {"stage_wall_seconds", "stage_queue_wait_seconds"}:
            if not isinstance(item, dict) or not all(_number(number) for number in item.values()):
                return False
        elif key == "queue_wait_complete":
            if type(item) is not bool:
                return False
        elif key == "note":
            if not isinstance(item, str):
                return False
        elif not _number(item):
            return False
    return True


def _capability_shape(value: Any) -> bool:
    if not _known_mapping(value, _CAPABILITY_KEYS):
        return False
    numbers = {"schema_version", "default_timeout_seconds", "max_timeout_seconds", "shared_queue_wait_seconds",
               "max_default_stage_seconds", "max_top_n", "instrumentation_revision"}
    return all(_number(item) if key in numbers else type(item) is bool if key == "available"
               else isinstance(item, list) and all(isinstance(mode, str) for mode in item) if key == "supported_modes"
               else item is None or isinstance(item, str) for key, item in value.items())


def _recognized(value: dict[str, Any], tool: str | None) -> str | None:
    if type(value.get("schema_version")) is not int or value["schema_version"] != 1:
        return None
    named = value.get("tool")
    if tool is not None and named is not None and tool != named:
        return None
    tool = tool or named
    if (not isinstance(tool, str) or tool not in _TOOLS or not isinstance(value.get("status"), str)
            or "valid" not in value or value["valid"] is not None and type(value["valid"]) is not bool):
        return None
    if tool == "edit_check":
        if ("mode" in value and value["mode"] not in ("quick", "exact", "advisory")
                or "operation" in value and value["operation"] not in ("check", "clone", "promote", "restore")):
            return None
        return tool if (value.get("mode") in ("quick", "exact", "advisory")
                        or value.get("operation") in ("clone", "promote", "restore")) else None
    if tool == "score_candidate":
        return tool if named == tool and isinstance(value.get("base_source_sha256"), str) else None
    if tool == "compare_candidates":
        # The batch wrapper has no validity field; each alternative does.
        return None
    return tool if value.get("measurement_mode") == "profile" and value.get("mode") in ("regions", "wall_time") else None


def _recognized_batch(value: dict[str, Any], tool: str | None) -> bool:
    return (tool == "compare_candidates" and value.get("tool", tool) == tool
            and type(value.get("schema_version")) is int and value["schema_version"] == 1
            and value.get("status") == "completed" and value.get("authoritative") is False
            and isinstance(value.get("base_source_sha256"), str)
            and isinstance(value.get("alternatives"), list)
            and all(isinstance(row, dict) and isinstance(row.get("status"), str)
                    and "valid" in row and (row["valid"] is None or type(row["valid"]) is bool)
                    for row in value["alternatives"]))


class _Presentation:
    def __init__(self, value: dict[str, Any]) -> None:
        self.result = deepcopy(value)
        self.omitted = 0
        self.prefix_summary: dict[str, Any] | None = None

    def omit(self, mapping: dict[str, Any], key: str, when: bool = True) -> None:
        if when and key in mapping:
            del mapping[key]
            self.omitted += 1

    def common(self, value: dict[str, Any]) -> None:
        # These are internal evidence locations, recoverable from the original
        # receipt. Candidate, checkpoint and diagnostic/goal locations stay inline.
        for key in ("snapshot_path", "details_path"):
            self.omit(value, key, isinstance(value.get(key), str))
        self.omit(value, "wall_seconds", _number(value.get("wall_seconds")))
        checkpoint = value.get("checkpoint")
        if isinstance(checkpoint, str) and checkpoint.endswith(".lean"):
            self.omit(value, "checkpoint_receipt_path",
                      value.get("checkpoint_receipt_path") == str(Path(checkpoint).with_suffix(".json")))
        request = value.get("feedback_request")
        if (_known_mapping(request, {"request_id", "request_path", "result_path", "arguments_sha256"})
                and isinstance(request.get("request_id"), str)
                and all(isinstance(item, str) for item in request.values())):
            for key in ("request_path", "result_path", "arguments_sha256"):
                self.omit(request, key)
        truncation = value.get("diagnostics_truncation")
        if (_known_mapping(truncation, _TRUNCATION_KEYS)
                and all(type(item) is int and item >= 0 for item in truncation.values())
                and all(truncation.get(key) == 0 for key in (
                    "omitted_message_utf8_bytes", "messages_truncated", "diagnostics_omitted"))):
            self.omit(value, "diagnostics_truncation")
        self.omit(value, "diagnostics_compacted", type(value.get("diagnostics_compacted")) is int
                  and value["diagnostics_compacted"] == 0)

    def edit(self, value: dict[str, Any], prefix_context: ImmutablePrefixContext | None = None) -> None:
        prefix_warnings = _prefix_warning_groups(value, prefix_context)
        if prefix_warnings is not None:
            indexes, self.prefix_summary = prefix_warnings
            omitted = set(indexes)
            value["diagnostics"] = [item for index, item in enumerate(value["diagnostics"]) if index not in omitted]
            self.omitted += 1
        self.common(value)
        # Cache and elapsed-time bookkeeping never establish validity. Keep it
        # on failed requests where it can help explain an infrastructure failure.
        if value.get("valid") is True:
            cache = value.get("cache")
            self.omit(value, "cache", _known_mapping(cache, _CACHE_KEYS)
                      and all(item is None or type(item) in {str, bool} for item in cache.values()))
            timing = value.get("timing")
            self.omit(value, "timing", _known_mapping(timing, _TIMING_KEYS)
                      and all(item is None or type(item) in {str, bool, int, float} for item in timing.values()))

    def score(self, value: dict[str, Any]) -> None:
        self.common(value)
        self.omit(value, "details_index", type(value.get("details_index")) is int and value["details_index"] == 0)

    def profile(self, value: dict[str, Any]) -> None:
        self.common(value)
        self.omit(value, "instrumented_path", isinstance(value.get("instrumented_path"), str))
        environment = value.get("environment")
        if isinstance(environment, dict):
            # Compiler hashes, toolchain, dependency caveats and fingerprint
            # remain inline. Executable locations and cache routing are host data.
            self.omit(environment, "lean_executable", isinstance(environment.get("lean_executable"), str))
            self.omit(environment, "launch_cache_status", isinstance(environment.get("launch_cache_status"), str))
        validation = value.get("source_validation")
        if isinstance(validation, dict) and validation.get("status") in ("compiled", "cached_valid", "cached_profile_validation"):
            for key, outer in (("source_sha256", "source_sha256"),
                               ("compile_source_sha256", "uninstrumented_compile_source_sha256")):
                self.omit(validation, key, isinstance(validation.get(key), str) and validation[key] == value.get(outer))
            self.omit(validation, "receipt_path", isinstance(validation.get("receipt_path"), str))
            self.omit(validation, "cache_path", isinstance(validation.get("cache_path"), str))
            if isinstance(environment, dict):
                self.omit(validation, "environment_fingerprint", isinstance(validation.get("environment_fingerprint"), str)
                          and validation["environment_fingerprint"] == environment.get("fingerprint"))
            binding = validation.get("binding")
            if isinstance(binding, dict):
                for key, outer in (("source_sha256", "source_sha256"),
                                   ("compile_source_sha256", "uninstrumented_compile_source_sha256")):
                    self.omit(binding, key, isinstance(binding.get(key), str) and binding[key] == value.get(outer))
                if isinstance(environment, dict):
                    self.omit(binding, "project_root", isinstance(binding.get("project_root"), str)
                              and binding["project_root"] == environment.get("project_root"))
                    nested = binding.get("environment")
                    if isinstance(nested, dict):
                        for key in tuple(nested):
                            self.omit(nested, key, key in environment and nested[key] == environment[key])
                        self.omit(binding, "environment", not nested)
                compiler = binding.get("compiler_file")
                if (_known_mapping(compiler, {"path", "size", "mtime_ns", "inode"})
                        and isinstance(compiler.get("path"), str)
                        and all(type(compiler.get(key)) is int for key in ("size", "mtime_ns", "inode"))):
                    self.omit(binding, "compiler_file")
        # Failed/unsupported/timeout profiles keep capability, process budgets
        # and timing context for repairs. Region/menu text and accounting are
        # retained unchanged, including generated positions and incomplete data.
        if value.get("status") == "profiled" and value.get("complete") is True:
            capability = value.get("capability")
            self.omit(value, "capability", _capability_shape(capability)
                      and capability.get("available") is True and capability.get("reason") is None)
            self.omit(value, "timings", _profile_timing_shape(value.get("timings")))
            self.omit(value, "budgets", _budget_shape(value.get("budgets")))


def present_result(value: dict[str, Any], *, artifact_dir: Path,
                   policy: str = "legacy", tool: str | None = None,
                   prefix_context: ImmutablePrefixContext | None = None) -> dict[str, Any]:
    """Present a raw journal receipt before ``bound_result`` at model delivery.

    Legacy is the exact historical behavior (including object identity and no
    artifact writes). Compact archives the complete input before returning any
    omissions; an archive error raises without modifying the original. The
    ``full_response_path`` artifact uses the same schema as byte-bound receipts.
    Call only on the result payload, before creating a native/CLI envelope.
    Repeated presentation is idempotent; neither journals nor events are edited.
    """
    if not isinstance(policy, str) or policy not in POLICIES:
        raise ValueError("response presentation policy must be legacy or compact-v1")
    if not isinstance(value, dict):
        raise TypeError("feedback result must be an object")
    if policy == "legacy":
        return value
    if "response_presentation" in value or "response_truncation" in value or "full_response_path" in value:
        # Do not re-archive a presentation/bounded replay as if it were raw.
        # The later byte boundary validates any claimed original artifact.
        return value
    kind = _recognized(value, tool)
    batch = _recognized_batch(value, tool)
    if kind is None and not batch:
        return value
    presentation = _Presentation(value)
    if kind == "edit_check":
        presentation.edit(presentation.result, prefix_context)
    elif kind == "score_candidate":
        presentation.score(presentation.result)
    elif kind == "profile_proof":
        presentation.profile(presentation.result)
    else:
        presentation.common(presentation.result)
        for row in presentation.result["alternatives"]:
            presentation.common(row)
    if presentation.omitted == 0:
        return value
    # Hash filenames have a fixed ASCII length. Check the complete projected
    # payload and MCP envelope before creating an otherwise unused artifact.
    # This keeps small failures/copy-operation receipts from becoming larger.
    projected = Path(os.path.abspath(artifact_dir)) / ("0" * 64 + ".json")
    presentation.result["full_response_path"] = str(projected)
    presentation.result["response_presentation"] = {"policy": policy, "omitted_fields": presentation.omitted}
    if presentation.prefix_summary is not None:
        presentation.result["response_presentation"]["immutable_prefix_warnings"] = presentation.prefix_summary
    if (response.serialized_bytes(presentation.result) >= response.serialized_bytes(value)
            or response.serialized_bytes(response.mcp_response(presentation.result))
            >= response.serialized_bytes(response.mcp_response(value))):
        return value
    path = response.archive_result(value, Path(artifact_dir))
    presentation.result["full_response_path"] = str(path)
    return presentation.result
