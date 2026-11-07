"""Candidate coordinates and compact diagnostics; raw observations stay on disk."""

from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import hashlib
import json
import os
import re
import tempfile
from bisect import bisect_right
from collections.abc import Sequence
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any


class PositionError(ValueError):
    pass


@lru_cache(maxsize=8)
def _line_starts(source: str) -> tuple[int, ...]:
    return (0, *(match.end() for match in re.finditer("\n", source)))


def human_position(source: str, offset: int) -> dict[str, int]:
    if not 0 <= offset <= len(source):
        raise PositionError("source offset is outside the document")
    starts = _line_starts(source)
    line = bisect_right(starts, offset)
    return {"line": line, "column": offset - starts[line - 1] + 1}


def lsp_offset(source: str, line: int, character: int) -> int:
    if type(line) is not int or type(character) is not int or min(line, character) < 0:
        raise PositionError("invalid LSP position")
    starts = _line_starts(source)
    if line >= len(starts):
        raise PositionError("LSP line is outside the document")
    start = starts[line]
    end = source.find("\n", start)
    if end < 0:
        end = len(source)
    if end > start and source[end - 1] == "\r":
        end -= 1
    units = 0
    for offset in range(start, end):
        if units == character:
            return offset
        units += len(source[offset].encode("utf-16-le")) // 2
        if units > character:
            raise PositionError("LSP character splits a UTF-16 surrogate pair")
    if units == character:
        return end
    raise PositionError("LSP character is outside the source line")


def _unique(source: str, declaration: str) -> int:
    first = source.find(declaration)
    if first < 0 or source.find(declaration, first + 1) >= 0:
        raise PositionError("could not identify one exact declaration span")
    return first


@dataclass(frozen=True)
class SourceMap:
    candidate: str
    generated: str
    candidate_start: int
    generated_start: int
    length: int
    original_candidate: str | None = None
    replacement: tuple[int, int, int] | None = None

    @classmethod
    def for_declaration(
        cls,
        candidate: str,
        generated: str,
        declaration: str,
        *,
        candidate_start: int | None = None,
        generated_start: int | None = None,
    ) -> SourceMap:
        declaration = declaration.rstrip()
        if not declaration:
            raise PositionError("cannot map an empty declaration")
        candidate_start = (
            _unique(candidate, declaration)
            if candidate_start is None
            else candidate_start
        )
        generated_start = (
            _unique(generated, declaration)
            if generated_start is None
            else generated_start
        )
        size = len(declaration)
        if (
            candidate[candidate_start : candidate_start + size] != declaration
            or generated[generated_start : generated_start + size] != declaration
        ):
            raise PositionError("declaration spans do not match exactly")
        return cls(candidate, generated, candidate_start, generated_start, size)

    def candidate_to_generated(self, offset: int) -> int:
        relative = offset - self.candidate_start
        if not 0 <= relative <= self.length:
            raise PositionError("cursor is outside the target declaration")
        return self.generated_start + relative

    @classmethod
    def for_replacement(
        cls, candidate: str, generated: str, declaration: str, old: str, new: str
    ) -> SourceMap:
        if candidate.count(old) != 1:
            raise PositionError("replacement marker must occur exactly once")
        variant = candidate.replace(old, new, 1)
        base = cls.for_declaration(variant, generated, declaration)
        return cls(
            variant,
            generated,
            base.candidate_start,
            base.generated_start,
            base.length,
            candidate,
            (candidate.index(old), len(old), len(new)),
        )

    def location(
        self, line: int, character: int, encoding: str = "utf-16"
    ) -> dict[str, Any]:
        offset = source_offset(self.generated, line, character, encoding)
        relative = offset - self.generated_start
        if 0 <= relative <= self.length:
            candidate_offset = self.candidate_start + relative
            anchor = {}
            if self.replacement is not None:
                start, old_length, new_length = self.replacement
                if candidate_offset >= start + new_length:
                    candidate_offset += old_length - new_length
                elif candidate_offset >= start:
                    candidate_offset = start
                    anchor = {"anchor": "suggestion_marker"}
            return {
                "scope": "candidate",
                **human_position(
                    self.original_candidate or self.candidate, candidate_offset
                ),
                **anchor,
            }
        return {"scope": "generated", **human_position(self.generated, offset)}


def source_offset(source: str, line: int, character: int, encoding: str) -> int:
    if encoding == "utf-16":
        return lsp_offset(source, line, character)
    if encoding != "unicode":
        raise PositionError("unsupported diagnostic column encoding")
    start = lsp_offset(source, line, 0)
    end = source.find("\n", start)
    if end < 0:
        end = len(source)
    if type(character) is not int or not 0 <= character <= end - start:
        raise PositionError("Unicode column is outside the source line")
    return start + character


def map_diagnostic(
    raw: dict[str, Any],
    source_map: SourceMap | None = None,
    *,
    source: str | None = None,
    position_encoding: str = "utf-16",
) -> dict[str, Any]:
    result = {
        "severity": raw.get("severity", "unknown"),
        "message": str(raw.get("message", "")),
        "location": None,
    }
    line, character = raw.get("line"), raw.get("character")
    if type(line) is not int or type(character) is not int:
        return result
    # Keep the original zero-based UTF-16 position even when a candidate mapping exists.
    result["generated_position"] = {
        "line": line,
        "character": character,
        "encoding": position_encoding,
    }
    try:
        if source_map is not None:
            result["location"] = source_map.location(line, character, position_encoding)
        elif source is not None:
            result["location"] = {
                "scope": "generated",
                **human_position(
                    source, source_offset(source, line, character, position_encoding)
                ),
            }
        else:
            result["location"] = {
                "scope": "generated",
                "line": line + 1,
                "column": character + 1,
                "column_encoding": position_encoding,
            }
    except PositionError:
        # Do not guess a Unicode column or candidate line for an invalid source position.
        result["location"] = {
            "scope": "generated",
            "line": line + 1,
            "column": character + 1,
            "column_encoding": position_encoding,
        }
    return result


ACTIONABLE = re.compile(
    r"(?i)\bTry (?:this|these):|LRH_HEARTBEATS|Used [0-9]+ heartbeats"
)
LINTER_OPTION = re.compile(r"\bset_option\s+(linter\.[A-Za-z0-9_.]+)\s+false\b")
MESSAGE_BYTE_LIMIT = 4096
MESSAGE_TOTAL_BYTE_LIMIT = 16 * 1024
DIAGNOSTICS_BYTE_LIMIT = 24 * 1024


def utf8_excerpt(text: str, byte_limit: int) -> tuple[str, int]:
    """Return a valid UTF-8 head/tail excerpt and the number of original bytes kept.

    The limit includes the marker. JSON escaping is deliberately handled by the
    separate serialized-response budget, rather than confused with UTF-8 text.
    """
    encoded = text.encode("utf-8")
    if len(encoded) <= byte_limit:
        return text, len(encoded)
    marker = "\n… [truncated] …\n"
    marker_bytes = len(marker.encode("utf-8"))
    if byte_limit < marker_bytes:
        excerpt = encoded[:max(0, byte_limit)].decode("utf-8", errors="ignore")
        return excerpt, len(excerpt.encode("utf-8"))
    available = byte_limit - marker_bytes
    head_bytes = (available * 3) // 4
    tail_bytes = available - head_bytes
    head = encoded[:head_bytes].decode("utf-8", errors="ignore")
    tail = encoded[-tail_bytes:].decode("utf-8", errors="ignore") if tail_bytes else ""
    kept = len(head.encode("utf-8")) + len(tail.encode("utf-8"))
    return head + marker + tail, kept


def bound_diagnostics(
    diagnostics: Sequence[dict[str, Any]], *,
    message_byte_limit: int = MESSAGE_BYTE_LIMIT,
    message_total_byte_limit: int = MESSAGE_TOTAL_BYTE_LIMIT,
    inline_byte_limit: int = DIAGNOSTICS_BYTE_LIMIT,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """Bound every severity, including errors and actionable suggestions.

    Message budgets count actual UTF-8 text, and the list budget counts its JSON
    representation. Complete originals belong in ``mapped_diagnostics`` and the
    durable diagnostic artifact; this function never mutates them.
    """
    if min(message_byte_limit, message_total_byte_limit) < 0 or inline_byte_limit < 2:
        raise ValueError("diagnostic budgets must be nonnegative and allow a JSON list")
    selected: list[dict[str, Any]] = []
    inline_bytes, message_bytes, kept_bytes, truncated = 2, 0, 0, 0
    original_bytes = sum(len(str(item.get("message", "")).encode("utf-8")) for item in diagnostics)
    for diagnostic in diagnostics:
        message = str(diagnostic.get("message", ""))
        available = min(message_byte_limit, message_total_byte_limit - message_bytes)
        if message and available <= 0:
            continue
        excerpt, kept = utf8_excerpt(message, available)
        shown = {**diagnostic, "message": excerpt}
        original = len(message.encode("utf-8"))
        if kept < original:
            shown["message_truncation"] = {
                "original_utf8_bytes": original,
                "omitted_utf8_bytes": original - kept,
            }
        encoded_size = len(json.dumps(shown, ensure_ascii=False).encode("utf-8"))
        added = encoded_size + (2 if selected else 0)
        if inline_bytes + added > inline_byte_limit:
            continue
        selected.append(shown)
        inline_bytes += added
        message_bytes += len(excerpt.encode("utf-8"))
        kept_bytes += kept
        truncated += kept < original
    return selected, {
        "message_utf8_byte_limit": message_byte_limit,
        "total_message_utf8_byte_limit": message_total_byte_limit,
        "inline_json_utf8_byte_limit": inline_byte_limit,
        "inline_json_utf8_bytes": inline_bytes,
        "inline_message_utf8_bytes": message_bytes,
        "original_message_utf8_bytes": original_bytes,
        "omitted_message_utf8_bytes": original_bytes - kept_bytes,
        "messages_truncated": truncated,
        "diagnostics_omitted": len(diagnostics) - len(selected),
    }


def warning_family(message: str) -> str:
    option = LINTER_OPTION.search(message)
    if option:
        return option[1]
    for pattern, family in (
        (r"(?i)^unused variable\b", "unused-variable"),
        (r"(?i)^This simp argument is unused\b", "unused-simp-argument"),
        (r"(?i)^This tactic is never executed\b", "unreachable-tactic"),
        (r"^`[^`]+` has been deprecated\b", "deprecated-declaration"),
    ):
        if re.search(pattern, message):
            return family
    # Unknown warnings only collapse when their entire normalized messages match.
    return "message:" + re.sub(r"\s+", " ", message).strip()


def _compact_diagnostics(
    diagnostics: Sequence[dict[str, Any]], *, information_limit: int = 30
) -> tuple[list[dict[str, Any]], int]:
    errors, actionable, information = [], [], []
    warnings: dict[str, list[dict[str, Any]]] = {}
    for diagnostic in diagnostics:
        severity, message = (
            diagnostic.get("severity"),
            str(diagnostic.get("message", "")),
        )
        if severity == "error":
            errors.append(diagnostic)
        elif ACTIONABLE.search(message):
            actionable.append(diagnostic)
        elif severity == "warning":
            warnings.setdefault(warning_family(message), []).append(diagnostic)
        elif message.strip() != "Goals accomplished!":
            information.append(diagnostic)
    groups = []
    for family, values in warnings.items():
        # Prefer a target warning to an earlier prefix warning from the same linter.
        representative = next(
            (
                item
                for item in values
                if (item.get("location") or {}).get("scope") == "candidate"
            ),
            values[0],
        )
        if len(values) == 1:
            groups.append(representative)
            continue
        locations = [item.get("location") for item in values]
        groups.append(
            {
                **representative,
                "warning_family": family
                if not family.startswith("message:")
                else "repeated-warning",
                "count": len(values),
                "locations": locations[:8],
                "locations_omitted": max(0, len(locations) - 8),
            }
        )
    selected = [
        *errors,
        *actionable,
        *groups,
        *information[: max(0, information_limit)],
    ]
    return selected, len(diagnostics) - len(selected)


def compact_diagnostics(
    diagnostics: Sequence[dict[str, Any]], *, information_limit: int = 30
) -> tuple[list[dict[str, Any]], int]:
    selected, compacted = _compact_diagnostics(diagnostics, information_limit=information_limit)
    bounded, metadata = bound_diagnostics(selected)
    return bounded, compacted + metadata["diagnostics_omitted"]


def present_diagnostics(
    raw: Sequence[dict[str, Any]],
    source_map: SourceMap | None = None,
    *,
    source: str | None = None,
    information_limit: int = 30,
    position_encoding: str = "utf-16",
) -> dict[str, Any]:
    mapped = [
        map_diagnostic(
            item, source_map, source=source, position_encoding=position_encoding
        )
        for item in raw
    ]
    selected, compacted = _compact_diagnostics(mapped, information_limit=information_limit)
    compact, bounds = bound_diagnostics(selected)
    # Count all original messages, including warning groups and information that
    # were compacted before applying the byte budgets.
    original_bytes = sum(len(item["message"].encode("utf-8")) for item in mapped)
    bounds["omitted_message_utf8_bytes"] += original_bytes - bounds["original_message_utf8_bytes"]
    bounds["original_message_utf8_bytes"] = original_bytes
    bounds["diagnostics_omitted"] += compacted
    return {
        "diagnostics": compact,
        "diagnostics_compacted": bounds["diagnostics_omitted"],
        "diagnostics_truncation": bounds,
        "mapped_diagnostics": mapped,
    }


def location_text(location: dict[str, Any] | None) -> str:
    if not location:
        return "unknown"
    encoding = " (UTF-16 column)" if location.get("column_encoding") == "utf-16" else ""
    return f"{location['scope']}:{location['line']}:{location['column']}{encoding}"


def diagnostic_text(diagnostics: Sequence[dict[str, Any]]) -> str:
    lines = []
    for item in diagnostics:
        group = ""
        if item.get("count", 1) > 1:
            locations = ", ".join(location_text(value) for value in item["locations"])
            more = item.get("locations_omitted", 0)
            group = f" [{item['warning_family']}: {item['count']} occurrences at {locations}"
            if more:
                group += f", +{more} locations in full diagnostics"
            group += "]"
        lines.append(
            f"{location_text(item.get('location'))}: {item.get('severity', 'unknown')}{group}: {item.get('message', '')}"
        )
    return "\n".join(lines)


def artifact_directory(candidate_path: Path | None = None) -> Path:
    if candidate_path is not None:
        parent = candidate_path.resolve().parent
        for ancestor in (parent, *parent.parents):
            if ancestor.name == ".feedback":
                return ancestor / "diagnostics"
        return parent / ".feedback" / "diagnostics"
    configured = os.environ.get("LEAN_REFACTOR_EVALUATION_CACHE")
    root = Path(configured) if configured else Path(tempfile.gettempdir()) / "lrh"
    return root / "diagnostics"


def archive_diagnostics(
    raw: Sequence[dict[str, Any]],
    presentation: dict[str, Any],
    *,
    source: str,
    candidate_path: Path | None = None,
    candidate_bytes: bytes | None = None,
    source_map: SourceMap | None = None,
    service_omitted: int = 0,
) -> Path:
    payload = {
        "schema_version": 1,
        "generated_source": source,
        "generated_source_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest(),
        "candidate": str(candidate_path.resolve()) if candidate_path else None,
        "candidate_source_sha256": (
            hashlib.sha256(candidate_bytes).hexdigest()
            if candidate_bytes is not None
            else hashlib.sha256(
                (source_map.original_candidate or source_map.candidate).encode("utf-8")
            ).hexdigest()
            if source_map
            else None
        ),
        "raw_diagnostics": list(raw),
        "service_diagnostics_omitted": service_omitted,
        **presentation,
    }
    encoded = (json.dumps(payload, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    source_key = payload["candidate_source_sha256"]
    path = artifact_directory(candidate_path) / (
        (source_key + "-" if source_key else "")
        + hashlib.sha256(encoded).hexdigest() + ".json"
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists():
        descriptor, temporary = tempfile.mkstemp(
            prefix="diagnostics-", suffix=".json", dir=path.parent
        )
        try:
            with os.fdopen(descriptor, "wb") as stream:
                stream.write(encoded)
            os.replace(temporary, path)
        finally:
            Path(temporary).unlink(missing_ok=True)
    return path
