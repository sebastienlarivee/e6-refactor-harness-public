"""The persisted one-declaration task schema and its read boundary."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from lean_tools.workflow_errors import WorkflowError

def normalize_arena_row(raw_row: dict[str, Any]) -> dict[str, Any]:
    """Adapt a current Arena row to the one-declaration workflow schema."""
    row = dict(raw_row)
    if not isinstance(row.get("name"), str) or not row["name"]:
        raise WorkflowError("Arena row has no valid name")
    signature = row.get("signature", row.get("statement"))
    if not isinstance(signature, str) or not signature:
        raise WorkflowError(f"{row['name']}: Arena row has no statement/signature")
    row["signature"] = signature.rstrip()
    row.setdefault("contexts", [])
    if not isinstance(row.get("src"), str):
        raise WorkflowError(f"{row['name']}: Arena row has no proof declaration")
    return row


def load_task(path: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    document = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(document, dict) or document.get("schema_version") != 1:
        raise WorkflowError(f"{path}: unsupported task document")
    row = document.get("row")
    if not isinstance(row, dict):
        raise WorkflowError(f"{path}: task document has no row")
    return document, normalize_arena_row(row)
