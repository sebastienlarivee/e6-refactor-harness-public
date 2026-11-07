"""POSIX shell fallbacks for the configured native feedback service."""
from __future__ import annotations

import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import json
import shlex
import sys
from pathlib import Path

from lean_tools import feedback_workflow as feedback


def feedback_command(capsule: Path, workflow: Path, mode: str) -> str:
    request = json.dumps({"mode": mode}, separators=(",", ":"))
    arguments = [
        str(Path(sys.executable).resolve()),
        str(workflow.resolve().with_name("feedback_workflow.py")),
        "--config", str((capsule / feedback.CONFIG_NAME).resolve()),
    ]
    return "printf '%s\\n' " + shlex.quote(request) + " | " + shlex.join(arguments)


def fallback_document(
    capsule: Path, workflow: Path, timeout_seconds: int, *, lean_timeout_scope: str | None = None,
) -> str:
    scope = lean_timeout_scope or feedback.arena.lean_timeout_scope()
    timeout_guidance = (
        "The timeout covers each Lean compilation; resource admission and the complete call can take longer."
        if scope == "compile" else
        "The timeout covers each Lean request, including resource admission; a complete call may make several requests."
    )
    status_command = shlex.join([str(Path(sys.executable).resolve()),
                                 str(workflow.resolve().with_name("feedback_requests.py")),
                                 "--root", str(capsule.resolve()), "--limit", "5"])
    return f"""If the native tool is unavailable, run these POSIX shell commands. They use the
same task, candidate, checkpoint directory, inherited broker and {timeout_seconds}-second
validation timeout setting from `feedback-config.json`. {timeout_guidance}
They check the current file:

```sh
{feedback_command(capsule, workflow, 'quick')}
{feedback_command(capsule, workflow, 'advisory')}
{feedback_command(capsule, workflow, 'exact')}
```

The JSON accepts the same `body`, `edits`, `goal`, and `candidate` fields as the native
tool. For an alternate draft, set `candidate` to its filename. For multiline edits, write
a request JSON file and redirect it into the same Python command with `< request.json`.

For a call with no visible completion, inspect durable request status from a separate
shell, even while the synchronous MCP server is busy: `{status_command}`.
Read a completed result before retrying; avoid concurrent edits to a candidate with
in-progress work. This read-only query does not cancel work. A response write does
not establish that the model received it. Await native tool promises in JavaScript.
"""
