"""Isolated E6 capsule preparation and the shared Lean worker recipes.

This module deliberately contains no swarm, planner, or campaign runtime.
"""
from __future__ import annotations

# Direct CLI execution and package imports share the same module identities.
import sys as _sys
from pathlib import Path as _Path
if not __package__:
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent))

import datetime as dt
import json
import math
import os
import shlex
import shutil
import sys
import time
import uuid
from collections.abc import Sequence
from pathlib import Path
from typing import Any

from lean_tools import advisory_feedback
from lean_tools import arena_workflow as arena
from lean_tools import feedback_commands
from lean_tools.measurement_policy import LEGACY_POLICY, SCORING_POLICY_ENV, resolve_scoring_policy
from lean_tools import persistent_quick_workflow as persistent_quick
def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )

def agent_writable_roots(project_root: Path, run_dir: Path) -> tuple[Path, ...]:
    """Return the narrow shared roots required by evaluators inside agent capsules."""
    candidates = [
        run_dir / "event-spool",
        run_dir / "lean-logs",
        run_dir / "evaluation-cache",
    ]
    for variable in ("LEAN_REFACTOR_LEAN_GATE", "LEAN_REFACTOR_SCRATCH_ROOT"):
        value = os.environ.get(variable)
        if value:
            candidates.append(Path(value))
    roots: list[Path] = []
    for candidate in candidates:
        root = candidate.resolve()
        root.mkdir(parents=True, exist_ok=True)
        if root not in roots:
            roots.append(root)
    return tuple(roots)

def copy_or_validate_file(source: Path, destination: Path) -> None:
    if destination.is_file():
        if arena.sha256_file(source) != arena.sha256_file(destination):
            raise arena.WorkflowError(
                f"resume input changed: {source} differs from {destination}"
            )
        return
    shutil.copy2(source, destination)

def quoted(path: Path) -> str:
    """Quote an absolute path as one POSIX shell argument."""
    return shlex.quote(str(path.resolve()))

def compact_initial_briefing(
    capsule: Path,
    project_root: Path,
    *,
    incumbent: dict[str, Any] | None = None,
    original_tokens: int | None = None,
    original_heartbeats: int | None = None,
    compatibility_roots: Sequence[Path] = (),
    goal_retrieval: bool = False,
    candidate_batches: bool = False,
    statement_first: bool = False,
    search_extensions: bool = False,
) -> str:
    """Place useful task facts on the first screen without copying Task.json.

    The caller supplies the already verified incumbent. Statement-first passes
    expose only the redacted candidate identity, never private original metrics
    or source bytes. Source paths describe the mounted legal-prefix overlay.
    """
    _, row = arena.load_task(capsule / "Task.json")
    primary = project_root.resolve()
    source_path = row.get("file_path")
    if source_path:
        target = require_child(primary / source_path, primary)
        source_map = f"Target source: `{target}`. Source directory: `{target.parent}`."
        if statement_first:
            source_map += " Statement-only overlay; the target's original proof and source suffix are unavailable. Dependent build artifacts and project history are masked; other project source files remain readable."
        elif type(row.get("start_line")) is int and row["start_line"] > 0:
            source_map += f" Legal project prefix ends before target line {row['start_line']}."
    else:
        source_map = "No project target filename is supplied; use the frozen imports and contexts in Candidate.lean."
    tools = ["lean_feedback.edit_check"]
    if type(original_tokens) is int and original_tokens > 0 and type(original_heartbeats) is int and original_heartbeats > 0:
        tools.append("lean_feedback.score_candidate")
    if candidate_batches:
        tools.append("lean_feedback.compare_candidates")
    if goal_retrieval:
        tools.append("lean_feedback.retrieve_lemmas")
    if search_extensions:
        tools.extend(("lean_feedback.suggest_proof", "lean_feedback.search_examples", "lean_feedback.example_neighbours"))
    lines = [
        f"Task: {row['name']}. Project root: `{primary}`.",
        source_map,
        f"Current Candidate.lean SHA-256 (full UTF-8 bytes): {arena.sha256_file(capsule / 'Candidate.lean')}.",
    ]
    if incumbent is not None and not statement_first:
        lines.append(
            f"Verified current incumbent: {incumbent['tokens']} local tokens; "
            f"{incumbent['heartbeats']} exact primary heartbeats; "
            f"{incumbent['compatibility_pct']:g}% compatibility; "
            f"combined score {incumbent['score']:g}/100 (host checks complete)."
        )
    if original_tokens is not None and original_heartbeats is not None:
        lines.append(f"Fixed scoring denominators: {original_tokens} local tokens and {original_heartbeats} heartbeats.")
    lines.extend([
        f"Compatibility: primary plus {len(compatibility_roots)} supplied versions; compare by the combined score.",
        "Edit only the proof body after :=. Preserve the signature, frozen header and contexts; use only declarations available in the legal prefix and supplied libraries.",
        f"Available native tools: {', '.join(tools)}. Read Candidate.lean and begin a concrete improvement; use COMMANDS.md for optional discovery and shell recipes.",
        "Use quick checks for speculative structural or dependent-type changes, then exact checks for promising proofs. Stable small optimizations may go directly to exact measurement.",
        "source_text is literal Lean source; checkpoint_id loads a saved checkpoint. Supply the current expected_sha256 when replacing or restoring source. Tool results carry the next source hash and snapshot-bound goal handles.",
    ])
    if goal_retrieval:
        lines.append("Use a returned goal_id for retrieval, or omit goal selection to use the first proof-body tactic's recorded pre-tactic goal; it may already be discharged. Avoid guessed line numbers.")
    if search_extensions:
        lines.append(
            "Optional search: suggest_proof proposes a direct proof term for a recorded goal. Paste the returned term "
            "with exact or refine, remove the exploratory search tactic from the scored proof, and validate normally. "
            "search_examples returns small source examples for analogy; a displayed name is not verified callable here. "
            "Use example_neighbours for a promising example's exact seed_name when useful. Further searches are optional; "
            "do not repeat calls merely to satisfy a routine.")
    return "\n".join(lines) + "\n"

def discovery_tools_prompt(
    capsule: Path,
    workflow: Path,
    project_root: Path,
    compatibility_roots: Sequence[Path] = (),
    *,
    allow_aesop_output: bool,
    timeout_seconds: int = 600,
    local_attempts_guidance: bool = False,
    rerank_config: dict[str, Any] | None = None,
) -> str:
    from lean_tools import rerank_service_client as reranking

    options, automatic = ((rerank_config, True) if rerank_config is not None
                          else reranking.resolve_options())
    limits = reranking.search_limit_contract(options, automatic, enabled=bool(options))
    search_limit = min(20, limits["result_limit"]["default"])
    search_limits = (
        f"Search limits are frozen by the host: `1 <= --limit <= --candidate-limit <= {limits['candidate_limit']['maximum']}`. "
        f"Defaults: `--limit {limits['result_limit']['default']}` and `--candidate-limit {limits['candidate_limit']['default']}`."
        if limits["frozen"] else
        f"Plain search accepts any positive `--limit`. Optional reranking requires `1 <= --limit <= --candidate-limit <= {reranking.MAX_CANDIDATES}`."
    )
    search_ranking = (
        f" Frozen ranking: `{options['ranker']}`; omit `--ranker` and `--model` to use the host configuration."
        if automatic else ""
    )
    tools = workflow.resolve().parent
    context = tools / "context_tools.py"
    goal_state = tools / "lean_goal_state.py"
    oracle = tools / "oracle_search.py"
    task = capsule / "Task.json"
    candidate = capsule / "Candidate.lean"
    fingerprint_registry = capsule / "environment-fingerprints.json"
    fingerprint_argument = (
        f"--fingerprint-registry {quoted(fingerprint_registry)}"
    )
    root_arguments = " ".join(
        f"--project-root {quoted(root)}"
        for root in (project_root, *compatibility_roots)
    )
    aesop_output = (
        f" --candidate-output {quoted(capsule / 'AesopCandidate.lean')}"
        if allow_aesop_output
        else ""
    )
    aesop_command = (
        f"{quoted(Path(sys.executable))} {quoted(oracle)} aesop --task {quoted(task)} "
        f"--project-root {quoted(project_root)} {fingerprint_argument} --timeout {timeout_seconds}"
    )
    compatibility_oracle = ""
    if compatibility_roots:
        fallback_commands = "\n".join(
            f"  - `{aesop_command} --oracle-project-root {quoted(root)}{aesop_output}`"
            for root in compatibility_roots
        )
        compatibility_oracle = (
            "\n  If the primary probe is unavailable, retry each supplied oracle "
            "checkout in order; pristine replay stays on the primary root:\n"
            + fallback_commands
        )
    local_attempts = ""
    if local_attempts_guidance:
        probe = capsule / "LocalProbe.lean"
        local_attempts = f"""

Compare two or three relevant tactics at the same interior goal when useful. Copy
`Candidate.lean` to `LocalProbe.lean`; in the copy, replace the intended tactic block
with exactly one `__LRH_SUGGEST__` marker at its existing indentation. Preserve the
frozen header, contexts, signature, and any continuation you want checked. For example:
`{quoted(Path(sys.executable))} {quoted(context)} suggest --task {quoted(task)} {root_arguments} {fingerprint_argument} --candidate {quoted(probe)} --tactic 'exact?' --tactic 'simp?' --tactic 'simpa?' --timeout {timeout_seconds}`
Choose tactics relevant to the goal; repeated `--tactic` arguments override the sweep.
Each alternative independently replaces the same marker, and later tactics still run.
A replacement that closes the goal may require removing its old continuation in the
copy. Inspect every result and explicit suggestion. `solved` means the whole disposable
probe has no errors; it is not an optimization rank or a saved checkpoint. Partial
progress is provisional: fewer remaining goals are not an optimization score. Keep
`Candidate.lean` untouched during probes, then apply a complete promising alternative
and compare all relevant alternatives by exact whole-proof and compatibility evaluation,
using the actual combined score."""
    return f"""Arena-safe discovery tools (JSON stdout). Alongside the evaluator and feedback wrappers
named elsewhere in this prompt, these are the only additional out-of-capsule helper files
you may execute:

- capability intersection: `{quoted(Path(sys.executable))} {quoted(context)} capabilities --task {quoted(task)} {root_arguments} {fingerprint_argument} --timeout {timeout_seconds}`
- theorem-entry suggestion sweep: `{quoted(Path(sys.executable))} {quoted(context)} suggest --task {quoted(task)} {root_arguments} {fingerprint_argument} --timeout {timeout_seconds}`
- goals/hypotheses: `{quoted(Path(sys.executable))} {quoted(goal_state)} --task {quoted(task)} --candidate {quoted(candidate)} --project-root {quoted(project_root)} --line <one-based-line> --pretty --timeout {timeout_seconds}`
- prefix-bounded declaration search: `{quoted(Path(sys.executable))} {quoted(oracle)} search --task {quoted(task)} --project-root {quoted(project_root)} --name-query "map" --limit {search_limit} --timeout {timeout_seconds}`
  Add `--type-query "Finset"` to filter the rendered declaration types as well.
  {search_limits}{search_ranking}
- optional cached Aesop sidecar: `{aesop_command}{aesop_output}`{compatibility_oracle}

For suggestions at an interior goal, put one `__LRH_SUGGEST__` marker in a disposable
candidate copy and pass that copy with `--candidate`. Never leave the marker in the real
candidate. Aesop output is usable only when `pristine_replay.valid` is true, and it still
requires normal exact and cross-version evaluation. No scratch-only import, tactic,
declaration, or generated helper may remain in the final proof.{local_attempts}"""

def require_child(path: Path, parent: Path) -> Path:
    resolved = path.resolve()
    try:
        resolved.relative_to(parent.resolve())
    except ValueError as error:
        raise arena.WorkflowError(
            f"path escaped its intended parent: {resolved} not under {parent.resolve()}"
        ) from error
    return resolved

def prepare_capsule(
    capsule: Path,
    task_path: Path,
    guide_path: Path,
    candidate_text: str,
    *,
    interrupted_root: Path | None = None,
    fingerprint_registry: Path | None = None,
    retry_failed: bool = False,
) -> bool:
    prior_attempts = []
    if capsule.exists():
        result_path = capsule / "agent-run.json"
        try:
            result = json.loads(result_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            result = None
        terminal = isinstance(result, dict) and result.get("status") in {"completed", "failed", "interrupted"}
        if terminal and (result["status"] == "completed" or not retry_failed):
            copy_or_validate_file(task_path, capsule / "Task.json")
            copy_or_validate_file(guide_path, capsule / "LEAN_PROOF_GUIDE.md")
            if fingerprint_registry is not None:
                copy_or_validate_file(
                    fingerprint_registry, capsule / "environment-fingerprints.json"
                )
            return False
        if not retry_failed or interrupted_root is None:
            raise arena.WorkflowError(
                f"incomplete capsule already exists: {capsule}; use explicit --retry-failed with --resume to retry it"
            )
        interrupted_root.mkdir(parents=True, exist_ok=True)
        destination = interrupted_root / (
            f"{capsule.name}-{dt.datetime.now(dt.timezone.utc).strftime('%Y%m%d-%H%M%S')}-"
            f"{uuid.uuid4().hex[:8]}"
        )
        require_child(destination, interrupted_root)
        require_child(capsule, interrupted_root.parent)
        previous_identity = attempt_identity(capsule)
        manifest_path = capsule / "attempt.json"
        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8")) if manifest_path.exists() else {}
        except (OSError, ValueError):
            manifest = {}
        if not isinstance(manifest, dict):
            manifest = {}
        prior_attempts = [*manifest.get("prior_attempts", []), {
            "attempt_id": previous_identity,
            "result_path": str((destination / "agent-run.json").relative_to(interrupted_root.parent)),
            "events_path": str((destination / "codex-events.jsonl").relative_to(interrupted_root.parent)),
            "status": result.get("status", "interrupted") if isinstance(result, dict) else "interrupted",
        }]
        # Preserve every byte of the old capsule; recovery metadata is a new sidecar.
        if not manifest_path.exists():
            write_json(manifest_path, {"attempt_id": previous_identity, "prior_attempts": []})
        shutil.move(str(capsule), str(destination))
    capsule.mkdir(parents=True)
    shutil.copy2(task_path, capsule / "Task.json")
    shutil.copy2(guide_path, capsule / "LEAN_PROOF_GUIDE.md")
    if fingerprint_registry is not None:
        shutil.copy2(fingerprint_registry, capsule / "environment-fingerprints.json")
    (capsule / "Candidate.lean").write_text(candidate_text, encoding="utf-8")
    write_json(capsule / "attempt.json", {"attempt_id": uuid.uuid4().hex, "prior_attempts": prior_attempts})
    return True

def attempt_identity(capsule: Path) -> str:
    for name in ("attempt.json", "agent-run.json"):
        try:
            payload = json.loads((capsule / name).read_text(encoding="utf-8"))
        except (OSError, ValueError):
            continue
        if isinstance(payload, dict) and isinstance(payload.get("attempt_id"), str):
            return payload["attempt_id"]
    # Stable before a legacy attempt is moved; its sidecar carries this identity.
    return "legacy-" + arena.sha256_bytes(str(capsule.resolve()).encode())[:24]

def evaluator_commands(
    capsule: Path, workflow: Path, project_root: Path, timeout_seconds: int = 600
) -> tuple[str, str]:
    config = capsule / "feedback-config.json"
    settings = json.loads(config.read_text(encoding="utf-8")) if config.is_file() else {}
    policy = resolve_scoring_policy(settings.get("scoring_policy", LEGACY_POLICY))
    base = (
        f"{SCORING_POLICY_ENV}={shlex.quote(policy)} "
        f"{quoted(Path(sys.executable))} {quoted(workflow)} evaluate --task {quoted(capsule / 'Task.json')} "
        f"--candidate {quoted(capsule / 'Candidate.lean')} "
        f"--project-root {quoted(project_root)} --fingerprint-registry "
        f"{quoted(capsule / 'environment-fingerprints.json')} --checkpoint-dir "
        f"{quoted(capsule / 'valid-candidates')} --timeout {timeout_seconds}"
    )
    quick = f"{base} --quick"
    exact = f"{base} --json-output {quoted(capsule / 'latest-exact.json')}"
    return quick, exact

def scratch_evaluator_command(
    capsule: Path, workflow: Path, project_root: Path, timeout_seconds: int = 600
) -> str:
    return (
        f"{quoted(Path(sys.executable))} {quoted(workflow)} lean-file --path "
        f"{quoted(capsule / 'Scratch.lean')} --project-root {quoted(project_root)} --timeout {timeout_seconds}"
    )

def worker_commands_document(
    capsule: Path,
    workflow: Path,
    project_root: Path,
    mathlib_root: Path,
    include_project_source: bool = False,
    compatibility_roots: Sequence[Path] = (),
    timeout_seconds: int = 600,
    local_attempts_guidance: bool = False,
    candidate_batches: bool = False,
    goal_retrieval: bool = False,
    search_extensions: bool = False,
    rerank_config: dict[str, Any] | None = None,
    lean_timeout_scope: str | None = None,
) -> str:
    from lean_tools.feedback_contract import feature_flags, score_capability
    feature_flags({"candidate_batches": candidate_batches, "goal_retrieval": goal_retrieval,
                   "search_extensions": search_extensions})
    settings_path = capsule / "feedback-config.json"
    settings = json.loads(settings_path.read_text(encoding="utf-8")) if settings_path.is_file() else {}
    score_available = score_capability(settings)
    quick, exact = evaluator_commands(capsule, workflow, project_root, timeout_seconds)
    scratch = scratch_evaluator_command(capsule, workflow, project_root, timeout_seconds)
    fallback = feedback_commands.fallback_document(
        capsule, workflow, timeout_seconds, lean_timeout_scope=lean_timeout_scope)
    discovery = discovery_tools_prompt(
        capsule,
        workflow,
        project_root,
        compatibility_roots,
        allow_aesop_output=True,
        timeout_seconds=timeout_seconds,
        local_attempts_guidance=local_attempts_guidance,
        rerank_config=rerank_config,
    )
    search_scope = (
        f"- Project source: `{project_root}`\n- Mathlib source: `{mathlib_root}`"
        if include_project_source
        else f"- Mathlib source: `{mathlib_root}`"
    )
    document = f"""# Useful commands

Run all Lean work through these wrappers so it shares the experiment's cached
environments and resource gate. Do not invoke `lean` or `lake env lean` directly.

## Candidate validation

Prefer the native `lean_feedback.edit_check` tool: send `body` with a complete proof
after `:=`, or unique `edits` pairs, to edit, validate, count tokens, and checkpoint
in one call. Omit edits to check the current candidate. Use `source_text` for literal
complete Lean source, or `checkpoint_id` to restore an immutable saved checkpoint;
a pathname is not source text. Bind replacement/restoration to `expected_sha256`.
The legacy `source` alias still accepts literal source text. Supply exactly one
mutation field per request; `checkpoint_id` may instead supply the base for an
`edits` or `body` change. `operation="clone"` copies to a distinct `candidate`
without evaluation; `operation="restore"` restores the selected draft and
`operation="promote"` targets Candidate.lean. Copy-only results explicitly report
`evaluation_status="not_run"`; validate before treating a copy as proved.
`mode="quick"` cheaply checks speculative structural
or dependent-type changes; `mode="advisory"` gives a warm heartbeat estimate;
use `mode="exact"` to verify promising candidates. Stable small edits can go
directly to exact measurement. An optional `goal` uses one-based candidate
line/column; returned `goal_id` handles are bound to that source snapshot.

{fallback}

Direct evaluator commands also use the configured timeout:

- quick validation, local tokens, and immutable checkpoint: `{quick}`
- exact primary heartbeat and axiom measurement: `{exact}`

## Scratch discovery

For `#check` or other scratch work, create `Scratch.lean` and run:
`{scratch}`

Narrow read-only source searches may inspect only:

{search_scope}

## Arena-safe discovery

{discovery}
"""
    if not candidate_batches and not goal_retrieval and not score_available and not search_extensions:
        return document
    digest = arena.sha256_file(capsule / "Candidate.lean")
    tool_script = workflow.resolve().parent / "feedback_workflow.py"
    config = capsule / "feedback-config.json"

    def command(name: str, request: dict[str, Any]) -> str:
        encoded = shlex.quote(json.dumps(request, ensure_ascii=False))
        return (f"printf '%s\\n' {encoded} | {quoted(Path(sys.executable))} {quoted(tool_script)} "
                f"--config {quoted(config)} --tool {name}")

    document += f"""
## Experiment tools

These tools require `expected_sha256`, the 64 lowercase hex SHA-256 of the current
candidate's complete UTF-8 source. The starting candidate hash is `{digest}`;
refresh it after editing. Each request is bound to that exact source snapshot.
"""
    if score_available:
        document += """
Use `lean_feedback.score_candidate` with the current `expected_sha256` to measure
one promising candidate's complete combined score: exact primary heartbeats,
tokens, allowed axioms and every supplied compatibility version. The draft stays
unchanged; the optional `body`, `edits`, literal `source_text` or `checkpoint_id`
supplies an alternative. Incomplete measurements never receive a score. Inspect
the immutable checkpoint and explicitly promote or restore it if you choose it;
host final validation remains authoritative.
"""
    if candidate_batches:
        example = {"expected_sha256": digest, "alternatives": [
            {"label": "first", "body": "by\n  <complete first proof>"},
            {"label": "second", "body": "by\n  <complete second proof>"}]}
        document += f"""
Use `lean_feedback.compare_candidates` to compare two to four complete alternatives
from the same source. Each alternative has a unique `label` and exactly one `body`
or unique-match `edits` list. For example, replace the proof placeholders here:

```json
{json.dumps(example, ensure_ascii=False, indent=2)}
```

Shell fallback: `{command('compare_candidates', example)}`

The batch leaves the draft unchanged. It evaluates complete candidates by exact
primary heartbeats, local tokens, compatibility, and the fixed original combined
score; inspect every result, including timeouts and unscored rows. Raw tactic probes
report local observations and cannot supply this score. Partial progress remains
provisional; fewer goals do not establish improvement. Read the chosen immutable
checkpoint and explicitly restore it with `edit_check` using `checkpoint_id` and
the current `expected_sha256`, or apply literal source through `source_text`,
then validate normally.
The host still performs final exact and compatibility validation and selection.
"""
    if goal_retrieval:
        from lean_tools import rerank_service_client as reranking
        options, automatic = ((rerank_config, True) if rerank_config is not None
                              else reranking.resolve_options())
        limits = reranking.search_limit_contract(options, automatic, result_max=12, default_limit=8)
        example = {"expected_sha256": digest, "limit": limits["result_limit"]["default"]}
        retrieval_limits = (
            f"The frozen host allows `1 <= limit <= {limits['result_limit']['maximum']}` and "
            f"`limit <= candidate_limit <= {limits['candidate_limit']['maximum']}`; "
            f"the default candidate pool is {limits['candidate_limit']['default']}."
            if limits["frozen"] else
            "Use `1 <= limit <= 12` and `limit <= candidate_limit <= 5000`; without reranking the pool defaults to `limit`."
        )
        pool_mode = settings.get("retrieval_pool_mode", "overlap")
        pool_guidance = (
            "This pass uses the frozen overlap candidate pool. `name_query` has no effect here."
            if pool_mode == "overlap" else
            f"This pass uses the frozen {pool_mode} candidate pool. `name_query` and `search_intent` "
            "supply declaration words for complementary pool construction."
        )
        pool_guidance += f' Omit `pool_mode`, or use `"{pool_mode}"`; other pool modes are unavailable in this pass.'
        ranker = options.get("ranker", "baseline")
        ranker_guidance = (
            "This pass preserves baseline ordering, so `search_intent` and `same_run_context` "
            "do not change the ordering of the candidate pool."
            if ranker == "baseline" else
            f"Use `search_intent` or `same_run_context` to inform {ranker.upper() if ranker == 'jev' else ranker} "
            "ordering within the same candidate pool; reranking does not expand it."
        )
        if ranker == "baseline" and pool_mode == "overlap":
            ranker_guidance = (
                "This pass preserves baseline ordering, so `search_intent` and `same_run_context` "
                "do not change the shortlist."
            )
        elif ranker == "baseline":
            ranker_guidance = (
                "This pass preserves the constructed pool order without further reranking. "
                f"`search_intent` can change {pool_mode} pool admission and order; "
                "`same_run_context` has no effect."
            )
        document += f"""
Use `lean_feedback.retrieve_lemmas` with a returned snapshot-bound `goal_id`, or
omit goal selection to choose the first proof-body tactic's recorded pre-tactic goal automatically.
The recorded goal may already be discharged. Explicit one-based `goal` line/column
coordinates remain available; avoid guessed line numbers.
{retrieval_limits}
{pool_guidance}
{ranker_guidance}
For example, with automatic goal selection:

```json
{json.dumps(example, ensure_ascii=False, indent=2)}
```

Shell fallback: `{command('retrieve_lemmas', example)}`

Results are bounded declarations from the supplied primary environment's actual
prefix, ranked as discovery hints. Ranking is not Lean unification or proof
validation. Empty or unavailable retrieval is explicit. The tool leaves source
unchanged and saves no accepted checkpoint; test a suggested lemma through normal
editing and validation.
"""
    if search_extensions:
        direct_example = {"expected_sha256": digest, "limit": 3}
        source_example = {"expected_sha256": digest, "query": "<goal shape or proof idea>", "limit": 3}
        neighbour_example = {"expected_sha256": digest, "seed_name": "<exact returned example name>", "limit": 3}
        document += f"""
## Optional direct proofs and source examples

Use `lean_feedback.suggest_proof` with the current `expected_sha256` and a returned
snapshot-bound `goal_id`, or omit goal selection for the first recorded proof-body
pre-tactic goal. Explicit `goal` coordinates remain available. The bounded native
probe leaves the candidate unchanged and proposes a direct term. Paste a useful
returned term into the proof with `exact <term>` or `refine <term>`, remove the
exploratory search tactic from the scored proof, and validate the complete edited
candidate. A search result is not an accepted checkpoint or an exact cost measurement.
The recorded goal may already be discharged. Default result limit is 3 (maximum 5);
optional `native_heartbeats` is at most 200000 and `timeout_seconds` at most 30.
Shell fallback: `{command('suggest_proof', direct_example)}`

Use `lean_feedback.search_examples` for small source examples matching a proof idea
or structural pattern. Supply a useful `query`, `used_names`, or `tactic_shapes`;
for example replace the query placeholder in this shell fallback:
`{command('search_examples', source_example)}`

The immutable corpus contains only the exact legal source prefix and its recursive
imports from supplied cached sources. It excludes the target proof, its source suffix
and experiment history. Matches provide source snippets for analogy: adapt a useful
proof pattern, then test it in the actual goal. `callable_verified=false` means a
displayed declaration (including private, local or anonymous examples) is not verified
callable by name in this context. Source ranking is a discovery hint, never Lean
unification, correctness, compatibility or an optimization score. The host uses its
frozen source reranker when configured and otherwise retains lexical ordering.

Use `lean_feedback.example_neighbours` with the exact `seed_name` of a promising
returned example for lexical source references and nearby proof patterns. Optional
`query` narrows the followup:
`{command('example_neighbours', neighbour_example)}`

Both source tools return `matches`, default 3 and maximum 5. Individual source
snippets are bounded to 4000 characters and aggregate snippets to 12000 characters.
Searches and neighbour followups are optional. Use them when they resolve a concrete
uncertainty; do not force retries or repeated calls after unhelpful results. All
three tools require the current candidate's complete source hash and preserve it.
"""
    return document

def start_quick_broker(
    row: dict[str, Any],
    project_root: Path,
    work_root: Path,
    timeout_seconds: int,
    *,
    startup_timeout_seconds: float = 600,
) -> persistent_quick.PersistentQuickBroker:
    """Prepare and elaborate the original once, before starting the model timer."""
    if not math.isfinite(startup_timeout_seconds) or startup_timeout_seconds <= 0:
        raise arena.WorkflowError("startup timeout must be positive and finite")
    started = time.monotonic()
    deadline = started + startup_timeout_seconds
    work_root.mkdir(parents=True, exist_ok=True)
    setup: dict[str, Any] = {
        "status": "starting",
        "started_at": arena.utc_now(),
        "startup_timeout_seconds": startup_timeout_seconds,
        "request_timeout_seconds": timeout_seconds,
    }

    def remaining() -> float:
        if os.environ.get("LEAN_REFACTOR_LEAN_TIMEOUT_SCOPE") == "compile":
            # Each setup operation bounds its active work. Waiting for another
            # proof's compiler must not consume the later prewarm allowance.
            return startup_timeout_seconds
        budget = deadline - time.monotonic()
        if budget <= 0:
            raise persistent_quick.PersistentQuickError("Lean startup budget expired")
        return budget

    initial_source = arena.quick_compile_harness(
        row, arena.canonical_candidate_declaration(row), project_root
    )
    broker = None
    phase = "measurement_support"
    try:
        support = advisory_feedback.prepare_support(row, project_root, remaining())
        setup["support_seconds"] = round(time.monotonic() - started, 6)
        phase = "broker_start"
        broker = persistent_quick.PersistentQuickBroker(
            project_root,
            work_root,
            initial_source,
            timeout_seconds=timeout_seconds,
            startup_timeout_seconds=startup_timeout_seconds,
            lean_path_prefixes=[support] if support is not None else None,
        )
        broker.start()
        phase = "prewarm"
        setup["readiness"] = broker.prewarm(timeout_seconds=remaining())
        if not setup["readiness"].get("ready"):
            raise persistent_quick.PersistentQuickError("Lean prewarm did not report readiness")
        setup["status"] = "ready"
        setup["total_seconds"] = round(time.monotonic() - started, 6)
        setup["finished_at"] = arena.utc_now()
        write_json(work_root / "setup.json", setup)
        # Agents only inherit a broker after its document is ready for warm edits.
        os.environ.update(broker.environment())
        return broker
    except BaseException as error:
        setup.update(status="failed", failure_phase=phase, error=str(error))
        if broker is not None:
            try:
                broker.close()
            except (OSError, persistent_quick.PersistentQuickError) as close_error:
                setup["close_error"] = str(close_error)
        setup["total_seconds"] = round(time.monotonic() - started, 6)
        setup["finished_at"] = arena.utc_now()
        try:
            write_json(work_root / "setup.json", setup)
        except OSError as log_error:
            error.add_note(f"Could not record Lean startup failure: {log_error}")
        raise
