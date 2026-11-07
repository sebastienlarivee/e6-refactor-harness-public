"""Bounded advisory profiling of immutable source, using cached native Lean only.

No broker, evaluator writes, package build, candidate edits, or score is involved.
Selected spans are checked against the original parsed tactic syntax before AST
wrappers are inserted. Native Firefox export is used only in wall-time mode.
"""
from __future__ import annotations

import contextlib
import hashlib
import json
import math
import os
import re
import subprocess
import tempfile
import time
import uuid
from dataclasses import asdict
from pathlib import Path
from typing import Any, TYPE_CHECKING

from lean_tools.feedback_workflow import bind_feedback_scoring_policy
from lean_tools import arena_workflow as arena, lean_launch, lean_source, native_wall_time, resource_gate
if TYPE_CHECKING:
    from lean_tools.feedback_workflow import Feedback

TOOL_NAME = "profile_proof"
MAX_REGIONS = 8
MAX_MENU_REGIONS = 16
MAX_PROFILE_BYTES = native_wall_time.DEFAULT_MAX_PROFILE_BYTES
MAX_SAMPLES = native_wall_time.DEFAULT_MAX_SAMPLES
DEFAULT_TIMEOUT_SECONDS = 30
QUEUE_TIMEOUT_SECONDS = 10
INSTRUMENTATION_REVISION = 4
TOOL = {
    "name": TOOL_NAME,
    "description": "Optional advisory costs for a compiling immutable proof, including module-form sources. timeout_seconds is a separate process budget for validation and profiling, default/max 30 seconds each; shared admission waits have a separate 10-second budget and setup is bounded by timeout_seconds. Default stage allowance is 100 seconds before parsing; wall_time adds an independent 60-second native parsing allowance. Cleanup and artifact finalization may add time. No automatic retries. top_n is 1..8. Defaults to the unique outermost parsed tactic sequence, including nested by bodies in term/lambda proofs. Ambiguous or unsupported selections return a bounded source-bound menu with copyable byte-span selectors. Selected exact text/spans must be complete parsed tactics or tactic sequences. Repeated completions return partial observed count/total/min/max summaries with incomplete accounting and no parent remainder. Raw heartbeat counts and elapsed nanoseconds are inclusive instrumented observations, never a score or removable savings. wall_time enables tracing on the synchronous candidate and groups summed native thread-slice costs by tactic kind, without source-line attribution; the synthetic frontend remainder still includes imports/prefix work. Ordinary uninstrumented scoring remains authoritative.",
    "inputSchema": {
        "type": "object", "additionalProperties": False,
        "required": ["expected_sha256"],
        "properties": {
            "expected_sha256": {"type": "string", "pattern": "^[0-9a-f]{64}$",
                "description": "SHA256 of the selected source bytes. With checkpoint_id, use that checkpoint's source_sha256, not the current draft hash; otherwise use the selected candidate's current hash."},
            "candidate": {"type": "string",
                "description": "Capsule .lean filename. Mutually exclusive with checkpoint_id; omitting both selects the configured current candidate."},
            "checkpoint_id": {"type": "string",
                "description": "Saved checkpoint basename in this capsule. Mutually exclusive with candidate; expected_sha256 must match this checkpoint's source hash."},
            "mode": {"type": "string", "enum": ["regions", "wall_time"], "default": "regions"},
            "timeout_seconds": {"type": "number", "exclusiveMinimum": 0, "maximum": 30, "default": DEFAULT_TIMEOUT_SECONDS,
                "description": "Separate process cap for source validation and profiling; also bounds setup. Admission waits share a separate 10-second cap. No automatic retries."},
            "top_n": {"type": "integer", "minimum": 1, "maximum": 8, "default": 5},
            "regions": {"type": "array", "minItems": 1, "maxItems": 8,
                "description": "Regions mode only. Copy each menu region's selector object directly into this array, without a selector wrapper. Select complete supported parsed tactics or tactic sequences; omit for the unique outermost parsed tactic sequence.",
                "items": {
                "type": "object", "additionalProperties": False,
                "properties": {"id": {"type": "string", "pattern": "^[A-Za-z][A-Za-z0-9_-]{0,31}$"},
                               "text": {"type": "string", "minLength": 1, "maxLength": 65536,
                                   "description": "Exact selected-source text of a complete supported parsed tactic or tactic sequence. Use text or a byte span, not both; use a menu byte span if the text is ambiguous."},
                               "start_byte": {"type": "integer", "minimum": 0,
                                   "description": "Inclusive 0-based UTF-8 byte offset into the complete selected source. Pair with end_byte instead of text; copy menu offsets unchanged."},
                               "end_byte": {"type": "integer", "minimum": 1,
                                   "description": "Exclusive UTF-8 byte offset into the complete selected source. Pair with start_byte; the span must cover a complete supported parsed tactic or tactic sequence."}},
                "oneOf": [{"required": ["text"]}, {"required": ["start_byte", "end_byte"]}],
            }},
        },
    },
}
NOTE = ("Advisory instrumented observation only. Parent relationships describe syntax; any published remainder "
        "uses singleton containing observations and includes recording overhead. Region counts and totals cover "
        "observed surviving successful wrapper completions, not all attempted invocations: failed attempts emit "
        "no completion and backtracking can discard messages. "
        "Do not add parents to children or interpret a region as removable official heartbeats. "
        "Ordinary uninstrumented complete-proof scoring remains authoritative.")


class _AdmissionTimeout(TimeoutError):
    """A bounded resource wait expired, as distinct from a gate failure."""


def _budgets(timeout: float, maximum: float, mode: str = "regions") -> dict[str, Any]:
    pre_parse = 3 * timeout + QUEUE_TIMEOUT_SECONDS
    parse = native_wall_time.DEFAULT_MAX_PARSE_SECONDS if mode == "wall_time" else 0.0
    return {"timeout_scope": "per_lean_process", "setup_seconds": timeout,
        "maximum_process_seconds": maximum,
        "source_validation_process_seconds": timeout, "profile_process_seconds": timeout,
        "shared_queue_wait_seconds": QUEUE_TIMEOUT_SECONDS, "native_parse_seconds": parse,
        "pre_parse_stage_seconds": pre_parse, "total_stage_seconds": pre_parse + parse,
        "note": "At most one validation process and one profile process, with separate process caps; admission pools share one queue allowance. Wall-time parsing has its own fixed allowance, independent of timeout_seconds and quick-check budgets. Cleanup and artifact finalization may add time outside the stage allowance."}


def profiler_capability(row: dict[str, Any], project: Path, *, enabled: bool = True) -> dict[str, Any]:
    """Deterministic source-form preflight. Does not launch Lean or build files."""
    result: dict[str, Any] = {"schema_version": 1, "available": False, "supported_modes": [],
        "outcome": "disabled", "reason": "regional_profiler is disabled for this capsule",
        "prefix_sha256": None, "source_form": None, "default_timeout_seconds": DEFAULT_TIMEOUT_SECONDS,
        "max_timeout_seconds": 30, "timeout_scope": "per_lean_process",
        "shared_queue_wait_seconds": QUEUE_TIMEOUT_SECONDS,
        "native_parse_seconds": native_wall_time.DEFAULT_MAX_PARSE_SECONDS,
        "max_default_stage_seconds": _budgets(DEFAULT_TIMEOUT_SECONDS, 30, "wall_time")["total_stage_seconds"],
        "max_default_stage_seconds_by_mode": {mode: _budgets(DEFAULT_TIMEOUT_SECONDS, 30, mode)["total_stage_seconds"]
            for mode in ("regions", "wall_time")},
        "max_top_n": 8, "instrumentation_revision": INSTRUMENTATION_REVISION}
    if not enabled:
        return result
    try:
        prefix = lean_source.exact_source_prefix(row, project)
        _, module = lean_source.import_header_end(prefix.text)
    except (arena.WorkflowError, OSError, ValueError) as error:
        return {**result, "outcome": "prefix_unavailable", "reason": str(error)[:500]}
    return {**result, "available": True, "supported_modes": ["regions", "wall_time"],
            "outcome": "available", "reason": None, "prefix_sha256": prefix.sha256,
            "source_form": "module" if module else "ordinary"}


def _sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _remaining(deadline: float) -> float:
    remaining = deadline - time.perf_counter()
    if remaining <= 0:
        raise TimeoutError("profile request deadline expired")
    return remaining


def _request(request: Any) -> tuple[str, float, int]:
    allowed = set(TOOL["inputSchema"]["properties"])
    if not isinstance(request, dict) or set(request) - allowed:
        raise arena.WorkflowError("unknown profile_proof argument or arguments are not an object")
    if not isinstance(request.get("expected_sha256"), str) or not re.fullmatch(r"[0-9a-f]{64}", request["expected_sha256"]):
        raise arena.WorkflowError("expected_sha256 is required and must be a lowercase SHA256 of the selected source; use the checkpoint hash when checkpoint_id is set")
    if "candidate" in request and "checkpoint_id" in request:
        raise arena.WorkflowError("select either candidate or checkpoint_id; omit candidate when profiling a checkpoint")
    mode, timeout, top_n = request.get("mode", "regions"), request.get("timeout_seconds", DEFAULT_TIMEOUT_SECONDS), request.get("top_n", 5)
    if mode not in ("regions", "wall_time"):
        raise arena.WorkflowError("mode must be regions or wall_time")
    if isinstance(timeout, bool) or not isinstance(timeout, (int, float)) or not math.isfinite(timeout) or not 0 < timeout <= 30:
        raise arena.WorkflowError("timeout_seconds must be finite, positive, and at most 30")
    if type(top_n) is not int or not 1 <= top_n <= 8:
        raise arena.WorkflowError("top_n must be an integer from 1 to 8")
    if "regions" in request and (mode != "regions" or not isinstance(request["regions"], list) or not 1 <= len(request["regions"]) <= MAX_REGIONS):
        raise arena.WorkflowError("regions requires regions mode and 1 to 8 selections")
    return mode, float(timeout), top_n


def _artifact_directory(root: Path) -> Path:
    directory = root / ".feedback" / "profiles"
    for part in (root / ".feedback", directory):
        if part.is_symlink() or not part.resolve().is_relative_to(root):
            raise arena.WorkflowError("profile artifacts must remain inside the capsule")
        part.mkdir(exist_ok=True)
    return Path(tempfile.mkdtemp(prefix="profile-", dir=directory))


def _publish(path: Path, raw: bytes) -> None:
    """Publish each private source once and mark it read-only for later tools."""
    with path.open("xb") as stream:
        stream.write(raw)
    path.chmod(0o444)


def _freeze(feedback: Feedback, request: dict[str, Any], deadline: float) -> tuple[bytes, str, Path, str]:
    if "checkpoint_id" in request:
        path, source, _ = feedback.resolve_checkpoint(request["checkpoint_id"])
        raw = source.encode("utf-8")
        kind = "checkpoint"
    else:
        path = feedback.candidate_path(request)
        lexical = feedback.root / request.get("candidate", feedback.candidate.name)
        if lexical.is_symlink():
            raise arena.WorkflowError("profile source must be a regular capsule file")
        with arena.exclusive_file_lock(path.with_suffix(".edit.lock"), _remaining(deadline)):
            if not path.is_file():
                raise arena.WorkflowError("profile source file is missing; check the candidate first")
            raw = path.read_bytes()
        kind = "current"
    digest = _sha(raw)
    if digest != request["expected_sha256"]:
        from lean_tools.feedback_workflow import EditRequestError
        raise EditRequestError("source conflict: expected_sha256 does not match the selected profile source",
                               code="source_conflict", source_kind=kind,
                               selected_source_path=str(path), selected_source_sha256=digest,
                               checkpoint_id=request.get("checkpoint_id"),
                               current_candidate_path=str(feedback.candidate),
                               current_candidate_sha256=(arena.sha256_file(feedback.candidate)
                                   if feedback.candidate.is_file() else None),
                               **({"current_snapshot_sha256": digest} if kind == "current" else {}))
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise arena.WorkflowError("profile source is not valid UTF-8") from error
    if "\r" in text:
        raise arena.WorkflowError("profiling requires LF source; newline conversion would invalidate byte mapping")
    return raw, text, path, kind


def _selections(request: dict[str, Any], source: str, candidate: lean_source.CandidateSnapshot) -> list[dict[str, Any]]:
    raw = source.encode("utf-8")
    body_min = len(source[:candidate.proof_body_start].encode("utf-8"))
    declaration_end = candidate.declaration_start + len(candidate.declaration)
    body_end = len(source[:declaration_end].encode("utf-8"))
    if "regions" not in request:
        return [{"id": "whole_proof", "automatic": True, "body_start_byte": body_min}]
    regions: list[dict[str, Any]] = []
    for index, item in enumerate(request["regions"]):
        if not isinstance(item, dict) or set(item) - {"id", "text", "start_byte", "end_byte"}:
            raise arena.WorkflowError("malformed region selection; copy the menu's selector object directly into regions, without a selector wrapper")
        label = item.get("id", f"region_{index + 1}")
        if not isinstance(label, str) or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]{0,31}", label):
            raise arena.WorkflowError("region id must start with a letter and use at most 32 ASCII letters, digits, _ or -")
        if "text" in item:
            needle = item["text"]
            if set(item) & {"start_byte", "end_byte"} or not isinstance(needle, str) or not needle.strip() or len(needle) > 65536:
                raise arena.WorkflowError("region uses either nonempty exact text or start_byte/end_byte")
            pos = source.find(needle)
            if pos < 0:
                raise arena.WorkflowError("region text must occur in the immutable source")
            if source.find(needle, pos + 1) >= 0:
                if source.find(needle, candidate.proof_body_start, declaration_end) < 0:
                    raise arena.WorkflowError("regions must lie inside the candidate proof body")
                # Preserve exact-substring semantics: `ring` inside `ring1`
                # remains ambiguous. The existing profile process can report
                # actual parsed alternatives without guessing an occurrence.
                regions.append({"id": label, "ambiguous_text": True, "text": needle})
                continue
            start, end = len(source[:pos].encode("utf-8")), len(source[:pos + len(needle)].encode("utf-8"))
        else:
            start, end = item.get("start_byte"), item.get("end_byte")
            if type(start) is not int or type(end) is not int or not 0 <= start < end <= len(raw):
                raise arena.WorkflowError("region byte span must be a nonempty half-open UTF-8 range")
        try:
            fragment = raw[start:end].decode("utf-8")
            raw[:start].decode("utf-8")
        except UnicodeDecodeError as error:
            raise arena.WorkflowError("region span must align to UTF-8 character boundaries") from error
        requested_span = {"start_byte": start, "end_byte": end}
        leading = len(fragment) - len(fragment.lstrip())
        start += len(fragment[:leading].encode("utf-8"))
        end -= len(fragment[len(fragment.rstrip()):].encode("utf-8"))
        if not body_min <= start < end <= body_end:
            raise arena.WorkflowError("regions must lie inside the candidate proof body")
        regions.append({"id": label, "start_byte": start, "end_byte": end, "requested_span": requested_span})
    if len({item["id"] for item in regions}) != len(regions):
        raise arena.WorkflowError("region ids must be unique")
    for index, left in enumerate(regions):
        for right in regions[index + 1:]:
            if left.get("ambiguous_text") or right.get("ambiguous_text"):
                continue
            a, b, c, d = left["start_byte"], left["end_byte"], right["start_byte"], right["end_byte"]
            if (a, b) == (c, d) or a < c < b < d or c < a < d < b:
                raise arena.WorkflowError("regions must be distinct and disjoint or properly nested")
    return regions


# Only parsed tactic sequences and immediate tactics in standard indented
# sequences are accepted. Other parser layouts fail before elaboration.
_HELPER = r"""
namespace @N@
open Lean Elab Command Tactic
syntax "@R@ " str " => " tacticSeq : tactic
elab_rules : tactic
  | `(tactic| @R@ $label:str => $seq:tacticSeq) => do
    let h0 ← IO.getNumHeartbeats
    let n0 ← IO.monoNanosNow
    evalTactic seq
    let n1 ← IO.monoNanosNow
    let h1 ← IO.getNumHeartbeats
    logInfo m!"@TOKEN@ REGION {label.getString} {h1 - h0} {n1 - n0}"
def selections : Array (Nat × Nat × String) := @SELECTIONS@
def proofStart : Nat := @PROOF_START@
def proofEnd : Nat := @PROOF_END@
def automatic : Bool := @AUTOMATIC@
def ambiguousText : Bool := @AMBIGUOUS@
def targets : Array (Nat × Nat) := @TARGETS@
structure Catalog where
  menu : Array (Nat × Nat × Bool × Nat) := #[]
  roots : Array (Nat × Nat) := #[]
  truncated : Bool := false
def consider (state : Catalog) (start finish : Nat) (sequence root : Bool) : Catalog := Id.run do
  let mut state := state
  if root && state.roots.size < 2 then
    state := { state with roots := state.roots.push (start, finish) }
  if state.menu.any (fun entry => entry.1 == start && entry.2.1 == finish) then
    return state
  let mut priority := if root then 0 else if sequence then 2 else 1
  if !targets.isEmpty then
    priority := targets.foldl (fun best target =>
      min best (start - target.1 + (target.1 - start) +
        (finish - target.2) + (target.2 - finish))) (proofEnd * 4 + 1)
  let entry := (start, finish, sequence, priority)
  if state.menu.size < @MENU_LIMIT@ then
    return { state with menu := state.menu.push entry }
  let mut worst := 0
  for i in [1:state.menu.size] do
    if state.menu[i]!.2.2.2 > state.menu[worst]!.2.2.2 then
      worst := i
  let menu := if priority < state.menu[worst]!.2.2.2 then state.menu.set! worst entry else state.menu
  return { state with menu, truncated := true }
partial def catalog (stx : Syntax) (state : Catalog)
    (asTactic : Bool := false) (asList : Bool := false)
    (inSequence : Bool := false) : Catalog := Id.run do
  let start := (stx.getPos?.getD 0).byteIdx
  let finish := (stx.getTailPos?.getD 0).byteIdx
  let sequence := stx.getKind == ``Lean.Parser.Tactic.tacticSeq
  let supported := (sequence || asTactic) && proofStart <= start && start < finish && finish <= proofEnd
  let mut state := state
  if supported then
    state := consider state start finish sequence (sequence && !inSequence)
  if let .node _ kind args := stx then
    for i in [:args.size] do
      state := catalog args[i]! state (asList && i % 2 == 0)
        (kind == ``Lean.Parser.Tactic.tacticSeq1Indented && i == 0)
        (inSequence || (sequence && supported))
  return state
partial def transform (stx : Syntax) (seen : Array Nat)
    (asTactic : Bool := false) (asList : Bool := false) : CommandElabM (Syntax × Array Nat) := do
  let start := (stx.getPos?.getD 0).byteIdx
  let finish := (stx.getTailPos?.getD 0).byteIdx
  let sequence := stx.getKind == ``Lean.Parser.Tactic.tacticSeq
  let mut selected : Option Nat := none
  let mut seen := seen
  if sequence || asTactic then
    for i in [:selections.size] do
      let (a, b, _) := selections[i]!
      if !seen.contains i && ((a == start && b == finish) ||
          (automatic && b == 0 && sequence && proofStart <= start && finish <= proofEnd)) then
        selected := some i
        seen := seen.push i
        logInfo m!"@TOKEN@ MATCH {i} {start} {finish}"
        break
  let mut result := stx
  if let .node info kind args := stx then
    let mut updated := #[]
    for i in [:args.size] do
      let (child, next) ← transform args[i]! seen
        (asList && i % 2 == 0)
        (kind == ``Lean.Parser.Tactic.tacticSeq1Indented && i == 0)
      seen := next
      updated := updated.push child
    result := .node info kind updated
  if let some i := selected then
    let label := Syntax.mkStrLit (selections[i]!).2.2
    if sequence then
      let seq : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨result⟩
      result := (← `(tacticSeq| @R@ $label:str => $seq:tacticSeq)).raw
    else
      let tac : TSyntax `tactic := ⟨result⟩
      result := (← `(tactic| @R@ $label:str => $tac:tactic)).raw
  return (result, seen)
syntax "@C@ " command : command
elab_rules : command
  | `(@C@ $cmd:command) => do
    let choices := catalog cmd {}
    for (start, finish, sequence, _) in choices.menu do
      let kind : Nat := if sequence then 1 else 0
      logInfo m!"@TOKEN@ MENU {start} {finish} {kind}"
    logInfo m!"@TOKEN@ MENU_STATE {choices.truncated} {choices.roots.size}"
    if ambiguousText then
      throwError "@TOKEN@ AMBIGUOUS_REGION: exact text occurs more than once; use a menu byte span"
    if automatic && choices.roots.size != 1 then
      throwError "@TOKEN@ UNSUPPORTED_REGION: default requires one outermost parsed tactic sequence; select a menu byte span"
    let (instrumented, seen) ← transform cmd #[]
    if seen.size != selections.size then
      throwError "@TOKEN@ UNSUPPORTED_REGION: selection is not a complete supported parsed tactic or tactic sequence"
    let h0 ← IO.getNumHeartbeats
    let n0 ← IO.monoNanosNow
    let instrumented : TSyntax `command := ⟨instrumented⟩
    elabCommand (← `(command| set_option Elab.async false in $instrumented:command))
    let n1 ← IO.monoNanosNow
    let h1 ← IO.getNumHeartbeats
    logInfo m!"@TOKEN@ COMMAND {h1 - h0} {n1 - n0}"
end @N@
"""


def _instrument(prefix: str, declaration: str, candidate: lean_source.CandidateSnapshot,
                regions: list[dict[str, Any]], token: str) -> tuple[str, int]:
    namespace, region_name, command_name = "E6Profile" + token, "e6_region_" + token, "e6_command_" + token
    proof_start = len(candidate.text[:candidate.proof_body_start].encode("utf-8"))
    proof_end = len(candidate.text[:candidate.declaration_start + len(candidate.declaration)].encode("utf-8"))
    targets = []
    for item in regions:
        if item.get("ambiguous_text"):
            pos = candidate.text.find(item["text"], candidate.proof_body_start)
            # Guidance stays bounded even for a very common substring. Never
            # turn these lexical occurrences into claimed parsed regions.
            for _ in range(MAX_MENU_REGIONS):
                if pos < 0:
                    break
                start = len(candidate.text[:pos].encode("utf-8"))
                end = start + len(item["text"].encode("utf-8"))
                if end <= proof_end:
                    targets.append((start, end))
                pos = candidate.text.find(item["text"], pos + 1)
        elif not item.get("automatic"):
            targets.append((item["start_byte"], item["end_byte"]))

    def helper(offset: int) -> str:
        selection_text = "#[" + ", ".join(
            f'({item.get("start_byte", item.get("body_start_byte", proof_start)) + offset}, {0 if item.get("automatic") or item.get("ambiguous_text") else item["end_byte"] + offset}, "{item["id"]}")'
            for item in regions) + "]"
        result = _HELPER
        for key, value in (("@N@", namespace), ("@R@", region_name), ("@C@", command_name),
                           ("@TOKEN@", token), ("@SELECTIONS@", selection_text),
                           ("@PROOF_START@", str(proof_start + offset)), ("@PROOF_END@", str(proof_end + offset)),
                           ("@AUTOMATIC@", str(any(item.get("automatic") for item in regions)).lower()),
                           ("@AMBIGUOUS@", str(any(item.get("ambiguous_text") for item in regions)).lower()),
                           ("@TARGETS@", "#[" + ", ".join(f"({a + offset}, {b + offset})" for a, b in targets) + "]"),
                           ("@MENU_LIMIT@", str(MAX_MENU_REGIONS))):
            result = result.replace(key, value)
        # Module files distinguish compile-time helpers from runtime definitions.
        # Close this scope before replaying the original prefix/target.
        return "meta section\n" + result + "\nend\n" if module else result

    header_end, module = lean_source.import_header_end(prefix)
    header, body_prefix = prefix[:header_end], prefix[header_end:]
    helper_import = "public meta import Lean" if module else "import Lean"
    # Decimal offset width can change helper size; stabilize before publishing.
    offset = 0
    for _ in range(12):
        before = (header + "\n" + helper_import + "\n" + helper(offset) + "\n" + body_prefix
                  + "\nset_option Elab.async false in\n" + command_name + "\n")
        next_offset = len(before.encode("utf-8")) - len(candidate.text[:candidate.declaration_start].encode("utf-8"))
        if next_offset == offset:
            return before + declaration.rstrip() + "\n", offset
        offset = next_offset
    raise arena.WorkflowError("could not stabilize private instrumentation source map")


def _prepare_launch(project: Path, deadline: float) -> lean_launch.LaunchEnvironment:
    # The exporter refuses absent/stale lakefiles and dependencies. It exports
    # an existing environment only, and never builds or downloads anything.
    try:
        return lean_launch.prepare_launch(project, deadline=deadline, environment=os.environ,
                                          record_event=arena.record_event)
    except lean_launch.LaunchCacheError as error:
        # Launch preparation wraps both deadlines and configuration failures in
        # one exception class. Classify its explicit timeout forms only.
        if str(error) in {"Lean launch preparation deadline expired", "Lake environment exporter timed out"} or re.fullmatch(
                r"Lean launch cache preparation failed: timed out waiting for \S+ permit", str(error)):
            raise TimeoutError(str(error)) from error
        raise


def _run(path: Path, project: Path, launch: lean_launch.LaunchEnvironment,
         deadline: float, args: list[str] | None = None, *, expected_sha256: str | None = None,
         process_timeout_seconds: float | None = None, admission: dict[str, Any] | None = None,
         purpose: str = "profile") -> arena.LeanRun:
    """Bound queueing separately from a single native process, without retries.

    The optional admission ledger is shared by validation and profiling. A
    finite outer deadline also covers preparation and protects every lane,
    independent of the authoritative scorer's timeout-scope setting.
    """
    admitted_digest = _sha(path.read_bytes())
    if expected_sha256 is not None and admitted_digest != expected_sha256:
        raise ValueError("private Lean source changed before process admission")
    priority = int(os.environ.get("LEAN_REFACTOR_LEAN_PRIORITY", "10"))
    environment = lean_launch.native_environment(launch.environment)
    command = lean_launch.native_command([launch.executable, "-j1", "--json", *(args or []), str(path.resolve())])
    with contextlib.ExitStack() as permits:
        metadata = {"source": str(path), "project_root": str(project), "purpose": "regional_profiler",
                    "profile_stage": purpose}
        queue_deadline = (min(deadline, time.perf_counter() + max(0.0,
            admission["budget_seconds"] - admission["wait_seconds"])) if admission is not None else deadline)
        queue_started = time.perf_counter()
        try:
            if os.environ.get("LEAN_REFACTOR_COLD_LEAN_GATE") or os.environ.get("LEAN_REFACTOR_COLD_LEAN_CAPACITY"):
                permits.enter_context(resource_gate.permit_from_environment("cold_lean", priority=priority,
                    timeout_seconds=_remaining(queue_deadline), metadata=metadata))
            permits.enter_context(resource_gate.permit_from_environment("lean", priority=priority,
                timeout_seconds=_remaining(queue_deadline), metadata=metadata))
        except (TimeoutError, resource_gate.ResourceGateError) as error:
            if admission is not None:
                admission["failure_stage"] = purpose
            if isinstance(error, TimeoutError) or re.fullmatch(r"timed out waiting for \S+ permit", str(error)):
                raise _AdmissionTimeout(str(error)) from error
            raise
        finally:
            queued = time.perf_counter() - queue_started
            if admission is not None:
                admission["wait_seconds"] += queued
                stages = admission.setdefault("stage_wait_seconds", {})
                stages[purpose] = stages.get(purpose, 0.0) + queued
        _remaining(deadline)
        if _sha(path.read_bytes()) != admitted_digest:
            raise ValueError("private Lean source changed while queued")
        process_started = time.perf_counter()
        process_deadline = (min(deadline, process_started + process_timeout_seconds)
                            if process_timeout_seconds is not None else deadline)
        process = subprocess.Popen(command, cwd=project, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            encoding="utf-8", errors="replace", env=environment,
            creationflags=subprocess.CREATE_NEW_PROCESS_GROUP if os.name == "nt" else 0,
            start_new_session=os.name != "nt")
        lean_launch.process_memory.capture_process_identity(process)
        timed_out = False
        try:
            output, _ = process.communicate(timeout=_remaining(process_deadline))
        except (subprocess.TimeoutExpired, TimeoutError) as error:
            timed_out = True
            arena.terminate_process_tree(process)
            output, _ = lean_launch.drain_process(process, error if isinstance(error, subprocess.TimeoutExpired)
                else subprocess.TimeoutExpired(command, 0))
    if _sha(path.read_bytes()) != admitted_digest:
        raise ValueError("private Lean source changed during native compilation")
    result = arena.LeanRun(command, process.returncode if process.returncode is not None else -1,
        time.perf_counter() - process_started, output, timed_out=timed_out, queue_wait_seconds=queued)
    arena.record_event("regional_profile_process", {**asdict(result), "output": None,
        "output_bytes": len(output.encode("utf-8")), "project_root": str(project),
        "source_sha256": admitted_digest, "timeout_scope": "per_lean_process" if process_timeout_seconds is not None else "request",
        "process_timeout_seconds": process_timeout_seconds, "profile_stage": purpose, "authoritative": False})
    return result


def _cache_evidence(feedback: Feedback, candidate: lean_source.CandidateSnapshot,
                    snapshot: Path, fingerprint: str | None) -> dict[str, Any] | None:
    root = arena.evaluation_cache_root()
    if root is None or fingerprint is None:
        return None
    for mode in ("exact", "quick"):
        key = arena.evaluation_cache_key(feedback.task, feedback.row, candidate.declaration, fingerprint, mode)
        path = arena.evaluation_cache_path(root, mode, key)
        cached = arena.cached_evaluation(path, snapshot)
        if cached is not None and cached.environment_fingerprint == fingerprint:
            return {"status": "cached_valid", "mode": mode, "cache_path": str(path),
                    "source_sha256": _sha(candidate.text.encode("utf-8")), "environment_fingerprint": fingerprint}
    return None


def _validation_binding(feedback: Feedback, raw: bytes, compile_raw: bytes,
                        environment: dict[str, Any]) -> dict[str, Any]:
    """A local compile receipt can never serve as a score or checkpoint.

    Like the existing evaluator cache, identities assume the pinned cached
    dependency artifacts are immutable; the launch guard is not an olean audit.
    """
    executable = Path(environment["lean_executable"]).resolve()
    try:
        stat = executable.stat()
        compiler_file = {"path": str(executable), "size": stat.st_size,
                         "mtime_ns": stat.st_mtime_ns, "inode": stat.st_ino}
    except OSError:
        compiler_file = {"path": str(executable), "unavailable": True}
    return {"schema_version": 1, "source_sha256": _sha(raw), "compile_source_sha256": _sha(compile_raw),
            "task_sha256": arena.sha256_file(feedback.task), "scoring_policy": feedback.scoring_policy,
            "project_root": str(feedback.project),
            "environment": {key: environment.get(key) for key in (
                "fingerprint", "launch_guard_sha256", "prefix_sha256", "lean_githash", "lean_toolchain")},
            "compiler_file": compiler_file}


def _local_validation_path(directory: Path, binding: dict[str, Any]) -> Path:
    key = _sha(json.dumps(binding, sort_keys=True, separators=(",", ":")).encode())
    return directory.parent / f"validation-{key}.json"


def _local_validation_evidence(path: Path, binding: dict[str, Any]) -> dict[str, Any] | None:
    if path.is_symlink() or binding["compiler_file"].get("unavailable"):
        return None
    try:
        receipt = json.loads(path.read_text(encoding="utf-8"))
        source = Path(receipt["compile_source_path"])
        if (receipt["binding"] != binding or receipt["returncode"] != 0
                or receipt["timed_out"] is not False or not source.is_file()
                or source.is_symlink() or source.resolve().parent.parent != path.parent.resolve()
                or _sha(source.read_bytes()) != binding["compile_source_sha256"]):
            return None
    except (OSError, ValueError, KeyError, TypeError):
        return None
    return {"status": "cached_profile_validation", "receipt_path": str(path), "binding": binding,
            "authoritative": False, "scope": "uninstrumented compilation only; no score or axiom audit",
            "environment_assumption": "pinned cached compiler/dependency artifacts remain immutable; no dependency-content audit"}


@contextlib.contextmanager
def _stage(full: dict[str, Any], name: str):
    started = time.perf_counter()
    full["active_stage"] = name
    try:
        yield
    finally:
        full.setdefault("stage_wall_seconds", {})[name] = time.perf_counter() - started


def _compiler_identity(launch: lean_launch.LaunchEnvironment) -> dict[str, Any]:
    """Read the cached compiler's recorded commit without launching a process."""
    header = Path(launch.executable).resolve().parent.parent / "lib" / "lean" / "Init.olean"
    with header.open("rb") as stream:
        prefix = stream.read(96)
    commits = re.findall(rb"[0-9a-f]{40}", prefix)
    if not prefix.startswith(b"olean") or len(commits) != 1:
        raise ValueError("cached Lean compiler identity is unavailable")
    return {"lean_toolchain": launch.provenance.get("toolchain"), "lean_githash": commits[0].decode("ascii")}


def _diagnostics(output: str) -> list[dict[str, Any]]:
    errors = []
    for line in output.splitlines():
        try:
            value = json.loads(line)
        except ValueError:
            continue
        if isinstance(value, dict) and value.get("severity") in {"error", "warning"}:
            errors.append({"severity": value["severity"], "message": str(value.get("data", ""))[:1200],
                           "generated_position": value.get("pos")})
    return errors[:5]


def _span(raw: bytes, start: int, end: int) -> dict[str, Any]:
    before, fragment = raw[:start].decode("utf-8"), raw[start:end].decode("utf-8")
    last = before + fragment
    return {"start_byte": start, "end_byte": end, "start_line": before.count("\n") + 1,
            "start_column": len(before.rsplit("\n", 1)[-1]),
            "end_line": last.count("\n") + 1, "end_column": len(last.rsplit("\n", 1)[-1]),
            "byte_convention": "half-open UTF-8", "line_convention": "1-based lines, 0-based Unicode code-point columns",
            "text": fragment[:400], "text_truncated": len(fragment) > 400,
            "text_sha256": _sha(raw[start:end]), "mapping_confidence": "exact_original_parsed_syntax"}


def _region_menu(output: str, token: str, offset: int, original: bytes,
                 instrumented: bytes) -> dict[str, Any] | None:
    """Accept only bounded native parser positions mapped to the frozen bytes."""
    entries: dict[tuple[int, int], bool] = {}
    state = None
    for line in output.splitlines():
        try:
            fields = str(json.loads(line).get("data", "")).split()
        except (ValueError, AttributeError):
            continue
        if len(fields) == 5 and fields[:2] == [token, "MENU"]:
            a, b, sequence = map(int, fields[2:])
            start, end = a - offset, b - offset
            if (len(entries) >= MAX_MENU_REGIONS or (start, end) in entries or sequence not in (0, 1)
                    or not 0 <= start < end <= len(original)
                    or original[start:end] != instrumented[a:b]):
                raise ValueError("invalid or ambiguous parsed region menu mapping")
            # Reject a generated byte range splitting a Unicode character too.
            original[:start].decode("utf-8")
            original[start:end].decode("utf-8")
            entries[start, end] = bool(sequence)
        elif len(fields) == 4 and fields[:2] == [token, "MENU_STATE"]:
            if state is not None or fields[2] not in ("true", "false") or fields[3] not in ("0", "1", "2"):
                raise ValueError("invalid or ambiguous parsed region menu state")
            state = (fields[2] == "true", int(fields[3]))
    if state is None:
        return None
    choices = []
    for index, ((start, end), sequence) in enumerate(sorted(entries.items()), 1):
        label = f"region_{index}"
        choices.append({"id": label, "kind": "tactic_sequence" if sequence else "tactic",
            "original_span": _span(original, start, end),
            "selector": {"id": label, "start_byte": start, "end_byte": end}})
    return {"source_sha256": _sha(original), "regions": choices, "truncated": state[0],
            "max_regions": MAX_MENU_REGIONS,
            "outermost_sequence_count": state[1], "outermost_sequence_count_capped_at": 2,
            "selection_hint": ("Copy up to 8 selectors into regions with the same expected_sha256; choose distinct disjoint or nested regions. A partial tactic or arbitrary multi-tactic substring is unsupported. Menu membership describes parsed syntax, not a completed measurement."
                if choices else "No supported parsed tactic region exists in this proof. Use mode=wall_time for aggregate native costs, or ordinary uninstrumented scoring.")}


def _region_results(output: str, token: str, regions: list[dict[str, Any]], offset: int,
                    original: bytes, instrumented: bytes) -> dict[str, Any]:
    matches, events, command = {}, {}, None
    for line in output.splitlines():
        try:
            message = str(json.loads(line).get("data", ""))
        except (ValueError, AttributeError):
            continue
        fields = message.split()
        if len(fields) == 5 and fields[0] == token and fields[1] == "MATCH":
            index, a, b = map(int, fields[2:])
            if not 0 <= index < len(regions) or index in matches:
                raise ValueError("ambiguous region syntax mapping")
            start, end = a - offset, b - offset
            if not 0 <= start < end <= len(original) or original[start:end] != instrumented[a:b]:
                raise ValueError("profile syntax does not map byte-for-byte to frozen original")
            matches[index] = (start, end)
        elif len(fields) == 5 and fields[0] == token and fields[1] == "REGION":
            label = fields[2]
            if label not in {item["id"] for item in regions}:
                raise ValueError("unknown region measurement")
            observation = (int(fields[3]), int(fields[4]))
            if min(observation) < 0:
                raise ValueError("negative region measurement")
            events.setdefault(label, []).append(observation)
        elif len(fields) == 4 and fields[0] == token and fields[1] == "COMMAND":
            if command is not None:
                raise ValueError("ambiguous command measurement")
            command = (int(fields[2]), int(fields[3]))
            if min(command) < 0:
                raise ValueError("negative command measurement")
    measured = []
    for index, item in enumerate(regions):
        if index not in matches:
            continue
        start, end = matches[index]
        parents = [(other_end - other_start, regions[other]["id"]) for other, (other_start, other_end) in matches.items()
                   if other != index and other_start <= start and end <= other_end]
        parent_id = min(parents)[1] if parents else "declaration_command"
        calls = events.get(item["id"], [])
        measured.append({"id": item["id"], "parent_id": parent_id, "inclusive": True,
            "original_span": _span(original, start, end), "instrumented_span": {"start_byte": start + offset, "end_byte": end + offset},
            "raw_heartbeats": sum(call[0] for call in calls) if calls else None,
            "user_heartbeat_equivalent": sum(call[0] for call in calls) / 1000 if calls else None,
            "elapsed_nanoseconds": sum(call[1] for call in calls) if calls else None,
            "observations": len(calls), "observed_completed_invocations": len(calls),
            "observed_raw_heartbeats": _observed_summary([call[0] for call in calls]),
            "observed_elapsed_nanoseconds": _observed_summary([call[1] for call in calls]),
            "outcome": "measured" if calls else "not_completed"})
    missing = [item["id"] for index, item in enumerate(regions) if not events.get(item["id"]) or index not in matches]
    repeated = [item["id"] for item in measured if item["observations"] > 1]
    complete = command is not None and not missing and not repeated
    remainder = None
    mismatches = []
    if complete:
        roots = [item for item in measured if item["parent_id"] == "declaration_command"]
        remainder = {"raw_heartbeats": command[0] - sum(item["raw_heartbeats"] for item in roots),
                     "elapsed_nanoseconds": command[1] - sum(item["elapsed_nanoseconds"] for item in roots),
                     "includes": "unselected elaboration, declaration/kernel work, wrapper and child-recording overhead"}
        for parent in [{"id": "declaration_command", "raw_heartbeats": command[0], "elapsed_nanoseconds": command[1]}, *measured]:
            children = [item for item in measured if item["parent_id"] == parent["id"]]
            for unit in ("raw_heartbeats", "elapsed_nanoseconds"):
                children_total = sum(item[unit] for item in children)
                if parent[unit] < children_total:
                    mismatches.append({"parent_id": parent["id"], "unit": unit,
                        "parent_measurement": parent[unit], "direct_children_total": children_total,
                        "child_ids": [item["id"] for item in children]})
        if mismatches:
            complete = False
            remainder = None
            for item in measured:
                if any(mismatch["parent_id"] == item["id"] for mismatch in mismatches):
                    item["inclusive"] = False
    outcome = ("repeated_region_events" if repeated else "missing_region_events" if missing
               else "missing_command_event" if command is None
               else "containment_mismatch" if mismatches else "complete")
    return {"regions": measured, "complete": complete, "accounting_complete": complete,
            "measurement_outcome": outcome, "missing_regions": missing, "repeated_regions": repeated,
            "containment_mismatches": mismatches,
            "observation_semantics": "Observed surviving successful wrapper completions only; failed attempts emit no completion and backtracking may discard messages. Counts do not establish all attempted invocations. Parent IDs describe syntax containment, not a dynamic invocation tree.",
            "accounting_scope": "Singleton observed source regions with validated syntactic containment; no claim of attempted-invocation completeness.",
            "declaration_command": {"id": "declaration_command", "inclusive": complete,
                "scope": "synchronous instrumented command elaborator call",
                "raw_heartbeats": command[0], "elapsed_nanoseconds": command[1]} if command else None,
            "unattributed": remainder,
            "useful_region_observations": [item["id"] for item in measured if item["observations"] > 0],
            "instrumentation_overhead": {"status": "not_separately_measured", "included_in": "parent counts and unattributed remainder"}}


def _observed_summary(values: list[int]) -> dict[str, int | None]:
    return {"total": sum(values) if values else None,
            "min": min(values) if values else None, "max": max(values) if values else None}


def _native_instrument(prefix: str, declaration: str, profile_path: Path) -> tuple[str, list[str]]:
    """Enable native trace creation on the candidate; export remains global.

    The exporter still emits a synthetic runFrontend span, so its unattributed
    remainder can include imports/prefix work. Explicit trace settings in the
    immutable prefix are preserved, rather than silently rewriting that source.
    """
    source = (prefix + "\nset_option Elab.async false in\n"
              + "set_option trace.profiler true in\n" + declaration.rstrip() + "\n")
    arguments = ["-Dtrace.profiler.threshold=0", "-Dtrace.profiler.useHeartbeats=false",
                 "-Dtrace.profiler.output=" + str(profile_path)]
    return source, arguments


def _wall_time(path: Path, top_n: int) -> dict[str, Any]:
    return native_wall_time.summarize(path, top_n, max_profile_bytes=MAX_PROFILE_BYTES, max_samples=MAX_SAMPLES)


@bind_feedback_scoring_policy
def profile_proof(feedback: Feedback, request: dict[str, Any]) -> dict[str, Any]:
    """Synchronous tool entry point. No candidate, score, or broker mutation."""
    started = time.perf_counter()
    mode, timeout, top_n = _request(request)
    if feedback.settings.get("regional_profiler") is not True:
        raise arena.WorkflowError("regional_profiler is disabled for this capsule")
    process_timeout = min(timeout, feedback.timeout)
    setup_deadline = started + process_timeout
    # Each compiler gets its own allowance. Queueing never consumes either
    # process budget, and there is no validation/profile retry inside a call.
    budgets = _budgets(process_timeout, min(DEFAULT_TIMEOUT_SECONDS, feedback.timeout), mode)
    deadline = started + budgets["pre_parse_stage_seconds"]
    full: dict[str, Any] = {"runs": [], "requested_regions": [], "stage_wall_seconds": {},
        "admission": {"budget_seconds": QUEUE_TIMEOUT_SECONDS, "wait_seconds": 0.0, "stage_wait_seconds": {}}}
    try:
        with _stage(full, "source_freeze"):
            raw, source, selected_path, source_kind = _freeze(feedback, request, setup_deadline)
    except (TimeoutError, arena.CacheLockTimeout) as error:
        # A lock timeout does not grant permission to read the source without
        # its lock. Publish the expected identity only, never a fake snapshot.
        directory = _artifact_directory(feedback.root)
        result = {"schema_version": 1, "status": "timeout", "outcome": "source_freeze_timeout",
            "authoritative": False, "measurement_mode": "profile", "mode": mode,
            "source_sha256": None, "selected_source_sha256": None, "snapshot_path": None,
            "expected_source_sha256": request["expected_sha256"], "instrumented_sha256": None,
            "source_kind": "checkpoint" if "checkpoint_id" in request else "current",
            "checkpoint": None, "valid": None, "note": NOTE, "truncated": False,
            "details_path": str(directory / "details.json"), "timeout_seconds": process_timeout,
            "budgets": budgets, "timeout_stage": "source_lock", "error": str(error),
            "capability": profiler_capability(feedback.row, feedback.project),
            "instrumentation_revision": INSTRUMENTATION_REVISION}
        return _finish(result, full, directory, started)
    candidate = lean_source.snapshot_candidate(feedback.row, source, selected_path)
    prefix = lean_source.exact_source_prefix(feedback.row, feedback.project)
    regions = _selections(request, source, candidate) if mode == "regions" else []
    directory = _artifact_directory(feedback.root)
    snapshot = directory / "Source.lean"
    _publish(snapshot, raw)
    result: dict[str, Any] = {"schema_version": 1, "status": "unavailable", "outcome": "unavailable",
        "authoritative": False, "measurement_mode": "profile", "mode": mode,
        "source_sha256": _sha(raw), "instrumented_sha256": None,
        "source_kind": source_kind, "selected_source_path": str(selected_path),
        "selected_source_sha256": _sha(raw), "snapshot_path": str(snapshot),
        "checkpoint": None, "valid": None, "note": NOTE, "truncated": False,
        "details_path": str(directory / "details.json"), "timeout_seconds": process_timeout,
        "budgets": budgets,
        "units": {"heartbeats": "raw allocation heartbeats (1000 raw = 1 user-facing heartbeat)",
                  "elapsed": "monotonic nanoseconds", "native_wall_time": "milliseconds"}}
    full["requested_regions"] = regions
    result["capability"] = profiler_capability(feedback.row, feedback.project)
    result["instrumentation_revision"] = INSTRUMENTATION_REVISION
    try:
        with _stage(full, "launch_preparation"):
            launch = _prepare_launch(feedback.project, setup_deadline)
        fingerprint, fingerprint_note = None, None
        registry = feedback.settings.get("fingerprint_registry")
        if registry:
            fingerprint = arena.measurement_environment_fingerprint(feedback.row, feedback.project, registry_path=Path(registry))
        else:
            fingerprint_note = "no official fingerprint registry; advisory reuse assumes pinned cached dependencies are immutable; launch guard and prefix identities are not a dependency-content audit"
        result["environment"] = {"project_root": str(feedback.project), "fingerprint": fingerprint,
            "launch_guard_sha256": launch.provenance.get("guard_hash"), "prefix_sha256": prefix.sha256,
            "prefix_kind": prefix.kind, "lean_toolchain": launch.provenance.get("toolchain"),
            "lean_executable": launch.executable, "launch_cache_status": launch.provenance.get("status"),
            "note": fingerprint_note}
        result["environment"].update(_compiler_identity(launch))
        compile_source = lean_source.quick_compile_harness(feedback.row, candidate.declaration, feedback.project)
        original_compile = directory / "Uninstrumented.lean"
        _publish(original_compile, compile_source.encode("utf-8"))
        result["uninstrumented_compile_source_sha256"] = _sha(compile_source.encode("utf-8"))
        binding = _validation_binding(feedback, raw, compile_source.encode("utf-8"), result["environment"])
        validation_path = _local_validation_path(directory, binding)
        evidence = (_cache_evidence(feedback, candidate, snapshot, fingerprint)
                    or _local_validation_evidence(validation_path, binding))
        _remaining(setup_deadline)
        if evidence is None:
            with _stage(full, "source_validation"):
                checked = _run(original_compile, feedback.project, launch, deadline,
                    expected_sha256=result["uninstrumented_compile_source_sha256"],
                    process_timeout_seconds=process_timeout, admission=full["admission"], purpose="original_compile")
            full["runs"].append({"purpose": "original_compile", **asdict(checked)})
            if original_compile.read_bytes() != compile_source.encode("utf-8"):
                raise ValueError("private original compilation source changed during checking")
            if checked.timed_out:
                result.update(status="timeout", outcome="source_compile_timeout")
                return _finish(result, full, directory, started)
            if checked.returncode:
                result.update(status="invalid", outcome="source_invalid", valid=False,
                              diagnostics=_diagnostics(checked.output), error="Uninstrumented source did not compile; profile not run")
                return _finish(result, full, directory, started)
            evidence = {"status": "compiled", "source_sha256": _sha(raw),
                        "compile_source_sha256": result["uninstrumented_compile_source_sha256"],
                        "binding": binding, "receipt_path": str(validation_path)}
            if not validation_path.exists() and not binding["compiler_file"].get("unavailable"):
                try:
                    _publish(validation_path, (json.dumps({"binding": binding, "returncode": 0,
                        "timed_out": False, "compile_source_path": str(original_compile)}, sort_keys=True) + "\n").encode())
                except FileExistsError:
                    pass
        result["source_validation"] = evidence
        result["valid"] = True
        token = uuid.uuid4().hex
        if mode == "regions":
            instrumented, offset = _instrument(prefix.text, candidate.declaration, candidate, regions, token)
            args = []
        else:
            # Native tracing needs no helper import. Keep `module` first and
            # preserve any scoped command at the end of the exact prefix.
            profile_path = directory / "native-wall-time.json"
            instrumented, args = _native_instrument(prefix.text, candidate.declaration, profile_path)
            result["native_trace_configuration"] = {"trace_profiler_scope": "candidate_declaration",
                "candidate_async": False, "threshold": 0, "use_heartbeats": False,
                "note": "Profiling is enabled by a scoped candidate option. Explicit options in the immutable prefix are preserved. The synthetic runFrontend span and its unattributed remainder still include imports/prefix work; totals are not proof-only elapsed time."}
        instrumented_path = directory / "Instrumented.lean"
        instrumented_raw = instrumented.encode("utf-8")
        _publish(instrumented_path, instrumented_raw)
        result.update(instrumented_sha256=_sha(instrumented_raw), instrumented_path=str(instrumented_path))
        with _stage(full, "profile"):
            measured = _run(instrumented_path, feedback.project, launch, deadline, args,
                expected_sha256=result["instrumented_sha256"], process_timeout_seconds=process_timeout,
                admission=full["admission"], purpose="profile")
        full["runs"].append({"purpose": "profile", **asdict(measured)})
        if instrumented_path.read_bytes() != instrumented_raw or snapshot.read_bytes() != raw:
            raise ValueError("private profile source changed during measurement")
        result["diagnostics"] = _diagnostics(measured.output)
        menu = None
        if mode == "regions":
            menu = _region_menu(measured.output, token, offset, raw, instrumented_raw)
            if menu is not None:
                full["region_menu"] = menu
            if regions[0].get("automatic"):
                result["selection_strategy"] = "unique_outermost_parsed_tactic_sequence"
            result.update(_region_results(measured.output, token, regions, offset, raw, instrumented_raw))
        elif profile_path.is_file() and not measured.timed_out:
            with _stage(full, "native_parse"):
                result.update(_wall_time(profile_path, top_n))
            result["native_profile_path"] = str(profile_path)
        if measured.timed_out:
            result.update(status="timeout", outcome="profile_timeout")
        elif measured.returncode:
            ambiguous = mode == "regions" and f"{token} AMBIGUOUS_REGION:" in measured.output
            unsupported = (mode == "regions" and f"{token} UNSUPPORTED_REGION:" in measured.output) or ambiguous
            if unsupported and menu is not None:
                result["region_menu"] = menu
            selection_error = ("Region text occurs more than once in the immutable source; use an exact parsed byte span from region_menu"
                if ambiguous else "Selection requires a complete supported parsed tactic/sequence; use a byte span from region_menu")
            if unsupported and menu is not None and not menu["regions"]:
                selection_error = "No supported parsed tactic region exists in this proof; use wall_time mode or ordinary uninstrumented scoring"
            elif unsupported and regions[0].get("automatic") and menu is not None and menu["outermost_sequence_count"] == 2:
                selection_error = "Default profiling found multiple outermost tactic sequences; select an exact byte span from region_menu"
            result.update(status="unsupported" if unsupported else "unavailable",
                          outcome=("ambiguous_region" if ambiguous else "unsupported_region") if unsupported else "instrumented_compile_failed",
                          error=selection_error if unsupported else "Private instrumented copy did not compile")
        elif mode == "regions" and not result.get("complete"):
            result.update(status="partial" if result.get("useful_region_observations") else "unavailable",
                          outcome=result.get("measurement_outcome", "missing_region_events"),
                          profile_note=("Source-bound observations remain useful, including repeated completed invocations. "
                              "Accounting is incomplete and no parent remainder is published; observed completions do not establish all attempted invocations."))
            if not result.get("useful_region_observations"):
                result["error"] = "No completed source-bound region observation was obtained"
        elif mode == "wall_time" and not result.get("complete"):
            result.update(status="unavailable", outcome="native_profile_unavailable_or_truncated",
                          error=result.get("profile_note", "Lean did not produce a supported wall-time profile"))
        else:
            result.update(status="profiled", outcome="complete")
    except (TimeoutError, arena.CacheLockTimeout) as error:
        queued_out = isinstance(error, _AdmissionTimeout)
        result.update(status="timeout", outcome="resource_queue_timeout" if queued_out else "profile_deadline",
            error=str(error), timeout_stage=(full.get("active_stage", "setup") + "_queue"
                if queued_out else full.get("active_stage", "setup")))
    except resource_gate.ResourceGateError as error:
        result.update(status="unavailable", outcome="resource_admission_failed", error=str(error)[:800],
            error_stage=full.get("active_stage"))
    except (OSError, RuntimeError, ValueError, KeyError, TypeError, IndexError) as error:
        result.update(status="unavailable", outcome="profile_unavailable", error=str(error)[:800])
    return _finish(result, full, directory, started)


def _timeout_hint(result: dict[str, Any]) -> str:
    stage = result.get("timeout_stage") or "setup"
    seconds = result["timeout_seconds"]
    maximum = result["budgets"]["maximum_process_seconds"]
    larger = (f" An explicit timeout_seconds={maximum:g} permits a larger process budget."
              if seconds < maximum else " The maximum process budget is already in use.")
    validation = result.get("source_validation", {}).get("status")
    reuse = (" Completed source validation is reusable only for the same source and matching task/environment/compiler binding."
             if result.get("valid") is True else " Incomplete validation is not cached.")
    if stage.endswith("_queue"):
        return (f"Resource admission reached its queue deadline (shared allowance {QUEUE_TIMEOUT_SECONDS} seconds; gate policy may be tighter); "
                "no process is retried automatically. Retry explicitly when capacity is available." + reuse)
    if stage == "source_lock":
        return (f"The selected source lock was not acquired within the {seconds:g}-second setup allowance; "
                "no source snapshot or validity claim was produced. Retry explicitly after the edit lock is released." + larger)
    if stage == "source_validation":
        return (f"Uninstrumented validation exhausted its {seconds:g}-second process budget; profiling did not start."
                + reuse + larger + " Check or score the unchanged source to obtain matching validity evidence before another profile.")
    if stage == "profile":
        return (f"The instrumented profile exhausted its own {seconds:g}-second process budget; "
                f"validation status is {validation or 'unavailable'}." + reuse + larger
                + " An explicit retry keeps that process cap; consider a simpler supported selection or continue with uninstrumented scoring.")
    return (f"Source or cached-launch preparation exhausted its {seconds:g}-second setup allowance."
            + larger + " Inspect the preparation error or retry explicitly after the relevant lock is released.")


def _finish(result: dict[str, Any], full: dict[str, Any], directory: Path, started: float) -> dict[str, Any]:
    result["wall_seconds"] = round(time.perf_counter() - started, 6)
    if result["status"] == "timeout":
        result["complete"] = False
        if result.get("mode") == "regions":
            result["accounting_complete"] = False
            result["unattributed"] = None
            if result.get("measurement_outcome") == "complete":
                result["measurement_outcome"] = "profile_process_incomplete"
            if result.get("declaration_command"):
                result["declaration_command"]["inclusive"] = False
        result.setdefault("timeout_stage", full.get("active_stage"))
        result.setdefault("retry_hint", _timeout_hint(result))
    stages = {name: 0.0 for name in ("launch_preparation", "source_validation", "profile", "native_parse")}
    stages.update(full.get("stage_wall_seconds", {}))
    result["timings"] = {"stage_wall_seconds": {name: round(value, 6) for name, value in stages.items()},
        "other_wall_seconds": round(max(0, result["wall_seconds"] - sum(stages.values())), 6),
        "queue_wait_seconds": round(full["admission"]["wait_seconds"], 6),
        "queue_wait_complete": True,
        "stage_queue_wait_seconds": {purpose: round(full["admission"]["stage_wait_seconds"].get(purpose, 0.0), 6)
            for purpose in ("original_compile", "profile")},
        "source_validation_process_seconds": round(sum(run["seconds"] for run in full["runs"]
            if run["purpose"] == "original_compile"), 6),
        "profile_process_seconds": round(sum(run["seconds"] for run in full["runs"]
            if run["purpose"] == "profile"), 6),
        "native_parse_seconds": round(stages["native_parse"], 6),
        "note": "Stage wall time includes admission; process seconds exclude queue time. Admission waits share a separate 10-second allowance and include failed admission attempts. Validation and profiling have independent process caps. Native parsing is a separately budgeted timed stage. Cleanup and artifact finalization may add wall time outside stage allowances."}
    # Diagnostics are explicitly generated-source positions, never guessed lines.
    (directory / "details.json").write_text(json.dumps({"summary": result, **full}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    arena.record_event(TOOL_NAME, result)
    return result
