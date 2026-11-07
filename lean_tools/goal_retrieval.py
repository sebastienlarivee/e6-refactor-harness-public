"""Deterministic, advisory lemma retrieval from actual prefix-bound Lean goals.

The generated wrapper records tactic info in the original declaration. No import,
proof edit, metavariable assignment, checkpoint or model call is made. Retrieval
uses weighted signature-constant overlap, not type unification or proof search.
"""
from __future__ import annotations

import hashlib
import json
import re
import time
from pathlib import Path
from typing import Any

from lean_tools.feedback_workflow import bind_feedback_scoring_policy
from lean_tools import arena_workflow as arena
from lean_tools import lean_goal_state, lean_source, goal_signature_index as signature_index
from lean_tools import persistent_quick_workflow as persistent

MARKER = "__LRH_GOAL_RETRIEVAL_V1__"
MAX_SYMBOLS = 128
MAX_SIGNATURE = 1800
MAX_LIMIT = 12
MAX_CANDIDATE_LIMIT = 5000
TOOL = {
    "name": "retrieve_lemmas",
    "description": "Rank legal strict-prefix theorem signatures for one actual Lean goal. Requires the current candidate SHA256. Prefer an actual residual goal_id returned by unfinished_cases or failed edit_check; retrieval reuses that full residual context. Legacy cursor/entry handles and omitted selectors use recorded pre-tactic goals, which may already be discharged. Explicit cursors can access the entire declaration. Read-only advisory discovery; limit 1..12. Default pool is weighted overlap; host can freeze diverse or hybrid pool. Per-call pool_mode must match that configuration. Complete types/context are preserved; full diagnostics are in details_path.",
    "inputSchema": {
        "type": "object",
        "properties": {
            "candidate": {"type": "string"},
            "expected_sha256": {"type": "string", "pattern": "^[0-9a-f]{64}$"},
            "goal": {
                "type": "object",
                "properties": {"line": {"type": "integer", "minimum": 1}, "column": {"type": "integer", "minimum": 1}, "index": {"type": "integer", "minimum": 0}},
                "required": ["line"], "additionalProperties": False,
            },
            "goal_id": {"type": "string", "pattern": "^goal-[0-9a-f]{64}$"},
            "limit": {"type": "integer", "minimum": 1, "maximum": MAX_LIMIT},
            "candidate_limit": {"type": "integer", "minimum": 1, "maximum": MAX_CANDIDATE_LIMIT},
            "include_pool": {"type": "boolean"},
            "search_intent": {"type": "string", "maxLength": 16000, "description": "Mathematical operation used by diverse or hybrid pool construction and contextual rerankers. Overlap pool construction ignores this field; baseline reranking preserves the constructed pool order."},
            "same_run_context": {"type": "string", "maxLength": 64000, "description": "Context supplied to the configured reranker; does not expand the candidate pool. Baseline ordering ignores this field."},
            "name_query": {"type": "string", "maxLength": 2000, "description": "Declaration words used by diverse or hybrid pool construction; ignored by the overlap pool."},
            "pool_mode": {"type": "string", "enum": ["overlap", "diverse", "hybrid"], "description": "Omit to use the host-configured pool, or supply the same mode. A different mode is rejected."},
            "full_output": {"type": "boolean"},
        },
        "required": ["expected_sha256"], "additionalProperties": False,
    },
}


def _sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _validate(request: Any) -> tuple[dict[str, Any] | None, int]:
    if not isinstance(request, dict) or set(request) - set(TOOL["inputSchema"]["properties"]):
        raise ValueError("request contains an unsupported retrieval field")
    if not isinstance(request.get("expected_sha256"), str) or not re.fullmatch(r"[0-9a-f]{64}", request["expected_sha256"]):
        raise ValueError("expected_sha256 is required and must be 64 lowercase hexadecimal characters")
    goal = request.get("goal")
    if "goal" in request:
        if not isinstance(goal, dict) or set(goal) - {"line", "column", "index"} or "line" not in goal:
            raise ValueError("goal must contain a one-based line, optional column and zero-based index")
        for key, value in goal.items():
            if type(value) is not int or value < (0 if key == "index" else 1):
                raise ValueError(f"goal {key} must be {'a nonnegative' if key == 'index' else 'a positive'} integer")
    if "goal_id" in request:
        if goal is not None or not isinstance(request["goal_id"], str) or not re.fullmatch(r"goal-[0-9a-f]{64}", request["goal_id"]):
            raise ValueError("goal_id must be a source-bound goal handle; supply either goal_id or goal")
    limit = request.get("limit", 8)
    for key in ("include_pool", "full_output"):
        if key in request and type(request[key]) is not bool:
            raise ValueError(f"{key} must be a boolean")
    if "pool_mode" in request and request["pool_mode"] not in ("overlap", "diverse", "hybrid"):
        raise ValueError("pool_mode must be overlap, diverse or hybrid")
    for key, bound in (("search_intent", 16000), ("same_run_context", 64000), ("name_query", 2000)):
        if key in request and (not isinstance(request[key], str) or len(request[key]) > bound):
            raise ValueError(f"{key} must be text with at most {bound} characters")
    return goal, limit


# Kept inline so generated discovery needs no new imports or compiled helper.
# The helper is an elaborator definition, never a retrievable theorem. Its random-
# looking name is derived from the query, making identical harnesses reproducible.
# Named patterns force local bindings despite constructors in the caller namespace.
_WRAPPER = r'''
elab "__COMMAND__ " cmd:command : command => do
  let elaborationStarted ← IO.monoMsNow
  Lean.Elab.modifyInfoState fun s => { s with enabled := true }
  Lean.Elab.Command.elabCommand cmd
  let elaborationFinished ← IO.monoMsNow
  let rec visit (fuel : Nat) (ctx : Option Lean.Elab.ContextInfo) (tree : Lean.Elab.InfoTree)
      (found : Array (Nat × Nat × Lean.Elab.ContextInfo × Lean.Elab.TacticInfo)) :=
    match fuel with
    | 0 => found
    | Nat.succ fuel@_ =>
      match tree with
      | .context info@_ child@_ => visit fuel (info.mergeIntoOuter? ctx) child found
      | .node info@_ children@_ => Id.run do
        let mut found := found
        if let some ctx@_ := ctx then
          if let .ofTacticInfo tactic@_ := info then
            if let some start@_ := tactic.stx.getPos? then
              if let some finish@_ := tactic.stx.getTailPos? then
                if __DECL_START__ <= start.byteIdx && finish.byteIdx <= __DECL_END__ && (!__AUTO__ || __BODY_START__ <= start.byteIdx) then
                  found := found.push (start.byteIdx, finish.byteIdx, ctx, tactic)
        let ctx := info.updateContext? ctx
        for child@_ in children do
          found := visit fuel ctx child found
        return found
      | .hole _ => found
  let mut found := #[]
  for tree@_ in (← Lean.Elab.getInfoState).trees do
    found := visit 10000 none tree found
  let mut best : Option (Nat × Nat × Lean.Elab.ContextInfo × Lean.Elab.TacticInfo) := none
  for item@_ in found do
    if (if __AUTO__ then !item.2.2.2.goalsBefore.isEmpty else item.1 <= __CURSOR__ && __CURSOR__ < item.2.1) then
      match best with
      | none => best := some item
      | some previous@_ =>
        if (if __AUTO__ then item.1 < previous.1 || (item.1 == previous.1 && item.2.1 - item.1 <= previous.2.1 - previous.1) else item.2.1 - item.1 <= previous.2.1 - previous.1) then best := some item
  let available := (found.filter fun item => !item.2.2.2.goalsBefore.isEmpty).qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 - a.1 < b.2.1 - b.1)
  let suggestions := (available.take 12).map fun item => Lean.Json.mkObj [("tactic_start_byte", Lean.toJson item.1), ("tactic_end_byte", Lean.toJson item.2.1), ("goal_count", Lean.toJson item.2.2.2.goalsBefore.length)]
  let emit (value : Lean.Json) := Lean.logInfo (Lean.toMessageData ("__MARKER__" ++ value.compress))
  match best with
  | none => emit (Lean.Json.mkObj [("status", Lean.toJson "no_goal"), ("suggested_tactics", Lean.toJson suggestions), ("reason", Lean.toJson "no eligible tactic with recorded pre-tactic goals; use a suggested goal cursor or omit the selector to search the editable proof body")])
  | some (start@_, finish@_, ctx@_, tactic@_) =>
    if tactic.goalsBefore.isEmpty then
      emit (Lean.Json.mkObj [("status", Lean.toJson "no_goal"), ("suggested_tactics", Lean.toJson suggestions), ("reason", Lean.toJson "the selected tactic has no goals before execution; use a suggested goal cursor or omit the selector")])
    else if __GOAL_INDEX__ >= tactic.goalsBefore.length then
      emit (Lean.Json.mkObj [("status", Lean.toJson "no_goal"), ("goal_count", Lean.toJson tactic.goalsBefore.length), ("suggested_tactics", Lean.toJson suggestions), ("reason", Lean.toJson "goal index is outside this tactic's goals; use zero-based index 0 or a returned goal handle")])
    else
      let selectedGoals := (tactic.goalsBefore.drop __GOAL_INDEX__).take 1
      let value ← ( { ctx with mctx := tactic.mctxBefore } : Lean.Elab.ContextInfo ).runMetaM {} do
        let mut conclusions : Array Lean.Name := #[]
        let mut hypotheses : Array Lean.Name := #[]
        for goal@_ in selectedGoals do
          let (goalConstants@_, hypConstants@_) ← goal.withContext do
            let goalConstants := (← Lean.instantiateMVars (← goal.getType)).getUsedConstants
            let mut hypConstants : Array Lean.Name := #[]
            for decl@_ in (← Lean.getLCtx) do
              if !decl.isImplementationDetail then
                for name@_ in (← Lean.instantiateMVars decl.type).getUsedConstants do
                  if !hypConstants.contains name then hypConstants := hypConstants.push name
            return (goalConstants, hypConstants)
          for name@_ in goalConstants do
            if !conclusions.contains name then conclusions := conclusions.push name
          for name@_ in hypConstants do
            if !hypotheses.contains name then hypotheses := hypotheses.push name
        conclusions := conclusions.qsort (fun a b => a.toString < b.toString)
        hypotheses := hypotheses.qsort (fun a b => a.toString < b.toString)
        let generic : Array String := #["Eq", "HEq", "Iff", "And", "Or", "Not", "Exists", "True", "False", "Nat", "Int", "Bool", "OfNat.ofNat", "OfNat", "LT.lt", "LE.le", "HAdd.hAdd", "HMul.hMul", "HSub.hSub", "HDiv.hDiv", "Neg.neg", "Membership.mem", "Decidable", "DecidableEq", "instDecidableEqNat"]
        let mut symbols : Array (Lean.Name × Nat × Bool × Bool) := #[]
        for name@_ in conclusions do
          let isGeneric := generic.contains name.toString
          symbols := symbols.push (name, (if isGeneric then 2 else 12) + (if hypotheses.contains name then (if isGeneric then 1 else 3) else 0), true, hypotheses.contains name)
        for name@_ in hypotheses do
          if !conclusions.contains name then
            symbols := symbols.push (name, if generic.contains name.toString then 1 else 3, false, true)
        let symbolCount := symbols.size
        symbols := symbols.take __SYMBOLS__
        let symbolJson := symbols.map fun (name@_, weight@_, conclusion@_, hypothesis@_) => Lean.Json.mkObj [("name", Lean.toJson name.toString), ("weight", Lean.toJson weight), ("conclusion", Lean.toJson conclusion), ("hypothesis", Lean.toJson hypothesis), ("generic", Lean.toJson (generic.contains name.toString))]
        let extracted ← IO.monoMsNow
        return Lean.Json.mkObj [("status", Lean.toJson "ok"), ("goal_count", Lean.toJson tactic.goalsBefore.length), ("selected_goal_index", Lean.toJson __GOAL_INDEX__), ("tactic_start_byte", Lean.toJson start), ("tactic_end_byte", Lean.toJson finish), ("context_symbols", Lean.toJson symbolJson), ("context_symbols_total", Lean.toJson symbolCount), ("context_symbols_truncated", Lean.toJson (decide (symbolCount > __SYMBOLS__))), ("elaboration_ms", Lean.toJson (elaborationFinished - elaborationStarted)), ("extraction_ms", Lean.toJson (extracted - elaborationFinished))]
      emit value
'''

_RENDER = r'''
elab "__COMMAND__" : command => do
  let started ← IO.monoMsNow
  let env ← Lean.getEnv
  let value ← Lean.Elab.Command.liftTermElabM do
    let names : Array String := __NAMES__
    let symbols : Array (String × Nat × Bool × Bool) := __SYMBOL_DATA__
    let mut rendered : Array Lean.Json := #[]
    let mut rejected : Array Lean.Json := #[]
    for name@_ in names do
      let n := name.toName
      let mut reason := if name == __TARGET__ then "excluded_target"
        else if n.isInternal || Lean.isPrivateName n then "internal_or_private"
        else if (env.find? n).isNone then "unavailable"
        else if !Lean.wasOriginallyTheorem env n then "not_theorem"
        else ""
      if reason.isEmpty && (env.getModuleIdxFor? n).isNone then
        if let some ranges@_ ← Lean.findDeclarationRanges? n then
          let fileMap ← Lean.getFileMap
          let selection := (fileMap.source.toRawSubstring.extract
            (fileMap.ofPosition ranges.selectionRange.pos)
            (fileMap.ofPosition ranges.selectionRange.endPos)).toString
          if selection == "instance" then
            reason := "local_anonymous_instance"
      if !reason.isEmpty then
        rejected := rejected.push (Lean.Json.mkObj [("name", Lean.toJson name), ("reason", Lean.toJson reason)])
        continue
      let some info@_ := env.find? n | throwError "validated signature index winner disappeared: {name}"
      let constants := info.type.getUsedConstants |>.map Lean.Name.toString
      let mut score := 0
      let mut matched : Array String := #[]
      let mut conclusionCount := 0
      let mut hypothesisCount := 0
      for (symbol@_, weight@_, conclusion@_, hypothesis@_) in symbols do
        if constants.contains symbol then
          score := score + weight
          matched := matched.push symbol
          if conclusion then conclusionCount := conclusionCount + 1
          if hypothesis then hypothesisCount := hypothesisCount + 1
      let signature := toString (← Lean.Meta.ppExpr info.type)
      let boundedSignature := (signature.toList.take __SIGNATURE__).foldl (fun text char => text.push char) ""
      rendered := rendered.push (Lean.Json.mkObj [("name", Lean.toJson name), ("signature", Lean.toJson boundedSignature), ("signature_truncated", Lean.toJson (decide (signature.length > __SIGNATURE__))), ("score", Lean.toJson score), ("matched_symbols", Lean.toJson (matched.take 32)), ("matched_symbol_counts", Lean.Json.mkObj [("total", Lean.toJson matched.size), ("conclusion", Lean.toJson conclusionCount), ("hypothesis", Lean.toJson hypothesisCount)])])
    return (rendered, rejected)
  let finished ← IO.monoMsNow
  Lean.logInfo (Lean.toMessageData ("__MARKER__" ++ (Lean.Json.mkObj [("status", Lean.toJson "ok"), ("matches", Lean.toJson value.1), ("rejected", Lean.toJson value.2), ("render_ms", Lean.toJson (finished - started))]).compress))
__COMMAND__
'''


def build_render_harness(prefix: str, names: list[str], symbols: list[dict[str, Any]], target: str, *, complete_signatures: bool = False) -> str:
    strings = lambda values: "#[" + ",".join(json.dumps(value, ensure_ascii=False) for value in values) + "]"
    data = "#[" + ",".join("(" + json.dumps(s["name"], ensure_ascii=False) + f",{s['weight']},{str(s['conclusion']).lower()},{str(s['hypothesis']).lower()})" for s in symbols) + "]"
    command = "lrhRenderSignatures" + _sha(prefix + json.dumps([names, symbols], sort_keys=True))[:16]
    template = _RENDER
    if complete_signatures:
        template = template.replace('let signature := toString (← Lean.Meta.ppExpr info.type)', 'let signature ← Lean.withOptions (fun opts => Lean.Option.set ((opts.setBool `pp.deepTerms true).setBool `pp.proofs true) Lean.pp.maxSteps 1000000000) do\n        pure (toString (← Lean.Meta.ppExpr info.type))')
        template = template.replace('(signature.toList.take __SIGNATURE__).foldl (fun text char => text.push char) ""', "signature").replace("Lean.toJson (decide (signature.length > __SIGNATURE__))", "Lean.toJson (signature.contains '⋯')")
    return prefix + template.replace("__COMMAND__", command).replace("__NAMES__", strings(names)).replace("__SYMBOL_DATA__", data).replace("__TARGET__", json.dumps(target, ensure_ascii=False)).replace("__SIGNATURE__", str(MAX_SIGNATURE)).replace("__MARKER__", MARKER)


def build_harness(prefix: str, declaration: str, offset: int | None, limit: int, target_name: str = "", *, include_rerank_context: bool = False, goal_index: int = 0, proof_body_offset: int | None = None) -> tuple[str, int]:
    """Wrap one original command; Lean syntax ranges select the exact tactic."""
    if offset is None and proof_body_offset is None:
        raise ValueError("automatic goal selection requires the validated proof-body offset")
    if proof_body_offset is not None and (type(proof_body_offset) is not int or not 0 <= proof_body_offset < len(declaration)):
        raise ValueError("proof-body offset must be inside the target declaration")
    command = "lrhRetrieve" + _sha(prefix + declaration + str(offset) + str(limit))[:16]
    helper = _WRAPPER.replace("__COMMAND__", command).replace("__MARKER__", MARKER).replace("__HELPER_ID__", command[-16:]).replace("__AUTO__", str(offset is None).lower()).replace("__GOAL_INDEX__", str(goal_index))
    if include_rerank_context:
        rendered_context = r'''
        let renderComplete (expr : Lean.Expr) : Lean.MetaM String := do
          Lean.withOptions (fun opts => Lean.Option.set ((opts.setBool `pp.deepTerms true).setBool `pp.proofs true) Lean.pp.maxSteps 1000000000) do
            pure (toString (← Lean.Meta.ppExpr (← Lean.instantiateMVars expr)))
        let mut goalTexts : Array String := #[]
        let mut hypothesisTexts : Array String := #[]
        let mut hypothesisGroups : Array (Array String) := #[]
        for goal@_ in selectedGoals do
          let (goalText@_, hypTexts@_) ← goal.withContext do
            let goalText ← renderComplete (← goal.getType)
            let mut hypTexts : Array String := #[]
            for decl@_ in (← Lean.getLCtx) do
              if !decl.isImplementationDetail then
                let hypType ← renderComplete decl.type
                let valueText ← match decl.value? (allowNondep := true) with
                  | none => pure ""
                  | some value@_ => do pure (" := " ++ (← renderComplete value))
                hypTexts := hypTexts.push s!"{decl.userName} : {hypType}{valueText}"
            return (goalText, hypTexts)
          goalTexts := goalTexts.push goalText
          hypothesisGroups := hypothesisGroups.push hypTexts
          for text@_ in hypTexts do
            if !hypothesisTexts.contains text then
              hypothesisTexts := hypothesisTexts.push text
'''
        helper = helper.replace("        let extracted ← IO.monoMsNow", rendered_context + "        let extracted ← IO.monoMsNow")
        helper = helper.replace('[("status", Lean.toJson "ok"), ("goal_count",', '[("rendered_goals", Lean.toJson goalTexts), ("rendered_hypotheses", Lean.toJson hypothesisTexts), ("rendered_hypotheses_by_goal", Lean.toJson hypothesisGroups), ("status", Lean.toJson "ok"), ("goal_count",')
    helper = helper.replace("__LIMIT__", str(limit)).replace("__SYMBOLS__", str(MAX_SYMBOLS)).replace("__SIGNATURE__", str(MAX_SIGNATURE))
    helper = helper.replace("__TARGET__", json.dumps(target_name, ensure_ascii=False))
    suffix = "\nset_option Elab.async false in\n" + command + " "
    # Cursor substitution has fixed width, so UTF8 source offsets remain exact.
    helper_width = 12
    placeholder = helper.replace("__CURSOR__", "0" * helper_width).replace("__DECL_START__", "0" * helper_width).replace("__DECL_END__", "0" * helper_width).replace("__BODY_START__", "0" * helper_width)
    lead = prefix + placeholder + suffix
    declaration_start = len(lead.encode("utf-8"))
    declaration_end = declaration_start + len(declaration.encode("utf-8"))
    body_start = declaration_start + len(declaration[:proof_body_offset or 0].encode("utf-8"))
    cursor = declaration_start + len(declaration[:offset or 0].encode("utf-8"))
    if max(cursor, declaration_end, body_start) >= 10 ** helper_width:
        raise ValueError("generated source is too large for cursor binding")
    source = prefix + helper.replace("__CURSOR__", f"{cursor:0{helper_width}d}").replace("__DECL_START__", f"{declaration_start:0{helper_width}d}").replace("__DECL_END__", f"{declaration_end:0{helper_width}d}").replace("__BODY_START__", f"{body_start:0{helper_width}d}") + suffix + declaration + "\n"
    return source, len(lead.encode("utf-8"))


def _parse(diagnostics: list[dict[str, Any]], marker: str = MARKER) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    records, errors = [], []
    for item in diagnostics:
        message = item.get("message", item.get("data", ""))
        if isinstance(message, str) and message.startswith(marker):
            try:
                value = json.loads(message[len(marker):])
            except ValueError:
                errors.append({"code": "malformed_discovery_payload", "message": message})
            else:
                if isinstance(value, dict):
                    records.append(value)
        elif item.get("severity") in {"error", "warning", 1, 2}:
            # Preserve source locations for helper/candidate classification, but
            # avoid retaining a second unbounded copy of the diagnostic text.
            errors.append({**{key: value for key, value in item.items() if key not in {"data", "message"}},
                           "code": "lean_diagnostic", "message": str(message)})
    return records, errors


def run_harness(source: str, project: Path, timeout: int, *, marker: str = MARKER, force_cold: bool = False) -> dict[str, Any]:
    """Reuse the resident session when configured, otherwise the gated cold lane."""
    if not force_cold and arena.persistent_quick_matches_project(project):
        response = persistent.feedback_request(source, timeout, operation="validate")
        records, diagnostics = _parse(response["diagnostics"], marker)
        return {"records": records, "diagnostics": diagnostics, "backend": "resident", "document_version": response["document_version"], "seconds": response.get("wall_seconds"), "queue_wait_seconds": response.get("queue_wait_seconds")}
    with arena.temporary_evaluation_directory("lrh-goal-retrieval-") as temporary:
        scratch = Path(temporary)
        path = scratch / "Retrieval.lean"
        path.write_bytes(source.encode("utf-8"))
        run = arena.run_lean(path, project, timeout, lean_args=["--json", "-R", str(scratch)])
    raw = []
    for line in run.output.splitlines():
        try:
            item = json.loads(line)
        except ValueError:
            if line.strip():
                raw.append({"severity": "error", "message": line})
        else:
            if isinstance(item, dict):
                raw.append(item)
    records, diagnostics = _parse(raw, marker)
    if run.timed_out:
        diagnostics.append({"code": "discovery_timeout", "message": f"Lean discovery exceeded {timeout} seconds"})
    return {"records": records, "diagnostics": diagnostics, "backend": "cold", "seconds": round(run.seconds, 6), "timed_out": run.timed_out, "queue_wait_seconds": run.queue_wait_seconds}


def _run_index(source: str, project: Path, timeout: int) -> dict[str, Any]:
    return run_harness(source, project, timeout, marker=signature_index.INDEX_MARKER, force_cold=True)


def prepare_index(row: dict[str, Any], project: Path, cache_root: Path, *, fingerprint_registry: Path | None = None) -> dict[str, Any]:
    """Prepare an immutable host artifact before inference, for read-only mounting."""
    prefix = lean_source.exact_source_prefix(row, project)
    fingerprint = arena.measurement_environment_fingerprint(row, project, registry_path=fingerprint_registry)
    material = signature_index.identity(prefix.sha256, fingerprint, row["name"])
    path, build = signature_index.ensure_index(cache_root, prefix.text, material, project, _run_index)
    return {"schema_version": 1, "key": build["key"], "path": str(path),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "identity": material, "build": build}


def validate_prepared_index(artifact: dict[str, Any], row: dict[str, Any], project: Path, *, fingerprint_registry: Path | None = None) -> Path:
    """Validate the host artifact and current prefix without building or elaboration."""
    prefix = lean_source.exact_source_prefix(row, project)
    fingerprint = arena.measurement_environment_fingerprint(row, project, registry_path=fingerprint_registry)
    material = signature_index.identity(prefix.sha256, fingerprint, row["name"])
    path = Path(artifact["path"])
    if artifact.get("schema_version") != 1 or artifact.get("identity") != material or artifact.get("key") != signature_index.key_for(material):
        raise signature_index.IndexUnavailable("prepared retrieval index identity does not match this exact prefix and environment")
    if hashlib.sha256(path.read_bytes()).hexdigest() != artifact.get("sha256") or not signature_index._valid(path, material):
        raise signature_index.IndexUnavailable("prepared retrieval index SHA256 or database metadata mismatch")
    return path


def _query_index(feedback: Any, prefix: lean_source.SourcePrefix, fingerprint: str) -> tuple[Path, dict[str, Any]]:
    material = signature_index.identity(prefix.sha256, fingerprint, feedback.row["name"])
    supplied = feedback.settings.get("retrieval_index")
    if supplied:
        path = Path(supplied)
        expected = feedback.settings.get("retrieval_index_sha256")
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise signature_index.IndexUnavailable("prepared retrieval index requires a SHA256 digest")
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected or not signature_index._valid(path, material):
            raise signature_index.IndexUnavailable("prepared retrieval index identity or SHA256 mismatch; rebuild on the host")
        return path, {"key": signature_index.key_for(material), "cache_hit": True, "prepared": True}
    return signature_index.ensure_index(signature_index.cache_root(feedback.settings, feedback.project), prefix.text, material, feedback.project, _run_index)


def _finish(feedback: Any, request: dict[str, Any], result: dict[str, Any]) -> dict[str, Any]:
    """Keep full evidence locally, present one context and bounded diagnostics."""
    full = dict(result)
    diagnostics = result.get("diagnostics", [])
    unique: list[dict[str, Any]] = []
    seen = set()
    for item in diagnostics:
        identity = (item.get("code"), item.get("message"))
        if identity not in seen:
            seen.add(identity)
            unique.append(item)
    compact = [{**item, "message": str(item.get("message", ""))[:600],
                **({"message_truncated": True} if len(str(item.get("message", ""))) > 600 else {})}
               for item in unique[:3]]
    if not request.get("full_output", False):
        result["diagnostics"] = compact
        result["diagnostics_omitted"] = len(diagnostics) - len(compact)
        for key in ("rendered_goals", "rendered_hypotheses", "rendered_hypotheses_by_goal"):
            result.pop(key, None)
    candidate = result.get("candidate")
    root = getattr(feedback, "root", Path(candidate).parent if candidate else None)
    if root is not None:
        try:
            path = Path(root) / ".feedback" / "retrieval" / f"{time.time_ns()}-{result.get('source_sha256', 'unknown')[:12]}.json"
            path.parent.mkdir(parents=True, exist_ok=True)
            result["details_path"] = str(path)
            path.write_text(json.dumps({"summary": result, "full": full}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        except OSError as error:
            result["details_error"] = str(error)[:300]
    return result


def _selected_context(record: dict[str, Any], goal_index: int) -> dict[str, Any]:
    goals = record.get("rendered_goals")
    hypotheses = record.get("rendered_hypotheses")
    if not isinstance(goals, list) or not goals or any(not isinstance(value, str) for value in goals):
        raise signature_index.IndexUnavailable("retrieval requires the complete actual selected goal context")
    groups = record.get("rendered_hypotheses_by_goal")
    if groups is None and len(goals) == 1 and isinstance(hypotheses, list):
        groups = [hypotheses]
    if not isinstance(groups, list) or len(groups) != len(goals) or any(not isinstance(group, list) or any(not isinstance(value, str) for value in group) for group in groups):
        raise signature_index.IndexUnavailable("retrieval requires hypotheses bound to each actual goal")
    # New harnesses render only the selected goal. Accept old multi-goal records
    # in offline fixtures, selecting the requested index without merging context.
    ordinal = 0 if "selected_goal_index" in record else goal_index
    if not 0 <= ordinal < len(goals) or ("selected_goal_index" in record and record["selected_goal_index"] != goal_index):
        raise signature_index.IndexUnavailable("selected goal index does not match the elaborated context")
    target, group = goals[ordinal], groups[ordinal]
    if any("⋯" in value for value in [target, *group]):
        raise signature_index.IndexUnavailable("retrieval cannot use elided goal or hypothesis text")
    return {"goal_index": goal_index, "target": target, "hypotheses": group}


def _validated_index_render(ranked: list[dict[str, Any]], rendered: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Recover only an independently verified subsequence of the bounded pool.

    Module-dependent anonymous declaration names may exist in the cold index but
    not in the resident prefix. Local anonymous instances are also excluded by
    their source selection range, even when their synthetic name resolves here.
    Never alias those names or expand the pool. Every requested name is accounted
    for exactly once,
    and each retained signature must reproduce its indexed overlap score/order.
    Older render payloads without rejection records retain the all-or-nothing
    contract. Malformed payloads and score mismatches still fail closed.
    """
    records = rendered.get("records", [])
    if not isinstance(records, list) or len(records) != 1 or not isinstance(records[0], dict) or records[0].get("status") != "ok":
        raise signature_index.IndexUnavailable("exact-prefix signature renderer did not emit one successful validation record")
    matches, rejected = records[0].get("matches"), records[0].get("rejected", [])
    if (not isinstance(matches, list) or not isinstance(rejected, list)
            or any(not isinstance(match, dict) or not isinstance(match.get("name"), str) for match in [*matches, *rejected])):
        raise signature_index.IndexUnavailable("exact-prefix signature renderer emitted malformed winner validation records")
    expected_names = [match["name"] for match in ranked]
    accepted_names = [match["name"] for match in matches]
    rejected_names = [match["name"] for match in rejected]
    accepted_set, rejected_set = set(accepted_names), set(rejected_names)
    accounted = [*accepted_names, *rejected_names]
    reasons = {"excluded_target", "internal_or_private", "unavailable", "not_theorem", "local_anonymous_instance"}
    if (len(set(expected_names)) != len(expected_names)
            or len(accounted) != len(expected_names) or len(set(accounted)) != len(accounted)
            or set(accounted) != set(expected_names)
            or accepted_names != [name for name in expected_names if name in accepted_set]
            or rejected_names != [name for name in expected_names if name in rejected_set]
            or any(match.get("reason") not in reasons for match in rejected)):
        raise signature_index.IndexUnavailable("exact-prefix signature renderer did not account for every indexed winner exactly once in pool order")
    expected_scores = {match["name"]: match["score"] for match in ranked}
    if any(type(match.get("score")) is not int or match["score"] != expected_scores[match["name"]] for match in matches):
        raise signature_index.IndexUnavailable("exact-prefix signature scores disagree with the immutable index; rebuild the index on the host")
    return matches, rejected


@bind_feedback_scoring_policy
def retrieve_lemmas(feedback: Any, request: dict[str, Any]) -> dict[str, Any]:
    """One source-bound read-only query, compatible with Feedback instances."""
    result: dict[str, Any] = {"schema_version": 1, "tool": TOOL["name"], "authoritative": False, "checkpoint": None, "matches": [], "total_hits": 0, "diagnostics": []}
    started = time.perf_counter()
    timings: dict[str, Any] = {}
    result["timings"] = timings
    try:
        from lean_tools import rerank_service_client as reranking

        goal, limit = _validate(request)
        options, automatic = reranking.resolve_options()
        if "limit" not in request and automatic:
            limit = min(limit, options.get("candidate_limit", 30))
        configured_mode = feedback.settings.get("retrieval_pool_mode", "overlap")
        pool_mode = request.get("pool_mode", configured_mode)
        if pool_mode not in ("overlap", "diverse", "hybrid"):
            raise ValueError("retrieval_pool_mode must be overlap, diverse or hybrid")
        if pool_mode != configured_mode:
            raise ValueError(f"pool_mode differs from the frozen host configuration; use pool_mode={configured_mode!r} or omit it")
        enhanced = bool(options) or "candidate_limit" in request or request.get("include_pool", False) or pool_mode != "overlap"
        result["search_limits"] = reranking.search_limit_contract(
            options, automatic, result_max=MAX_LIMIT, default_limit=8,
        )
        pool_limit = reranking.resolve_search_limits(
            limit, request.get("candidate_limit"), options=options, automatic=automatic,
            result_max=MAX_LIMIT, default_limit=8, cli_arguments=False,
        )
        candidate = feedback.candidate_path(request)
        raw = candidate.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        result.update(candidate=str(candidate), source_sha256=digest)
        if request["expected_sha256"] != digest:
            return _finish(feedback, request, {**result, "status": "source_conflict", "diagnostics": [{"code": "source_conflict", "message": "expected_sha256 does not match the current candidate; read the candidate and retry with its current hash"}]})
        text = lean_source.candidate_text_from_bytes(raw)
        snapshot = lean_source.snapshot_candidate(feedback.row, text, candidate)
        prefix = lean_source.exact_source_prefix(feedback.row, feedback.project)
        handle = None
        if "goal_id" in request:
            handle = lean_goal_state.resolve_goal_handle(feedback, candidate, digest, request["goal_id"], prefix.sha256)
            goal = handle["goal"]
        goal_index = goal.get("index", 0) if goal else 0
        declaration_offset = None
        column = None
        if goal:
            offset, column = lean_goal_state.candidate_position_to_offset(text, goal["line"], goal.get("column"))
            declaration_offset = offset - snapshot.declaration_start
            if not 0 <= declaration_offset < len(snapshot.declaration):
                raise ValueError("goal cursor is outside the target declaration; choose a character inside a proof tactic or omit goal to search the editable proof body")
        registry = feedback.settings.get("fingerprint_registry")
        fingerprint = arena.measurement_environment_fingerprint(feedback.row, feedback.project, registry_path=Path(registry) if registry else None)
        if handle and handle.get("environment_fingerprint") not in {None, fingerprint}:
            raise lean_goal_state.GoalStateError("goal_id belongs to a different Lean environment; observe goals again")
        residual = handle is not None and handle.get("phase") == "residual"
        result.update(goal={**({"line": goal["line"], "column": column} if goal else {}), "index": goal_index, "selection": "actual_residual_goal" if residual else "innermost_tactic_goals_before" if goal else "first_proof_body_tactic_goals_before"}, limit=limit, prefix={"kind": prefix.kind, "source_path": str(prefix.source_path) if prefix.source_path else None, "sha256": prefix.sha256, "target_visible": False, "later_declarations_visible": False}, environment_fingerprint=fingerprint, project_root=str(feedback.project), ranking={"method": "weighted_signature_constant_overlap", "pool_mode": pool_mode, "conclusion_weight": 12, "hypothesis_weight": 3, "generic_conclusion_weight": 2, "generic_hypothesis_weight": 1, "type_unification": False})
        if residual:
            # The structured diagnostic held an actual unassigned MVarId and its
            # frozen context. Reuse its rendered context/constants; a cursor query
            # at this location would select the historical goalsBefore instead.
            observed = {"records": [handle["record"]], "diagnostics": [], "backend": "residual_cache"}
            declaration_byte = 0
            timings["goal_seconds"] = 0
            result.update(goal_id=request["goal_id"], phase="residual", occurrence=handle["occurrence"])
        else:
            source, declaration_byte = build_harness(prefix.text, snapshot.declaration, declaration_offset, limit, feedback.row["name"], include_rerank_context=True, goal_index=goal_index, proof_body_offset=snapshot.proof_body_start - snapshot.declaration_start)
            result["discovery_source_sha256"] = _sha(source)
            goal_started = time.perf_counter()
            observed = run_harness(source, feedback.project, min(feedback.timeout, 120))
            timings["goal_seconds"] = round(time.perf_counter() - goal_started, 6)
        result.update({key: value for key, value in observed.items() if key != "records"})
        # A concurrent edit cannot turn an old goal observation into current advice.
        if candidate.read_bytes() != raw:
            return _finish(feedback, request, {**result, "status": "source_conflict", "matches": [], "total_hits": 0, "diagnostics": [{"code": "candidate_changed_during_query", "message": "candidate changed during retrieval; retry with its current hash"}]})
        records = observed["records"]
        if len(records) != 1:
            return _finish(feedback, request, {**result, "status": "unavailable", "diagnostics": observed["diagnostics"] + [{"code": "goal_discovery_unavailable", "message": "Lean did not emit exactly one source-bound goal record; fix preceding elaboration errors or omit the selector to search the editable proof body. The tool adds no imports."}]})
        record = records[0]
        if record.get("status") not in {"ok", "empty", "no_goal"} or not isinstance(record.get("matches", []), list) or len(record.get("matches", [])) > limit:
            return _finish(feedback, request, {**result, "status": "unavailable", "diagnostics": [{"code": "malformed_discovery_payload", "message": "Lean discovery result violated the bounded result contract"}]})
        result.update(record)
        if record["status"] == "ok":
            selected_context = _selected_context(record, goal_index) if pool_mode != "overlap" else None
            symbols = record.get("context_symbols", [])
            if not isinstance(symbols, list) or len(symbols) > MAX_SYMBOLS or any(not isinstance(s, dict) or not isinstance(s.get("name"), str) or type(s.get("weight")) is not int or s["weight"] < 1 or type(s.get("conclusion")) is not bool or type(s.get("hypothesis")) is not bool for s in symbols) or len({s["name"] for s in symbols}) != len(symbols):
                raise signature_index.IndexUnavailable("malformed bounded context symbols")
            index_started = time.perf_counter()
            path, index_details = _query_index(feedback, prefix, fingerprint)
            timings["index_seconds"] = round(time.perf_counter() - index_started, 6)
            result["signature_index"] = index_details
            ranking_started = time.perf_counter()
            if pool_mode == "overlap":
                ranked = signature_index.rank(path, symbols, pool_limit)
            else:
                ranker = signature_index.rank_hybrid if pool_mode == "hybrid" else signature_index.rank_diverse
                ranked = ranker(path, symbols, pool_limit, search_intent=request.get("search_intent", ""),
                                name_query=request.get("name_query", ""), conclusion=selected_context["target"])
                result["ranking"]["method"] = ("idf_normalized_hybrid" if pool_mode == "hybrid"
                                                else "diverse_signature_and_lexical")
            timings["ranking_seconds"] = round(time.perf_counter() - ranking_started, 6)
            result.update({key: ranked[key] for key in ("status", "total_hits", "examined_constants", "visible_theorems")})
            for key in ("pool_sources", "signature_overlap_total_hits", "pool_total_hits_lower_bound",
                        "pool_version", "ranking_policy", "context_budget", "admission_quotas"):
                if key in ranked:
                    result[key] = ranked[key]
            result["matches"] = []
            if ranked["matches"]:
                render_source = build_render_harness(prefix.text, [match["name"] for match in ranked["matches"]], symbols, feedback.row["name"], complete_signatures=True)
                render_started = time.perf_counter()
                rendered = run_harness(render_source, feedback.project, min(feedback.timeout, 120))
                timings["render_seconds"] = round(time.perf_counter() - render_started, 6)
                result["diagnostics"] += rendered["diagnostics"]
                try:
                    result["matches"], rejected = _validated_index_render(ranked["matches"], rendered)
                except signature_index.IndexUnavailable as error:
                    result["diagnostics"].insert(0, {"code": "signature_index_inconsistent", "message": str(error)})
                    raise
                result["index_validation"] = {"status": "partial" if rejected else "verified",
                                              "requested_matches": len(ranked["matches"]),
                                              "verified_matches": len(result["matches"]), "rejected": rejected,
                                              "pool_expanded": False, "index_modified": False}
                if rejected:
                    result["diagnostics"].insert(0, {"code": "signature_index_inconsistent",
                        "message": f"Exact-prefix validation rejected {len(rejected)} of {len(ranked['matches'])} indexed winners; returning only {len(result['matches'])} independently verified signatures from the same bounded pool. Inspect index_validation.rejected and the host index/render module contexts: anonymous declaration names can depend on their module. The index was not modified."})
                    if not result["matches"]:
                        raise signature_index.IndexUnavailable("no indexed winners survived exact-prefix validation; no hints are available from this pool")
                ranked_by_name = {match["name"]: match for match in ranked["matches"]}
                for match in result["matches"]:
                    ranked_match = ranked_by_name[match["name"]]
                    for key in ("candidate_sources", "signal_scores", "signal_ranks", "hybrid_score", "corpus_prior"):
                        if key in ranked_match:
                            match[key] = ranked_match[key]
                timings["render_ms"] = rendered["records"][0].get("render_ms")
            # Goal state must remain bound through indexing and signature rendering.
            if candidate.read_bytes() != raw or (residual and lean_goal_state.source_revision(candidate) != handle["source_revision"]):
                return _finish(feedback, request, {**result, "status": "source_conflict", "matches": [], "total_hits": 0, "diagnostics": [{"code": "candidate_changed_during_query", "message": "candidate changed during retrieval; retry with its current hash"}]})
            selected_context = selected_context or _selected_context(record, goal_index)
            result["context"] = selected_context
            if handle and (record.get("goal_count", handle["goal_count"]) != handle["goal_count"] or
                           ("⋯" not in handle["target"] and re.sub(r"\s+", "", handle["target"]) != re.sub(r"\s+", "", selected_context["target"]))):
                raise lean_goal_state.GoalStateError("goal_id no longer identifies the observed goal context; observe goals again or omit the selector")
            if any(not isinstance(match.get("signature"), str) or match.get("signature_truncated") is not False for match in result["matches"]):
                raise signature_index.IndexUnavailable("retrieval requires complete exact prefix signatures; see diagnostics artifact")
            if enhanced:
                pool = result["matches"]
                context = {"goal": selected_context["target"], "hypotheses": selected_context["hypotheses"],
                           "task_signature": feedback.row["signature"], "source_sha256": digest,
                           "search_intent": request.get("search_intent", ""),
                           "same_run_context": request.get("same_run_context", "")}
                binding = reranking.make_binding(pool, context, task_id=feedback.row["name"], prefix_sha256=prefix.sha256, environment_fingerprint=fingerprint, source_sha256=digest)
                rerank_started = time.perf_counter()
                reranked = reranking.rerank(pool, context, binding=binding, options=options or {"ranker": "baseline"}, automatic=automatic)
                timings["rerank_seconds"] = round(time.perf_counter() - rerank_started, 6)
                result.update(candidate_limit=pool_limit, candidate_matches=len(pool), candidate_pool_sha256=binding["pool_sha256"], candidate_pool_truncated=result["total_hits"] > len(pool) or result.get("pool_total_hits_lower_bound", False))
                result["reranking"] = reranking.compact_result(reranked, pool, limit, include_pool=request.get("include_pool", False))
                result["matches"] = reranked["matches"][:limit]
                if request.get("include_pool", False):
                    result["candidate_pool"] = pool
                # Network latency must not make advice for an old draft look current.
                if candidate.read_bytes() != raw or (residual and lean_goal_state.source_revision(candidate) != handle["source_revision"]):
                    return _finish(feedback, request, {**result, "status": "source_conflict", "matches": [], "total_hits": 0, "diagnostics": [{"code": "candidate_changed_during_rerank", "message": "candidate changed during reranking; retry with its current hash"}]})
        timings["elaboration_ms"] = record.get("elaboration_ms")
        timings["extraction_ms"] = record.get("extraction_ms")
        def position_at_byte(byte: int) -> dict[str, int]:
            local_byte = byte - declaration_byte
            if not 0 <= local_byte <= len(snapshot.declaration.encode("utf-8")):
                raise signature_index.IndexUnavailable("Lean tactic range is outside the bound declaration")
            local_offset = len(snapshot.declaration.encode("utf-8")[:local_byte].decode("utf-8"))
            return lean_goal_state.offset_to_human_position(text, snapshot.declaration_start + local_offset)
        for key in ("tactic_start_byte", "tactic_end_byte"):
            if key in result:
                result["goal"][key.replace("_byte", "")] = position_at_byte(result.pop(key))
        if "context" in result and not residual:
            selected_position = result["goal"].get("tactic_start") or (goal and {"line": goal["line"], "column": column})
            if selected_position:
                result["goal"].update(selected_position)
                result.update(lean_goal_state.attach_goal_handles(feedback, candidate, digest,
                    {"goals": [{"index": goal_index, "target": result["context"]["target"]}],
                     "goal_count": record.get("goal_count", 1), "position": {"candidate": selected_position},
                     "context_origin": "retrieval", "environment_fingerprint": fingerprint}))
        result["returned_matches"] = len(result["matches"])
        result["truncated"] = result["total_hits"] > result["returned_matches"]
        if result["status"] == "no_goal":
            result["diagnostics"].append({"code": "no_goal", "message": record.get("reason", "selected position has no goal")})
            suggested = []
            for item in result.pop("suggested_tactics", []):
                if isinstance(item, dict) and type(item.get("tactic_start_byte")) is int:
                    cursor = position_at_byte(item["tactic_start_byte"])
                    if cursor not in [entry["goal"] for entry in suggested]:
                        suggested.append({"goal": cursor, "goal_count": item.get("goal_count")})
            if suggested:
                result["suggested_goals"] = suggested
            result["retry"] = {"expected_sha256": digest, **({"goal": suggested[0]["goal"]} if suggested else {})}
        timings["total_seconds"] = round(time.perf_counter() - started, 6)
        result["seconds"] = timings["total_seconds"]
        return _finish(feedback, request, result)
    except (ValueError, OSError, arena.WorkflowError, persistent.PersistentQuickError, lean_goal_state.GoalStateError, signature_index.IndexUnavailable) as error:
        timings["total_seconds"] = round(time.perf_counter() - started, 6)
        if isinstance(error, reranking.SearchLimitError):
            result["search_limits"] = error.contract
            result["retry"] = {**request, **error.retry}
        if result.get("source_sha256"):
            result["retry"] = {"expected_sha256": result["source_sha256"]}
            result.update(lean_goal_state.known_goal_handles(feedback, Path(result["candidate"]), result["source_sha256"]))
        return _finish(feedback, request if isinstance(request, dict) else {}, {**result, "status": "invalid_request" if "environment_fingerprint" not in result else "unavailable", "matches": [], "diagnostics": [*result["diagnostics"], {"code": "retrieval_failed", "message": str(error)}]})
