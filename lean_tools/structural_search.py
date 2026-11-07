"""Experimental exact-prefix, actual-goal structural declaration discovery.

The generated Lean harness scans the captured prefix environment, filters by
syntactic conclusion head, and probes each candidate with ``MVarId.apply`` in a
saved Meta state. This is bounded applicability discovery, not proof search.
Residual obligations are returned; a small count is not a proof-quality score.
No imports, source edits, model calls, or additional dependencies are needed.
"""
from __future__ import annotations

import hashlib
import json
import re
import time
from pathlib import Path
from typing import Any

from lean_tools import arena_workflow as arena
from lean_tools import goal_retrieval, lean_goal_state, lean_source

MARKER = "__LRH_STRUCTURAL_SEARCH_V1__"


def _integer(name: str, value: int, low: int, high: int) -> int:
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f"{name} must be an integer in {low}..{high}")
    return value


_PROBE = r'''
        let goal := selectedGoals.head!
        goal.withContext do
          let started ← IO.monoMsNow
          let target ← Lean.instantiateMVars (← goal.getType)
          let render (expr : Lean.Expr) : Lean.MetaM String := do
            Lean.withOptions (fun opts => Lean.Option.set ((opts.setBool `pp.deepTerms true).setBool `pp.proofs true) Lean.pp.maxSteps 1000000000) do
              pure (toString (← Lean.Meta.ppExpr (← Lean.instantiateMVars expr)))
          let renderHypotheses : Lean.MetaM (Array String) := do
            let mut hypotheses : Array String := #[]
            for decl in (← Lean.getLCtx) do
              if !decl.isImplementationDetail then
                let valueText ← match decl.value? (allowNondep := true) with
                  | none => pure ""
                  | some value => do pure (" := " ++ (← render value))
                hypotheses := hypotheses.push s!"{← render (Lean.mkFVar decl.fvarId)} : {← render decl.type}{valueText}"
            return hypotheses
          let rec conclusion : Lean.Expr → Lean.Expr
            | .forallE _ _ body _ => conclusion body
            | .mdata _ body => conclusion body
            | expr => expr
          let rec unfoldConclusion (fuel : Nat) (expr : Lean.Expr) : Lean.Expr :=
            match fuel with
            | 0 => conclusion expr
            | fuel + 1 =>
              let expr := conclusion expr
              match expr.getAppFn with
              | .const name _ =>
                match prefixEnv.find? name with
                | some (.defnInfo value) => unfoldConclusion fuel (Lean.mkAppN value.value expr.getAppArgs).headBeta
                | _ => expr
              | _ => expr
          let surfaceTargetHead := (conclusion target).getAppFn
          let normalizedTarget := unfoldConclusion 8 target
          let targetHead := normalizedTarget.getAppFn
          let headName := match targetHead with
            | .const name _ => some name
            | _ => none
          let candidateConclusion (type : Lean.Expr) : Lean.Expr :=
            let raw := conclusion type
            match raw.getAppFn, surfaceTargetHead with
            | .const name _, .const surface _ =>
              if name == surface || headName == some name then unfoldConclusion 8 type else raw
            | _, _ => raw
          let fixedConclusionHead (type : Lean.Expr) : Bool :=
            match headName, (candidateConclusion type).getAppFn with
              | some wanted, .const actual _ => wanted == actual
              | _, _ => false
          let rec shape (fuel : Nat) (pattern actual : Lean.Expr) : Bool × Nat :=
            match fuel with
            | 0 => (true, 0)
            | fuel + 1 =>
              match pattern, actual with
              | .mdata _ body, actual => shape fuel body actual
              | pattern, .mdata _ body => shape fuel pattern body
              | .bvar _, _ | .mvar _, _ => (true, 0)
              | .const wanted _, .const found _ => (wanted == found, (wanted == found).toNat)
              | .sort _, .sort _ => (true, 0)
              | .app fn arg, .app actualFn actualArg =>
                match fn.getAppFn with
                | .bvar _ | .mvar _ => (true, 0)
                | _ =>
                  let left := shape fuel fn actualFn
                  let right := shape fuel arg actualArg
                  (left.1 && right.1, left.2 + right.2)
              | .lam _ domain body _, .lam _ actualDomain actualBody _
              | .forallE _ domain body _, .forallE _ actualDomain actualBody _ =>
                let left := shape fuel domain actualDomain
                let right := shape fuel body actualBody
                (left.1 && right.1, left.2 + right.2)
              | pattern, actual => (pattern == actual, 0)
          let candidatePriority (type : Lean.Expr) : Nat :=
            let structural := shape 96 (candidateConclusion type) normalizedTarget
            let surface := match surfaceTargetHead, (conclusion type).getAppFn with
              | .const wanted _, .const actual _ => (wanted != actual).toNat
              | _, _ => 2
            (if structural.1 then 0 else 100000) + (10000 - min structural.2 10000) * 3 + surface
          let names : Array String := __NAMES__
          if headName.isNone && names.isEmpty then
            return Lean.Json.mkObj [("status", Lean.toJson "unsupported_goal_head"), ("matches", Lean.toJson (#[] : Array Lean.Json)), ("goal", Lean.toJson (← render target)), ("hypotheses", Lean.toJson (← renderHypotheses)), ("reason", Lean.toJson "broad discovery requires a constant conclusion head after bounded alias unfolding; specialize/introduce the goal or check an explicit name pool")]
          let candidates := prefixEnv.constants.toList.filterMap fun (name, info) => Id.run do
            let originalTheorem := Lean.wasOriginallyTheorem prefixEnv name
            let exactHead := fixedConclusionHead info.type
            let compatibleHead := match headName, (candidateConclusion info.type).getAppFn with
              | some wanted, .const actual _ => wanted == actual
              | _, _ => true
            let eligible := !name.isInternal && !Lean.isPrivateName name && name.toString != __TARGET__ &&
              (originalTheorem || (__NON_THEOREMS__ && (exactHead || !names.isEmpty))) &&
              (names.isEmpty || names.contains name.toString) && (!names.isEmpty || compatibleHead)
            if eligible then
              let helperConstant := (name.toString.splitOn "__HELPER_ID__").length > 1
              if helperConstant then return none
              let priority := if names.isEmpty then candidatePriority info.type else names.toList.idxOf name.toString
              return some (priority, name, info)
            else
              return none
          let ordered := candidates.toArray.qsort fun a b =>
            a.1 < b.1 || (a.1 == b.1 && a.2.1.toString < b.2.1.toString)
          let probeStarted ← IO.monoMsNow
          let mut hits : Array (Nat × Nat × Nat × String × Lean.Json) := #[]
          let mut tested := 0
          let mut failed := 0
          let mut heartbeatFailures := 0
          let mut bounded := false
          for (_, name, info) in ordered do
            if tested >= __PROBE_LIMIT__ || (← IO.monoMsNow) - probeStarted >= __WALL_MS__ then
              bounded := true
              break
            tested := tested + 1
            let saved ← Lean.Meta.saveState
            try
              let result : Nat × Nat × Nat × String × Lean.Json ← Lean.Core.withCurrHeartbeats <| withTheReader Lean.Core.Context (fun ctx => { ctx with maxHeartbeats := __HEARTBEATS__ * 1000 }) do
                Lean.withIncRecDepth do
                  let expr ← Lean.Meta.mkConstWithFreshMVarLevels name
                  let initialResidual ← goal.apply expr
                  let mut residual : List Lean.MVarId := []
                  let mut discharged : Array Lean.Json := #[]
                  for obligation in initialResidual do
                    let mut closed := false
                    if __DISCHARGE_TRIVIAL__ then
                      let trial ← Lean.Meta.saveState
                      try
                        obligation.assumption
                        closed := true
                      catch _ => trial.restore
                      if !closed then
                        let trial ← Lean.Meta.saveState
                        try
                          obligation.refl
                          closed := true
                        catch _ => trial.restore
                    if !closed then
                      residual := residual ++ [obligation]
                    else
                      let item ← obligation.withContext do
                        pure (Lean.Json.mkObj [("target", Lean.toJson (← render (← obligation.getType))), ("proof", Lean.toJson (← render (Lean.mkMVar obligation)))])
                      discharged := discharged.push item
                  let mut obligations : Array Lean.Json := #[]
                  let mut unchanged := 0
                  let mut reversed := 0
                  let mut unconstrained := 0
                  let compare (left right : Lean.Expr) : Lean.MetaM Bool := do
                    let comparison ← Lean.Meta.saveState
                    try Lean.Meta.isDefEq left right finally comparison.restore
                  let args := target.getAppArgs
                  let reversedTarget := if args.size >= 2 then
                    Lean.mkAppN target.getAppFn ((args.extract 0 (args.size - 2)).push args[args.size - 1]! |>.push args[args.size - 2]!)
                    else target
                  for obligation in residual do
                    let (item, sameGoal, reverseGoal, freePremise) ← obligation.withContext do
                      let residualType ← Lean.instantiateMVars (← obligation.getType)
                      let sameGoal ← compare residualType target
                      let reverseGoal ← if args.size >= 2 then compare residualType reversedTarget else pure false
                      let freePremise := residualType.hasExprMVar
                      return (Lean.Json.mkObj [("target", Lean.toJson (← render residualType)), ("hypotheses", Lean.toJson (← renderHypotheses)), ("same_as_goal", Lean.toJson sameGoal), ("reversed_goal_arguments", Lean.toJson reverseGoal), ("contains_unassigned_metavariables", Lean.toJson freePremise)], sameGoal, reverseGoal, freePremise)
                    if sameGoal then unchanged := unchanged + 1
                    if reverseGoal then reversed := reversed + 1
                    if freePremise then unconstrained := unconstrained + 1
                    obligations := obligations.push item
                  let fixedHead : Bool := fixedConclusionHead info.type
                  let noProgress : Bool := residual.length == 1 && unchanged == 1
                  let structural := shape 96 (candidateConclusion info.type) normalizedTarget
                  let record := Lean.Json.mkObj [
                    ("name", Lean.toJson name.toString),
                    ("signature", Lean.toJson (← render info.type)),
                    ("originally_theorem", Lean.toJson (Lean.wasOriginallyTheorem prefixEnv name)),
                    ("fixed_conclusion_head", Lean.toJson fixedHead),
                    ("structural_shape_compatible", Lean.toJson structural.1),
                    ("structural_rigid_matches", Lean.toJson structural.2),
                    ("discovery_rank", Lean.toJson tested),
                    ("unchanged_goal_obligations", Lean.toJson unchanged),
                    ("reversed_goal_obligations", Lean.toJson reversed),
                    ("unconstrained_obligations", Lean.toJson unconstrained),
                    ("no_progress", Lean.toJson noProgress),
                    ("cyclicity", Lean.toJson (if unchanged > 0 then "same_goal" else if reversed > 0 then "reversed_goal_arguments" else "none_detected")),
                    ("result_class", Lean.toJson (if residual.isEmpty then "direct_closes" else "leaves_obligations")),
                    ("initial_residual_count", Lean.toJson initialResidual.length),
                    ("trivially_discharged_count", Lean.toJson (initialResidual.length - residual.length)),
                    ("discharged_goals", Lean.toJson discharged),
                    ("residual_count", Lean.toJson residual.length),
                    ("residual_goals", Lean.toJson obligations),
                    ("probe", Lean.toJson (if __DISCHARGE_TRIVIAL__ then "apply_then_assumption_or_reflexivity" else "apply"))]
                  return (noProgress.toNat, (!fixedHead).toNat, residual.length, name.toString, record)
              hits := hits.push result
            catch ex =>
              failed := failed + 1
              if ex.isMaxHeartbeat then heartbeatFailures := heartbeatFailures + 1
            finally
              saved.restore
          let hypotheses ← renderHypotheses
          let finished ← IO.monoMsNow
          let ranked := hits.qsort fun a b =>
            a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 &&
              (a.2.2.1 < b.2.2.1 || (a.2.2.1 == b.2.2.1 && a.2.2.2.1 < b.2.2.2.1)))))
          return Lean.Json.mkObj [
            ("status", Lean.toJson "ok"),
            ("method", Lean.toJson "bounded_prefix_apply_discovery"),
            ("goal", Lean.toJson (← render target)),
            ("hypotheses", Lean.toJson hypotheses),
            ("matches", Lean.toJson ((ranked.take __LIMIT__).map fun item => item.2.2.2.2)),
            ("ordering", Lean.toJson "unchanged_goal_last_then_fixed_head_then_residual_count_then_name_not_proof_quality"),
            ("candidate_ordering", Lean.toJson (if names.isEmpty then "compatible_conclusion_shape_then_rigid_matches_then_surface_head_then_name" else "supplied_name_order")),
            ("applicable_found", Lean.toJson hits.size),
            ("returned_matches", Lean.toJson (min hits.size __LIMIT__)),
            ("matches_omitted", Lean.toJson (hits.size - min hits.size __LIMIT__)),
            ("tested_candidates", Lean.toJson tested),
            ("failed_probes", Lean.toJson failed),
            ("heartbeat_exhausted_probes", Lean.toJson heartbeatFailures),
            ("head_candidates", Lean.toJson ordered.size),
            ("scan_complete", Lean.toJson (!bounded)),
            ("pool_scope", Lean.toJson (if names.isEmpty then "all_public_prefix_declarations" else "supplied_names")),
            ("corpus_filter", Lean.toJson "public_theorems_plus_non_theorems_with_matching_conclusion_head"),
            ("include_non_theorems", Lean.toJson __NON_THEOREMS__),
            ("enumeration_ms", Lean.toJson (probeStarted - started)),
            ("probe_ms", Lean.toJson (finished - probeStarted)),
            ("elaboration_ms", Lean.toJson (elaborationFinished - elaborationStarted)),
            ("goal_count", Lean.toJson tactic.goalsBefore.length),
            ("selected_goal_index", Lean.toJson __GOAL_INDEX__),
            ("tactic_start_byte", Lean.toJson start),
            ("tactic_end_byte", Lean.toJson finish)]
'''


_NATIVE_PROBE = r'''
        let goal := selectedGoals.head!
        let saved ← Lean.Meta.saveState
        try
          Lean.withEnv prefixEnv do
            goal.withContext do
              let started ← IO.monoMsNow
              let render (expr : Lean.Expr) : Lean.MetaM String := do
                Lean.withOptions (fun opts => Lean.Option.set ((opts.setBool `pp.deepTerms true).setBool `pp.proofs true) Lean.pp.maxSteps 1000000000) do
                  pure (toString (← Lean.Meta.ppExpr (← Lean.instantiateMVars expr)))
              let renderHypotheses : Lean.MetaM (Array String) := do
                let mut hypotheses : Array String := #[]
                for decl in (← Lean.getLCtx) do
                  if !decl.isImplementationDetail then
                    let valueText ← match decl.value? (allowNondep := true) with
                      | none => pure ""
                      | some value => do pure (" := " ++ (← render value))
                    hypotheses := hypotheses.push s!"{← render (Lean.mkFVar decl.fvarId)} : {← render decl.type}{valueText}"
                return hypotheses
              let target ← goal.getType
              let targetText ← render target
              let hypotheses ← renderHypotheses
              let run ← Lean.Core.withCurrHeartbeats <| withTheReader Lean.Core.Context (fun ctx => { ctx with maxHeartbeats := __NATIVE_HEARTBEATS__ * 1000 }) do
                let probeGoal ← if __NATIVE_NORMALIZE__ then
                  goal.change (← Lean.Meta.withDefault (Lean.Meta.whnf target))
                  else pure goal
                let (_, searchGoal) ← probeGoal.intros
                let answer ← searchGoal.withContext do
                  nativeSearch searchGoal
                let renderResult (residual : List Lean.MVarId) : Lean.MetaM Lean.Json := do
                  let proof ← Lean.instantiateMVars (Lean.mkMVar goal)
                  let constants := proof.getUsedConstants
                  for name in constants do
                    if (name.toString.splitOn "__HELPER_ID__").length > 1 then
                      throwError "native suggestion depended on the generated query helper"
                    if name.toString == "sorryAx" || name.toString == "Lean.sorryAx" then
                      throwError "native search returned an admitted proof term"
                    if (prefixEnv.find? name).isNone then
                      throwError "native suggestion used a constant unavailable in the captured prefix: {name}"
                  let mut obligations : Array Lean.Json := #[]
                  for obligation in residual do
                    let item ← obligation.withContext do
                      return Lean.Json.mkObj [("target", Lean.toJson (← render (← obligation.getType))), ("hypotheses", Lean.toJson (← renderHypotheses))]
                    obligations := obligations.push item
                  let closed := residual.isEmpty && !proof.hasExprMVar && !proof.hasLevelMVar
                  return Lean.Json.mkObj [
                    ("proof_term", Lean.toJson (← render proof)),
                    ("used_constants", Lean.toJson (constants.map Lean.Name.toString)),
                    ("result_class", Lean.toJson (if closed then "direct_closes" else "leaves_obligations")),
                    ("residual_count", Lean.toJson residual.length),
                    ("residual_goals", Lean.toJson obligations),
                    ("contains_unassigned_metavariables", Lean.toJson proof.hasExprMVar),
                    ("contains_unassigned_universe_metavariables", Lean.toJson proof.hasLevelMVar),
                    ("probe", Lean.toJson "native_library_search")]
                match answer with
                | none =>
                  let proof ← Lean.instantiateMVars (Lean.mkMVar goal)
                  if proof.hasExprMVar || proof.hasLevelMVar then
                    throwError "native search reported closure with unassigned metavariables"
                  return (#[← renderResult []], 1, true)
                | some suggestions =>
                  let mut results : Array Lean.Json := #[]
                  for (residual, context) in suggestions.take __LIMIT__ do
                    results := results.push (← Lean.Meta.withMCtx context (renderResult residual))
                  return (results, suggestions.size, false)
              let finished ← IO.monoMsNow
              return Lean.Json.mkObj [
                ("status", Lean.toJson "ok"),
                ("engine", Lean.toJson "native"),
                ("method", Lean.toJson "prefix_bound_native_library_search"),
                ("goal", Lean.toJson targetText),
                ("hypotheses", Lean.toJson hypotheses),
                ("matches", Lean.toJson run.1),
                ("suggestions_found", Lean.toJson run.2.1),
                ("returned_matches", Lean.toJson run.1.size),
                ("closed", Lean.toJson run.2.2),
                ("native_normalize_goal", Lean.toJson __NATIVE_NORMALIZE__),
                ("native_heartbeats", Lean.toJson __NATIVE_HEARTBEATS__),
                ("probe_ms", Lean.toJson (finished - started)),
                ("elaboration_ms", Lean.toJson (elaborationFinished - elaborationStarted)),
                ("goal_count", Lean.toJson tactic.goalsBefore.length),
                ("selected_goal_index", Lean.toJson __GOAL_INDEX__),
                ("tactic_start_byte", Lean.toJson start),
                ("tactic_end_byte", Lean.toJson finish)]
        catch ex =>
          return Lean.Json.mkObj [("status", Lean.toJson (if ex.isMaxHeartbeat then "search_exhausted" else "native_search_failed")), ("engine", Lean.toJson "native"), ("matches", Lean.toJson (#[] : Array Lean.Json)), ("reason", Lean.toJson (← ex.toMessageData.toString))]
        finally
          saved.restore
'''


# Load executable metaprogram support in a separate environment. In particular,
# adding an import before the captured prefix would quietly broaden the premise
# corpus. A typed bridge lets each cached Lean version elaborate its own native
# defaults instead of casting version-dependent librarySearch argument layouts.
# The importer helper only appends initial extension slots; its type and the
# complete legal constant map are checked before the search closure can run.
_NATIVE_LOADER = r'''
  Lean.enableInitializersExecution
  let helperEnv ← Lean.importModules #[{module := `Lean.Meta.Tactic.LibrarySearch}] {} (loadExts := true)
  let nativeSearch ← Lean.withEnv helperEnv do
    let bridgeName := Lean.mkIdent `_root_.lrhNativeBridge__HELPER_ID__
    let nativeName := Lean.mkIdent `Lean.Meta.LibrarySearch.librarySearch
    Lean.Elab.Command.elabCommand (← `(command|
      def $bridgeName:ident (goal : Lean.MVarId) :
          Lean.MetaM (Option (Array (List Lean.MVarId × Lean.MetavarContext))) :=
        $nativeName:ident goal))
    let bridgeEnv ← Lean.getEnv
    match bridgeEnv.evalConst
        (Lean.MVarId → Lean.MetaM (Option (Array (List Lean.MVarId × Lean.MetavarContext))))
        {} `lrhNativeBridge__HELPER_ID__ (checkMeta := false) with
    | .ok value => pure value
    | .error message => throwError message
  let padding := helperEnv.constants.toList.filter fun item =>
    Lean.privateToUserName item.1 == `Lean.ensureExtensionsArraySize &&
      item.1.toString.startsWith "_private.Lean.Environment."
  if padding.length != 1 then
    throwError "native helper requires one known Lean environment-extension padding function"
  let paddingName := padding.head!.1
  let validPaddingType ← Lean.withEnv helperEnv do
    Lean.Elab.Command.liftTermElabM do
      let expected ← Lean.Elab.Term.elabType (← `(term| Lean.Environment → IO Lean.Environment))
      Lean.Meta.isDefEq padding.head!.2.type expected
  if !validPaddingType then
    throwError "native helper environment-extension padding has an unsupported type"
  let pad ← match helperEnv.evalConst (Lean.Environment → IO Lean.Environment) {} paddingName (checkMeta := false) with
    | .ok value => pure value
    | .error message => throwError message
  let legalConstants := prefixEnv.constants.toList
  let paddedPrefixEnv ← pad prefixEnv
  if paddedPrefixEnv.constants.toList.length != legalConstants.length ||
      legalConstants.any (fun item => match paddedPrefixEnv.find? item.1 with
        | none => true
        | some info => info.type != item.2.type) then
    throwError "native helper changed the captured legal prefix constants"
  if (prefixEnv.find? `lrhNativeBridge__HELPER_ID__).isSome ||
      (paddedPrefixEnv.find? `lrhNativeBridge__HELPER_ID__).isSome then
    throwError "native helper bridge leaked into the legal prefix"
  let prefixEnv := paddedPrefixEnv
  Lean.setEnv prefixEnv
'''


def build_harness(
    prefix: str,
    declaration: str,
    offset: int | None,
    limit: int = 20,
    target_name: str = "",
    *,
    goal_index: int = 0,
    proof_body_offset: int | None = None,
    candidate_names: list[str] | None = None,
    probe_limit: int = 1000,
    heartbeats: int = 10000,
    wall_ms: int = 5000,
    include_non_theorems: bool = True,
    discharge_trivial: bool = False,
    engine: str = "structural",
    native_heartbeats: int = 200000,
    native_normalize_goal: bool = False,
) -> tuple[str, int]:
    """Build an observational wrapper; source byte offsets stay snapshot-bound.

    ``candidate_names=None`` discovers over the entire legal public theorem
    corpus. A supplied list is explicitly reported as checking a supplied pool.
    A conclusion-head prefilter unfolds at most eight definition heads of the
    goal and matching candidate heads. Other candidate aliases can be checked
    through an explicit name pool; broad discovery may miss them. Nested
    conclusion shape (theorem binders act as wildcards) orders compatible shapes
    before generic statements. This is deliberately incomplete, including for
    aliases needing deeper reduction; no completeness or relevance is claimed.
    ``probe_limit`` and ``wall_ms`` bound the probe phase between probes; Lean
    heartbeats bound each probe. The process/request timeout also bounds corpus
    enumeration, which is reported separately. Results are not proof-quality
    scores, and a final candidate still needs an independent Lean check.
    """
    _integer("limit", limit, 1, 1000)
    _integer("goal_index", goal_index, 0, 1000)
    _integer("probe_limit", probe_limit, 1, 100000)
    _integer("heartbeats", heartbeats, 1, 1000000)
    _integer("wall_ms", wall_ms, 1, 60000)
    _integer("native_heartbeats", native_heartbeats, 1, 1000000)
    if engine not in {"structural", "native"}:
        raise ValueError("engine must be structural or native")
    if type(native_normalize_goal) is not bool:
        raise ValueError("native_normalize_goal must be a boolean")
    if engine == "native" and candidate_names is not None:
        raise ValueError("native engine searches its own legal prefix index; candidate_names requires engine=structural")
    if type(include_non_theorems) is not bool:
        raise ValueError("include_non_theorems must be a boolean")
    if type(discharge_trivial) is not bool:
        raise ValueError("discharge_trivial must be a boolean")
    if candidate_names is not None:
        if not isinstance(candidate_names, list) or not candidate_names or any(not isinstance(name, str) or not name or len(name) > 1000 for name in candidate_names):
            raise ValueError("candidate_names must be a nonempty list of declaration names")
        if len(candidate_names) > 10000:
            raise ValueError("candidate_names cannot exceed 10000")
    wrapper = goal_retrieval._WRAPPER
    if engine == "native":
        wrapper = wrapper.replace('elab "__COMMAND__ " cmd:command : command => do',
            'syntax (name := __COMMAND__Syntax) "__COMMAND__ " command : command\n'
            '@[command_elab __COMMAND__Syntax] unsafe def __COMMAND__Elab : Lean.Elab.Command.CommandElab := fun stx => do\n'
            '  let cmd := stx[1]')
    begin = wrapper.index("        let mut conclusions :")
    end = wrapper.index("      emit value", begin)
    probe = ((_NATIVE_PROBE if engine == "native" else _PROBE).replace("__NAMES__", "#[" + ",".join(json.dumps(name, ensure_ascii=False) for name in candidate_names or []) + "]")
             .replace("__TARGET__", json.dumps(target_name, ensure_ascii=False))
             .replace("__PROBE_LIMIT__", str(probe_limit))
             .replace("__HEARTBEATS__", str(heartbeats))
             .replace("__WALL_MS__", str(wall_ms))
             .replace("__NON_THEOREMS__", str(include_non_theorems).lower())
             .replace("__DISCHARGE_TRIVIAL__", str(discharge_trivial).lower())
             .replace("__NATIVE_HEARTBEATS__", str(native_heartbeats))
             .replace("__NATIVE_NORMALIZE__", str(native_normalize_goal).lower())
             .replace("__LIMIT__", str(limit))
             .replace("__GOAL_INDEX__", str(goal_index)))
    wrapper = wrapper[:begin] + probe + wrapper[end:]
    wrapper = wrapper.replace("  let elaborationStarted ← IO.monoMsNow", "  let prefixEnv ← Lean.getEnv\n  let elaborationStarted ← IO.monoMsNow", 1)
    if engine == "native":
        # Record the original target's InfoTree before helper initialization can
        # register any global syntax or elaborator. The search later overrides
        # each recorded context with the unchanged captured prefix environment.
        wrapper = wrapper.replace("  let elaborationFinished ← IO.monoMsNow\n",
            "  let elaborationFinished ← IO.monoMsNow\n" + _NATIVE_LOADER, 1)
    # Reuse the established InfoTree cursor selector while binding byte offsets
    # after our larger helper is inserted. Never mutate its module-level template.
    command = "lrhStructural" + hashlib.sha256((prefix + declaration + str(offset) + probe).encode()).hexdigest()[:16]
    helper = (wrapper.replace("__COMMAND__", command).replace("__MARKER__", MARKER)
              .replace("__AUTO__", str(offset is None).lower()).replace("__GOAL_INDEX__", str(goal_index))
              .replace("__HELPER_ID__", command[-16:]))
    if offset is None and proof_body_offset is None:
        raise ValueError("automatic goal selection requires proof_body_offset")
    for label, position in (("offset", offset), ("proof_body_offset", proof_body_offset)):
        if position is not None and (type(position) is not int or not 0 <= position < len(declaration)):
            raise ValueError(f"{label} must be inside declaration")
    suffix = "\nset_option Elab.async false in\n" + command + " "
    width = 12
    tokens = ("__CURSOR__", "__DECL_START__", "__DECL_END__", "__BODY_START__")
    placeholder = helper
    for token in tokens:
        placeholder = placeholder.replace(token, "0" * width)
    start = len((prefix + placeholder + suffix).encode())
    positions = (start + len(declaration[:offset or 0].encode()), start,
                 start + len(declaration.encode()), start + len(declaration[:proof_body_offset or 0].encode()))
    if max(positions) >= 10 ** width:
        raise ValueError("generated source exceeds cursor capacity")
    for token, position in zip(tokens, positions):
        helper = helper.replace(token, str(position).zfill(width))
    return prefix + helper + suffix + declaration + "\n", start


def run_harness(source: str, project: Any, timeout: int = 30, engine: str = "structural") -> dict[str, Any]:
    """Use the existing gated Lean runner; never launch a separate environment."""
    return goal_retrieval.run_harness(source, project, timeout, marker=MARKER, force_cold=engine == "native")


def search_candidate(
    row: dict[str, Any], project: Path, candidate: Path, expected_sha256: str,
    *, goal: dict[str, int] | None = None, goal_index: int = 0,
    timeout: int = 30, fingerprint_registry: Path | None = None,
    engine: str = "structural",
    **bounds: Any,
) -> dict[str, Any]:
    """Read-only research entrypoint with frozen-source and prefix binding.

    A cursor is one-based in the complete candidate file. Omitting it selects
    the first recorded tactic in the editable body, which is a historical goal
    and may already be discharged. Results are advice, never a checkpoint.
    """
    started = time.perf_counter()
    result: dict[str, Any] = {"schema_version": 1, "tool": "search_structural",
        "authoritative": False, "checkpoint": None, "matches": [], "diagnostics": []}
    try:
        if not isinstance(expected_sha256, str) or not re.fullmatch(r"[0-9a-f]{64}", expected_sha256):
            raise ValueError("expected_sha256 must be 64 lowercase hexadecimal characters")
        _integer("timeout", timeout, 1, 180)
        if goal is not None:
            if not isinstance(goal, dict) or not goal or set(goal) - {"line", "column"} or "line" not in goal:
                raise ValueError("goal must contain a one-based line and optional column")
            for key, value in goal.items():
                _integer("goal " + key, value, 1, 10000000)
        candidate, project = Path(candidate).resolve(), Path(project).resolve()
        raw = candidate.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        result.update(candidate=str(candidate), source_sha256=digest)
        if digest != expected_sha256:
            return {**result, "status": "source_conflict", "diagnostics": [{"code": "source_conflict", "message": "expected_sha256 does not match the current candidate"}]}
        text = lean_source.candidate_text_from_bytes(raw)
        snapshot = lean_source.snapshot_candidate(row, text, candidate)
        prefix = lean_source.exact_source_prefix(row, project)
        offset = None
        if goal is not None:
            absolute, column = lean_goal_state.candidate_position_to_offset(text, goal["line"], goal.get("column"))
            offset = absolute - snapshot.declaration_start
            if not 0 <= offset < len(snapshot.declaration):
                raise ValueError("goal cursor is outside the target declaration")
            result["goal_selector"] = {"line": goal["line"], "column": column, "index": goal_index}
        else:
            result["goal_selector"] = {"selection": "first_proof_body_tactic_goals_before", "index": goal_index}
        source, _ = build_harness(prefix.text, snapshot.declaration, offset, engine=engine,
            target_name=row["name"], goal_index=goal_index,
            proof_body_offset=snapshot.proof_body_start - snapshot.declaration_start, **bounds)
        fingerprint = arena.measurement_environment_fingerprint(row, project, registry_path=fingerprint_registry)
        result.update(prefix={"kind": prefix.kind, "sha256": prefix.sha256, "target_visible": False,
                              "later_declarations_visible": False}, project_root=str(project),
                      environment_fingerprint=fingerprint,
                      discovery_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                      engine=engine,
                      search_limits=({"limit": bounds.get("limit", 20), "native_heartbeats": bounds.get("native_heartbeats", 200000), "request_timeout_seconds": timeout} if engine == "native" else {"limit": bounds.get("limit", 20), "probe_limit": bounds.get("probe_limit", 1000),
                          "per_probe_heartbeats": bounds.get("heartbeats", 10000), "wall_ms": bounds.get("wall_ms", 5000),
                          "request_timeout_seconds": timeout}))
        observed = run_harness(source, project, timeout, engine)
        result.update({key: value for key, value in observed.items() if key != "records"})
        if candidate.read_bytes() != raw or lean_source.exact_source_prefix(row, project).sha256 != prefix.sha256:
            return {**result, "status": "source_conflict", "matches": [], "diagnostics": [{"code": "source_changed_during_query", "message": "candidate or exact prefix changed during discovery; discard these probes"}]}
        records = observed["records"]
        if len(records) != 1:
            return {**result, "status": "unavailable", "diagnostics": result["diagnostics"] + [{"code": "structural_discovery_unavailable", "message": "Lean did not emit exactly one source-bound goal record"}]}
        result.update(records[0])
        result["seconds"] = round(time.perf_counter() - started, 6)
        return result
    except (ValueError, OSError, arena.WorkflowError) as error:
        return {**result, "status": "invalid_request", "diagnostics": [{"code": "invalid_request", "message": str(error)}]}
