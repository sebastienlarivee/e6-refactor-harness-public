namespace E6SemanticSearch
open Lean Elab Command Meta

private meta def span? (stx : Syntax) : Option (Nat × Nat) := do
  let a ← stx.getPos?
  let b ← stx.getTailPos?
  if a.byteIdx < b.byteIdx then return (a.byteIdx, b.byteIdx) else none

private meta partial def declarationName? (stx : Syntax) : Option Name := do
  if stx.getKind == `Lean.Parser.Command.declId then return stx[0].getId
  stx.getArgs.toList.findSome? declarationName?

private structure Snapshot where
  start : Nat
  finish : Nat
  ctx : ContextInfo
  info : TacticInfo

private meta partial def scan (boundary : Nat) (ctx? : Option ContextInfo)
    (tree : InfoTree) (fuel : Nat := 512) (ancestors : Array (Nat × Nat) := #[]) : Array Snapshot := Id.run do
  if fuel == 0 then return #[]
  match tree with
  | .hole _ => return #[]
  | .context ctx child => return scan boundary (ctx.mergeIntoOuter? ctx?) child (fuel - 1) ancestors
  | .node info children =>
    let mut found := #[]
    let mut covered := ancestors
    if let some ctx := ctx? then
      if let .ofTacticInfo tactic := info then
        if let some (a, b) := span? tactic.stx then
          if boundary <= a then
            if !ancestors.contains (a, b) then found := found.push ⟨a, b, ctx, tactic⟩
            covered := covered.push (a, b)
    for child in children do
      found := found ++ scan boundary (info.updateContext? ctx?) child (fuel - 1) covered
    return found

private meta partial def suffixes (stx : Syntax) (boundary : Nat) (fuel : Nat := 512) : Array (Nat × Nat × Nat) := Id.run do
  if fuel == 0 then return #[]
  let mut found := #[]
  let bracketed := stx.getKind == `Lean.Parser.Tactic.tacticSeqBracketed
  if bracketed || stx.getKind == `Lean.Parser.Tactic.tacticSeq1Indented then
    if let some (_, b) := span? stx then
      let items := (if bracketed then stx[1] else stx[0]).getArgs
      for i in [:items.size] do
        if i % 2 == 0 then
          if let some (a, childEnd) := span? items[i]! then
            -- The closing brace belongs to the sequence, not to its last tactic.
            let finish := if bracketed then
              ((items.back?).bind span?).map Prod.snd |>.getD childEnd
              else b
            if boundary <= a && a < finish then found := found.push (a, childEnd, finish)
  for child in stx.getArgs do found := found ++ suffixes child boundary (fuel - 1)
  return found

private meta def render (expr : Expr) : MetaM String :=
  withOptions (fun opts => opts.setBool `pp.universes false |>.setBool `pp.proofs true
      |>.setBool `pp.mvars true |>.setBool `pp.deepTerms true
      |>.setBool `pp.funBinderTypes true |>.setBool `pp.letVarTypes true) do
    return (← ppExpr expr).pretty 100000

-- Other old metavariables belong to the surrounding proof. A solver may only
-- solve the selected goal and fresh metavariables created by its own attempt.
private meta def leaks (before after : MetavarContext) (goal : MVarId) : Bool :=
  let exprLeak := after.eAssignment.foldl (init := false) fun bad id _ =>
    bad || (id != goal && before.decls.contains id && !before.eAssignment.contains id)
  let delayedLeak := after.dAssignment.foldl (init := false) fun bad id _ =>
    bad || (before.decls.contains id && !before.dAssignment.contains id)
  let levelLeak := after.lAssignment.foldl (init := false) fun bad id _ =>
    bad || ((before.findLevelDepth? id).isSome && !before.lAssignment.contains id)
  exprLeak || delayedLeak || levelLeak

-- Equivalent to modern zetaReduce (zetaDelta := false), using APIs also
-- available before that option existed. Only locals introduced while entering
-- this expression's own let/have binders may be unfolded; ambient lets remain.
private meta def internalZeta (expression : Expr) : MetaM Expr := do
  let boundary := (← getLCtx).numIndices
  Meta.transform expression (usedLetOnly := true) (pre := fun value => do
    let .fvar id := value.getAppFn | return .continue
    let some decl := (← getLCtx).find? id | return .continue
    if decl.index < boundary then return .continue
    let some replacement := decl.value? (allowNondep := true) | return .continue
    return .visit <| (← instantiateMVars replacement).beta value.getAppArgs)

private meta def betaEta (expression : Expr) : MetaM Expr := do
  let expression ← Core.betaReduce expression
  Core.transform expression (post := fun value => pure (.done value.eta))

private meta def normalize (expression : Expr) : MetaM Expr := do
  betaEta (← internalZeta expression)

-- Reuse only proposition proofs already in scope at the source suffix. This
-- never introduces source lets and never chooses values inhabiting data types.
private meta def reuseLocalProofs (expression : Expr) : MetaM (Expr × Nat) := do
  let mut localProofs : Array (Expr × Expr × Option Name) := #[]
  for decl in (← getLCtx) do
    if localProofs.size >= 64 then break
    if !decl.isImplementationDetail then
      let type ← instantiateMVars decl.type
      if !type.hasMVar && (← isProp type) then
        localProofs := localProofs.push (mkFVar decl.fvarId, type, (← whnf type).getAppFn.constName?)
  if localProofs.isEmpty then return (expression, 0)
  let visits ← IO.mkRef (0 : Nat)
  let comparisons ← IO.mkRef (0 : Nat)
  let reused ← IO.mkRef (0 : Nat)
  let expression ← Meta.transform expression (pre := fun value => do
    let count ← visits.get
    if count >= 2048 then return .done value
    visits.set (count + 1)
    if value.isFVar || value.isBVar || value.isConst || value.isSort || value.isForall then
      return .continue
    try
      let type ← instantiateMVars (← inferType value)
      if type.hasMVar || !(← isProp type) then return .continue
      let head := (← whnf type).getAppFn.constName?
      for (proof, proofType, proofHead) in localProofs do
        if head != proofHead then continue
        let count ← comparisons.get
        if count >= 256 then break
        comparisons.set (count + 1)
        let saved ← Meta.saveState
        let same ← try isDefEq type proofType finally saved.restore
        if same then
          reused.modify (· + 1)
          return .done proof
      return .continue
    catch _ => return .continue)
  return (expression, ← reused.get)

private meta def solve (snapshot : Snapshot) (solver : String) (target : Name)
    (preEnv : Environment) (finalMCtx : MetavarContext) (heartbeats : Nat) : IO Json := do
  let begun ← IO.monoMsNow
  try
    if preEnv.contains target then
      return Json.mkObj [("status", toJson "target_present")]
    let original := solver.startsWith "original_suffix_"
    -- Even auxiliary declarations created during the original target may not
    -- enter search. The exact environment from before the command is restored.
    let ctx := { snapshot.ctx with
      env := preEnv
      cmdEnv? := none
      mctx := if original then finalMCtx else snapshot.info.mctxBefore }
    let answer ← ctx.runMetaM {} do
      Core.withCurrHeartbeats <| withTheReader Core.Context
          (fun value => { value with maxHeartbeats := heartbeats * 1000 }) do
        let goal := snapshot.info.goalsBefore.head!
        goal.withContext do
          let expected ← instantiateMVars (← goal.getType)
          if !(← isProp expected) then throwError "semantic search only replaces proofs of Prop"
          Core.setMessageLog {}
          if !original then
            let stx ← match Parser.runParserCategory (← getEnv) `tactic solver with
              | .ok stx => pure stx
              | .error error => throwError error
            let residual ← Term.TermElabM.run' do
              let remaining ← Tactic.run goal do
                Tactic.withoutRecover <| Tactic.evalTactic stx
              Term.synthesizeSyntheticMVarsNoPostponing
              return remaining
            if !residual.isEmpty then throwError "solver left goals"
          if (← Core.getMessageLog).hasErrors then throwError "solver logged an elaboration error"
          let expression ← instantiateMVars (mkMVar goal)
          let expression ← match solver with
            | "original_suffix_zeta" => internalZeta expression
            | "original_suffix_beta_eta" => betaEta expression
            | "original_suffix_normalized" | "original_suffix_local_reuse" => normalize expression
            | _ => pure expression
          let (expression, reuseCount) ← if solver == "original_suffix_local_reuse" then
            reuseLocalProofs expression else pure (expression, 0)
          let expression ← if solver == "original_suffix_local_reuse" then normalize expression else pure expression
          if expression.hasMVar || expression.hasSorry then throwError "incomplete proof expression"
          if !(expression.getUsedConstants.all preEnv.contains) then
            throwError "proof references a declaration absent from the original prefix"
          let type ← instantiateMVars (← inferType expression)
          if !(← isDefEq type expected) then throwError "proof type mismatch"
          if leaks ctx.mctx (← getMCtx) goal then throwError "solver assigned surrounding metavariables"
          return Json.mkObj [("status", toJson "solved"), ("term", toJson (← render expression)),
            ("target_type", toJson (← render expected)),
            ("target_present", toJson ((← getEnv).contains target)),
            ("is_proposition", toJson true), ("has_metavariable_leakage", toJson false),
            ("prefix_only_constants", toJson true),
            ("local_proof_reuse_count", toJson reuseCount),
            ("has_metavariables", toJson expression.hasMVar), ("has_sorry", toJson expression.hasSorry)]
    return Json.mkObj [("solver", toJson solver), ("elapsed_ms", toJson ((← IO.monoMsNow) - begun)),
      ("result", answer)]
  catch error =>
    return Json.mkObj [("solver", toJson solver), ("elapsed_ms", toJson ((← IO.monoMsNow) - begun)),
      ("result", Json.mkObj [("status", toJson "failed"), ("error", toJson (toString error))])]

private structure Site where
  start : Nat
  finish : Nat
  snapshot : Snapshot

private meta def runSearch (output : TSyntax `str) (proofOffset maxSites heartbeats scanMs : Nat)
    (siteOrder solvers : TSyntax `str) (cmd : TSyntax `command) : CommandElabM Unit := do
  if maxSites == 0 || maxSites > 128 || heartbeats == 0 || heartbeats > 100000 || scanMs == 0 || scanMs > 300000 then
    throwError "semantic search discovery limits are outside their hard bounds"
  if !["source", "reverse", "span_short_first"].contains siteOrder.getString then
    throwError "invalid semantic search site order"
  let previous := (← getInfoState).trees.size
  let preEnv ← getEnv
  let namespaceName ← getCurrNamespace
  let shortName ← match declarationName? cmd.raw with
    | some name => pure name
    | none => throwError "semantic search requires a named target declaration"
  let target := namespaceName ++ shortName
  if preEnv.contains target || preEnv.contains shortName then throwError "semantic search target already present"
  let opts := (← getOptions).setBool `Elab.async false
  withScope (fun s => { s with opts }) do elabCommand cmd
  let target := if (← getEnv).contains target then target else shortName
  let boundary := (cmd.raw.getPos?.getD 0).byteIdx + proofOffset
  let mut snapshots := #[]
  for tree in (← getInfoState).trees.toArray.extract previous do
    snapshots := snapshots ++ scan boundary none tree
  -- The outermost completed tactic contains all assignments from its children.
  let mut finalMCtx : MetavarContext := {}
  let mut completedSpan := 0
  for snapshot in snapshots do
    if snapshot.finish - snapshot.start > completedSpan then
      completedSpan := snapshot.finish - snapshot.start
      finalMCtx := snapshot.info.mctxAfter
  let choices := suffixes cmd.raw boundary
  let mut visited : Array (Nat × Nat) := #[]
  let mut sites : Array Site := #[]
  let mut missing := 0
  let mut repeated := 0
  let mut multipleGoals := 0
  let begun ← IO.monoMsNow
  for (a, childEnd, b) in choices do
    if visited.contains (a, b) then continue
    visited := visited.push (a, b)
    let suitable := snapshots.filter fun value => value.start == a && value.finish <= childEnd
    -- Preserve preorder on equal spans: macro-expanded inner nodes can share
    -- source coordinates but already have a changed local proof state.
    let mut selected : Option Snapshot := none
    for value in suitable do
      if selected.all (fun previous => value.finish > previous.finish) then selected := some value
    if let some snapshot := selected then
      -- Separate sibling occurrences represent repeated execution (all_goals,
      -- <;>, etc.). A proof of one occurrence cannot replace them all.
      let executions := suitable.filter fun value => value.finish == snapshot.finish
      if executions.size != 1 then
        repeated := repeated + 1
      else if snapshot.info.goalsBefore.length != 1 then
        multipleGoals := multipleGoals + 1
      else sites := sites.push ⟨a, b, snapshot⟩
    else missing := missing + 1
  if siteOrder.getString == "reverse" then sites := sites.reverse
  if siteOrder.getString == "span_short_first" then
    sites := sites.qsort fun a b =>
      a.finish - a.start < b.finish - b.start ||
      (a.finish - a.start == b.finish - b.start && (a.start < b.start || (a.start == b.start && a.finish < b.finish)))
  let solverNames := solvers.getString.splitOn "\n" |>.filter (fun value => !value.isEmpty)
  let mut records := #[]
  let mut attemptCount := 0
  let mut timeCapReached := false
  for site in sites do
    if records.size >= maxSites then break
    if (← IO.monoMsNow) - begun >= scanMs then
      timeCapReached := true
      break
    let snapshot := site.snapshot
    let mut attempts := #[]
    for solver in solverNames do
      if (← IO.monoMsNow) - begun >= scanMs then
        timeCapReached := true
        break
      attemptCount := attemptCount + 1
      attempts := attempts.push (← solve snapshot solver target preEnv finalMCtx heartbeats)
    records := records.push <| Json.mkObj [("start_byte", toJson site.start), ("end_byte", toJson site.finish),
        ("snapshot_end_byte", toJson snapshot.finish), ("goal_count", toJson snapshot.info.goalsBefore.length),
        ("snapshot_elaborator", toJson snapshot.info.elaborator.toString),
        ("execution_count", toJson (1 : Nat)),
        ("snapshot_target_present", toJson (preEnv.contains target)),
        ("captured_context_target_present", toJson (snapshot.ctx.env.contains target)), ("attempts", Json.arr attempts)]
  IO.FS.writeFile output.getString <| (Json.mkObj [("schema_version", toJson (1 : Nat)),
    ("native_environment_target_present", toJson (preEnv.contains target)),
    ("snapshot_count", toJson snapshots.size), ("suffix_count", toJson choices.size),
    ("available_site_count", toJson visited.size), ("eligible_site_count", toJson sites.size),
    ("attempted_site_count", toJson records.size), ("skipped_site_count", toJson (visited.size - records.size)),
    ("ineligible_site_count", toJson (visited.size - sites.size)),
    ("eligible_unattempted_site_count", toJson (sites.size - records.size)),
    ("duplicate_suffix_count", toJson (choices.size - visited.size)),
    ("solver_attempt_count", toJson attemptCount),
    ("available_solver_attempt_count", toJson (sites.size * solverNames.length)),
    ("skipped_solver_attempt_count", toJson (sites.size * solverNames.length - attemptCount)),
    ("site_cap_reached", toJson (records.size >= maxSites && records.size < sites.size)),
    ("scan_time_cap_reached", toJson timeCapReached),
    ("skip_reasons", Json.mkObj [("no_snapshot", toJson missing), ("repeated_execution", toJson repeated),
      ("non_single_goal", toJson multipleGoals), ("site_or_time_cap", toJson (sites.size - records.size))]),
    ("resolved_limits", Json.mkObj [("max_sites", toJson maxSites), ("scan_milliseconds", toJson scanMs),
      ("solver_heartbeats", toJson heartbeats), ("site_order", toJson siteOrder.getString)]),
    ("records", Json.arr records), ("elapsed_ms", toJson ((← IO.monoMsNow) - begun))]).compress

elab "#e6_semantic_search " output:str " after " boundary:num " sites " maxSites:num
    " heartbeats " heartbeats:num " scan_ms " scanMs:num " order " siteOrder:str
    " solvers " solvers:str " in " cmd:command : command =>
  runSearch output boundary.getNat maxSites.getNat heartbeats.getNat scanMs.getNat siteOrder solvers cmd

end E6SemanticSearch
