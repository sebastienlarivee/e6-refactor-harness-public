namespace E6GenericDictionaryCensus
open Lean Elab Command Meta

meta partial def declarationName? (stx : Syntax) : Option Name := do
  if stx.getKind == `Lean.Parser.Command.declId then return stx[0].getId
  stx.getArgs.toList.findSome? declarationName?

meta def prefixConstant (env : Environment) (n : Name) : Bool :=
  env.contains n && (n.toString.splitOn "E6GenericDictionaryCensus").length == 1

meta def prefixClosure (e : Expr) (env : Environment) : MetaM Unit := do
  let mut pending := #[e]
  let mut visited : Array FVarId := #[]
  let mut i := 0
  while i < pending.size do
    if i >= 512 then throwError "dependency cap"
    let value := pending[i]!
    i := i + 1
    if value.hasMVar || value.hasSorry || value.hasLooseBVars then throwError "incomplete dependency"
    if !(value.getUsedConstants.all (prefixConstant env)) then throwError "foreign constant"
    for id in (collectFVars {} value).fvarIds do
      if !visited.contains id then
        visited := visited.push id
        let some d := (← getLCtx).find? id | throwError "unavailable free variable"
        if d.isAuxDecl then throwError "recursive auxiliary local"
        pending := pending.push (← instantiateMVars d.type)
        if let some rhs := d.value? (allowNondep := true) then pending := pending.push (← instantiateMVars rhs)

meta def render (e : Expr) : MetaM String :=
  withOptions (fun o => o.setBool `pp.proofs true |>.setBool `pp.fullNames true
    |>.setBool `pp.deepTerms true |>.setBool `pp.universes false) do
    return (← ppExpr e).pretty 100000

meta def children (e : Expr) : Array Expr := match e with
  | .app f a => #[f,a]
  | .lam _ t b _ | .forallE _ t b _ => #[t,b]
  | .letE _ t v b _ => #[t,v,b]
  | .mdata _ b | .proj _ _ b => #[b]
  | _ => #[]

meta def sizeBounded (e : Expr) : Nat := Id.run do
  let mut stack := #[e]
  let mut count := 0
  while !stack.isEmpty && count < 1024 do
    let some last := stack.back? | break
    stack := stack.pop ++ children last
    count := count + 1
  return count

meta partial def codomainClass? (env : Environment) (type : Expr) : Option Name :=
  match type with
  | .forallE _ _ b _ => codomainClass? env b
  | .mdata _ b => codomainClass? env b
  | other => do
    let n ← other.getAppFn.constName?
    if isClass env n then some n else none

meta def maybeDictionary (env : Environment) (e : Expr) : MetaM Bool := do
  if e.hasLooseBVars || e.hasMVar then return false
  if let .proj .. := e then return true
  if let some name := e.getAppFn.constName? then
    return ((env.find? name).bind (fun ci => codomainClass? env ci.type)).isSome
  if let .fvar id := e.getAppFn then
    let some decl := (← getLCtx).find? id | return false
    return (codomainClass? env decl.type).isSome
  return false

meta def simpleArg (e : Expr) : Bool := match e with
  | .const .. | .fvar .. | .sort .. | .lit .. => true
  | _ => false

meta def shape (e : Expr) : String :=
  if e.isFVar then "existing_local"
  else if e.isConst then "direct_constant"
  else if e.getAppArgs.all simpleArg && e.getAppFn.isConst then "constant_applied_only_to_parameters"
  else "compound"

structure Entry where
  value : Expr
  type : Expr
  count : Nat
  nodes : Nat
  shape : String
  prefixSafe : Bool

meta def resourceException (err : Exception) : MetaM Bool :=
  pure err.isRuntime

meta def roundTrip (entry : Entry) (env : Environment) : MetaM Json := do
  let saved ← saveState
  try
    tryCatchRuntimeEx (do
      let tt ← render entry.type
      let vt ← render entry.value
      if tt.length > 4000 || vt.length > 4000 then throwError "render cap"
      let ts ← match Parser.runParserCategory (← getEnv) `term tt with
        | .ok s => pure s | .error err => throwError err
      let vs ← match Parser.runParserCategory (← getEnv) `term vt with
        | .ok s => pure s | .error err => throwError err
      let action : Term.TermElabM (Expr × Expr) := do
        let t ← Term.elabTermEnsuringType ts none (catchExPostpone := false)
        let v ← Term.elabTermEnsuringType vs (some entry.type) (catchExPostpone := false)
        Term.synthesizeSyntheticMVarsNoPostponing
        return (t,v)
      let (t,v) ← action.run' { errToSorry := false }
      if !(← isDefEq t entry.type) || !(← isDefEq v entry.value) then throwError "roundtrip differs"
      let t ← instantiateMVars t
      let v ← instantiateMVars v
      prefixClosure t env
      prefixClosure v env
      return Json.mkObj [("status",toJson "passed"),("type",toJson tt),("value",toJson vt),
        ("no_proving_calls",toJson true)]
    ) (fun err => do
      if ← resourceException err then throw err
      return Json.mkObj [("status",toJson "failed"),
        ("error",toJson (← err.toMessageData.toString)),("max_heartbeat",toJson err.isMaxHeartbeat)])
  finally saved.restore

meta def withRoundTripHeartbeats (action : MetaM Json) : MetaM Json := do
  Core.checkSystem "E6GenericDictionaryCensus"
  let started ← IO.getNumHeartbeats
  let limit := 1000*1000
  let result ← tryCatchRuntimeEx
    (withTheReader Core.Context
      (fun c => {c with initHeartbeats := started, maxHeartbeats := limit}) action)
    (fun err => do
      -- This handler runs after the entry's budget scope has unwound. Never
      -- turn an exhausted census budget (or cancellation) into a skipped entry.
      Core.checkSystem "E6GenericDictionaryCensus"
      if !err.isMaxHeartbeat || (← IO.getNumHeartbeats) - started <= limit then throw err
      return Json.mkObj [("status",toJson "failed"),
        ("error",toJson "dictionary roundtrip heartbeat limit reached"),
        ("max_heartbeat",toJson true),("heartbeat_limit_scope",toJson "dictionary_roundtrip")])
  Core.checkSystem "E6GenericDictionaryCensus"
  return result

meta def inspect (value : Expr) (preEnv : Environment) : MetaM Json := do
  let env ← getEnv
  let begun ← IO.monoMsNow
  let mut stack := #[value]
  let mut seen : Std.HashSet Expr := {}
  let mut index : Std.HashMap Expr Nat := {}
  let mut entries : Array Entry := #[]
  let mut nodes := 0
  let mut typeChecks := 0
  let mut errors := 0
  let mut capped := false
  while !stack.isEmpty do
    if nodes >= 30000 || typeChecks >= 2000 || entries.size >= 256 ||
        (← IO.monoMsNow) - begun >= 20000 then
      capped := true
      break
    let some e := stack.back? | break
    stack := stack.pop ++ children e
    nodes := nodes + 1
    if let some entryIndex := index[e]? then
      entries := entries.modify entryIndex fun r => {r with count := r.count+1}
    else if !seen.contains e then
      seen := seen.insert e
      if ← maybeDictionary env e then
        typeChecks := typeChecks + 1
        let found ← tryCatchRuntimeEx (do
          let t ← instantiateMVars (← inferType e)
          let t ← whnf t
          let some cls := t.getAppFn.constName? | return none
          if !isClass env cls then return none
          let safe ← tryCatchRuntimeEx (do prefixClosure e preEnv; prefixClosure t preEnv; pure true) (fun err => do
            if ← resourceException err then throw err
            pure false)
          return some (t,safe)
        ) (fun err => do
          if ← resourceException err then throw err
          pure none)
        if let some (t,safe) := found then
          index := index.insert e entries.size
          entries := entries.push ⟨e,t,1,sizeBounded e,shape e,safe⟩
        else errors := errors + 1
  entries := entries.qsort fun a b => a.count*a.nodes > b.count*b.nodes
  let mut rows := #[]
  let mut roundTrips := 0
  for entry in entries do
    if (← IO.monoMsNow) - begun >= 20000 then
      capped := true
      break
    let candidate := entry.prefixSafe && entry.count >= 4 && entry.nodes >= 12 && entry.shape == "compound"
    let trip ← if candidate && roundTrips < 4 then do
      roundTrips := roundTrips + 1
      withRoundTripHeartbeats <| roundTrip entry preEnv
      else pure <| Json.mkObj [("status",toJson "not_attempted")]
    let tt ← tryCatchRuntimeEx (render entry.type) (fun err => do
      if ← resourceException err then throw err
      pure "<render failed>")
    let vt ← tryCatchRuntimeEx (render entry.value) (fun err => do
      if ← resourceException err then throw err
      pure "<render failed>")
    rows := rows.push <| Json.mkObj [("count",toJson entry.count),("nodes",toJson entry.nodes),
      ("shape",toJson entry.shape),("prefix_safe",toJson entry.prefixSafe),
      ("type",toJson tt),("value",toJson vt),("candidate_heuristic",toJson candidate),
      ("roundtrip",trip)]
    if rows.size >= 64 then break
  let locals := (← getLCtx).foldl (fun a d => a.push <| Json.mkObj [
    ("name",toJson d.userName.toString),("auxiliary",toJson d.isAuxDecl),
    ("instance",toJson d.binderInfo.isInstImplicit)]) (#[] : Array Json)
  let elapsed ← IO.monoMsNow
  capped := capped || elapsed - begun >= 20000
  return Json.mkObj [("status",toJson "completed"),("expr_node_visits",toJson nodes),
    ("unique_exprs_seen",toJson seen.size),("dictionary_type_checks",toJson typeChecks),
    ("non_dictionary_or_type_errors",toJson errors),("unique_dictionaries",toJson entries.size),
    ("walk_cap_reached",toJson capped),("roundtrip_attempt_count",toJson roundTrips),
    ("root_parameters",Json.arr locals),("records",Json.arr rows),
    ("elapsed_ms",toJson (elapsed-begun)),("analysis_time_limit_kind",toJson "boundary_checked_cooperative"),
    ("proving_calls",toJson (0:Nat))]

meta def original (info : SourceInfo) : Bool := match info with
  | .original .. => true
  | _ => false

structure RootSnapshot where
  start : Nat
  finish : Nat
  ctx : ContextInfo
  info : TacticInfo

meta partial def rootSnapshots (boundary : Nat) (ctx? : Option ContextInfo)
    (tree : InfoTree) (fuel : Nat := 512) : Array RootSnapshot := Id.run do
  if fuel == 0 then return #[]
  match tree with
  | .hole _ => return #[]
  | .context ctx child => return rootSnapshots boundary (ctx.mergeIntoOuter? ctx?) child (fuel - 1)
  | .node info children =>
    let mut found := #[]
    if let some ctx := ctx? then
      if let .ofTacticInfo term := info then
        if term.stx.getKind == `Lean.Parser.Term.byTactic &&
            original term.stx.getHeadInfo && original term.stx.getTailInfo then
          if let some a := term.stx.getPos? then
            if let some b := term.stx.getTailPos? then
              if a.byteIdx == boundary && a.byteIdx < b.byteIdx then
                found := found.push ⟨a.byteIdx,b.byteIdx,ctx,term⟩
    for child in children do
      found := found ++ rootSnapshots boundary (info.updateContext? ctx?) child (fuel - 1)
    return found

meta partial def nearbyTerms (boundary : Nat) (tree : InfoTree) (fuel : Nat := 512) : Array Json := Id.run do
  if fuel == 0 then return #[]
  match tree with
  | .hole _ => return #[]
  | .context _ child => return nearbyTerms boundary child (fuel - 1)
  | .node info children =>
    let mut found := #[]
    if let .ofTermInfo term := info then
      if let some a := term.stx.getPos? then
        if let some b := term.stx.getTailPos? then
          if a.byteIdx <= boundary + 64 && boundary <= b.byteIdx then
            found := found.push <| Json.mkObj [("start",toJson a.byteIdx),("end",toJson b.byteIdx),
              ("kind",toJson term.stx.getKind.toString),("binder",toJson term.isBinder),
              ("head_original",toJson (original term.stx.getHeadInfo)),
              ("tail_original",toJson (original term.stx.getTailInfo)),
              ("locals",toJson (term.lctx.foldl (fun a d => a.push d.userName.toString) (#[] : Array String)))]
    for child in children do
      if found.size < 64 then found := found ++ nearbyTerms boundary child (fuel - 1)
    return found

elab "#e6_generic_dictionary_census " output:str " after " proofOffset:num " in " cmd:command : command => do
  let previous := (← getInfoState).trees.size
  let preEnv ← getEnv
  let ns ← getCurrNamespace
  let some shortName := declarationName? cmd.raw | throwError "named target required"
  let target := ns ++ shortName
  if preEnv.contains target || preEnv.contains shortName then throwError "target already in preEnv"
  let opts := (← getOptions).setBool `Elab.async false
  withScope (fun s => {s with opts}) do elabCommand cmd
  let boundary := (cmd.raw.getPos?.getD 0).byteIdx + proofOffset.getNat
  let mut snapshots := #[]
  let mut nearby := #[]
  let trees := (← getInfoState).trees.toArray.extract previous
  for tree in trees do
    snapshots := snapshots ++ rootSnapshots boundary none tree
    nearby := nearby ++ nearbyTerms boundary tree
  let orderedSnapshots := snapshots.qsort fun a b => a.finish > b.finish
  let result ← if let some snapshot := orderedSnapshots[0]? then do
    if (orderedSnapshots.filter fun s => s.finish == snapshot.finish).size != 1 ||
        snapshot.info.goalsBefore.length != 1 then
      pure <| Json.mkObj [("status",toJson "coverage_failed"),("error",toJson "ambiguous original proof-root context")]
    else
      try
        let ctx : ContextInfo := {
          env := preEnv
          fileMap := snapshot.ctx.fileMap
          mctx := snapshot.info.mctxAfter
          options := snapshot.ctx.options
          currNamespace := snapshot.ctx.currNamespace
          openDecls := snapshot.ctx.openDecls
          ngen := snapshot.ctx.ngen
          parentDecl? := snapshot.ctx.parentDecl?
          autoImplicits := snapshot.ctx.autoImplicits }
        let answer ← ctx.runMetaM {} do
          Core.withCurrHeartbeats <| withTheReader Core.Context
            (fun c => {c with maxHeartbeats := 20000*1000}) do
              let root := snapshot.info.goalsBefore.head!
              root.withContext do
                let value ← instantiateMVars (mkMVar root)
                if value.hasMVar || value.hasSorry || value.hasLooseBVars then throwError "unresolved original root expression"
                inspect value preEnv
        pure <| Json.mkObj [("schema_version",toJson (2:Nat)),("status",toJson "completed"),
          ("root_context_kind",toJson "original_by_tactic_info"),("root_start_byte",toJson snapshot.start),
          ("root_end_byte",toJson snapshot.finish),("target_absent_from_analysis_env",toJson true),
          ("local_instance_context",toJson "captured_original_root_goal"),
          ("opened_proof_lambdas",toJson false),("analysis",answer)]
      catch err =>
        pure <| Json.mkObj [("status",toJson "analysis_failed"),("error",toJson (← err.toMessageData.toString))]
    else
      pure <| Json.mkObj [("status",toJson "coverage_failed"),("error",toJson "original whole-by TacticInfo unavailable"),
        ("boundary",toJson boundary),("new_info_trees",toJson trees.size),("nearby_terms",Json.arr nearby)]
  IO.FS.writeFile output.getString result.compress

end E6GenericDictionaryCensus
