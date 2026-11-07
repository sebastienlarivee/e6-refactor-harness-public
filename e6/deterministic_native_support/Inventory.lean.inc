namespace E6NativeInventory
open Lean Elab Command Meta

private structure ScanState where
  nodes : Nat := 0
  terms : Array Json := #[]
  termFailures : Nat := 0
  deriving Inhabited

private meta def original (info : SourceInfo) : Bool := match info with
  | .original .. => true
  | _ => false

private meta def span? (stx : Syntax) : Option (Nat × Nat) := do
  let first ← stx.getPos?
  let last ← stx.getTailPos?
  if first.byteIdx < last.byteIdx && original stx.getHeadInfo && original stx.getTailInfo then
    return (first.byteIdx, last.byteIdx)
  else none

private meta def seqKind (stx : Syntax) : Bool :=
  stx.getKind == `Lean.Parser.Tactic.tacticSeq1Indented ||
  stx.getKind == `Lean.Parser.Tactic.tacticSeqBracketed

private meta def childSpans (stx : Syntax) : Array Json := Id.run do
  let mut result := #[]
  let items := (if stx.getKind == `Lean.Parser.Tactic.tacticSeqBracketed then stx[1] else stx[0]).getArgs
  for i in [:items.size] do
    if i % 2 == 0 then
      if let some (a, b) := span? items[i]! then
        result := result.push <| Json.mkObj [
          ("start_byte", toJson a), ("end_byte", toJson b),
          ("kind", toJson items[i]!.getKind.toString)]
  return result

private meta partial def syntaxInventory (stx : Syntax) (fuel : Nat := 512) : Array Json := Id.run do
  if fuel == 0 then return #[]
  let mut result := #[]
  if let some (a, b) := span? stx then
    if seqKind stx then
      result := result.push <| Json.mkObj [
        ("start_byte", toJson a), ("end_byte", toJson b),
        ("kind", toJson stx.getKind.toString), ("children", Json.arr (childSpans stx))]
  for child in stx.getArgs do
    result := result ++ syntaxInventory child (fuel - 1)
  return result

private meta def render (expression : Expr) (explicit : Bool := false) : MetaM String := do
  withOptions (fun opts => opts.setBool `pp.explicit explicit |>.setBool `pp.instances explicit
      |>.setBool `pp.universes false |>.setBool `pp.proofs true |>.setBool `pp.mvars true
      |>.setBool `pp.deepTerms true) do
    return (← ppExpr expression).pretty

-- Preserve declaration binder names. forallTelescope's fresh local names are
-- useful internally but are not necessarily accepted by the surface function.
private meta partial def binderNames : Expr → Array Name
  | .forallE name _ body _ => #[name] ++ binderNames body
  | _ => #[]

private meta def freeVariableNames (expression : Expr) : MetaM (Array String) := do
  let mut result := #[]
  for id in (collectFVars {} expression).fvarIds do
    let decl ← id.getDecl
    result := result.push decl.userName.toString
  return result

private meta def termRecord (ctx : ContextInfo) (term : TermInfo) : IO (Option Json) := do
  let some (a, b) := span? term.stx | return none
  if term.isBinder then return none
  ctx.runMetaM {} do
    withLCtx term.lctx #[] do
      let expression ← instantiateMVars term.expr
      if expression.hasMVar || !(expression.isApp || expression.isFVar || expression.isConst) then return none
      let type ← instantiateMVars (← inferType expression)
      if type.hasMVar then return none
      let fn := expression.getAppFn
      let args := expression.getAppArgs
      let mut application := #[]
      if fn.isConst then
        let fnType ← inferType fn
        let names := binderNames fnType
        application ← forallTelescope fnType fun binders _ => do
          let mut result := #[]
          for i in [:min args.size binders.size] do
            let decl ← binders[i]!.fvarId!.getDecl
            let name := names[i]?.getD Name.anonymous
            let argType ← instantiateMVars (← inferType args[i]!)
            let normalized ← if (← whnf argType).isSort then render (← whnf args[i]!) else pure ""
            let mut inferable := false
            for j in [i + 1:min args.size binders.size] do
              let later ← binders[j]!.fvarId!.getDecl
              if later.binderInfo.isExplicit && later.type.containsFVar binders[i]!.fvarId! then
                inferable := true
            result := result.push <| Json.mkObj [
              ("name", toJson name.toString),
              ("name_is_accessible", toJson (!name.isAnonymous && !name.hasMacroScopes)),
              ("instance", toJson decl.binderInfo.isInstImplicit),
              ("explicit", toJson decl.binderInfo.isExplicit),
              ("inferable_from_explicit", toJson inferable),
              ("value", toJson (← render args[i]!)),
              ("type", toJson (← render argType)),
              ("whnf_type_value", toJson normalized), ("index", toJson i)]
          return result
      let mut headEnd := a
      if term.stx.getKind == `Lean.Parser.Term.app then
        if let some tail := term.stx[0].getTailPos? then headEnd := tail.byteIdx
      let expected ← match term.expectedType? with
        | some value => render (← instantiateMVars value)
        | none => pure ""
      return some <| Json.mkObj [
        ("start_byte", toJson a), ("end_byte", toJson b), ("head_end_byte", toJson headEnd),
        ("kind", toJson term.stx.getKind.toString),
        ("is_constant", toJson expression.isConst),
        ("constant_name", toJson (expression.constName?.getD Name.anonymous).toString),
        ("head_constant", toJson (fn.constName?.getD Name.anonymous).toString),
        ("free_variables", toJson (← freeVariableNames expression)),
        ("type_free_variables", toJson (← freeVariableNames type)),
        ("normal", toJson (← render expression)), ("explicit", toJson (← render expression true)),
        ("type", toJson (← render type)), ("whnf_type", toJson (← render (← whnf type))),
        ("expected_type", toJson expected), ("application", Json.arr application)]

private meta partial def scanTree (boundary : Nat) (ctx? : Option ContextInfo)
    (tree : InfoTree) : StateT ScanState IO Unit := do
  if (← get).nodes >= 50000 then return
  modify fun s => { s with nodes := s.nodes + 1 }
  match tree with
  | .context ctx child => scanTree boundary (ctx.mergeIntoOuter? ctx?) child
  | .hole _ => pure ()
  | .node info children =>
    if let .ofTermInfo term := info then
      if let some ctx := ctx? then
        if let some (a, _) := span? term.stx then
          if boundary <= a && (← get).terms.size < 4096 then
            try
              if let some record ← termRecord ctx term then
                modify fun s => { s with terms := s.terms.push record }
            catch _ => modify fun s => { s with termFailures := s.termFailures + 1 }
    for child in children do scanTree boundary ctx? child

private meta partial def declarationName? (stx : Syntax) : Option Lean.Name := do
  if stx.getKind == `Lean.Parser.Command.declId then return stx[0].getId
  stx.getArgs.toList.findSome? declarationName?

private meta def runInventory (output : TSyntax `str) (cmd : TSyntax `command)
    (proofOffset : Nat) : CommandElabM Unit := do
  let oldTrees := (← getInfoState).trees.size
  let preEnv ← getEnv
  let namespaceName ← getCurrNamespace
  let shortName := declarationName? cmd.raw
  let opts := (← getOptions).setBool `Elab.async false
  withScope (fun s => { s with opts }) do elabCommand cmd
  let env ← getEnv
  let forbidden := shortName.map fun name =>
    let full := namespaceName ++ name
    if env.contains full then full else name
  if forbidden.any preEnv.contains then throwError "native inventory target already present before command"
  let boundary := (cmd.raw.getPos?.getD 0).byteIdx + proofOffset
  let trees := (← getInfoState).trees.toArray.extract oldTrees
  let visit : StateT ScanState IO Unit := do
    for tree in trees do scanTree boundary none tree
  let (_, state) ← visit.run {}
  IO.FS.writeFile output.getString <| (Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("nodes", toJson state.nodes),
    ("native_environment", toJson "before_target_command"),
    ("native_environment_target_present", toJson (forbidden.any preEnv.contains)),
    ("proof_start_byte", toJson boundary),
    ("sequences", Json.arr (syntaxInventory cmd.raw)),
    ("terms", Json.arr state.terms), ("term_failures", toJson state.termFailures)]).compress

elab "#e6_native_inventory " output:str " after " boundary:num " in " cmd:command : command =>
  runInventory output cmd boundary.getNat

end E6NativeInventory
