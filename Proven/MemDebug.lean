import Lean
open Lean Meta Elab Tactic

/-- run `tac`, then find minimal subterms of the proof that the kernel rejects -/
partial def kfindAux (nm : Name) (e : Expr) (depth : Nat) : MetaM Bool := do
  -- returns true if a failure was found and reported at or below e
  let ok ← (do
    let ty ← inferType e
    unless ← isProp ty do return true
    let r ← Closure.mkValueTypeClosure ty e (zetaDelta := true)
    let decl := Declaration.thmDecl { name := nm ++ `_kfind_tmp, levelParams := r.levelParams.toList, type := r.type, value := r.value }
    match (← getEnv).addDeclCore 0 decl none with
    | Except.ok _ => return true
    | Except.error ex => do
      if depth == 0 then logInfo m!"top fails: {ex.toMessageData (← getOptions)}"
      return false)
  if ok then return false
  -- recurse into children
  let found ← match e with
    | .app .. => do
      let mut f := false
      for a in e.getAppArgs do
        if ← kfindAux nm a (depth+1) then f := true
      if !f then
        if ← kfindAux nm e.getAppFn (depth+1) then f := true
      pure f
    | .lam .. => lambdaTelescope e fun xs b => do
        let r ← kfindAux nm b (depth+1)
        pure r
    | .letE .. => lambdaLetTelescope e fun _ b => kfindAux nm b (depth+1)
    | .mdata _ b => kfindAux nm b (depth+1)
    | _ => pure false
  if !found then
    let ty ← inferType e
    logInfo m!"MINIMAL failing (depth {depth}, size {e.approxDepth}): {ty}\n----\n{e}"
  return true

elab "kfind " t:tacticSeq : tactic => do
  let g ← getMainGoal
  evalTactic t
  let e ← instantiateMVars (mkMVar g)
  g.withContext do
    let nm := (← Term.getDeclName?).getD `anon
    let _ ← kfindAux nm e 0
