/- Lean side of the Expr spot check (appended after the prelude and the source by run_check.sh): for every def of
the source, Lean's elaborated Expr, normalized (EXPR.md "Normalization"), printed in the S format. -/
open Lean Meta

/-- N1: a recursive def is read through its unfolding equation `f.eq_def` (RHS abstracted over its binders) -/
def rhsOf (n : Name) : MetaM Expr := do
  let ci ← getConstInfo n
  let some eq ← getUnfoldEqnFor? n (nonRec := false) | return ci.value!
  forallTelescope (← getConstInfo eq).type fun xs t => do
    let some (_, l, r) := t.eq? | throwError "eq_def shape"
    assert! l.getAppFn.constName? == some n
    mkLambdaFVars xs r

/-- N2: delta-unfold every matcher application, then beta-normalize (the source subset has no lambdas, so every
redex comes from an unfolded matcher) -/
partial def unfoldMatchers (e : Expr) : MetaM Expr :=
  Core.transform e (post := fun e => do
    let f := e.getAppFn
    if let some c := f.constName? then
      if e.isApp && (← isMatcher c) then
        let v ← instantiateValueLevelParams (← getConstInfo c) f.constLevels!
        return .visit (v.beta e.getAppArgs).headBeta
    return .done e)

/-- S format (EXPR.md): prefix tokens; binder names erased (N3) -/
partial def ser : Expr → String
  | .bvar i => s!"#{i}"
  | .const n ls => s!"c {n}" ++ (if ls.isEmpty then "" else ".{" ++ ",".intercalate (ls.map lvl) ++ "}")
  | .app f a => s!"@ {ser f} {ser a}"
  | .lam _ t b bi => assert! bi == .default; s!"\\ {ser t} {ser b}"
  | .forallE _ t b bi => assert! bi == .default; s!"> {ser t} {ser b}"
  | .letE _ t v b nd => s!"{if nd then "h" else "="} {ser t} {ser v} {ser b}"
  | .lit (.natVal k) => s!"n{k}"
  | .sort l => s!"s {lvl l}"
  | e => panic! s!"outside the fragment: {e}"
where lvl (l : Level) : String := match l.toNat with | some k => toString k | none => panic! s!"level {l}"

-- `srcDefs` (the source's def names, in order) is written by run_check.sh
#eval show MetaM Unit from do
  for n in srcDefs do
    let e ← Core.betaReduce (← unfoldMatchers (← instantiateMVars (← rhsOf n)))
    IO.println s!"D {n} {ser (← getConstInfo n).type} {ser e}"
