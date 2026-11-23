/- Lean side of the Expr spot check (appended after the prelude and the source by run_check.sh): for every def of
the source, Lean's elaborated Expr, normalized (EXPR.md "Normalization"), printed in the S format. -/
open Lean Meta

/-- N1: a recursive def (a fuel loop) is read through the RHS of Lean's unfolding equation `f.eq_def`, λ-abstracted
over its binders (`getUnfoldEqnFor?`): a KERNEL-CHECKED theorem `f xs = rhs` about the kernel's definition of f.
Only for the defs listed in `preDefs` (whose `eq_def` takes minutes to prove) the RHS is read from Lean's stored
pre-definition instead (`Lean.Elab.Structural.eqnInfoExt`, then `Meta.letToHave` as Lean applies it to def values
and to `eq_def`): ELABORATOR OUTPUT, not kernel-checked (EXPR.md §0). -/
def rhsOf (n : Name) : MetaM Expr := do
  let ci ← getConstInfo n
  if preDefs.contains n then
    let some info := Lean.Elab.Structural.eqnInfoExt.find? (← getEnv) n | throwError "no pre-definition: {n}"
    IO.eprintln s!"N1 via the pre-definition (not kernel-checked): {n}"
    return ← Meta.letToHave info.value
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
  | .const n ls => s!"c {strip n}" ++ (if ls.isEmpty then "" else ".{" ++ ",".intercalate (ls.map lvl) ++ "}")
  | .app f a => s!"@ {ser f} {ser a}"
  | .lam _ t b bi => assert! bi == .default; s!"\\ {ser t} {ser b}"
  | .forallE _ t b bi => assert! bi == .default; s!"> {ser t} {ser b}"
  | .letE _ t v b nd => s!"{if nd then "h" else "="} {ser t} {ser v} {ser b}"
  | .lit (.natVal k) => s!"n{k}"
  | .sort l => s!"s {lvl l}"
  | e => panic! s!"outside the fragment: {e}"
where
  /-- several sources in one file: source i is wrapped in `namespace P<i>`; the prefix is not part of the name -/
  strip (n : Name) : Name := if (n.getRoot.toString.drop 1).all Char.isDigit && n.getRoot.toString.startsWith "P"
    && n.getRoot != n then n.replacePrefix n.getRoot .anonymous else n
  lvl (l : Level) : String := match l.toNat with | some k => toString k | none => panic! s!"level {l}"

/-- the same normal form as an `ExprSpec.X` literal (for the kernel-checked comparison, Nano/Expr/CLean.lean) -/
partial def toX : Expr → String
  | .bvar i => s!"(.bv {i})"
  | .const n ls => s!"(.c \"{ser.strip n}\" [{",".intercalate (ls.map ser.lvl)}])"
  | .app f a => s!"(.app {toX f} {toX a})"
  | .lam _ t b bi => assert! bi == .default; s!"(.lam {toX t} {toX b})"
  | .forallE _ t b bi => assert! bi == .default; s!"(.pi {toX t} {toX b})"
  | .letE _ t v b nd => s!"(.lt {nd} {toX t} {toX v} {toX b})"
  | .lit (.natVal k) => s!"(.nat {k})"
  | e => panic! s!"outside the fragment: {e}"

-- `srcDefs` (the source's def names, in order) is written by run_check.sh
#eval show MetaM Unit from do
  for n in srcDefs do
    if !(← getEnv).contains n then IO.println s!"X {n}"; continue
    let e ← Core.betaReduce (← unfoldMatchers (← instantiateMVars (← rhsOf n)))
    if e.hasSorry then IO.println s!"X {n}"; continue  -- elaborated with errors
    IO.println s!"D {n} {ser (← getConstInfo n).type} {ser e}"
    if xOut then IO.println s!"X {n}\t{toX (← getConstInfo n).type}\t{toX e}"
