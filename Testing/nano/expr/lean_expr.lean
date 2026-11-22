/- Lean side of the Expr spot check (appended after the prelude and the source by run_check.sh): for every def of
the source, Lean's elaborated Expr, normalized (EXPR.md "Normalization"), printed in the S format. -/
open Lean Meta

/-- N1: a recursive def (a fuel loop, structural recursion) is read through Lean's own pre-definition value, the
RHS of its unfolding equation `f.eq_def` (`Lean.Elab.Structural.eqnInfoExt`: `f.eq_def` is `f xs = value xs`).
Read directly, so the equation is not proved here (that can take minutes for big loops); `letToHave` as Lean applies
it to def values (Elab/PreDefinition/Basic.lean) and to `eq_def`. -/
def rhsOf (n : Name) : MetaM Expr := do
  let ci ← getConstInfo n
  match Lean.Elab.Structural.eqnInfoExt.find? (← getEnv) n with
  | some info => Meta.letToHave info.value  -- as Lean does for def values and for `eq_def` (Meta/Eqns.lean)
  | none => return ci.value!

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
