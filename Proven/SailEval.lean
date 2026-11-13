/-
`sail_eval`: call-by-value symbolic executor for Sail's `EStateM` programs.

Goal `m s = rhs`.  Evaluates `m s` in program order: binds left to right, `if` by deciding the
condition, `match` by iota, calls by unfolding, leaves by `simp` with the supplied lemmas.
Plain `simp` normalises continuations before their argument is known, which is hopeless on the
27k-line decoder; this never looks at code that does not run.  Fails loudly where it gets stuck.
-/
import Lean
open Lean Meta Elab Tactic

namespace SailEval
universe u

theorem bind_ok {ε σ α β : Type u} {x : EStateM ε σ α} (f : α → EStateM ε σ β) {s s' : σ} {a : α}
    (h : x s = .ok a s') : (x >>= f) s = f a s' := by
  show EStateM.bind x f s = _
  unfold EStateM.bind; rw [h]

theorem bind_err {ε σ α β : Type u} {x : EStateM ε σ α} (f : α → EStateM ε σ β) {s s' : σ} {e : ε}
    (h : x s = .error e s') : (x >>= f) s = .error e s' := by
  show EStateM.bind x f s = _
  unfold EStateM.bind; rw [h]

/-- trace output goes straight to a file: Lean captures stderr until the command ends -/
def traceLine (s : String) : IO Unit :=
  IO.FS.withFile "/tmp/sail_eval.trace" .append fun h => h.putStrLn s

register_option sail_eval.trace : Bool := { defValue := false, descr := "trace sail_eval steps" }
register_option sail_eval.maxSteps : Nat := { defValue := 200000, descr := "sail_eval fuel" }

structure Ctx where
  /-- default simp set + user lemmas: conditions and `match` discriminants -/
  simp : Simp.Context
  /-- user lemmas only: tried at the root of every call (summaries, register reads) -/
  simpRoot : Simp.Context
  simprocs : Simp.SimprocsArray
  /-- constants never unfolded (treated as stuck unless a simp lemma rewrites them) -/
  noUnfold : NameSet := {}

abbrev M := ReaderT Ctx <| StateRefT Nat MetaM

def tick (what : String) (e : Expr) : M Unit := do
  modify (· + 1)
  if (← get) > sail_eval.maxSteps.get (← getOptions) then throwError "sail_eval: out of fuel"
  if sail_eval.trace.get (← getOptions) then
    traceLine s!"[{← get}] {what}: {e.getAppFn}"

/-- weak-head normalise a closed term with the kernel (defeq, so no proof needed) -/
def kernelWhnf? (e : Expr) : MetaM (Option Expr) := do
  if e.hasFVar || e.hasMVar then return none
  match Lean.Kernel.whnf (← getEnv) {} e with
  | .ok r => return some r
  | .error _ => return none

/-- simp pre-pass: evaluate closed `Bool` terms and closed decidable `Prop`s with the kernel
(handles `_get_Mstatus_MIE 0x..#64 == 1#1`, enum `==`, ... that simp lemmas cannot). -/
def closedPre : Simp.Simproc := fun e => do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars || e.isConstOf ``true || e.isConstOf ``false
    || e.isConstOf ``True || e.isConstOf ``False then return .continue
  let ty ← inferType e
  if sail_eval.trace.get (← getOptions) then traceLine s!"closedPre {e.getAppFn} : {ty.getAppFn}"
  -- the replacement `r` comes with a `decide` proof of `e = r`: the kernel then evaluates both
  -- sides (fast, GMP) instead of a lazy-delta defeq check (which can recurse deeply on `BitVec`)
  let byDecide (r : Expr) : MetaM Simp.Step := do
    return .done { expr := r, proof? := ← mkDecideProof (← mkEq e r) }
  if ty.isConstOf ``Bool then
    if let some r ← kernelWhnf? e then
      if r.isConstOf ``true || r.isConstOf ``false then return ← byDecide r
    return .continue
  if ty.isConstOf ``Nat then
    if e.nat?.isSome || e.rawNatLit?.isSome then return .continue
    if let some (.lit (.natVal n)) ← kernelWhnf? e then return ← byDecide (mkNatLit n)
    return .continue
  if ty.isConstOf ``Int then
    if e.int?.isSome then return .continue
    if let some r ← kernelWhnf? e then
      match r with
      | .app (.const ``Int.ofNat _) (.lit (.natVal n)) => return ← byDecide (toExpr (n : Int))
      | .app (.const ``Int.negSucc _) (.lit (.natVal n)) => return ← byDecide (toExpr (Int.negSucc n))
      | _ => pure ()
    return .continue
  if ty.isAppOfArity ``BitVec 1 then
    if e.isAppOfArity ``BitVec.ofNat 2 && (e.getArg! 1).nat?.isSome then return .continue
    if e.isAppOfArity ``OfNat.ofNat 3 then return .continue
    let some (.lit (.natVal w)) ← kernelWhnf? ty.appArg! | return .continue
    if let some (.lit (.natVal n)) ← kernelWhnf? (mkApp2 (mkConst ``BitVec.toNat) ty.appArg! e) then
      return ← byDecide (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit n))
    return .continue
  unless ty.isProp do return .continue
  let some inst ← (try synthInstance? (mkApp (mkConst ``Decidable) e) catch _ => pure none) | return .continue
  let some r ← kernelWhnf? (mkApp2 (mkConst ``Decidable.decide) e inst) | return .continue
  if r.isConstOf ``true then
    let pf ← mkEqTrue (mkApp3 (mkConst ``of_decide_eq_true) e inst (← mkEqRefl (mkConst ``true)))
    return .done { expr := mkConst ``True, proof? := pf }
  if r.isConstOf ``false then
    let pf ← mkEqFalse (mkApp3 (mkConst ``of_decide_eq_false) e inst (← mkEqRefl (mkConst ``false)))
    return .done { expr := mkConst ``False, proof? := pf }
  return .continue

def simpE (e : Expr) (root := false) : M Simp.Result := do
  let c ← read
  let m := Simp.mkDefaultMethodsCore c.simprocs
  let m := { m with pre := fun e => do
    match ← closedPre e with
    | .continue none => m.pre e
    | r => return r }
  let (r, _) ← tryCatchRuntimeEx (Simp.main e (if root then c.simpRoot else c.simp) (methods := m)) fun ex =>
    throwError "sail_eval: simp failed on{indentExpr e}\n{ex.toMessageData}"
  return r

/-- prove `p` by `omega` from the local context, if it can -/
def omega? (p : Expr) : MetaM (Option Expr) := do
  let g ← mkFreshExprSyntheticOpaqueMVar p
  try
    let gs ← Term.TermElabM.run' (Tactic.run g.mvarId! (evalTactic (← `(tactic| omega))))
    unless gs.isEmpty do return none
    return some (← instantiateMVars g)
  catch _ => return none

/-- decide a proposition: returns `(true, proof of c)` or `(false, proof of ¬c)` -/
def decideProp (c inst : Expr) : M (Bool × Expr) := do
  if let some r ← kernelWhnf? (mkApp2 (mkConst ``Decidable.decide) c inst) then
    if r.isConstOf ``true then
      return (true, mkApp3 (mkConst ``of_decide_eq_true) c inst (← mkEqRefl (mkConst ``true)))
    if r.isConstOf ``false then
      return (false, mkApp3 (mkConst ``of_decide_eq_false) c inst (← mkEqRefl (mkConst ``false)))
  let r ← simpE c
  if r.expr.isTrue then return (true, ← mkOfEqTrue (← r.getProof))
  if r.expr.isFalse then return (false, ← mkAppM ``of_eq_false #[← r.getProof])
  -- linear arithmetic over the goal's hypotheses
  if let some p ← omega? r.expr then return (true, ← mkAppM ``Eq.mpr #[← r.getProof, p])
  if let some p ← omega? (mkNot r.expr) then
    return (false, ← mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[mkConst ``Not, ← r.getProof], p])
  throwError "sail_eval: cannot decide condition{indentExpr c}\nsimplified to{indentExpr r.expr}"

def isEStateM (m : Expr) : MetaM Bool := do
  let m ← whnfR m
  return m.getAppFn.isConstOf ``EStateM

/-- unfold a recursive definition with its unfolding equation -/
def unfoldEqn? (e : Expr) : MetaM (Option Simp.Result) := do
  let f := e.getAppFn
  let .const n _ := f | return none
  let some thmName ← getUnfoldEqnFor? n (nonRec := false) | return none
  let thm ← mkConstWithFreshMVarLevels thmName
  let (ms, _, ty) ← forallMetaTelescope (← inferType thm)
  let some (_, lhs, rhs) := ty.eq? | return none
  let k := lhs.getAppNumArgs
  let args := e.getAppArgs
  if args.size < k then return none
  unless ← isDefEq lhs (mkAppN f args[:k]) do return none
  let mut pf := mkAppN thm ms
  let mut rhs ← instantiateMVars rhs
  for a in args[k:] do
    pf ← mkCongrFun pf a
    rhs := mkApp rhs a
  return some { expr := rhs.headBeta, proof? := ← instantiateMVars pf }

def stuck (e : Expr) : M Simp.Result := do
  let s := toString (← ppExpr e)
  throwError "sail_eval: stuck at\n{(s.take 3000).toString}"

def isResult (e : Expr) : Option Bool :=
  if e.isAppOf ``EStateM.Result.ok then some true
  else if e.isAppOf ``EStateM.Result.error then some false else none

def trans (r₁ r₂ : Simp.Result) : MetaM Simp.Result := r₁.mkEqTrans r₂

def isCtorApp (e : Expr) : MetaM Bool := do
  if e.isRawNatLit || e.nat?.isSome then return true
  let .const n _ := e.getAppFn | return false
  return (← getEnv).isConstructor n

/-- normalise a pure (non-monadic) term towards constructor form: kernel whnf if closed, else
simp, else unfold the head one step and retry (bounded). -/
partial def normPure (d : Expr) (fuel : Nat := 16) : M Simp.Result := do
  if ← isCtorApp d then return { expr := d }
  if let some d' ← kernelWhnf? d then
    return { expr := d', proof? := ← mkExpectedTypeHint (← mkEqRefl d') (← mkEq d d') }
  let r ← simpE d
  if r.expr != d then
    return ← trans r (← normPure r.expr (fuel - 1))
  if fuel == 0 then return r
  if d.isAppOf ``ite || d.isAppOf ``dite then
    let args := d.getAppArgs
    let (b, h) ← decideProp args[1]! args[2]!
    let pf ← mkAppOptM (if b then (if d.isAppOf ``ite then ``if_pos else ``dif_pos)
      else (if d.isAppOf ``ite then ``if_neg else ``dif_neg)) #[args[1]!, args[2]!, h, args[0]!, args[3]!, args[4]!]
    let br := if b then args[3]! else args[4]!
    let d' := (if d.isAppOf ``ite then br else mkApp br h).headBeta
    return ← trans { expr := d', proof? := pf } (← normPure d' (fuel - 1))
  let d' ← withReducible (whnfCore d)
  if d' != d then
    return ← trans { expr := d', proof? := ← mkExpectedTypeHint (← mkEqRefl d') (← mkEq d d') }
      (← normPure d' (fuel - 1))
  if let .const n _ := d.getAppFn then
    if (← read).noUnfold.contains n then return r
  if let some r ← unfoldEqn? d then return ← trans r (← normPure r.expr (fuel - 1))
  if let some d' ← delta? d then
    return ← trans { expr := d', proof? := ← mkExpectedTypeHint (← mkEqRefl d') (← mkEq d d') }
      (← normPure d'.headBeta (fuel - 1))
  return r

mutual
/-- evaluate `e : EStateM.Result ε σ α` to `.ok a s'` / `.error e s'` -/
partial def eval (e : Expr) : M Simp.Result := do
  let r ← evalCore e
  match r.proof? with
  | none => return r
  | some p => return { r with proof? := ← mkExpectedTypeHint p (← mkEq e r.expr) }

partial def evalCore (e : Expr) : M Simp.Result := do
  -- `headBeta` does not re-reduce a head that becomes a lambda after substitution: iterate
  let mut e := e
  while e.isHeadBetaTarget do e := e.headBeta
  if (isResult e).isSome then return { expr := e }
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .mdata _ b => eval (mkAppN b args)
  | .letE _ _ v b _ => eval (mkAppN (b.instantiate1 v) args)
  | .proj .. =>
    let fn' ← whnfCore fn
    if fn' == fn then stuck e else eval (mkAppN fn' args)
  | .const n _ =>
    if n == ``Bind.bind && args.size == 7 && (← isEStateM args[0]!) then
      tick "bind" args[4]!
      let x := args[4]!; let f := args[5]!; let s := args[6]!
      let r ← eval (mkApp x s)
      match isResult r.expr with
      | some true =>
        let pf ← mkAppOptM ``bind_ok #[none, none, none, none, x, f, s, none, none, ← r.getProof]
        let a := r.expr.getAppArgs[3]!; let s' := r.expr.getAppArgs[4]!
        trans { expr := mkApp2 f a s', proof? := pf } (← eval (mkApp2 f a s'))
      | some false =>
        let pf ← mkAppOptM ``bind_err #[none, none, none, none, x, f, s, none, none, ← r.getProof]
        let er := r.expr.getAppArgs[3]!; let s' := r.expr.getAppArgs[4]!
        let ty ← inferType e
        let res := mkAppN (mkConst ``EStateM.Result.error ty.getAppFn.constLevels!) (ty.getAppArgs ++ #[er, s'])
        return { expr := res, proof? := pf }
      | none => stuck r.expr
    else if n == ``ite && args.size ≥ 5 then
      tick "ite" args[1]!
      let (b, h) ← decideProp args[1]! args[2]!
      let mut pf ← mkAppOptM (if b then ``if_pos else ``if_neg)
        #[args[1]!, args[2]!, h, args[0]!, args[3]!, args[4]!]
      for a in args[5:] do pf ← mkCongrFun pf a
      let e' := mkAppN (if b then args[3]! else args[4]!) args[5:]
      trans { expr := e', proof? := pf } (← eval e')
    else if n == ``dite && args.size ≥ 5 then
      tick "dite" args[1]!
      let (b, h) ← decideProp args[1]! args[2]!
      let mut pf ← mkAppOptM (if b then ``dif_pos else ``dif_neg)
        #[args[1]!, args[2]!, h, args[0]!, args[3]!, args[4]!]
      for a in args[5:] do pf ← mkCongrFun pf a
      let e' := mkAppN (mkApp (if b then args[3]! else args[4]!) h) args[5:]
      trans { expr := e', proof? := pf } (← eval e')
    else if let some info ← getMatcherInfo? n then
      tick "match" (mkAppN fn (args.extract info.getFirstDiscrPos (info.getFirstDiscrPos + info.numDiscrs)))
      -- reducible transparency only: default `whnf` on e.g. 64-bit `BitVec` arithmetic in a
      -- discriminant can take forever / blow the recursion limit
      match ← withReducible (reduceMatcher? e) with
      | .reduced e' => eval e'
      | _ =>
        -- normalise discriminants: kernel whnf if closed, `eval` if a monadic result, else simp
        let mut args' := args
        let mut pf? : Option Expr := none
        let mut changed := false
        for i in [info.getFirstDiscrPos : info.getFirstDiscrPos + info.numDiscrs] do
          let d := args[i]!
          let isRes := (← whnfR (← inferType d)).isAppOf ``EStateM.Result
          let r ← if isRes then eval d else normPure d
          if r.expr != d then
            changed := true
            let ctxLam ← withLocalDeclD `d (← inferType d) fun x =>
              mkLambdaFVars #[x] (mkAppN fn (args'.set! i x))
            let step ← mkCongrArg ctxLam (← r.getProof)
            args' := args'.set! i r.expr
            pf? := some (← match pf? with | none => pure step | some p => mkEqTrans p step)
        unless changed do return ← stuck e
        let e' := mkAppN fn args'
        match ← withReducible (reduceMatcher? e') with
        | .reduced e'' => trans { expr := e', proof? := pf? } (← eval e'')
        | _ => match ← reduceMatcher? e' with
          | .reduced e'' => trans { expr := e', proof? := pf? } (← eval e'')
          | _ => stuck e'
    else
      tick "call" (mkAppN fn (args.extract 0 (args.size - 1)))
      -- 1. user lemma / simp at the root
      let r ← simpE e (root := true)
      if r.expr != e then return ← trans r (← eval r.expr)
      if (← read).noUnfold.contains n then return ← stuck e
      -- 2. unfold
      if let some r ← unfoldEqn? e then return ← trans r (← eval r.expr)
      if let some e' ← withDefault (unfoldDefinition? e) then return ← eval e'
      if let some e' ← delta? e then return ← eval e'
      stuck e
  | _ => stuck e
end

syntax (name := sailEvalStx) "sail_eval" (" frozen" "[" ident,* "]")? (Parser.Tactic.simpArgs)? : tactic

@[tactic sailEvalStx] def evalSailEval : Tactic := fun stx => do
  -- map lookups are leaves: a missing hypothesis should show up as `s.regs.get? r`, not its guts
  let base : NameSet := [``Std.ExtDHashMap.get?, ``Std.ExtHashMap.get?, ``GetElem?.getElem?,
    ``Std.ExtDHashMap.contains].foldl (·.insert ·) {}
  let opq : NameSet ← match stx[1].getArgs with
    | #[_, _, ids, _] => ids.getSepArgs.foldlM (fun acc i => do
        return acc.insert (← realizeGlobalConstNoOverloadWithInfo i)) base
    | _ => pure base
  -- map updates are always unfolded by lookups
  let dflt ← `(Parser.Tactic.simpArgs| [Std.ExtDHashMap.get?_insert, Std.ExtHashMap.getElem?_insert])
  let user := if stx[2].getNumArgs == 0 then #[] else stx[2][0][1].getSepArgs
  let items := dflt.raw[1].getSepArgs ++ user
  let args := mkNullNode #[mkAtom "[", Syntax.mkSep items (mkAtom ","), mkAtom "]"]
  let mk (only : Bool) := mkNode ``Parser.Tactic.simp
    #[mkAtom "simp", mkNullNode, mkNullNode, (if only then mkNullNode #[mkAtom "only"] else mkNullNode),
      args, mkNullNode]
  let { ctx, simprocs, .. } ← withMainContext <| mkSimpContext (mk false) (eraseLocal := false)
  let { ctx := ctxRoot, .. } ← withMainContext <| mkSimpContext (mk true) (eraseLocal := false)
  withMainContext do
    let g ← getMainGoal
    let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).consumeMData.eq? | throwError "sail_eval: goal is not an equation"
    let (r, steps) ← (eval lhs).run { simp := ctx, simpRoot := ctxRoot, simprocs, noUnfold := opq } |>.run 0
    if sail_eval.trace.get (← getOptions) then logInfo m!"sail_eval: {steps} steps"
    let gNew ← mkFreshExprSyntheticOpaqueMVar (← mkEq r.expr rhs) (← g.getTag)
    g.assign (← mkEqTrans (← r.getProof) gNew)
    replaceMainGoal [gNew.mvarId!]
    -- reducible only: a default-transparency `rfl` on symbolic `BitVec` arithmetic can run away
    try evalTactic (← `(tactic| with_reducible rfl)) catch _ => pure ()

end SailEval
