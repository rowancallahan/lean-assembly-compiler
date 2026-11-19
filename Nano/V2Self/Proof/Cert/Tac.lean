/- Nano/V2Self/Proof/Cert/Tac: the syntax-directed tactic of the meaning certificate.  `den` walks a `DenT`/`DenK` goal
by the node's constructor and the shape of the Lean value; `den_let` handles `let` / tuple patterns, `den_call` picks
the generated lemma `Cert.call_<i>` of the callee. -/
import Lean
import Nano.V2Self.Proof.Cert.Rules

namespace Cert
open Lean Meta Elab Tactic

/-- the elements of a list expression with a concrete spine -/
partial def listSpine (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  let e ← whnf e
  match_expr e with
  | List.cons _ h t => listSpine t (acc.push h)
  | List.nil _ => pure acc
  | _ => throwError "listSpine: no concrete spine{indentExpr e}"

/-- the components of the tuple `e : T` bound by a tuple pattern whose variables have the types `tys` (in order):
a component whose type is the next variable's type is that variable, otherwise it is a pair and is split -/
partial def tupleArgs (e T : Expr) (tys : List Expr) : MetaM (Array Expr × List Expr) := do
  match tys with
  | [] => throwError "tupleArgs: too few pattern variables"
  | ty :: rest =>
    if ← isDefEq T ty then return (#[e], rest)
    let T' ← whnf T
    unless T'.isAppOfArity ``Prod 2 do throwError "tupleArgs: a product expected{indentExpr T}"
    let (l, tys1) ← tupleArgs (← mkAppM ``Prod.fst #[e]) T'.getAppArgs[0]! tys
    let (r, tys2) ← tupleArgs (← mkAppM ``Prod.snd #[e]) T'.getAppArgs[1]! tys1
    return (l ++ r, tys2)

private def lamDomains : Expr → List Expr
  | .lam _ d b _ => d :: lamDomains b
  | _ => []

/-- a `letE` node against `let y := a; B` or `match a with | (y₁, …) => B`: rule `letE` with `a`, `fun y => B` given
explicitly; leaves the value goal and the body goal (the new variable introduced, the slots written) -/
elab "den_let" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let nm := tgt.getAppFn.constName?.getD .anonymous
  unless nm == ``DenT || nm == ``DenK do throwError "den_let: not a Den goal"
  let t := tgt.getAppArgs.back!.consumeMData
  let (a, B, yn, isMatch) ← match t with
    | .letE n ty v b _ => pure (v, Expr.lam n ty b .default, n, false)
    | _ => do
      let some m ← matchMatcherApp? t | throwError "den_let: the value is neither a let nor a match"
      unless m.discrs.size == 1 && m.alts.size == 1 do throwError "den_let: unexpected match"
      let d := m.discrs[0]!
      -- `B a` must be SYNTACTICALLY the goal's value after beta: a defeq check through the match would unfold `a`
      let B ← withLocalDeclD `y (← inferType d) fun y => mkLambdaFVars #[y] ({ m with discrs := #[y] }.toExpr)
      pure (d, B, `y, true)
  let lem := mkIdent (if nm == ``DenT then ``DenT.letE else ``DenK.letE)
  let aS ← Term.exprToSyntax a
  let bS ← Term.exprToSyntax B
  evalTactic (← `(tactic| refine $lem $aS $bS ?_ rfl ?_))
  let [g1, g2] ← getGoals | throwError "den_let: two goals expected"
  let (_, g2) ← g2.intro yn
  setGoals [g2]
  -- the new environment as a literal list (an unreduced `setSlots` chain makes later lookups exponential)
  let ex ← instantiateMVars (← g2.getType)
  let body := ex.getAppArgs[1]!.bindingBody!
  let lhs := body.getAppArgs[0]!.getAppArgs[1]!
  unless lhs.isAppOfArity ``NanoMain.setSlots 3 do throwError "den_let: setSlots expected{indentExpr lhs}"
  let envE ← g2.withContext (listSpine lhs.getAppArgs[0]!)
  let sE ← whnf lhs.getAppArgs[1]!
  let some sN := sE.nat? <|> sE.rawNatLit? | throwError "den_let: the slot is not a literal"
  let vs ← g2.withContext (listSpine lhs.getAppArgs[2]!)
  unless sN + vs.size ≤ envE.size do throwError "den_let: slots out of range"
  let env' ← mkListLit (mkConst ``NanoMain.W) ((envE.extract 0 sN ++ vs ++ envE.extract (sN + vs.size) envE.size).toList)
  let eS ← g2.withContext (Term.exprToSyntax env')
  evalTactic (← `(tactic| refine ⟨$eS, rfl, ?_⟩))
  let g3 ← getMainGoal
  let tgt3 ← instantiateMVars (← g3.getType)
  let args := tgt3.getAppArgs
  -- the body's value: beta, then the tuple pattern on the new variable becomes projections
  let mut t3 := args.back!.headBeta
  if isMatch then
    let some m3 ← g3.withContext (matchMatcherApp? t3) | throwError "den_let: match expected"
    -- instantiate the alternative by hand (`reduceMatcher?` would go on reducing a `match` at the head of the body)
    let d := m3.discrs[0]!
    let alt := m3.alts[0]!
    let (as, rest) ← g3.withContext (do tupleArgs d (← inferType d) (lamDomains alt |>.take m3.altNumParams[0]!))
    unless rest.isEmpty do throwError "den_let: pattern variables left over"
    t3 := (mkAppN alt as).headBeta
  let g3 ← g3.replaceTargetDefEq (mkAppN tgt3.getAppFn (args.pop.push t3))
  setGoals [g1, g3]

/-- the Lean value is a loop def unfolded by `eq_def` at fuel `0` (`den_match 0`) or `n + 1` (`den_match 1`): pick the
arm by hand (variable patterns only), keeping `let`s and inner matches -/
elab "den_match" k:num : tactic => withMainContext do
  let g ← getMainGoal
  let tgt := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let args := tgt.getAppArgs
  let last := args.back!
  let pick (t : Expr) : MetaM Expr := do
    let some m ← matchMatcherApp? t | throwError "den_match: no match{indentExpr t}"
    let ds := m.discrs
    if k.getNat == 0 then return (mkAppN m.alts[0]! (ds.extract 1 ds.size)).headBeta
    let d0 ← whnf ds[0]!
    let n ← match_expr ds[0]! with
      | HAdd.hAdd _ _ _ _ n _ => pure n
      | Nat.succ n => pure n
      | _ => match_expr d0 with
        | Nat.succ n => pure n
        | _ => throwError "den_match: fuel is not a successor{indentExpr ds[0]!}"
    return (mkAppN m.alts[1]! (#[n] ++ ds.extract 1 ds.size)).headBeta
  -- `Ref (loopRun …) (enc t)`: the value sits under `enc`
  unless last.isAppOf ``Enc.enc do throwError "den_match: `enc` expected"
  let e ← pick last.getAppArgs.back!
  let last' := mkAppN last.getAppFn (last.getAppArgs.pop.push e)
  replaceMainGoal [← g.replaceTargetDefEq (mkAppN tgt.getAppFn (args.pop.push last'))]

/-- a `call i` node: apply `Cert.call_<i>` -/
elab "den_call" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt := (← instantiateMVars (← g.getType)).cleanupAnnotations
  unless tgt.getAppFn.constName? == some ``DenT do throwError "den_call: not a DenT goal"
  let e ← whnf tgt.getAppArgs[1]!
  unless e.isAppOfArity ``ParSpec.Nd.call 2 do throwError "den_call: not a call"
  let ie ← whnf e.getAppArgs[0]!
  let some i := ie.nat? <|> ie.rawNatLit? | throwError "den_call: the def id is not a literal"
  evalTactic (← `(tactic| apply $(mkIdent (Name.mkStr `Cert s!"call_{i}"))))

private def natArg (e : Expr) : MetaM Nat := do
  let e ← whnf e
  let some n := e.nat? <|> e.rawNatLit? | throwError "den: a literal expected{indentExpr e}"
  return n

/-- one rule, chosen by the judgment and the node's constructor -/
elab "den_step" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let nm := tgt.getAppFn.constName?.getD .anonymous
  let args := tgt.getAppArgs
  let run (t : TacticM (TSyntax `tactic)) : TacticM Unit := do evalTactic (← t)
  if nm == ``DenP then
    let es ← listSpine args[1]!
    if es.size == 0 then run `(tactic| exact DenP.nil)
    else if es.size == 1 then run `(tactic| apply DenP.one)
    else run `(tactic| apply DenP.cons)
  else if nm == ``DenT || nm == ``DenK then
    let k := nm == ``DenK
    let e ← whnf (if k then args[2]! else args[1]!)
    let some c := e.getAppFn.constName? | throwError "den: no node constructor{indentExpr e}"
    let a := e.getAppArgs
    if c == ``ParSpec.Nd.letE then run `(tactic| den_let)
    else if c == ``ParSpec.Nd.ite then
      match (← natArg a[0]!), k with
      | 1, false => run `(tactic| apply DenT.iteEq)
      | 2, false => run `(tactic| apply DenT.iteLt)
      | 1, true => run `(tactic| apply DenK.iteEq)
      | 2, true => run `(tactic| apply DenK.iteLt)
      | _, _ => throwError "den: comparison code"
    else if k then run `(tactic| apply DenK.ofT)
    else if c == ``ParSpec.Nd.const then run `(tactic| first | exact DenT.const _ | exact DenT.constN rfl)
    else if c == ``ParSpec.Nd.loc then run `(tactic| exact DenT.loc rfl rfl)
    else if c == ``ParSpec.Nd.bin then
      match ← natArg a[0]! with
      | 1 => run `(tactic| apply DenT.add) | 2 => run `(tactic| apply DenT.sub) | 3 => run `(tactic| apply DenT.mul)
      | 4 => run `(tactic| apply DenT.and) | 5 => run `(tactic| apply DenT.or) | 6 => run `(tactic| apply DenT.shl)
      | 7 => run `(tactic| apply DenT.shr) | 8 => run `(tactic| apply DenT.xor)
      | _ => throwError "den: operator code"
    else if c == ``ParSpec.Nd.pair then run `(tactic| apply DenT.pair)
    else if c == ``ParSpec.Nd.call then run `(tactic| den_call)
    else if c == ``ParSpec.Nd.prim then
      match ← natArg a[0]! with
      | 1 => run `(tactic| exact DenT.lenN) | 2 => run `(tactic| apply DenT.rd) | 3 => run `(tactic| exact DenT.len)
      | 4 => run `(tactic| apply DenT.put)
      | 5 => run `(tactic| exact DenT.bnew) | 6 => run `(tactic| apply DenT.bsize) | 7 => run `(tactic| apply DenT.bget)
      | 8 => run `(tactic| apply DenT.bset) | 9 => run `(tactic| apply DenT.bpush)
      | _ => throwError "den: prim code"
    else throwError "den: no rule for{indentExpr e}"
  else run `(tactic| first | assumption | decide | omega)

/-- `den`: value position; `den [h]`: tail position of a step arm, `h` = the CONTINUE rule from the induction hypothesis -/
syntax "den" ("[" term "]")? : tactic
macro_rules
  | `(tactic| den) => `(tactic| repeat' den_step)
  | `(tactic| den [$h]) => `(tactic| repeat' (first | apply $h | den_step))

end Cert
