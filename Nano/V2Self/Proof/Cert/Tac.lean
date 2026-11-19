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

/-- a `letE` node against `let y := a; B` or `match a with | (y₁, …) => B`: rule `letE` with `a`, `fun y => B` given
explicitly; leaves the value goal and the body goal (the new variable introduced, the slots written) -/
elab "den_let" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let nm := tgt.getAppFn.constName?.getD .anonymous
  unless nm == ``DenT || nm == ``DenK do throwError "den_let: not a Den goal"
  let t := tgt.getAppArgs.back!.consumeMData
  let (a, B, yn) ← match t with
    | .letE n ty v b _ => pure (v, Expr.lam n ty b .default, n)
    | _ => do
      let some m ← matchMatcherApp? t | throwError "den_let: the value is neither a let nor a match"
      unless m.discrs.size == 1 && m.alts.size == 1 do throwError "den_let: unexpected match"
      let d := m.discrs[0]!
      let B ← withLocalDeclD `y (← inferType d) fun y => do
        let .reduced e ← reduceMatcher? ({ m with discrs := #[y] }.toExpr) | throwError "den_let: the match does not reduce"
        mkLambdaFVars #[y] e.headBeta
      pure (d, B, `y)
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
  let g3 ← g3.replaceTargetDefEq (mkAppN tgt3.getAppFn (args.pop.push args.back!.headBeta))
  setGoals [g1, g3]

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
