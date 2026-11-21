/- Testing/nano/v2self/fuzz/litcheck.lean: PROTOTYPE of the class-B check (Lean's Nat defaulting; SYNTAX_EXP.md
"B: literal typing"), on ParSpec's AST (`Nd`).  UNPROVEN test glue, not a spec: it fixes the rules before the trusted
predicate is written.  `chk lc e`: `lc` = the position has no expected type (let value, comparison operand, operator or
shift operand); a word is "literal" when its Lean type is still an unresolved numeral type.
usage: lake env lean --run Testing/nano/v2self/fuzz/litcheck.lean FILE...   (prints FILE true|false|LEXFAIL|PARSEFAIL) -/
import Nano.SelfHost.Cert.PC
import Nano.Lexer.DsSpec
open ParSpec
namespace LitP
def isShift (op : Nat) : Bool := op == 6 || op == 7
def setW (env : List Bool) (s : Nat) (ws : List Bool) : List Bool :=
  (List.range (max env.length (s + ws.length))).map fun i => if s ≤ i ∧ i < s + ws.length then ws.getD (i - s) false else env.getD i false
/-- per word of the value: is it literal-typed (Lean: a numeral type not yet known) -/
def fl : Nat → List Nat → List Bool → Nd → List Bool
  | 0, _, _, _ => []
  | _ + 1, _, _, .const _ => [true]
  | _ + 1, _, env, .loc s w => (List.range w).map fun i => env.getD (s + i) false
  | f + 1, ws, env, .bin op a b =>
    if isShift op then [(fl f ws env a).getD 0 false] else [(fl f ws env a).getD 0 false && (fl f ws env b).getD 0 false]
  | f + 1, ws, env, .ite _ _ _ t e => List.zipWith (· && ·) (fl f ws env t) (fl f ws env e)
  | f + 1, ws, env, .letE s _ v b => fl f ws (setW env s (fl f ws env v)) b
  | f + 1, ws, env, .pair cs => cs.attach.flatMap fun ⟨c, _⟩ => fl f ws env c
  | _ + 1, ws, _, .call id _ => List.replicate (ws.getD id 1) false
  | _ + 1, _, _, .prim _ _ => [false]
  | _ + 1, _, _, _ => []
def isL (f : Nat) (ws : List Nat) (env : List Bool) (e : Nd) : Bool := fl f ws env e == [true]
/-- the leaves of the operator tree at `e` (non-shift `bin` nodes are inner nodes) -/
def leaves : Nat → Nd → List Nd
  | 0, e => [e]
  | f + 1, .bin op a b => if isShift op then [.bin op a b] else leaves f a ++ leaves f b
  | _, e => [e]
def isCmpd : Nd → Bool
  | .letE .. => true | .ite .. => true | .bin op _ _ => isShift op | .pair _ => true | _ => false
def isConst : Nd → Bool | .const _ => true | _ => false
def isBin : Nd → Bool | .bin op _ _ => !isShift op | _ => false
/-- a let (possibly a desugared match) on the result spine (if branches, let bodies) -/
def isLet : Nat → Nd → Bool
  | 0, _ => true
  | _ + 1, .letE .. => true
  | f + 1, .ite _ _ _ t e => isLet f t || isLet f e
  | _ + 1, _ => false
/-- a let, tuple-let or (desugared) match directly as an operator or comparison operand: Lean's result depends on the
surrounding position (LEAN-DIFF M15 variant), so it is rejected by shape -/
def isLetH : Nd → Bool | .letE .. => true | _ => false
def isShiftN : Nd → Bool | .bin op _ _ => isShift op | _ => false
/-- `p ls j`: leaf j is of a kind Lean elaborates late; a literal leaf left of it is defaulted to Nat first -/
def leftLit (lit : List Bool) (ls : List Nd) (p : Nd → Bool) : Bool :=
  (List.range ls.length).any fun j => p (ls.getD j (.const 0)) && (lit.take j).any id
/-- a let whose bound value has a literal word (a tuple-let `(6, x)`, a match on one) -/
def letLitVal : Nat → List Nat → List Bool → Nd → Bool
  | 0, _, _, _ => true
  | f + 1, ws, env, .letE s _ v b => (fl f ws env v).any id || letLitVal f ws (setW env s (fl f ws env v)) b
  | f + 1, ws, env, .ite _ _ _ t e => letLitVal f ws env t || letLitVal f ws env e
  | _ + 1, _, _, _ => false
def treeOk (f : Nat) (ws : List Nat) (env : List Bool) (lc : Bool) (ls : List Nd) : Bool :=
  let lit := ls.map (isL f ws env)
  !(lit.all id && (lc || !ls.all isConst)) && !leftLit lit ls isShiftN && !ls.any isLetH
def cmpOk (f : Nat) (ws : List Nat) (env : List Bool) (a b : Nd) : Bool :=
  let ls := leaves f a ++ leaves f b
  let lit := ls.map (isL f ws env)
  !(lit.all id && (isBin a || isBin b)) && !leftLit lit ls isShiftN && !ls.any isLetH && !leftLit lit ls (letLitVal f ws env)
/-- an if with a literal branch and a let-headed (possibly match) branch -/
def litLetIte (f : Nat) (ws : List Nat) (env : List Bool) : Nd → Bool
  | .ite _ _ _ t e => (isL f ws env t && isLet f e) || (isL f ws env e && isLet f t)
  | _ => false
def chk : Nat → List Nat → List Bool → Bool → Nd → Bool
  | 0, _, _, _, _ => false
  | _ + 1, _, _, _, .const _ => true
  | _ + 1, _, _, _, .loc _ _ => true
  | f + 1, ws, env, lc, .bin op a b =>
    if isShift op then !isL f ws env a && !isLet f a && chk f ws env true a && chk f ws env true b
    else
      let ls := leaves f (.bin op a b)
      treeOk f ws env lc ls && ls.attach.all fun ⟨l, _⟩ => chk f ws env true l
  | f + 1, ws, env, lc, .ite c a b t e =>
    let ls := leaves f a ++ leaves f b
    !(lc && litLetIte f ws env (.ite c a b t e)) && cmpOk f ws env a b &&
      ls.attach.all (fun ⟨l, _⟩ => chk f ws env true l) && chk f ws env lc t && chk f ws env lc e
  | f + 1, ws, env, lc, .letE s _ v b => chk f ws env true v && chk f ws (setW env s (fl f ws env v)) lc b
  | f + 1, ws, env, lc, .pair cs => cs.attach.all fun ⟨c, _⟩ => chk f ws env lc c
  | f + 1, ws, env, _, .call _ as => as.attach.all fun ⟨a, _⟩ => chk f ws env false a
  | f + 1, ws, env, _, .prim _ as => as.attach.all fun ⟨a, _⟩ => chk f ws env false a
  | f + 1, ws, env, _, .loop z s => chk f ws env false z && chk f ws env false s
  | f + 1, ws, env, _, .cont e => chk f ws env false e
/-- the whole program: def bodies have their declared result type -/
def progOk (p : List DefA) : Bool :=
  let ws := p.map (·.nres)
  p.all fun d => chk 100000 ws [] false d.body
end LitP


def runOne (path : String) : IO Unit := do
  let b ← IO.FS.readBinFile path
  let x := b.toList
  match (ParSpec.lexAll (x.length + 1) x).bind DsSpec.ds with
  | none => IO.println s!"{path} LEXFAIL"
  | some ts => match refParse ts with
    | none => IO.println s!"{path} PARSEFAIL"
    | some p => IO.println s!"{path} {LitP.progOk p}"
def main (args : List String) : IO Unit := args.forM runOne
