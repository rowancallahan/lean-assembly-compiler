/- Testing/nano/v2self/fuzz/numcheck.lean: PROTOTYPE of Nat step 1 (EXPR.md §7 "Step 1 spec") combined with the
class-B shape rules (litcheck.lean without its literal-only rules 1, 2).  Derived from litcheck: PROTOTYPE of the class-B check (Lean's Nat defaulting; SYNTAX_EXP.md
"B: literal typing"), on ParSpec's AST (`Nd`).  UNPROVEN test glue, not a spec: it fixes the rules before the trusted
predicate is written.  `chk lc e`: `lc` = the position has no expected type (let value, comparison operand, operator or
shift operand); a word is "literal" when its Lean type is still an unresolved numeral type.
usage: lake env lean --run Testing/nano/v2self/fuzz/numcheck.lean FILE...   (prints FILE true|false|LEXFAIL|PARSEFAIL) -/
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
-- treeOk/cmpOk: a let, tuple-let or (desugared) match on the result spine of an operand (`isLet`) is rejected by shape:
-- Lean's verdict depends on the surrounding position (LEAN-DIFF, M15 variants)
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
  !leftLit lit ls isShiftN && !ls.any (isLet f)
def cmpOk (f : Nat) (ws : List Nat) (env : List Bool) (a b : Nd) : Bool :=
  let ls := leaves f a ++ leaves f b
  let lit := ls.map (isL f ws env)
  !leftLit lit ls isShiftN && !ls.any (isLet f) && !leftLit lit ls (letLitVal f ws env)
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



namespace NumP
/-- a group: the literal-bound slots of one literal-only expression, its demand (0 none, 1 UInt64, 2 Nat), and
whether it does arithmetic -/
structure G where
  vs : List Nat
  d : Nat
  ar : Bool
def isShift (op : Nat) : Bool := op == 6 || op == 7
def setW (env : List Bool) (s : Nat) (ws : List Bool) : List Bool :=
  (List.range (max env.length (s + ws.length))).map fun i => if s ≤ i ∧ i < s + ws.length then ws.getD (i - s) false else env.getD i false
/-- per word: literal-only (Lean: an open numeral type) -/
def fl : Nat → List Nat → List Bool → Nd → List Bool
  | 0, _, _, _ => []
  | _ + 1, _, _, .const _ => [true]
  | _ + 1, _, env, .loc s w => (List.range w).map fun i => env.getD (s + i) false
  | f + 1, ws, env, .bin op a b =>
    if isShift op then [false] else [(fl f ws env a).getD 0 false && (fl f ws env b).getD 0 false]
  | f + 1, ws, env, .ite _ _ _ t e => List.zipWith (· && ·) (fl f ws env t) (fl f ws env e)
  | f + 1, ws, env, .letE s _ v b => fl f ws (setW env s (fl f ws env v)) b
  | f + 1, ws, env, .pair cs => cs.attach.flatMap fun ⟨c, _⟩ => fl f ws env c
  | _ + 1, ws, _, .call id _ => List.replicate (ws.getD id 1) false
  | _ + 1, _, _, .prim _ _ => [false]
  | _ + 1, _, _, _ => []
def isL (f : Nat) (ws : List Nat) (env : List Bool) (e : Nd) : Bool := fl f ws env e == [true]
/-- the result: groups, and `false` if a shift has a literal left operand -/
abbrev R := List G × Bool
def R.app (a b : R) : R := (a.1 ++ b.1, a.2 && b.2)
mutual
/-- a literal-only expression: its slots and arithmetic flag; nested comparisons and lets add their own groups -/
def litI : Nat → List Nat → List Nat → List Bool → Nd → (List Nat × Bool) × R
  | 0, _, _, _, _ => (([], false), ([], false))
  | _ + 1, _, _, _, .const _ => (([], false), ([], true))
  | _ + 1, _, _, _, .loc s _ => (([s], false), ([], true))
  | f + 1, ks, ws, env, .bin op a b =>
    if isShift op then (([], false), ([], false))
    else
      let (ia, ra) := litI f ks ws env a
      let (ib, rb) := litI f ks ws env b
      ((ia.1 ++ ib.1, true), ra.app rb)
  | f + 1, ks, ws, env, .ite _ a b t e =>
    let rc := cmpG f ks ws env a b
    let (it, rt) := litI f ks ws env t
    let (ie, re) := litI f ks ws env e
    ((it.1 ++ ie.1, it.2 || ie.2), rc.app (rt.app re))
  | f + 1, ks, ws, env, .letE s w v b =>
    let rv := letG f ks ws env s w v
    let (ib, rb) := litI f ks ws (setW env s (fl f ws env v)) b
    (ib, rv.app rb)
  | _ + 1, _, _, _, _ => (([], false), ([], true))
/-- an expression at demand `d` -/
def col : Nat → List Nat → List Nat → List Bool → Nat → Nd → R
  | 0, _, _, _, _, _ => ([], false)
  | f + 1, ks, ws, env, d, e =>
    if isL f ws env e then
      let (i, r) := litI f ks ws env e
      (⟨i.1, d, i.2⟩ :: r.1, r.2)
    else match e with
    | .bin op a b =>
      if isShift op && isL f ws env a then ([], false)
      else (col f ks ws env 1 a).app (col f ks ws env 1 b)
    | .ite _ a b t e => (cmpG f ks ws env a b).app ((col f ks ws env 1 t).app (col f ks ws env 1 e))
    | .letE s w v b => (letG f ks ws env s w v).app (col f ks ws (setW env s (fl f ws env v)) d b)
    | .pair cs => cs.attach.foldr (fun ⟨c, _⟩ r => (col f ks ws env 1 c).app r) ([], true)
    | .call id as => as.zipIdx.attach.foldr (fun ⟨(a, i), _⟩ r =>
        (col f ks ws env (if ks.getD id 0 == 1 && i == 0 then 2 else 1) a).app r) ([], true)
    | .prim _ as => as.attach.foldr (fun ⟨a, _⟩ r => (col f ks ws env 1 a).app r) ([], true)
    | .loop z s => (col f ks ws env 1 z).app (col f ks ws env 1 s)
    | .cont c => col f ks ws env 1 c
    | _ => ([], true)
/-- a comparison: two literal-only operands are one class; else each literal operand is UInt64 -/
def cmpG : Nat → List Nat → List Nat → List Bool → Nd → Nd → R
  | 0, _, _, _, _, _ => ([], false)
  | f + 1, ks, ws, env, a, b =>
    if isL f ws env a && isL f ws env b then
      let (ia, ra) := litI f ks ws env a
      let (ib, rb) := litI f ks ws env b
      (⟨ia.1 ++ ib.1, 0, ia.2 || ib.2⟩ :: (ra.app rb).1, (ra.app rb).2)
    else (col f ks ws env 1 a).app (col f ks ws env 1 b)
/-- `let s := v`: a literal-only value joins the slot's class; a tuple's literal fields join their slots' classes -/
def letG : Nat → List Nat → List Nat → List Bool → Nat → Nat → Nd → R
  | 0, _, _, _, _, _, _ => ([], false)
  | f + 1, ks, ws, env, s, _, v =>
    match v with
    | .pair cs =>
      cs.zipIdx.attach.foldr (fun ⟨(c, i), _⟩ r =>
        (if isL f ws env c then
          let (ic, rc) := litI f ks ws env c
          (⟨(s + i) :: ic.1, 0, ic.2⟩ :: rc.1, rc.2)
        else col f ks ws env 1 c).app r) ([], true)
    | _ =>
      if isL f ws env v then
        let (iv, rv) := litI f ks ws env v
        (⟨s :: iv.1, 0, iv.2⟩ :: rv.1, rv.2)
      else col f ks ws env 0 v
end
/-- class labels: every slot in a group gets the smallest label in the group, repeated -/
def labels (n : Nat) (gs : List G) : List Nat :=
  (List.range (n + 1)).foldl (fun lab _ =>
    gs.foldl (fun lab g =>
      let m := (g.vs.map fun v => lab.getD v v).foldl min (lab.getD (g.vs.headD 0) (g.vs.headD 0))
      lab.mapIdx fun i l => if g.vs.contains i then min l m else l) lab) (List.range n)
def defOk (ks ws : List Nat) (d : DefA) : Bool :=
  let (gs, shOk) := col 100000 ks ws [] 1 d.body
  let lab := labels d.nslots gs
  let cls := fun (g : G) => g.vs.map fun v => lab.getD v v
  -- a class: the groups sharing a label; groups without slots are their own class
  let dem := fun (g : G) => gs.filter (fun h => (cls h).any (fun l => (cls g).contains l)) |>.map (·.d)
  shOk && gs.all fun g =>
    let ds := if g.vs.isEmpty then [g.d] else dem g
    let u := ds.contains 1
    let n := ds.contains 2
    !(u && n) && !(!u && (if g.vs.isEmpty then g.ar else (gs.filter fun h => (cls h).any (fun l => (cls g).contains l)).any (·.ar)))
def progOk (p : List DefA) : Bool := p.all (defOk (p.map (·.kind)) (p.map (·.nres)))
end NumP
def runOne (path : String) : IO Unit := do
  let b ← IO.FS.readBinFile path
  let x := b.toList
  match (ParSpec.lexAll (x.length + 1) x).bind DsSpec.ds with
  | none => IO.println s!"{path} LEXFAIL"
  | some ts => match refParse ts with
    | none => IO.println s!"{path} PARSEFAIL"
    | some p => IO.println s!"{path} {NumP.progOk p && LitP.progOk p}"
def main (args : List String) : IO Unit := args.forM runOne
