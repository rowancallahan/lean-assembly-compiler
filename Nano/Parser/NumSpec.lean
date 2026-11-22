/- Nano/Parser/NumSpec: the NUMERAL TYPING check of a parsed program (owner-approved Nat step 1, Testing/notes/EXPR.md §7
"Step 1 spec"; Testing/notes/SYNTAX_EXP.md "Nat step 1").  TRUSTED: `numOkP` is a conjunct of `pOf`.
Lean 4.34.1 gives a numeral an open type `?α` (`OfNat ?α n`) and defaults it to Nat last (`instOfNatNat`,
Init/Prelude.lean:1280).  `+ - * &&& |||` are `binop%` and `== <` are `binrel%` (Init/Notation.lean:302-309, 390, 394):
one type for the whole operator tree or comparison (Lean/Elab/Extra.lean).  `<<< >>>` are plain applications
(Notation.lean:289-290).  nano computes every numeral as a UInt64 word, so a program is accepted only when Lean gives each
numeral the same meaning:
* CLASSES.  A literal-only expression (numerals, slots bound to one, operators/ifs/lets over them) is a GROUP; groups
  sharing a let slot are one class.  A class is UInt64 if a member meets a UInt64 position (an operator or comparison
  with a typed operand, a UInt64 parameter, prim argument, result or tuple field), Nat if it meets a fuel argument, and
  Nat by default.  Rejected: a class with both demands; a Nat class doing arithmetic (bignum Nat is not implemented);
  a literal-only shift operand.  Accepted Nat classes only compare and select literals below 2^64 (the lexer rejects
  larger numerals), where the word values agree with Lean's Nat.
* ELABORATION ORDER (shape rules, Testing/notes/SYNTAX_EXP.md "B"): Lean postpones `match`, which after desugaring is
  a let; so no let on the result spine (if branches, let bodies) of an operator, comparison or shift-left operand
  (LEAN_DIFF M15, M16); no literal operand left of a shift in an operator tree or comparison (M12); where no type is
  expected (a let value or tuple field, an operand), no `if` with a literal branch and a branch that waits (`mixIte`);
  and no slot bound to a value with a let on its result spine left of a shift (`lateOk`). -/
import Nano.Parser.ParSpec
namespace NumSpec
open ParSpec

def isShift (op : Nat) : Bool := op == 6 || op == 7

/-- `env` with the words `ws` stored from slot `s` on -/
def setW (env : List Bool) (s : Nat) (ws : List Bool) : List Bool :=
  (List.range (max env.length (s + ws.length))).map fun i =>
    if s ≤ i ∧ i < s + ws.length then ws.getD (i - s) false else env.getD i false

/-- per word of the value: literal-only?  (`env`: per slot; `ws`: each def's result width) -/
def lw : Nat → List Nat → List Bool → Nd → List Bool
  | 0, _, _, _ => []
  | _ + 1, _, _, .const _ => [true]
  | _ + 1, _, env, .loc s w => (List.range w).map fun i => env.getD (s + i) false
  | f + 1, ws, env, .bin op a b => [!isShift op && (lw f ws env a).getD 0 false && (lw f ws env b).getD 0 false]
  | f + 1, ws, env, .ite _ _ _ t e => List.zipWith (· && ·) (lw f ws env t) (lw f ws env e)
  | f + 1, ws, env, .letE s _ v b => lw f ws (setW env s (lw f ws env v)) b
  | f + 1, ws, env, .pair cs => cs.attach.flatMap fun ⟨c, _⟩ => lw f ws env c
  | _ + 1, ws, _, .call id _ => List.replicate (ws.getD id 1) false
  | _ + 1, _, _, _ => [false]

def isL (f : Nat) (ws : List Nat) (env : List Bool) (e : Nd) : Bool := lw f ws env e == [true]

/-- a let on the result spine (if branches, let bodies): possibly a desugared `match` -/
def spineLet : Nat → Nd → Bool
  | 0, _ => true
  | _ + 1, .letE .. => true
  | f + 1, .ite _ _ _ t e => spineLet f t || spineLet f e
  | _ + 1, _ => false

/-- a shift, or what Lean elaborates after one: an operator tree with such a leaf, an `if` with such a then-branch, a
let with such a body -/
def post : Nat → Nd → Bool
  | f + 1, .bin op a b => isShift op || post f a || post f b
  | f + 1, .ite _ _ _ t _ => post f t
  | f + 1, .letE _ _ _ b => post f b
  | _, _ => false

/-- an `if` Lean cannot type where no type is expected: one branch literal-only, the other waits (a let on its
result spine; for the else-branch also `post`) -/
def mixIte (f : Nat) (ws : List Nat) (env : List Bool) : Nd → Bool
  | .ite _ _ _ t e => (isL f ws env t && (spineLet f e || post f e)) || (isL f ws env e && spineLet f t)
  | _ => false

/-- the operands of the operator tree at `e` (non-shift operators are inner nodes) -/
def leaves : Nat → Nd → List Nd
  | f + 1, .bin op a b => if isShift op then [.bin op a b] else leaves f a ++ leaves f b
  | _, e => [e]

/-- the order and spine rules for the operands `ls` of one operator tree or comparison -/
def shapeOk (f : Nat) (ws : List Nat) (env : List Bool) (ls : List Nd) : Bool :=
  !ls.any (spineLet f) && !ls.any (mixIte f ws env) &&
  !(List.range ls.length).any fun j =>
    (match ls.getD j (.const 0) with | .bin op _ _ => isShift op | _ => false) &&
    (ls.take j).any (isL f ws env)

/-- a group: the literal-bound slots of a literal-only expression, its demand (0 none, 1 UInt64, 2 Nat), and whether
it does arithmetic -/
structure G where
  vs : List Nat
  d : Nat
  ar : Bool

/-- groups, and whether the shape rules hold -/
abbrev R := List G × Bool
def R.app (a b : R) : R := (a.1 ++ b.1, a.2 && b.2)
def R.ok : R := ([], true)

mutual
/-- a literal-only expression: its slots and arithmetic flag (nested comparisons and lets add their own groups) -/
def litG : Nat → List Nat → List Nat → List Bool → Nd → (List Nat × Bool) × R
  | 0, _, _, _, _ => (([], false), ([], false))
  | _ + 1, _, _, _, .loc s _ => (([s], false), R.ok)
  | f + 1, ks, ws, env, .bin _ a b =>
    let (ia, ra) := litG f ks ws env a
    let (ib, rb) := litG f ks ws env b
    ((ia.1 ++ ib.1, true), ra.app rb)
  | f + 1, ks, ws, env, .ite _ a b t e =>
    let (it, rt) := litG f ks ws env t
    let (ie, re) := litG f ks ws env e
    ((it.1 ++ ie.1, it.2 || ie.2), (cmpG f ks ws env a b).app (rt.app re))
  | f + 1, ks, ws, env, .letE s w v b =>
    let (ib, rb) := litG f ks ws (setW env s (lw f ws env v)) b
    (ib, (letG f ks ws env s w v).app rb)
  | _ + 1, _, _, _, _ => (([], false), R.ok)
/-- an expression at demand `d` (`lc`: no type is expected here) -/
def col : Nat → List Nat → List Nat → List Bool → Nat → Nd → R
  | 0, _, _, _, _, _ => ([], false)
  | f + 1, ks, ws, env, d, e =>
    if isL f ws env e then
      let (i, r) := litG f ks ws env e
      (⟨i.1, d, i.2⟩ :: r.1, r.2)
    else match e with
    | .bin op a b =>
      if isShift op then
        R.app ([], !isL f ws env a && !spineLet f a && !mixIte f ws env a && !mixIte f ws env b)
          ((col f ks ws env 1 a).app (col f ks ws env 1 b))
      else
        let ls := leaves f e
        R.app ([], shapeOk f ws env ls) (ls.attach.foldr (fun ⟨l, _⟩ r => (col f ks ws env 1 l).app r) R.ok)
    | .ite c a b t el =>
      R.app ([], !(d == 0 && mixIte f ws env (.ite c a b t el)))
        ((cmpG f ks ws env a b).app ((col f ks ws env 1 t).app (col f ks ws env 1 el)))
    | .letE s w v b => (letG f ks ws env s w v).app (col f ks ws (setW env s (lw f ws env v)) d b)
    | .pair cs => cs.attach.foldr (fun ⟨c, _⟩ r => (col f ks ws env 1 c).app r) R.ok
    | .call id as => as.zipIdx.attach.foldr (fun ⟨(a, i), _⟩ r =>
        (col f ks ws env (if ks.getD id 0 == 1 && i == 0 then 2 else 1) a).app r) R.ok
    | .prim _ as => as.attach.foldr (fun ⟨a, _⟩ r => (col f ks ws env 1 a).app r) R.ok
    | .loop z s => (col f ks ws env 1 z).app (col f ks ws env 1 s)
    | .cont c => col f ks ws env 1 c
    | _ => R.ok
/-- a comparison: two literal-only operands are one group; else each literal operand is UInt64 -/
def cmpG : Nat → List Nat → List Nat → List Bool → Nd → Nd → R
  | 0, _, _, _, _, _ => ([], false)
  | f + 1, ks, ws, env, a, b =>
    let sh : R := ([], shapeOk f ws env (leaves f a ++ leaves f b))
    if isL f ws env a && isL f ws env b then
      let (ia, ra) := litG f ks ws env a
      let (ib, rb) := litG f ks ws env b
      sh.app ((⟨ia.1 ++ ib.1, 0, ia.2 || ib.2⟩ :: (ra.app rb).1, (ra.app rb).2))
    else sh.app ((col f ks ws env 1 a).app (col f ks ws env 1 b))
/-- `let s := v`: a literal-only value joins the slot's class; a tuple's literal-only fields join their slots' -/
def letG : Nat → List Nat → List Nat → List Bool → Nat → Nat → Nd → R
  | 0, _, _, _, _, _, _ => ([], false)
  | f + 1, ks, ws, env, s, _, v =>
    match v with
    | .pair cs =>
      cs.zipIdx.attach.foldr (fun ⟨(c, i), _⟩ r =>
        (if isL f ws env c then
          let (ic, rc) := litG f ks ws env c
          (⟨(s + i) :: ic.1, 0, ic.2⟩ :: rc.1, rc.2)
        else col f ks ws env 0 c).app r) R.ok
    | _ =>
      if isL f ws env v then
        let (iv, rv) := litG f ks ws env v
        (⟨s :: iv.1, 0, iv.2⟩ :: rv.1, rv.2)
      else col f ks ws env 0 v
end

/-- the slots whose class has demand `d`: a group with demand `d` or with such a slot marks all its slots
(repeated `n` times: enough for `n` slots) -/
def marked (d : Nat) (gs : List G) : Nat → List Nat → List Nat
  | 0, m => m
  | n + 1, m => marked d gs n (m ++ (gs.filter fun g => g.d == d || g.vs.any m.contains).flatMap (·.vs))

/-- the nodes of `e`, pre-order -/
def nodes : Nat → Nd → List Nd
  | 0, _ => []
  | f + 1, e => e :: (match e with
    | .bin _ a b => [a, b] | .ite _ a b t e => [a, b, t, e] | .letE _ _ v b => [v, b] | .pair cs => cs
    | .call _ as => as | .prim _ as => as | .loop z s => [z, s] | .cont e => [e] | _ => []).flatMap (nodes f)

/-- the slots a let binds to a value (per tuple field) with a let on its result spine: Lean types them late -/
def late (f : Nat) : Nd → List Nat
  | .letE s _ (.pair cs) _ => (cs.zipIdx.filter fun (c, _) => spineLet f c).map fun (_, i) => s + i
  | .letE s w v _ => if spineLet f v then (List.range w).map (s + ·) else []
  | _ => []

/-- no late slot is the left operand of a shift -/
def lateOk (f : Nat) (e : Nd) : Bool :=
  (nodes f e).all fun
    | .bin op (.loc s _) _ => !(isShift op && ((nodes f e).flatMap (late f)).contains s)
    | _ => true

/-- a def's slot groups and shape verdict (`ks`, `ws`: each def's kind and result width) -/
def colD (ks ws : List Nat) (df : DefA) : List G × Bool := col (2 ^ 24) ks ws [] 1 df.body
/-- the slots of a def's groups forced to numeral class `d` (1: UInt64, 2: Nat) -/
def markD (d : Nat) (gs : List G) (df : DefA) : List Nat := marked d gs (df.nslots + 1) []

/-- **one def's numerals mean what Lean's mean** (`ks`, `ws`: each def's kind and result width) -/
def numOkD (ks ws : List Nat) (df : DefA) : Bool :=
  let (gs, shape) := colD ks ws df
  let u := markD 1 gs df
  let n := markD 2 gs df
  shape && lateOk (2 ^ 24) df.body && gs.all fun g =>
    let isU := g.d == 1 || g.vs.any u.contains
    let isN := g.d == 2 || g.vs.any n.contains
    !(isU && isN) && !(g.ar && !isU)

/-- **the program's numerals mean what Lean's mean** -/
def numOkP (p : List DefA) : Bool := p.all (numOkD (p.map (·.kind)) (p.map (·.nres)))

/-- slot `s` of a def has numeral class Nat: it is in a group, and no UInt64 evidence reaches it -/
def slotNat (ks ws : List Nat) (df : DefA) (s : Nat) : Bool :=
  let gs := (colD ks ws df).1
  gs.any (·.vs.contains s) && !(markD 1 gs df).contains s
/-- `slotNat` for slot `s` of def `i` of program `p` -/
def slotNatP (p : List DefA) (i s : Nat) : Bool :=
  match p[i]? with
  | some df => slotNat (p.map (·.kind)) (p.map (·.nres)) df s
  | none => false

end NumSpec
