/- `frontx_compile f`: translate a first-order tail-recursive Lean definition into a `Tree` and prove,
automatically, that the tree computes the function.  The translator is untrusted; what counts are the
kernel-checked theorems it adds:

* `f.tree : Tree`, `f.lay : Lay`, `f.Rep args σ` (the state `σ` holds the arguments), `f.out args : LOut _`
  (the body of `f` with its leaves tagged `ret` / `call`)
* `f.step1 : ∀ args σ, f.Rep args σ → Sim _ f.tree σ (f.out args)`  (one iteration; no induction)
* `f.runs : ∀ args σ, f.Rep args σ → ∃ σ', f.tree.Runs σ (rep (f args)) σ'`
* `f.exec : ∀ args σ, f.Rep args σ → ∃ σ', BExec (prog f.lay f.tree out) σ σ' ∧ σ'.env out = rep (f args) ∧ σ'.heap = σ.heap`

The definition is read through its unfolding equation (`f.eq_def`), never the compiler IR.

`f.step1` is built by the translator itself, node by node (`sim_dite`, `sim_let`, `sim_load`, `sim_ret`,
`sim_call` of `Tree.lean`): every emitted expression comes with one small obligation
`E.denote env = rep e`, closed by `simp` with the lemma set of `Rep.lean` after the Lean terms already held in
temporaries have been generalised to variables (so the cost is linear in the size of the body).
`f.runs` is functional induction on `f` (the recursion's own termination argument is reused; no measure is
ever stated): in each case the path conditions select the leaf of `f.step1`. -/
import Lean
import Proven.Frontx.Rep
import Proven.Frontx.For

namespace Proven.Frontx
open Lean Meta Elab Term Command Tactic

inductive Ty where | bv | u8 | u32 | u64 | nat | bool
  deriving BEq, Repr, Inhabited

def bv64 : Expr := mkApp (mkConst ``BitVec) (toExpr (64 : Nat))
def mkBV (n : Nat) : Expr := mkApp2 (mkConst ``BitVec.ofNat) (toExpr (64 : Nat)) (toExpr n)

def classify (t : Expr) : MetaM (Option Ty) := do
  let t ← whnfR t
  if t.isConstOf ``UInt8 then return some .u8
  if t.isConstOf ``UInt32 then return some .u32
  if t.isConstOf ``UInt64 then return some .u64
  if t.isConstOf ``Nat then return some .nat
  if t.isConstOf ``Bool then return some .bool
  if t.isAppOfArity ``BitVec 1 then
    if ← isDefEq t bv64 then return some .bv
  return none

def Ty.rep (ty : Ty) (e : Expr) : Expr :=
  match ty with
  | .bv => e
  | .u8 => mkApp (mkConst ``r8) e
  | .u32 => mkApp (mkConst ``r32) e
  | .u64 => mkApp (mkConst ``r64) e
  | .nat => mkApp (mkConst ``rN) e
  | .bool => mkApp (mkConst ``rB) e

def Ty.mask : Ty → Option Nat
  | .u8 => some 0xff
  | .u32 => some 0xffffffff
  | _ => none

/-- mask for shift amounts -/
def Ty.shMask : Ty → Option Nat
  | .u8 => some 7
  | .u32 => some 31
  | .u64 => some 63
  | _ => none

/-! ## meta-level syntax of `BExp` / `Tree` -/

inductive ME where
  | var (n : Nat)
  | const (c : Expr)
  | bin (op : Name) (a b : ME)
  | ite (c a b : ME)
  deriving Inhabited

inductive MT where
  | ret (e : ME)
  | call (as : List (Nat × ME))
  | ite (c : ME) (t e : MT)
  | let_ (v : Nat) (e : ME) (k : MT)
  | load (v b : Nat) (i : ME) (k : MT)
  | cload (v b : Nat) (i c d : ME) (k : MT)
  deriving Inhabited

def ME.toExpr : ME → Expr
  | .var n => mkApp (mkConst ``BExp.var) (Lean.toExpr n)
  | .const c => mkApp (mkConst ``BExp.const) c
  | .bin op a b => mkApp3 (mkConst ``BExp.bin) (mkConst op) a.toExpr b.toExpr
  | .ite c a b => mkApp3 (mkConst ``BExp.ite) c.toExpr a.toExpr b.toExpr

def pairTy : Expr := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``BExp)

def MT.toExpr : MT → MetaM Expr
  | .ret e => return mkApp (mkConst ``Tree.ret) e.toExpr
  | .call as => do
    let ps := as.map fun (v, e) =>
      mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``BExp) (Lean.toExpr v) e.toExpr
    return mkApp (mkConst ``Tree.call) (← mkListLit pairTy ps)
  | .ite c t e => return mkApp3 (mkConst ``Tree.ite) c.toExpr (← t.toExpr) (← e.toExpr)
  | .let_ v e k => return mkApp3 (mkConst ``Tree.let_) (Lean.toExpr v) e.toExpr (← k.toExpr)
  | .load v b i k => return mkApp4 (mkConst ``Tree.load) (Lean.toExpr v) (Lean.toExpr b) i.toExpr (← k.toExpr)
  | .cload v b i c d k => do
    let kE ← k.toExpr
    return mkAppN (mkConst ``Tree.cload) #[Lean.toExpr v, Lean.toExpr b, i.toExpr, c.toExpr, d.toExpr, kE]

def MT.maxK : MT → Nat
  | .ret _ => 0
  | .call as => as.length
  | .ite _ t e => max t.maxK e.maxK
  | .let_ _ _ k | .load _ _ _ k | .cload _ _ _ _ _ k => k.maxK

/-- nesting depth of the condition variables `comp` uses -/
def MT.cdepth : MT → Nat
  | .ret _ | .call _ => 0
  | .ite _ t e => 1 + max t.cdepth e.cdepth
  | .let_ _ _ k | .load _ _ _ k => k.cdepth
  | .cload _ _ _ _ _ k => max 1 k.cdepth

/-! ## translation -/

/-- translating the body of a `for` loop: tail terms have type `T = Id (ForInStep S)`, outcomes are `g tail` -/
structure LoopInfo where
  g : Expr
  T : Expr
  S : Expr
  /-- `fun s => rep (the code after the loop, applied to s)` -/
  postBV : Expr
  postLean : Expr
  /-- the index and its variable -/
  i : Expr
  iv : Nat
  /-- the mutable locals (free variables) and their variables; `none`: an `Option` local that is `none`
  throughout the loop (early `return`), held in no variable -/
  comps : Array (Expr × Option Nat)

structure Ctx where
  fn : Name
  params : Array Expr
  /-- byte-array parameters: (the fvar, block index, length variable) -/
  blocks : List (Expr × Nat × Nat) := []
  /-- the type of argument tuples, the relation "the state holds these arguments", the heap of the state -/
  A : Expr
  R : Expr
  heap : Expr
  repN : Name
  rty : Ty
  loop : Option LoopInfo := none

/-- a load or a temporary, emitted before the node being translated, with the Lean term it holds -/
inductive Item where
  | load (v b : Nat) (i : ME) (r : Expr) (idx : Expr) (temps : List Expr)
  | cload (v b : Nat) (i c d : ME) (r : Expr) (idx : Expr) (temps : List Expr)
  | let_ (v : Nat) (e : ME) (L L' : Expr) (ty : Ty) (temps : List Expr)
  /-- a temporary introduced only to keep expressions shallow: `v := e`, no Lean term attached -/
  | raw (v : Nat) (e : ME)

structure TrSt where
  next : Nat
  /-- Lean scalar terms that already live in a variable (newest first) -/
  memo : List (Expr × Nat) := []
  /-- the Lean terms held in temporaries (newest first); generalised in every obligation -/
  temps : List Expr := []
  pend : Array Item := #[]
  /-- helper definitions that were inlined (the proofs unfold them, one layer at a time) -/
  unfolded : Array Name := #[]
  nObl : Nat := 0
  deriving Inhabited

abbrev TrM := StateRefT TrSt TermElabM

def fresh : TrM Nat := modifyGet fun s => (s.next, { s with next := s.next + 1 })

def find? (e : Expr) : TrM (Option Nat) := do
  let memo := (← get).memo
  for (k, v) in memo do
    if k == e then return some v
  for (k, v) in memo do
    if k.getAppFn.constName? == e.getAppFn.constName? && k.getAppNumArgs == e.getAppNumArgs && k.isApp then
      if ← withReducible (isDefEq k e) then return some v
  return none

def Ctx.block? (ctx : Ctx) (e : Expr) : Option (Nat × Nat) :=
  (ctx.blocks.find? (·.1 == e)).map (·.2)

/-- `(xs, i)` if `e` is a read of a byte array -/
def read? (e : Expr) : Option (Expr × Expr) :=
  let args := e.getAppArgs
  match e.getAppFn.constName?, args.size with
  | some ``GetElem.getElem, 8 => some (args[5]!, args[6]!)
  | some ``GetElem?.getElem!, 8 => some (args[6]!, args[7]!)
  | _, _ => none

/-- the byte-array reads inside `e`, innermost first (not under binders) -/
partial def reads (ctx : Ctx) (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  match e with
  | .app .. =>
    match read? e with
    | some (xs, i) =>
      if (ctx.block? xs).isSome then (reads ctx i acc).push e else acc
    | none => e.getAppArgs.foldl (fun acc a => reads ctx a acc) acc
  | .mdata _ b => reads ctx b acc
  | _ => acc

/-- a closed `BitVec 64` term as a literal, if it evaluates -/
def litBV (c : Expr) : MetaM Expr := do
  let n ← whnfD (mkApp2 (mkConst ``BitVec.toNat) (toExpr (64 : Nat)) c)
  match n.rawNatLit? <|> n.nat? with
  | some n => return mkBV n
  | none => return c

def ME.depth : ME → Nat
  | .var _ | .const _ => 0
  | .bin _ a b => max a.depth (b.depth + 1)
  | .ite c a b => max c.depth (max (a.depth + 1) (b.depth + 2))

/-- the expression depth the translator allows itself (`BStmt.wf` needs `< 6` for indices and stored values,
`< 7` elsewhere) -/
def maxDepth : Nat := 5

/-- an expression of depth `≤ d` with the same value: subexpressions that do not fit go to fresh temporaries -/
partial def fit (m : ME) (d : Nat := maxDepth) : TrM ME := do
  if m.depth ≤ d then return m
  let tmp : TrM ME := do
    let m' ← fit m maxDepth
    let v ← fresh
    modify fun s => { s with pend := s.pend.push (.raw v m') }
    return .var v
  match m with
  | .bin op a b => if d == 0 then tmp else return .bin op (← fit a d) (← fit b (d - 1))
  | .ite c a b => if d < 2 then tmp else return .ite (← fit c d) (← fit a (d - 1)) (← fit b (d - 2))
  | m => return m

def cNot (c : ME) : ME := .bin ``Op.xor c (.const (mkBV 1))

mutual

/-- a scalar term `e`: its expression, and `e` with the inlined helpers unfolded (definitionally equal to `e`;
the terms held in temporaries occur in it syntactically) -/
partial def trE (ctx : Ctx) (e : Expr) : TrM (ME × Expr) := do
  let e := e.consumeMData.headBeta
  if let some v ← find? e then return (.var v, e)
  let some ty ← classify (← inferType e) | throwError "frontx: not a scalar:{indentExpr e}"
  if !e.hasFVar then return (.const (← litBV (ty.rep e)), e)
  if ty == .bool then return ← trB ctx e
  let args := e.getAppArgs
  let f := e.getAppFn
  -- a read of a byte array: a load into a fresh variable
  if let some (xs, i) := read? e then
    if let some (b, _) := ctx.block? xs then
      let (idx, i') ← trE ctx i
      let idx ← fit idx
      let v ← fresh
      modify fun s => { s with memo := (e, v) :: s.memo, pend := s.pend.push (.load v b idx e i' s.temps) }
      return (.var v, e)
  -- a guarded read `if h : i < xs.size then xs[i] else d` (`d` closed): a guarded load
  if e.isAppOfArity ``dite 5 && args[3]!.isLambda && args[4]!.isLambda then
    let P := args[1]!
    let t := args[3]!.bindingBody!
    let d := args[4]!.bindingBody!
    if P.isAppOfArity ``LT.lt 4 && P.appArg!.isAppOfArity ``ByteArray.size 1 && !d.hasLooseBVars && !d.hasFVar then
      let i := P.appFn!.appArg!
      let xs := P.appArg!.appArg!
      -- also `(xs[i]).toUInt64` etc. with `d = 0`: the byte is loaded with default `0`
      let isConv := (t.isAppOfArity ``UInt8.toUInt32 1 || t.isAppOfArity ``UInt8.toUInt64 1 ||
        t.isAppOfArity ``UInt8.toNat 1) && (d.nat? == some 0 || d.rawNatLit? == some 0)
      let rd := if isConv then t.appArg! else t
      match ctx.block? xs, read? rd with
      | some (b, len), some (xs', i') =>
        if xs' == xs && i' == i then
          let r ← if isConv then
              pure (mkAppN (mkConst ``dite [levelOne]) #[mkConst ``UInt8, P, args[2]!, .lam `h P rd .default,
                .lam `h (mkNot P) (toExpr (0 : UInt8)) .default])
            else pure e
          let (idx, i'') ← trE ctx i
          let idx ← fit idx
          let v ← fresh
          let c := ME.bin ``Op.ult idx (.var len)
          let dm := ME.const (← litBV (mkApp (mkConst ``r8) (if isConv then toExpr (0 : UInt8) else d)))
          modify fun s => { s with memo := (e, v) :: s.memo, pend := s.pend.push (.cload v b idx c dm r i'' s.temps) }
          return (.var v, e)
      | _, _ => pure ()
  let masked (m : Option Nat) (r : ME) : ME :=
    match m with
    | some m => .bin ``Op.and r (.const (mkBV m))
    | none => r
  let bin (op : Name) (m : Option Nat) : TrM (ME × Expr) := do
    let (a, a') ← trE ctx args[4]!
    let (b, b') ← trE ctx args[5]!
    return (masked m (.bin op a b), mkAppN f ((args.set! 4 a').set! 5 b'))
  let shift (op : Name) (m : Option Nat) : TrM (ME × Expr) := do
    let (a, a') ← trE ctx args[4]!
    let b := args[5]!
    let some bty ← classify (← inferType b) | throwError "frontx: shift amount{indentExpr b}"
    let (amt, b') ← (do
      match ty.shMask with
      | some sm =>
        if b.hasFVar then
          let (x, b') ← trE ctx b
          return (ME.bin ``Op.and x (.const (mkBV sm)), b')
        else return (ME.const (← litBV (← mkAppM ``HAnd.hAnd #[bty.rep b, mkBV sm])), b)
      | none => trE ctx b : TrM (ME × Expr))
    return (masked m (.bin op a amt), mkAppN f ((args.set! 4 a').set! 5 b'))
  let conv (m : Option Nat) : TrM (ME × Expr) := do
    let (a, a') ← trE ctx args[0]!
    return (masked m a, mkAppN f #[a'])
  match f.constName?, args.size with
  | some ``HAdd.hAdd, 6 => bin ``Op.add ty.mask
  | some ``HSub.hSub, 6 => bin ``Op.sub ty.mask
  | some ``HAnd.hAnd, 6 => bin ``Op.and none
  | some ``HOr.hOr, 6 => bin ``Op.or none
  | some ``HXor.hXor, 6 => bin ``Op.xor none
  | some ``HShiftRight.hShiftRight, 6 => shift ``Op.lshr none
  | some ``HShiftLeft.hShiftLeft, 6 => shift ``Op.shl ty.mask
  | some ``Pure.pure, 4 => trE ctx args[3]!
  | some ``Id.run, 2 => trE ctx args[1]!
  | some ``ite, 5 =>
    let (c, p') ← trC ctx args[1]!
    let (a, a') ← trE ctx args[3]!
    let (b, b') ← trE ctx args[4]!
    return (.ite c a b, ← mkAppOptM ``ite #[args[0]!, p', none, a', b'])
  | some ``UInt8.toUInt32, 1 | some ``UInt8.toUInt64, 1 | some ``UInt32.toUInt64, 1
  | some ``UInt8.toNat, 1 | some ``UInt32.toNat, 1 | some ``UInt64.toNat, 1 | some ``Nat.toUInt64, 1 => conv none
  | some ``UInt32.toUInt8, 1 | some ``UInt64.toUInt8, 1 | some ``Nat.toUInt8, 1 => conv (some 0xff)
  | some ``UInt64.toUInt32, 1 | some ``Nat.toUInt32, 1 => conv (some 0xffffffff)
  | some ``ByteArray.size, 1 =>
    match ctx.block? args[0]! with
    | some (_, len) => return (.var len, e)
    | none => throwError "frontx: size of an unknown array{indentExpr e}"
  | some c, _ =>
    if c == ctx.fn then throwError "frontx: recursive call not in tail position{indentExpr e}"
    -- a helper function: its compound scalar arguments go to temporaries, then it is inlined
    for a in args do
      if a.hasFVar && !a.isFVar && (← find? a).isNone then
        if let some aty ← classify (← inferType a) then
          let (m, a') ← trE ctx a
          let m ← fit m
          let v ← fresh
          modify fun s => { s with memo := (a, v) :: s.memo, temps := a :: s.temps,
                                   pend := s.pend.push (.let_ v m a a' aty s.temps) }
    match ← unfoldDefinition? e with
    | some e' =>
      modify fun s => if s.unfolded.contains c then s else { s with unfolded := s.unfolded.push c }
      trE ctx e'
    | none => throwError "frontx: unsupported term{indentExpr e}"
  | none, _ => throwError "frontx: unsupported term{indentExpr e}"

/-- a decidable proposition, as a `0`/`1` value; and the proposition with helpers unfolded -/
partial def trC (ctx : Ctx) (p : Expr) : TrM (ME × Expr) := do
  let p := p.consumeMData.headBeta
  let args := p.getAppArgs
  let f := p.getAppFn
  let cmp (i j : Nat) (neg : Bool) : TrM (ME × Expr) := do
    let (a, a') ← trE ctx args[i]!
    let (b, b') ← trE ctx args[j]!
    let r := ME.bin ``Op.ult a b
    return (if neg then cNot r else r, mkAppN f ((args.set! i a').set! j b'))
  match f.constName?, args.size with
  | some ``Eq, 3 =>
    if args[0]!.isConstOf ``Bool then
      let (b, b') ← trB ctx args[1]!
      let p' := mkAppN f #[args[0]!, b', args[2]!]
      if args[2]!.isConstOf ``Bool.true then return (b, p')
      else if args[2]!.isConstOf ``Bool.false then return (cNot b, p')
      else throwError "frontx: unsupported condition{indentExpr p}"
    else
      let (a, a') ← trE ctx args[1]!
      let (b, b') ← trE ctx args[2]!
      return (.bin ``Op.eq a b, mkAppN f #[args[0]!, a', b'])
  | some ``Ne, 3 =>
    let (a, a') ← trE ctx args[1]!
    let (b, b') ← trE ctx args[2]!
    return (cNot (.bin ``Op.eq a b), mkAppN f #[args[0]!, a', b'])
  | some ``Not, 1 =>
    let (c, q) ← trC ctx args[0]!
    return (cNot c, mkNot q)
  | some ``LT.lt, 4 => cmp 2 3 false
  | some ``GT.gt, 4 => cmp 3 2 false
  | some ``LE.le, 4 => cmp 3 2 true
  | some ``GE.ge, 4 => cmp 2 3 true
  | some ``And, 2 =>
    let (a, a') ← trC ctx args[0]!
    let (b, b') ← trC ctx args[1]!
    return (.bin ``Op.and a b, mkAnd a' b')
  | some ``Or, 2 =>
    let (a, a') ← trC ctx args[0]!
    let (b, b') ← trC ctx args[1]!
    return (.bin ``Op.or a b, mkOr a' b')
  | _, _ => throwError "frontx: unsupported condition{indentExpr p}"

/-- a `Bool`, as a `0`/`1` value -/
partial def trB (ctx : Ctx) (b : Expr) : TrM (ME × Expr) := do
  let b := b.consumeMData.headBeta
  let args := b.getAppArgs
  let f := b.getAppFn
  match f.constName?, args.size with
  | some ``BEq.beq, 4 =>
    let (x, x') ← trE ctx args[2]!
    let (y, y') ← trE ctx args[3]!
    return (.bin ``Op.eq x y, mkAppN f #[args[0]!, args[1]!, x', y'])
  | some ``bne, 4 =>
    let (x, x') ← trE ctx args[2]!
    let (y, y') ← trE ctx args[3]!
    return (cNot (.bin ``Op.eq x y), mkAppN f #[args[0]!, args[1]!, x', y'])
  | some ``and, 2 =>
    let (x, x') ← trB ctx args[0]!
    let (y, y') ← trB ctx args[1]!
    return (.bin ``Op.and x y, mkAppN f #[x', y'])
  | some ``or, 2 =>
    let (x, x') ← trB ctx args[0]!
    let (y, y') ← trB ctx args[1]!
    return (.bin ``Op.or x y, mkAppN f #[x', y'])
  | some ``not, 1 =>
    let (x, x') ← trB ctx args[0]!
    return (cNot x, mkAppN f #[x'])
  | some ``Decidable.decide, 2 =>
    let (c, q) ← trC ctx args[0]!
    return (c, ← mkAppOptM ``Decidable.decide #[q, none])
  | some c, _ =>
    if let some v ← find? b then return (.var v, b)
    if c == ctx.fn then throwError "frontx: recursive call not in tail position{indentExpr b}"
    for a in args do
      if a.hasFVar && !a.isFVar && (← find? a).isNone then
        if let some aty ← classify (← inferType a) then
          let (m, a') ← trE ctx a
          let m ← fit m
          let v ← fresh
          modify fun s => { s with memo := (a, v) :: s.memo, temps := a :: s.temps,
                                   pend := s.pend.push (.let_ v m a a' aty s.temps) }
    match ← unfoldDefinition? b with
    | some b' =>
      modify fun s => if s.unfolded.contains c then s else { s with unfolded := s.unfolded.push c }
      trB ctx b'
    | none => throwError "frontx: unsupported Bool{indentExpr b}"
  | _, _ => throwError "frontx: unsupported Bool{indentExpr b}"

end

/-- emit loads for the array reads of `e` that are not yet in a variable -/
def hoist (ctx : Ctx) (e : Expr) : TrM Unit := do
  for r in reads ctx e do
    if (← find? r).isSome then continue
    let some (xs, i) := read? r | unreachable!
    let some (b, _) := ctx.block? xs | unreachable!
    let (idx, i') ← trE ctx i
    let v ← fresh
    modify fun s => { s with memo := (r, v) :: s.memo, pend := s.pend.push (.load v b idx r i' s.temps) }

def takePend : TrM (List Item) := modifyGet fun s => (s.pend.toList, { s with pend := #[] })

/-- run `x` and forget the variables it bound (a branch) -/
def inBranch {α : Type} (x : TrM α) : TrM α := do
  let s ← get
  let r ← x
  modify fun s' => { s' with memo := s.memo, temps := s.temps }
  return r

/-! ## the rewriting set -/

def simpNames : Array Name :=
  #[``Tree.step, ``denote_var, ``denote_const, ``denote_bin, ``denote_ite, ``sel_c, ``Op.eval, ``parSet, ``BEnv.set,
    ``seqSet, ``rB_def, ``rd0, ``rd1, ``rd2, ``blk_get, ``r8_fold, ``ba_get!, ``c_not, ``c_and, ``c_or, ``c_eq0, ``c_not', ``c_and', ``c_or', ``c_eq0',
    ``rN_lit, ``r8_lit, ``r32_lit, ``r64_lit, ``rN_toNat, ``rN_add, ``rN_sub, ``rN_lt, ``rN_inj, ``rN_eq_lit, ``rN_lt_lit, ``rN_lit_lt, ``rN_ite,
    ``r64_add, ``r64_sub, ``r64_and, ``r64_or, ``r64_xor, ``r64_ite, ``r64_eq', ``r64_lt', ``r64_le', ``r64_toNat, ``r64_ofNat,
    ``r32_add, ``r32_sub, ``r32_and, ``r32_or, ``r32_xor, ``r32_ite, ``r32_eq', ``r32_lt', ``r32_le', ``r32_toNat, ``r32_shr,
    ``r8_add, ``r8_sub, ``r8_and, ``r8_or, ``r8_xor, ``r8_ite, ``r8_eq', ``r8_lt', ``r8_le', ``r8_toNat,
    ``r8_dite, ``r32_dite, ``r64_dite, ``rN_dite,
    ``r32_of8, ``r64_of8, ``r64_of32, ``r8_of32, ``r32_of64, ``r8_of64, ``r8_ofNat, ``r32_ofNat]

/-- expression evaluation, and every supported operation pushed through its representation function -/
macro "frontx_simp" "[" ts:ident,* "]" : tactic => do
  let ids := ts.getElems ++ simpNames.map mkIdent
  let ls ← ids.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:ident)
  `(tactic| simp +zetaDelta (disch := omega) [$ls,*, *])

/-- prove one obligation: generalise the Lean terms held in temporaries, then `frontx_simp` / `omega` -/
def oblig (type : Expr) (temps? : Option (List Expr) := none) : TrM Expr := do
  let st ← get
  let temps := temps?.getD st.temps
  modify fun s => { s with nObl := s.nObl + 1 }
  let mv ← mkFreshExprSyntheticOpaqueMVar type
  let mut g := mv.mvarId!
  for L in temps do
    let hyps ← g.withContext do
      (← getLCtx).foldlM (init := #[]) fun acc d => do
        if d.isImplementationDetail then return acc
        if (← isProp d.type) && (d.type.find? (· == L)).isSome then return acc.push d.fvarId else return acc
    -- a `Nat` temporary keeps its defining equation (for `omega`: bounds of the new arguments)
    let isNat := (← whnfR (← inferType L)).isConstOf ``Nat
    let hn ← mkFreshUserName `hg
    let arg : GeneralizeArg := { expr := L, hName? := if isNat then some hn else none }
    try
      let (_, _, g') ← g.generalizeHyp #[arg] hyps
      g := g'
    catch _ =>
      let (_, g') ← g.generalize #[arg]
      g := g'
  let us := st.unfolded.map mkIdent
  let tac ← `(tactic| first | rfl | omega | (frontx_simp [$us,*] <;> first | done | omega | rfl |
    (intro hq; frontx_simp [$us,*] <;> first | done | omega | rfl)))
  let rest ← try Tactic.run g (Tactic.withoutRecover (Tactic.evalTactic tac)) catch e =>
    throwError "frontx: could not prove{indentExpr type}\n{e.toMessageData}"
  unless rest.isEmpty do
    throwError "frontx: could not prove{indentExpr type}\nremaining:\n{goalsToMessageData rest}"
  instantiateMVars mv

def bv0 : Expr := mkBV 0
def denoteE (env : Expr) (m : ME) : Expr := mkApp2 (mkConst ``BExp.denote) env m.toExpr
def setE (env : Expr) (v : Nat) (x : Expr) : Expr := mkApp3 (mkConst ``BEnv.set) env (toExpr v) x

/-- the obligation of a test: `c.denote env = if P then 1 else 0`, turned into `c.denote env ≠ 0 ↔ P` -/
def testOblig (env : Expr) (c : ME) (P : Expr) : TrM Expr := do
  let inst ← synthInstance (mkApp (mkConst ``Decidable) P)
  let rhs := mkAppN (mkConst ``ite [levelOne]) #[bv64, P, inst, mkBV 1, mkBV 0]
  let h ← oblig (← mkEq (denoteE env c) rhs)
  return mkAppN (mkConst ``ne0_of_c) #[denoteE env c, P, inst, h]

/-- emit the pending items around the node built by `k` (which receives the environment after them) -/
partial def wrapItems (ctx : Ctx) (items : List Item) (env : Expr)
    (k : Expr → TrM (MT × Expr × Expr)) : TrM (MT × Expr × Expr) :=
  match items with
  | [] => k env
  | .let_ v m L L' ty temps :: rest => do
    let x := ty.rep L
    let hx ← oblig (← mkEq (denoteE env m) (ty.rep L')) temps
    let (t, o, p) ← wrapItems ctx rest (setE env v x) k
    return (.let_ v m t, o, mkAppN (mkConst ``sim_let)
      #[ctx.A, ctx.R, toExpr v, m.toExpr, ← t.toExpr, env, ctx.heap, x, o, hx, p])
  | .raw v m :: rest => do
    let x := denoteE env m
    let (t, o, p) ← wrapItems ctx rest (setE env v x) k
    return (.let_ v m t, o, mkAppN (mkConst ``sim_let)
      #[ctx.A, ctx.R, toExpr v, m.toExpr, ← t.toExpr, env, ctx.heap, x, o, ← mkEqRefl x, p])
  | .load v b i r idx temps :: rest => do
    let y := mkApp (mkConst ``UInt8.toBitVec) r
    let hj ← oblig (← mkEq (mkApp2 (mkConst ``BitVec.toNat) (toExpr (64 : Nat)) (denoteE env i)) idx) temps
    let hr ← oblig (← mkEq (mkApp3 (mkConst ``rd) ctx.heap (toExpr b) idx) (← mkAppM ``some #[y])) temps
    let (t, o, p) ← wrapItems ctx rest (setE env v (mkApp (mkConst ``r8) r)) k
    return (.load v b i t, o, mkAppN (mkConst ``sim_load)
      #[ctx.A, ctx.R, toExpr v, toExpr b, i.toExpr, ← t.toExpr, env, ctx.heap, idx, y, o, hj, hr, p])

  | .cload v b i c d r idx temps :: rest => do
    let z := mkApp (mkConst ``r8) r
    let hj ← oblig (← mkEq (mkApp2 (mkConst ``BitVec.toNat) (toExpr (64 : Nat)) (denoteE env i)) idx) temps
    let rdE := mkApp3 (mkConst ``rd) ctx.heap (toExpr b) idx
    let bv8 := mkApp (mkConst ``BitVec) (toExpr (8 : Nat))
    let mapped := mkApp4 (mkConst ``Option.map [0, 0]) bv8 bv64
      (mkApp2 (mkConst ``BitVec.setWidth) (toExpr (8 : Nat)) (toExpr (64 : Nat))) rdE
    let hc ← oblig (← mkArrow (← mkAppM ``Ne #[denoteE env c, bv0]) (← mkEq mapped (← mkAppM ``some #[z]))) temps
    let hd ← oblig (← mkArrow (← mkEq (denoteE env c) bv0) (← mkEq (denoteE env d) z)) temps
    let (t, o, p) ← wrapItems ctx rest (setE env v z) k
    return (.cload v b i c d t, o, mkAppN (mkConst ``sim_cload)
      #[ctx.A, ctx.R, toExpr v, toExpr b, i.toExpr, c.toExpr, d.toExpr, ← t.toExpr, env, ctx.heap, idx, z, o,
        hj, hc, hd, p])

/-- the conjuncts of a right-nested conjunction of `n` propositions -/
def splitAnd : Nat → Expr → List Expr
  | 0, _ => []
  | 1, e => [e]
  | n + 2, e => e.appFn!.appArg! :: splitAnd (n + 1) e.appArg!

def mkTuple : List (Expr × Expr) → MetaM (Expr × Expr)
  | [] => return (mkConst ``Unit, mkConst ``Unit.unit)
  | [(x, t)] => return (t, x)
  | (x, t) :: rest => do
    let (rt, rx) ← mkTuple rest
    return (mkApp2 (mkConst ``Prod [0, 0]) t rt, mkApp4 (mkConst ``Prod.mk [0, 0]) t rt x rx)

/-- strip the `Id` monad structure at the head of a term (`bind x f ↦ f x`, `pure x ↦ x`, `Id.run x ↦ x`; all
definitional) -/
partial def idNorm (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  let f := e.getAppFn.consumeMData
  if f.isLambda && e.isApp then return ← idNorm (f.beta e.getAppArgs)
  if e.isAppOfArity ``Bind.bind 6 then
    let x ← idNorm (e.getArg! 4)
    return ← idNorm (mkApp (e.getArg! 5) x)
  if e.isAppOfArity ``Pure.pure 4 then return ← idNorm (e.getArg! 3)
  if e.isAppOfArity ``Id.run 2 then return ← idNorm (e.getArg! 1)
  return e

/-- reduce `(MProd.mk a b).fst` etc. everywhere -/
def reduceProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    if e.isAppOfArity ``MProd.fst 3 || e.isAppOfArity ``MProd.snd 3 then
      let s := e.appArg!
      if s.isAppOfArity ``MProd.mk 4 then
        return .done (if e.isAppOfArity ``MProd.fst 3 then s.getArg! 2 else s.getArg! 3)
    if let .proj ``MProd i s := e then
      if s.isAppOfArity ``MProd.mk 4 then return .done (s.getArg! (2 + i))
    return .continue)

/-- the component types of a loop state `MProd α (MProd β …)` (or a single type, or `PUnit`) -/
partial def flattenS (S : Expr) : MetaM (List Expr) := do
  let S ← whnfR S
  if S.isAppOfArity ``MProd 2 then return S.getArg! 0 :: (← flattenS (S.getArg! 1))
  if S.isConstOf ``PUnit || S.isConstOf ``Unit then return []
  return [S]

/-- the components of a state term of type `S` -/
partial def stateComps (S s : Expr) : MetaM (List Expr) := do
  let S ← whnfR S
  if S.isAppOfArity ``MProd 2 then
    let s' ← whnfR s
    if s'.isAppOfArity ``MProd.mk 4 then return s'.getArg! 2 :: (← stateComps (S.getArg! 1) (s'.getArg! 3))
    return (← mkAppM ``MProd.fst #[s]) :: (← stateComps (S.getArg! 1) (← mkAppM ``MProd.snd #[s]))
  if S.isConstOf ``PUnit || S.isConstOf ``Unit then return []
  return [s]

/-- the state term of type `S` with the given components -/
partial def mkState (S : Expr) (xs : List Expr) : MetaM Expr := do
  let S ← whnfR S
  if S.isAppOfArity ``MProd 2 then
    match xs with
    | x :: r => return ← mkAppM ``MProd.mk #[x, ← mkState (S.getArg! 1) r]
    | [] => throwError "frontx: state arity"
  if S.isConstOf ``PUnit then return mkConst ``PUnit.unit S.constLevels!
  if S.isConstOf ``Unit then return mkConst ``Unit.unit
  match xs with
  | [x] => return x
  | _ => throwError "frontx: state arity"

/-- a value after the loop: beta, `Id`, `match` on the state tuple, `let` -/
partial def valNorm (v : Expr) (fuel : Nat := 16) : MetaM Expr := do
  let v ← idNorm v
  if fuel == 0 then return v
  if v.isLet then return ← valNorm (v.letBody!.instantiate1 v.letValue!) (fuel - 1)
  if (← matchMatcherApp? v).isSome then
    let v' ← whnfCore v
    if v' != v then return ← valNorm v' (fuel - 1)
  return v

def mkConjPf : List Expr → List Expr → MetaM Expr
  | [_], [p] => pure p
  | c :: cs, p :: ps => do
    let q ← mkConjPf cs ps
    return mkApp4 (mkConst ``And.intro) c (← inferType q) p q
  | _, _ => pure (mkConst ``True.intro)

/-- a `call` leaf: the assignments `v := e` (the changed variables), the arguments of `Rep` after them, the
argument tuple `a`, and the outcome term -/
def callLeaf (ctx : Ctx) (nconj : Nat) (env : Expr) (as : Array (Nat × Expr)) (repArgs : Array Expr → Array Expr)
    (a out : Expr) : TrM (MT × Expr × Expr) := do
  let mut ms := #[]
  let mut vals := #[]
  for (v, e) in as do
    let (m, e') ← trE ctx e
    ms := ms.push (v, ← fit m)
    vals := vals.push e'
  wrapItems ctx (← takePend) env fun env => do
    let mt := MT.call ms.toList
    let asE := (← mt.toExpr).appArg!
    let σ₁ := mkApp2 (mkConst ``BState.mk) (mkApp3 (mkConst ``parSet) env env asE) ctx.heap
    let some conj ← unfoldDefinition? (mkAppN (mkConst ctx.repN) ((repArgs vals).push σ₁))
      | throwError "frontx: cannot unfold {ctx.repN}"
    let cs := splitAnd nconj conj.headBeta
    let ps ← cs.mapM (oblig ·)
    let h ← mkConjPf cs ps
    return (mt, out, mkAppN (mkConst ``sim_call) #[ctx.A, ctx.R, asE, env, ctx.heap, a, h])

/-- a `ret` leaf returning the Lean value `e` (`r` is the `BitVec 64` term of the outcome) -/
def retLeaf (ctx : Ctx) (env : Expr) (e r out : Expr)
    (fix : Expr → Expr → MetaM Expr := fun _ h => pure h) : TrM (MT × Expr × Expr) := do
  let (m, e') ← trE ctx e
  let m ← fit m
  wrapItems ctx (← takePend) env fun env => do
    let h ← oblig (← mkEq (denoteE env m) (ctx.rty.rep e'))
    let h ← fix (denoteE env m) h
    return (.ret m, out, mkAppN (mkConst ``sim_ret) #[ctx.A, ctx.R, m.toExpr, env, ctx.heap, r, h])

/-- a term in tail position, in the environment `env`: its tree, its Lean outcome `o : LOut A`, and a proof of
`Sim R tree ⟨env, heap⟩ o` -/
partial def trT (ctx : Ctx) (nconj : Nat) (env : Expr) (e : Expr) : TrM (MT × Expr × Expr) := do
  let e ← if ctx.loop.isSome then idNorm e else pure e.consumeMData.headBeta
  let lout := mkApp (mkConst ``LOut) ctx.A
  if e.isLet then
    let v := e.letValue!
    if v.hasFVar && !v.isFVar && (← find? v).isNone then
      if let some ty ← classify e.letType! then
        let (m, v') ← trE ctx v
        let m ← fit m
        let x ← fresh
        modify fun s => { s with memo := (v, x) :: s.memo, temps := v :: s.temps,
                                 pend := s.pend.push (.let_ x m v v' ty s.temps) }
    return ← trT ctx nconj env (e.letBody!.instantiate1 v)
  let args := e.getAppArgs
  -- a two-way branch on `P`
  let branch (P inst : Expr) (mkT mkF : Expr → Expr) : TrM (MT × Expr × Expr) := do
    let (c, P') ← trC ctx P
    let c ← fit c
    wrapItems ctx (← takePend) env fun env => do
      let hc ← testOblig env c P'
      let br (hty : Expr) (mk : Expr → Expr) : TrM (MT × Expr × Expr × Expr) := inBranch do
        withLocalDeclD `h hty fun h => do
          let (t, o, p) ← trT ctx nconj env (mk h)
          let tail := if ctx.loop.isSome then o.appArg! else o
          return (t, ← mkLambdaFVars #[h] o, ← mkLambdaFVars #[h] p, ← mkLambdaFVars #[h] tail)
      let (t, o₁, p₁, x₁) ← br P mkT
      let (f, o₂, p₂, x₂) ← br (mkNot P) mkF
      match ctx.loop with
      | none =>
        let out := mkAppN (mkConst ``dite [levelOne]) #[lout, P, inst, o₁, o₂]
        let pf := mkAppN (mkConst ``sim_dite)
          #[ctx.A, ctx.R, c.toExpr, ← t.toExpr, ← f.toExpr, env, ctx.heap, P, inst, o₁, o₂, hc, p₁, p₂]
        return (.ite c t f, out, pf)
      | some li =>
        let out := mkApp li.g (mkAppN (mkConst ``dite [levelOne]) #[li.T, P, inst, x₁, x₂])
        let pf := mkAppN (mkConst ``sim_dite_g)
          #[ctx.A, ctx.R, li.T, li.g, c.toExpr, ← t.toExpr, ← f.toExpr, env, ctx.heap, P, inst, x₁, x₂, hc, p₁, p₂]
        return (.ite c t f, out, pf)
  if e.isAppOfArity ``ite 5 then
    return ← branch args[1]! args[2]! (fun _ => args[3]!) (fun _ => args[4]!)
  if e.isAppOfArity ``dite 5 then
    return ← branch args[1]! args[2]! (fun h => args[3]!.beta #[h]) (fun h => args[4]!.beta #[h])
  -- `match n with | 0 => A | m + 1 => B` on a `Nat`: a test `n = 0`, with `m := n - 1`
  if let some ma ← matchMatcherApp? e then
    if ma.discrs.size == 1 && ma.alts.size == 2 && ma.remaining.isEmpty then
      let n := ma.discrs[0]!
      if (← whnfR (← inferType n)).isConstOf ``Nat then
        let (iz, is) ← (do
          if ma.altNumParams[1]! == 1 && ma.altNumParams[0]! ≤ 1 then pure (0, 1)
          else if ma.altNumParams[0]! == 1 && ma.altNumParams[1]! ≤ 1 then pure (1, 0)
          else throwError "frontx: unsupported match{indentExpr e}" : TrM (Nat × Nat))
        let zero := ma.alts[iz]!
        let zero := if zero.isLambda then zero.beta #[mkConst ``Unit.unit] else zero
        let pred ← mkAppM ``HSub.hSub #[n, toExpr (1 : Nat)]
        let P ← mkEq n (toExpr (0 : Nat))
        let inst ← synthInstance (mkApp (mkConst ``Decidable) P)
        return ← branch P inst (fun _ => zero) (fun _ => ma.alts[is]!.beta #[pred])
    throwError "frontx: unsupported match{indentExpr e}"
  if let some li := ctx.loop then
    -- the leaves of a loop body
    if e.isAppOfArity ``ForInStep.yield 2 then
      let s' := e.appArg!
      let news ← stateComps li.S s'
      let i1 ← mkAppM ``HAdd.hAdd #[li.i, toExpr (1 : Nat)]
      let mut as := #[(li.iv, i1)]
      -- per local: `some k` = the k-th assigned value, `none` = this term as it is
      let mut src : Array (Option Nat × Expr) := #[]
      for ((x, v?), n) in li.comps.zip news.toArray do
        match v? with
        | none =>
          unless (← whnfR n).isAppOfArity ``Option.none 1 do
            throwError "frontx: an `Option` local must stay `none` in the loop{indentExpr n}"
          src := src.push (none, n)
        | some v =>
          if n == x then src := src.push (none, x)
          else
            src := src.push (some as.size, n)
            as := as.push (v, n)
      let repArgs (vals : Array Expr) : Array Expr :=
        ctx.params.push vals[0]! ++ src.map fun (k?, e) => match k? with | some k => vals[k]! | none => e
      let a := mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) li.S i1 s'
      return ← callLeaf ctx nconj env as repArgs a (mkApp li.g e)
    if e.isAppOfArity ``ForInStep.done 2 then
      let s' := e.appArg!
      let v ← valNorm (mkApp li.postLean s')
      return ← retLeaf ctx env v (mkApp li.postBV s') (mkApp li.g e)
    throwError "frontx: unsupported term in a loop body{indentExpr e}"
  if e.getAppFn.isConstOf ctx.fn && args.size == ctx.params.size then
    let mut as := #[]
    let mut idx := #[]
    for j in [0:args.size] do
      let p := ctx.params[j]!
      if args[j]! == p then continue
      if (ctx.block? p).isSome then throwError "frontx: array argument changed in the call{indentExpr e}"
      let some v ← find? p | throwError "frontx: parameter without a variable{indentExpr p}"
      as := as.push (v, args[j]!)
      idx := idx.push j
    let repArgs (vals : Array Expr) : Array Expr := Id.run do
      let mut r := args
      for (j, k) in idx.zipIdx do
        r := r.set! j vals[k]!
      return r
    let (_, a) ← mkTuple (← args.toList.mapM fun x => do return (x, ← inferType x))
    return ← callLeaf ctx nconj env as repArgs a (mkApp2 (mkConst ``LOut.call) ctx.A a)
  let r := ctx.rty.rep e
  retLeaf ctx env e r (mkApp2 (mkConst ``LOut.ret) ctx.A r)

/-! ## the induction -/

/-- apply the induction hypothesis: the first local hypothesis that `apply` accepts -/
elab "frontx_ih" : tactic => withMainContext do
  let g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless (← whnfR (← instantiateMVars d.type)).isForall do continue
    let s ← saveState
    try
      let gs ← g.apply d.toExpr
      replaceMainGoal gs
      return
    catch _ => s.restore
  throwError "frontx_ih: no hypothesis applies"

/-- in `h : Sim R k σ o`, follow the `if`s of `o` with the path conditions of the context -/
elab "frontx_path " h:ident : tactic => withMainContext do
  let mut pf := (← getLocalDeclFromUserName h.getId).toExpr
  repeat
    let ty ← whnfR (← inferType pf)
    unless ty.isAppOfArity ``Sim 5 do break
    let a := ty.getAppArgs
    let o ← whnfR a[4]!
    unless o.isAppOfArity ``dite 5 do break
    let oa := o.getAppArgs
    let P := oa[1]!
    let mut found := false
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let dty ← instantiateMVars d.type
      unless ← isProp dty do continue
      if ← isDefEq dty P then
        pf := mkAppN (mkConst ``sim_pos) #[a[0]!, a[1]!, a[2]!, a[3]!, P, oa[2]!, oa[3]!, oa[4]!, d.toExpr, pf]
        found := true; break
      if ← isDefEq dty (mkNot P) then
        pf := mkAppN (mkConst ``sim_neg) #[a[0]!, a[1]!, a[2]!, a[3]!, P, oa[2]!, oa[3]!, oa[4]!, d.toExpr, pf]
        found := true; break
    unless found do
      -- functional induction may have substituted an equation: the test is then closed by `rfl`
      match P.eq? with
      | some (_, x, y) =>
        if ← isDefEq x y then
          pf := mkAppN (mkConst ``sim_pos) #[a[0]!, a[1]!, a[2]!, a[3]!, P, oa[2]!, oa[3]!, oa[4]!, ← mkEqRefl x, pf]
          found := true
      | none => pure ()
    unless found do
      -- or the test is decided by arithmetic (a `match` on a `Nat` turned into `n = 0`)
      let tryProve (ty : Expr) : TacticM (Option Expr) := do
        let s ← saveState
        try
          let mv ← mkFreshExprSyntheticOpaqueMVar ty
          let rest ← Tactic.run mv.mvarId! (Tactic.withoutRecover (Tactic.evalTactic (← `(tactic| first | rfl | omega | simp))))
          if rest.isEmpty then return some (← instantiateMVars mv) else s.restore; return none
        catch _ => s.restore; return none
      if let some h ← tryProve P then
        pf := mkAppN (mkConst ``sim_pos) #[a[0]!, a[1]!, a[2]!, a[3]!, P, oa[2]!, oa[3]!, oa[4]!, h, pf]
        found := true
      else if let some h ← tryProve (mkNot P) then
        pf := mkAppN (mkConst ``sim_neg) #[a[0]!, a[1]!, a[2]!, a[3]!, P, oa[2]!, oa[3]!, oa[4]!, h, pf]
        found := true
    unless found do throwError "frontx_path: no hypothesis decides{indentExpr P}"
  let ty ← inferType pf
  let a := ty.getAppArgs
  let ty ← if ty.isAppOfArity ``Sim 5 then pure (mkAppN ty.getAppFn (a.set! 4 (← whnfR a[4]!))) else pure ty
  let g ← getMainGoal
  let (_, g) ← (← g.assert h.getId ty pf).intro1P
  replaceMainGoal [g]

/-! ## the command -/

def addThm (name : Name) (type : Expr) (tac : TSyntax `tactic) : TermElabM Unit := do
  let type ← instantiateMVars type
  let pf ← elabTermEnsuringType (← `(by $tac:tactic)) type
  synthesizeSyntheticMVarsNoPostponing
  let pf ← instantiateMVars pf
  if pf.hasSorry || pf.hasMVar then throwError "frontx: could not prove {name}"
  addDecl (.thmDecl { name, levelParams := [], type, value := pf })

def addDef (name : Name) (type value : Expr) (compile := false) : TermElabM Unit := do
  let d := Declaration.defnDecl (mkDefinitionValEx name [] type value .abbrev .safe [name])
  if compile then addAndCompile d else addDecl d
  setReducibleAttribute name
  enableRealizationsForConst name

/-- prove `type` by a tactic -/
def byTac (type : Expr) (tac : TSyntax `tactic) : TermElabM Expr := do
  let mv ← mkFreshExprSyntheticOpaqueMVar type
  let rest ← Tactic.run mv.mvarId! (Tactic.withoutRecover (Tactic.evalTactic tac))
  unless rest.isEmpty do throwError "frontx: could not prove{indentExpr type}"
  instantiateMVars mv

/-- the right-nested projections of a proof of an `n`-fold conjunction -/
def conjProjs (n : Nat) (h : Expr) : MetaM (Array Expr) := do
  let mut projs := #[]
  let mut cur := h
  for i in [0:n] do
    if i + 1 == n then projs := projs.push cur
    else
      projs := projs.push (← mkAppM ``And.left #[cur])
      cur ← mkAppM ``And.right #[cur]
  return projs

/-- strip `Id.run` and leading `let`s -/
partial def stripPre (e : Expr) : Expr :=
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``Id.run 2 then stripPre (e.getArg! 1)
  else if e.isLet then stripPre (e.letBody!.instantiate1 e.letValue!)
  else e

/-- `(forIn …, code after the loop)` if `e` is `forIn … >>= post` or `forIn …` in `Id` -/
def asFor? (e : Expr) : MetaM (Option (Expr × Option Expr)) := do
  if e.isAppOfArity ``Bind.bind 6 && (e.getArg! 4).consumeMData.isAppOfArity ``forIn 8 then
    return some ((e.getArg! 4).consumeMData, some (e.getArg! 5))
  if e.isAppOfArity ``forIn 8 then return some (e, none)
  return none

/-- the loop of a body, unfolding helper definitions at the head (so `skipWs bs i := skipWhile bs i isWs` is the
loop of `skipWhile` with the predicate filled in) -/
partial def findFor (fn : Name) (e : Expr) (fuel : Nat := 8) : MetaM (Option (Expr × Option Expr)) := do
  if let some r ← asFor? e then return some r
  if fuel == 0 then return none
  let some c := e.getAppFn.constName? | return none
  if c == fn || c == ``ite || c == ``dite || (← matchMatcherApp? e).isSome then return none
  unless (← getConstInfo c) matches .defnInfo _ do return none
  let some e' ← unfoldDefinition? e | return none
  findFor fn (stripPre e') (fuel - 1)

/-- `frontx_compile` for a function whose body is `Id.run do <lets>; for i in [a:b] do <body>; <result>`:
the mutable locals and `i` become variables, the loop becomes the tree loop (`for_exec`). Adds `f.tree`, `f.lay`,
`f.slots`, `f.inits`, `f.Rep0` (the state holds the parameters), `f.Rep` (… and `i` and the locals), `f.step1`,
`f.exec`. -/
def compileLoop (fn : Name) (xs : Array Expr) (rty : Ty) (lhs forE : Expr) (post? : Option Expr)
    (inv? : Option Term) (t0 : Nat) : TermElabM Unit := do
  let fa := forE.getAppArgs
  let S := fa[4]!
  let init := fa[6]!
  let F := fa[7]!
  let range ← whnfR fa[5]!
  unless (← whnfR fa[0]!).isConstOf ``Id && range.isAppOfArity ``Std.Legacy.Range.mk 4 do
    throwError "frontx: only `for i in [a:b]` in `Id` is supported{indentExpr forE}"
  let a := range.getArg! 0
  let b := range.getArg! 1
  unless (range.getArg! 2).nat? == some 1 || (range.getArg! 2).rawNatLit? == some 1 do
    throwError "frontx: range step must be 1"
  let nat := Lean.mkConst ``Nat
  let bstate := Lean.mkConst ``BState
  let repN := fn ++ `Rep
  let rep0N := fn ++ `Rep0
  let treeN := fn ++ `tree
  let layN := fn ++ `lay
  let stepN := fn ++ `step1
  let initsN := fn ++ `inits
  -- variables for the parameters
  let mut blocks : List (Expr × Nat × Nat) := []
  let mut next := 0
  let mut memo : List (Expr × Nat) := []
  let mut scal : Array (Expr × Ty × Nat) := #[]
  for x in xs do
    let xty ← inferType x
    if (← whnfR xty).isConstOf ``ByteArray then
      blocks := blocks ++ [(x, blocks.length, next + 1)]
      next := next + 2
    else
      let some ty ← classify xty | throwError "frontx: unsupported parameter type{indentExpr xty}"
      memo := (x, next) :: memo
      scal := scal.push (x, ty, next)
      next := next + 1
  let iv := next
  let ctys ← flattenS S
  -- per local: its kind (`none` = an `Option` that stays `none`) and its variable
  let mut ctyK : Array (Option Ty) := #[]
  let mut cvars : Array (Option Nat) := #[]
  let mut next' := iv + 1
  for t in ctys do
    if (← whnfR t).isAppOfArity ``Option 1 then
      ctyK := ctyK.push none
      cvars := cvars.push none
    else
      let some ty ← classify t | throwError "frontx: unsupported mutable local of type{indentExpr t}"
      ctyK := ctyK.push (some ty)
      cvars := cvars.push (some next')
      next' := next' + 1
  let invE? ← inv?.mapM fun inv => do
    let ty ← mkForallFVars xs (← (#[Lean.mkConst ``Nat] ++ ctys.toArray).foldrM (fun d acc => mkArrow d acc) (mkSort 0))
    let e ← elabTerm inv (some ty)
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let out : Nat := match scal[0]? with | some (_, _, v) => v | none => iv
  let two64 ← mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr (64 : Nat)]
  let hyps0 (σ : Expr) : TermElabM (Array Expr) := do
    let env := mkApp (mkConst ``BState.env) σ
    let heap := mkApp (mkConst ``BState.heap) σ
    let mut hyps : Array Expr := #[]
    if !blocks.isEmpty then
      let bl ← mkListLit (← mkAppM ``List #[mkApp (mkConst ``BitVec) (toExpr (8 : Nat))])
        (blocks.map fun (x, _, _) => mkApp (mkConst ``blk) x)
      hyps := hyps.push (← mkEq heap bl)
    for (x, _, len) in blocks do
      let sz := mkApp (mkConst ``ByteArray.size) x
      hyps := hyps.push (← mkEq (mkApp env (toExpr len)) (mkApp (mkConst ``rN) sz))
      hyps := hyps.push (← mkAppM ``LT.lt #[sz, two64])
    for (x, ty, v) in scal do
      hyps := hyps.push (← mkEq (mkApp env (toExpr v)) (ty.rep x))
      if ty == .nat then hyps := hyps.push (← mkAppM ``LT.lt #[x, two64])
    if hyps.isEmpty then hyps := #[mkConst ``True]
    return hyps
  let hypsL (σ i : Expr) (cs : Array Expr) : TermElabM (Array Expr) := do
    let env := mkApp (mkConst ``BState.env) σ
    let mut hyps ← hyps0 σ
    hyps := hyps.push (← mkEq (mkApp env (toExpr iv)) (mkApp (mkConst ``rN) i))
    hyps := hyps.push (← mkAppM ``LT.lt #[i, two64])
    for ((x, ty?), v?) in (cs.zip ctyK).zip cvars do
      match ty?, v? with
      | some ty, some v =>
        hyps := hyps.push (← mkEq (mkApp env (toExpr v)) (ty.rep x))
        if ty == .nat then hyps := hyps.push (← mkAppM ``LT.lt #[x, two64])
      | _, _ =>
        let xty ← whnfR (← inferType x)
        hyps := hyps.push (← mkEq x (mkApp (mkConst ``Option.none xty.getAppFn.constLevels!) xty.appArg!))
    if let some invE := invE? then hyps := hyps.push (invE.beta (xs ++ #[i] ++ cs))
    return hyps
  let mkConjE (hs : Array Expr) : Expr := hs.pop.foldr mkAnd hs.back!
  let A := mkApp2 (mkConst ``Prod [0, 0]) nat S
  let lout := mkApp (mkConst ``LOut) A
  let T := mkApp (mkConst ``Id [levelZero]) (mkApp (mkConst ``ForInStep [levelZero]) S)
  let postLean ← match post? with
    | some p => pure p
    | none => withLocalDeclD `s S fun s => mkLambdaFVars #[s] s
  let postBV ← withLocalDeclD `s S fun s => do mkLambdaFVars #[s] (rty.rep (mkApp postLean s).headBeta)
  let cdecls := ((List.range ctys.length).zip ctys).toArray.map fun (j, t) => (Name.mkSimple s!"x{j}", t)
  -- `Rep0`, `Rep`
  let n0 ← withLocalDeclD `σ bstate fun σ => do
    let hyps ← hyps0 σ
    addDef rep0N (← mkForallFVars (xs.push σ) (mkSort 0)) (← mkLambdaFVars (xs.push σ) (mkConjE hyps))
    return hyps.size
  let nconj ← withLocalDeclD `i nat fun i => withLocalDeclsDND cdecls fun cs => withLocalDeclD `σ bstate fun σ => do
    let hyps ← hypsL σ i cs
    let bs := xs ++ #[i] ++ cs ++ #[σ]
    addDef repN (← mkForallFVars bs (mkSort 0)) (← mkLambdaFVars bs (mkConjE hyps))
    return hyps.size
  let R ← withLocalDeclD `a A fun av => withLocalDeclD `σ bstate fun σ => do
    let comps ← stateComps S (← mkAppM ``Prod.snd #[av])
    mkLambdaFVars #[av, σ] (mkAppN (mkConst repN) (xs ++ #[← mkAppM ``Prod.fst #[av]] ++ comps.toArray ++ #[σ]))
  -- one iteration
  let (mt, st, stepClosed, P, inst) ←
    withLocalDeclD `i nat fun i => withLocalDeclsDND cdecls fun cs => withLocalDeclD `σ bstate fun σ => do
      let hyps ← hypsL σ i cs
      let decls := hyps.mapIdx fun k h => (Name.mkSimple s!"h{k}", h)
      let sT ← mkState S cs.toList
      let li : LoopInfo := { g := mkAppN (mkConst ``cvt) #[S, postBV, i], T, S, postBV, postLean, i, iv,
                             comps := cs.zip cvars }
      let ctx : Ctx := { fn, params := xs, blocks, A, R, heap := mkApp (mkConst ``BState.heap) σ, repN, rty,
                         loop := some li }
      let P ← mkAppM ``LT.lt #[i, b]
      let inst ← synthInstance (mkApp (mkConst ``Decidable) P)
      let memo' := (i, iv) :: (cs.zip cvars).toList.filterMap (fun (x, v?) => v?.map (x, ·)) ++ memo
      withLocalDeclsDND decls fun hs => do
        let env0 := mkApp (mkConst ``BState.env) σ
        let top : TrM (MT × Expr × Expr) := do
          let (c, P') ← trC ctx P
          let c ← fit c
          wrapItems ctx (← takePend) env0 fun env => do
            let hc ← testOblig env c P'
            let (t, o₁, p₁) ← inBranch <| withLocalDeclD `h P fun h => do
              let body ← reduceProjs (mkApp2 F i sT).headBeta
              let (t, o, p) ← trT ctx nconj env body
              return (t, ← mkLambdaFVars #[h] o, ← mkLambdaFVars #[h] p)
            let (f, o₂, p₂) ← inBranch <| withLocalDeclD `h (mkNot P) fun h => do
              -- the `Option` locals are `none` here: evaluate the code after the loop at `none`, then transport
              let frozen := (cs.zip ctyK).filter (·.2.isNone) |>.map (·.1)
              let mut sN := sT
              let mut eqs := #[]
              for x in frozen do
                let some d ← (← getLCtx).findDeclM? fun d => do
                    let ty ← instantiateMVars d.type
                    return if ty.isAppOfArity ``Eq 3 && ty.getArg! 1 == x then some d else none
                  | throwError "frontx: no hypothesis for the `Option` local"
                let noneE := (← instantiateMVars d.type).getArg! 2
                sN := sN.replaceFVar x noneE
                eqs := eqs.push (x, d.toExpr)
              let v ← valNorm (mkApp postLean sN)
              let r := mkApp postBV sT
              let fix (lhsE h : Expr) : MetaM Expr := do
                let mut h := h
                for k in [0:eqs.size] do
                  let (x, hx) := eqs[k]!
                  -- the state with the first `k + 1` `Option` locals free and the later ones `none`
                  let later := eqs.extract (k + 1) eqs.size
                  let sK := sT.replaceFVars (later.map (·.1))
                    (← later.mapM fun (_, hy) => do return (← inferType hy).getArg! 2)
                  let motive ← mkLambdaFVars #[x] (← mkEq lhsE (mkApp postBV sK).headBeta)
                  h ← mkEqMPR (← mkCongrArg motive hx) h
                return h
              let (t, o, p) ← retLeaf ctx env v r (mkApp2 (mkConst ``LOut.ret) A r) fix
              return (t, ← mkLambdaFVars #[h] o, ← mkLambdaFVars #[h] p)
            let out := mkAppN (mkConst ``dite [levelOne]) #[lout, P, inst, o₁, o₂]
            let pf := mkAppN (mkConst ``sim_dite)
              #[A, R, c.toExpr, ← t.toExpr, ← f.toExpr, env, ctx.heap, P, inst, o₁, o₂, hc, p₁, p₂]
            return (.ite c t f, out, pf)
        let ((mt, _, proof), st) ← top.run { next := next', memo := memo' }
        let closed ← mkLambdaFVars (#[i] ++ cs ++ #[σ] ++ hs) proof
        return (mt, st, closed, ← mkLambdaFVars #[i] P, ← mkLambdaFVars #[i] inst)
  let M := st.next
  let t1 ← IO.monoMsNow
  let nvars := M + 2 + mt.maxK + 2 * mt.cdepth
  addDef treeN (mkConst ``Tree) (← mt.toExpr) (compile := true)
  addDef layN (mkConst ``Lay) (mkApp2 (mkConst ``Lay.mk) (toExpr M) (toExpr mt.maxK)) (compile := true)
  addDef (fn ++ `slots) nat (toExpr (nvars - 8)) (compile := true)
  -- f.step1 : ∀ params i s σ, R (i, s) σ → Sim R tree σ (if i < b then cvt post i (F i s) else ret (post s))
  let (stepTy, stepPf) ← withLocalDeclD `i nat fun i => withLocalDeclD `s S fun s => withLocalDeclD `σ bstate fun σ => do
    let comps := (← stateComps S s).toArray
    let conj := mkConjE (← hypsL σ i comps)
    let Ris := mkApp2 R (mkApp4 (mkConst ``Prod.mk [0, 0]) nat S i s) σ
    let Pi := (mkApp P i).headBeta
    let o₁ := Expr.lam `h Pi (mkApp (mkAppN (mkConst ``cvt) #[S, postBV, i]) (mkApp2 F i s)) .default
    let o₂ := Expr.lam `h (mkNot Pi) (mkApp2 (mkConst ``LOut.ret) A (mkApp postBV s)) .default
    let spec := mkAppN (mkConst ``dite [levelOne]) #[lout, Pi, (mkApp inst i).headBeta, o₁, o₂]
    let ty ← mkForallFVars #[i, s, σ] (← mkArrow Ris (mkAppN (mkConst ``Sim) #[A, R, mkConst treeN, σ, spec]))
    let pf ← withLocalDeclD `hR conj fun hR => do
      let projs ← conjProjs nconj hR
      mkLambdaFVars #[i, s, σ, hR] (mkAppN stepClosed (#[i] ++ comps ++ #[σ] ++ projs)).headBeta
    return (ty, pf)
  let stepTy ← mkForallFVars xs stepTy
  let stepPf ← instantiateMVars (← mkLambdaFVars xs stepPf)
  if stepPf.hasSorry || stepPf.hasMVar then throwError "frontx: step proof incomplete"
  addDecl (.thmDecl { name := stepN, levelParams := [], type := stepTy, value := stepPf })
  let t2 ← IO.monoMsNow
  -- initialisation and f.exec
  let tI := mkIdent treeN
  let lI := mkIdent layN
  let (execTy, execPf, nObl) ← withLocalDeclD `σ bstate fun σ => do
    let hyps ← hyps0 σ
    let decls := hyps.mapIdx fun k h => (Name.mkSimple s!"h{k}", h)
    let env0 := mkApp (mkConst ``BState.env) σ
    let heap := mkApp (mkConst ``BState.heap) σ
    let ctx : Ctx := { fn, params := xs, blocks, A, R, heap, repN, rty }
    let inits0 := (← stateComps S (← whnfR init)).toArray
    let (pfBody, initsE, nObl) ← withLocalDeclsDND decls fun hs => do
      let go : TrM (Expr × Expr) := do
        let mut ms := #[]
        let mut vals := #[]
        for (v?, e) in #[(some iv, a)] ++ cvars.zip inits0 do
          match v? with
          | some v =>
            let (m, e') ← trE ctx e
            ms := ms.push (v, ← fit m)
            vals := vals.push e'
          | none => vals := vals.push e
        unless (← get).pend.isEmpty do throwError "frontx: the initial values need loads or temporaries"
        let initsE := (← (MT.call ms.toList).toExpr).appArg!
        let σ₁ := mkApp2 (mkConst ``BState.mk) (mkApp2 (mkConst ``seqSet) env0 initsE) heap
        let some conj ← unfoldDefinition? (mkAppN (mkConst repN) (xs ++ vals ++ #[σ₁]))
          | throwError "frontx: cannot unfold {repN}"
        let cs := splitAnd nconj conj.headBeta
        let ps ← cs.mapM (oblig ·)
        return (← mkConjPf cs ps, initsE)
      let ((h0, initsE), st') ← go.run { next := M, memo }
      let wfPf ← byTac (mkApp2 (mkConst ``Tree.wf) (mkConst layN) (mkConst treeN))
        (← `(tactic| simp [$tI:ident, $lI:ident, Tree.wf, BExp.vlt]))
      let roPf ← byTac (← mkEq (mkApp (mkConst ``Tree.ro) (mkConst treeN)) (mkConst ``Bool.true)) (← `(tactic| rfl))
      let pf := mkAppN (mkConst ``for_exec) #[S, mkConst layN, mkConst treeN, wfPf, roPf, R, F, postBV, a, b, init,
        mkConst initsN, toExpr out, mkAppN (mkConst stepN) xs, env0, heap, h0]
      return (← mkLambdaFVars hs pf, initsE, st'.nObl)
    addDef initsN (← mkAppM ``List #[pairTy]) initsE (compile := true)
    let prog := mkApp2 (mkConst ``initS) (mkConst initsN)
      (mkApp3 (mkConst ``prog) (mkConst layN) (mkConst treeN) (toExpr out))
    let concl ← withLocalDeclD `σ' bstate fun σ' => do
      let c1 := mkApp3 (mkConst ``BExec) prog σ σ'
      let c2 ← mkEq (mkApp (mkApp (mkConst ``BState.env) σ') (toExpr out)) (rty.rep lhs)
      let c3 ← mkEq (mkApp (mkConst ``BState.heap) σ') heap
      mkAppM ``Exists #[← mkLambdaFVars #[σ'] (mkAnd c1 (mkAnd c2 c3))]
    let ty ← mkForallFVars (xs.push σ) (← mkArrow (mkAppN (mkConst rep0N) (xs.push σ)) concl)
    let pf ← withLocalDeclD `hR (mkConjE hyps) fun hR => do
      mkLambdaFVars (xs ++ #[σ, hR]) (mkAppN pfBody (← conjProjs n0 hR)).headBeta
    return (ty, pf, nObl)
  let execPf ← instantiateMVars execPf
  if execPf.hasSorry || execPf.hasMVar then throwError "frontx: exec proof incomplete"
  addDecl (.thmDecl { name := fn ++ `exec, levelParams := [], type := execTy, value := execPf })
  let t3 ← IO.monoMsNow
  logInfo m!"frontx: {fn} (for loop): {nvars} variables ({M} user), {nvars - 8} slots, result in variable {out}, {st.nObl + nObl} obligations; translate + step proof {t1 - t0} ms, kernel check of step {t2 - t1} ms, init + exec theorem {t3 - t2} ms"


def compileCmd (f : Ident) (inv? : Option Term) : TermElabM Unit := do
  let t0 ← IO.monoMsNow
  let fn ← realizeGlobalConstNoOverloadWithInfo f
  let info ← getConstInfo fn
  let some eqn ← getUnfoldEqnFor? fn (nonRec := true) | throwError "frontx: no unfolding equation for {fn}"
  let eqnTy := (← getConstInfo eqn).type
  let repN := fn ++ `Rep
  let treeN := fn ++ `tree
  let layN := fn ++ `lay
  let outN := fn ++ `out
  let stepN := fn ++ `step1
  let bstate := Lean.mkConst ``BState
  forallTelescope info.type fun xs resTy => do
    let some rty ← classify resTy | throwError "frontx: unsupported result type{indentExpr resTy}"
    let some (_, lhs, body) := (← instantiateForall eqnTy xs).eq? | throwError "frontx: bad equation"
    if let some (forE, post?) ← findFor fn (stripPre body) then
      return ← compileLoop fn xs rty lhs forE post? inv? t0
    -- variables for the parameters
    let mut blocks : List (Expr × Nat × Nat) := []
    let mut next := 0
    let mut memo : List (Expr × Nat) := []
    let mut scal : Array (Expr × Ty × Nat) := #[]
    for x in xs do
      let xty ← inferType x
      if (← whnfR xty).isConstOf ``ByteArray then
        blocks := blocks ++ [(x, blocks.length, next + 1)]
        next := next + 2
      else
        let some ty ← classify xty | throwError "frontx: unsupported parameter type{indentExpr xty}"
        memo := (x, next) :: memo
        scal := scal.push (x, ty, next)
        next := next + 1
    let out : Nat := match scal[0]? with | some (_, _, v) => v | none => next
    let two64 ← mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr (64 : Nat)]
    -- `f.Rep`: the state holds the arguments
    let hypsOf (σ : Expr) : TermElabM (Array Expr) := do
      let env := mkApp (mkConst ``BState.env) σ
      let heap := mkApp (mkConst ``BState.heap) σ
      let mut hyps : Array Expr := #[]
      if !blocks.isEmpty then
        let bl ← mkListLit (← mkAppM ``List #[mkApp (mkConst ``BitVec) (toExpr (8 : Nat))])
          (blocks.map fun (x, _, _) => mkApp (mkConst ``blk) x)
        hyps := hyps.push (← mkEq heap bl)
      for (x, _, len) in blocks do
        let sz := mkApp (mkConst ``ByteArray.size) x
        hyps := hyps.push (← mkEq (mkApp env (toExpr len)) (mkApp (mkConst ``rN) sz))
        hyps := hyps.push (← mkAppM ``LT.lt #[sz, two64])
      for (x, ty, v) in scal do
        hyps := hyps.push (← mkEq (mkApp env (toExpr v)) (ty.rep x))
        if ty == .nat then hyps := hyps.push (← mkAppM ``LT.lt #[x, two64])
      if let some inv := inv? then
        let invE ← elabTerm inv (some (← mkForallFVars xs (mkSort 0)))
        synthesizeSyntheticMVarsNoPostponing
        hyps := hyps.push (mkAppN (← instantiateMVars invE) xs).headBeta
      if hyps.isEmpty then hyps := #[mkConst ``True]
      return hyps
    let mkConjE (hs : Array Expr) : Expr := hs.pop.foldr mkAnd hs.back!
    let nconj ← withLocalDeclD `σ bstate fun σ => do
      let hyps ← hypsOf σ
      addDef repN (← mkForallFVars (xs.push σ) (mkSort 0)) (← mkLambdaFVars (xs.push σ) (mkConjE hyps))
      return hyps.size
    -- argument tuples and the relation `R`
    let (A, _) ← mkTuple (← xs.toList.mapM fun x => do return (x, ← inferType x))
    let R ← withLocalDeclD `a A fun a => withLocalDeclD `σ bstate fun σ => do
      let mut projs := #[]
      let mut cur := a
      for i in [0:xs.size] do
        if i + 1 == xs.size then projs := projs.push cur
        else
          projs := projs.push (← mkAppM ``Prod.fst #[cur])
          cur ← mkAppM ``Prod.snd #[cur]
      mkLambdaFVars #[a, σ] (mkAppN (mkConst repN) (projs.push σ))
    withLocalDeclD `σ bstate fun σ => do
      let hyps ← hypsOf σ
      let decls := hyps.mapIdx fun i h => (Name.mkSimple s!"h{i}", h)
      let ctx : Ctx := { fn, params := xs, blocks, A, R, heap := mkApp (mkConst ``BState.heap) σ, repN, rty }
      let ((mt, outE, proof), st) ← withLocalDeclsDND decls fun hs => do
        let ((mt, outE, proof), st) ← (trT ctx nconj (mkApp (mkConst ``BState.env) σ) body).run { next, memo }
        return ((mt, outE, ← mkLambdaFVars hs proof), st)
      let M := st.next
      let t1 ← IO.monoMsNow
      addDef treeN (mkConst ``Tree) (← mt.toExpr) (compile := true)
      addDef layN (mkConst ``Lay) (mkApp2 (mkConst ``Lay.mk) (toExpr M) (toExpr mt.maxK)) (compile := true)
      let nvars := M + 2 + mt.maxK + 2 * mt.cdepth
      addDef (fn ++ `slots) (mkConst ``Nat) (toExpr (nvars - 8)) (compile := true)
      let lout := mkApp (mkConst ``LOut) A
      addDef outN (← mkForallFVars xs lout) (← mkLambdaFVars xs outE)
      -- f.step1
      let conj := mkConjE hyps
      let stepTy ← mkForallFVars (xs.push σ) (← mkArrow (mkAppN (mkConst repN) (xs.push σ))
        (mkAppN (mkConst ``Sim) #[A, R, mkConst treeN, σ, mkAppN (mkConst outN) xs]))
      let stepPf ← withLocalDeclD `hR conj fun hR => do
        let mut projs := #[]
        let mut cur := hR
        for i in [0:hyps.size] do
          if i + 1 == hyps.size then projs := projs.push cur
          else
            projs := projs.push (← mkAppM ``And.left #[cur])
            cur ← mkAppM ``And.right #[cur]
        mkLambdaFVars (xs ++ #[σ, hR]) (mkAppN proof projs).headBeta
      let stepPf ← instantiateMVars stepPf
      if stepPf.hasSorry || stepPf.hasMVar then throwError "frontx: step proof incomplete"
      addDecl (.thmDecl { name := stepN, levelParams := [], type := stepTy, value := stepPf })
      let t2 ← IO.monoMsNow
      -- f.runs
      let mkStmt (concl : Expr) : MetaM Expr := do
        mkForallFVars (xs.push σ) (← mkArrow (mkAppN (mkConst repN) (xs.push σ)) concl)
      let runsTy ← mkStmt (← withLocalDeclD `σ' bstate fun σ' => do
        mkAppM ``Exists #[← mkLambdaFVars #[σ'] (mkApp4 (mkConst ``Tree.Runs) (mkConst treeN) σ (rty.rep lhs) σ')])
      let as := (List.range xs.size).toArray.map fun i => mkIdent (Name.mkSimple s!"a{i}")
      let holes ← as.mapM fun _ => `(_)
      let σi := mkIdent `σ
      let fI := mkIdent fn
      let tI := mkIdent treeN
      let lI := mkIdent layN
      let sI := mkIdent stepN
      addThm (fn ++ `runs) runsTy (← `(tactic|
        (intro $as*
         fun_induction $fI:ident $as* <;> intro $σi:ident hR <;>
          (have hs := $sI:ident $holes* $σi hR
           frontx_path hs
           first
           | (obtain ⟨σ₁, hs₁, hR₁⟩ := sim_call_elim _ hs
              refine step_call σ₁ hs₁ ?_
              frontx_ih
              exact hR₁)
           | (obtain ⟨σ₁, hs₁⟩ := sim_ret_elim _ hs
              exact step_ret σ₁ hs₁)))))
      let t3 ← IO.monoMsNow
      -- f.exec
      let prog := mkApp3 (mkConst ``prog) (mkConst layN) (mkConst treeN) (toExpr out)
      let execTy ← mkStmt (← withLocalDeclD `σ' bstate fun σ' => do
        let c1 := mkApp3 (mkConst ``BExec) prog σ σ'
        let c2 ← mkEq (mkApp (mkApp (mkConst ``BState.env) σ') (toExpr out)) (rty.rep lhs)
        let c3 ← mkEq (mkApp (mkConst ``BState.heap) σ') (mkApp (mkConst ``BState.heap) σ)
        mkAppM ``Exists #[← mkLambdaFVars #[σ'] (mkAnd c1 (mkAnd c2 c3))])
      let runsI := mkIdent (fn ++ `runs)
      addThm (fn ++ `exec) execTy (← `(tactic|
        (intro $as* $σi:ident hR
         exact prog_ok_ro $lI (by simp [$tI:ident, $lI:ident, Tree.wf, BExp.vlt]) (by rfl) ($runsI:ident $as* $σi hR) _)))
      let t4 ← IO.monoMsNow
      logInfo m!"frontx: {fn}: {nvars} variables ({M} user), {nvars - 8} slots, result in variable {out}, {st.nObl} obligations; translate + step proof {t1 - t0} ms, kernel check of step {t2 - t1} ms, induction {t3 - t2} ms, exec theorem {t4 - t3} ms"

/-- `frontx_compile f` or `frontx_compile f with inv` (`inv : params → Prop`, an extra precondition that the
recursive calls must preserve; needed for `Nat` arguments whose bounds are not implied by the tests) -/
elab "frontx_compile " f:ident : command => liftTermElabM (compileCmd f none)
elab "frontx_compile " f:ident " with " inv:term : command => liftTermElabM (compileCmd f (some inv))

end Proven.Frontx
