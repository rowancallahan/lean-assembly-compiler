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

namespace Proven.Frontx
open Lean Meta Elab Term Command Tactic

inductive Ty where | bv | u8 | u32 | u64 | nat
  deriving BEq, Repr, Inhabited

def bv64 : Expr := mkApp (mkConst ``BitVec) (toExpr (64 : Nat))
def mkBV (n : Nat) : Expr := mkApp2 (mkConst ``BitVec.ofNat) (toExpr (64 : Nat)) (toExpr n)

def classify (t : Expr) : MetaM (Option Ty) := do
  let t ← whnfR t
  if t.isConstOf ``UInt8 then return some .u8
  if t.isConstOf ``UInt32 then return some .u32
  if t.isConstOf ``UInt64 then return some .u64
  if t.isConstOf ``Nat then return some .nat
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

/-! ## translation -/

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

/-- a load or a temporary, emitted before the node being translated, with the Lean term it holds -/
inductive Item where
  | load (v b : Nat) (i : ME) (r : Expr) (idx : Expr) (temps : List Expr)
  | cload (v b : Nat) (i c d : ME) (r : Expr) (idx : Expr) (temps : List Expr)
  | let_ (v : Nat) (e : ME) (L L' : Expr) (ty : Ty) (temps : List Expr)

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

def cNot (c : ME) : ME := .bin ``Op.xor c (.const (mkBV 1))

mutual

/-- a scalar term `e`: its expression, and `e` with the inlined helpers unfolded (definitionally equal to `e`;
the terms held in temporaries occur in it syntactically) -/
partial def trE (ctx : Ctx) (e : Expr) : TrM (ME × Expr) := do
  let e := e.consumeMData.headBeta
  if let some v ← find? e then return (.var v, e)
  let some ty ← classify (← inferType e) | throwError "frontx: not a scalar:{indentExpr e}"
  if !e.hasFVar then return (.const (← litBV (ty.rep e)), e)
  let args := e.getAppArgs
  let f := e.getAppFn
  -- a read of a byte array: a load into a fresh variable
  if let some (xs, i) := read? e then
    if let some (b, _) := ctx.block? xs then
      let (idx, i') ← trE ctx i
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
    ``rd0, ``rd1, ``rd2, ``blk_get, ``r8_fold, ``ba_get!, ``c_not, ``c_and, ``c_or, ``c_eq0, ``c_not', ``c_and', ``c_or', ``c_eq0',
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
    try
      let (_, _, g') ← g.generalizeHyp #[{ expr := L }] hyps
      g := g'
    catch _ =>
      let (_, g') ← g.generalize #[{ expr := L }]
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

/-- a term in tail position, in the environment `env`: its tree, its Lean outcome `o : LOut A`, and a proof of
`Sim R tree ⟨env, heap⟩ o` -/
partial def trT (ctx : Ctx) (nconj : Nat) (env : Expr) (e : Expr) : TrM (MT × Expr × Expr) := do
  let e := e.consumeMData.headBeta
  let lout := mkApp (mkConst ``LOut) ctx.A
  if e.isLet then
    let v := e.letValue!
    if v.hasFVar && !v.isFVar && (← find? v).isNone then
      if let some ty ← classify e.letType! then
        let (m, v') ← trE ctx v
        let x ← fresh
        modify fun s => { s with memo := (v, x) :: s.memo, temps := v :: s.temps,
                                 pend := s.pend.push (.let_ x m v v' ty s.temps) }
    return ← trT ctx nconj env (e.letBody!.instantiate1 v)
  let args := e.getAppArgs
  -- a two-way branch on `P`
  let branch (P inst : Expr) (mkT mkF : Expr → Expr) : TrM (MT × Expr × Expr) := do
    let (c, P') ← trC ctx P
    wrapItems ctx (← takePend) env fun env => do
      let hc ← oblig (mkIff (← mkAppM ``Ne #[denoteE env c, bv0]) P')
      let br (hty : Expr) (mk : Expr → Expr) : TrM (MT × Expr × Expr) := inBranch do
        withLocalDeclD `h hty fun h => do
          let (t, o, p) ← trT ctx nconj env (mk h)
          return (t, ← mkLambdaFVars #[h] o, ← mkLambdaFVars #[h] p)
      let (t, o₁, p₁) ← br P mkT
      let (f, o₂, p₂) ← br (mkNot P) mkF
      let out := mkAppN (mkConst ``dite [levelOne]) #[lout, P, inst, o₁, o₂]
      let pf := mkAppN (mkConst ``sim_dite)
        #[ctx.A, ctx.R, c.toExpr, ← t.toExpr, ← f.toExpr, env, ctx.heap, P, inst, o₁, o₂, hc, p₁, p₂]
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
  if e.getAppFn.isConstOf ctx.fn && args.size == ctx.params.size then
    let mut as := #[]
    let mut args' := args
    for j in [0:args.size] do
      let p := ctx.params[j]!
      if args[j]! == p then continue
      if (ctx.block? p).isSome then throwError "frontx: array argument changed in the call{indentExpr e}"
      let some v ← find? p | throwError "frontx: parameter without a variable{indentExpr p}"
      let (m, a') ← trE ctx args[j]!
      as := as.push (v, m)
      args' := args'.set! j a'
    return ← wrapItems ctx (← takePend) env fun env => do
      let mt := MT.call as.toList
      let asE := (← mt.toExpr).appArg!
      let σ₁ := mkApp2 (mkConst ``BState.mk) (mkApp3 (mkConst ``parSet) env env asE) ctx.heap
      let some conj ← unfoldDefinition? (mkAppN (mkConst ctx.repN) (args'.push σ₁))
        | throwError "frontx: cannot unfold {ctx.repN}"
      let cs := splitAnd nconj conj.headBeta
      let ps ← cs.mapM oblig
      let rec mkConj : List Expr → List Expr → MetaM Expr
        | [_], [p] => pure p
        | c :: cs, p :: ps => do
          let q ← mkConj cs ps
          return mkApp4 (mkConst ``And.intro) c (← inferType q) p q
        | _, _ => pure (mkConst ``True.intro)
      let h ← mkConj cs ps
      let (_, a) ← mkTuple (← args.toList.mapM fun x => do return (x, ← inferType x))
      return (mt, mkApp2 (mkConst ``LOut.call) ctx.A a,
        mkAppN (mkConst ``sim_call) #[ctx.A, ctx.R, asE, env, ctx.heap, a, h])
  let (m, e') ← trE ctx e
  return ← wrapItems ctx (← takePend) env fun env => do
    let h ← oblig (← mkEq (denoteE env m) (ctx.rty.rep e'))
    let r := ctx.rty.rep e
    return (.ret m, mkApp2 (mkConst ``LOut.ret) ctx.A r,
      mkAppN (mkConst ``sim_ret) #[ctx.A, ctx.R, m.toExpr, env, ctx.heap, r, h])

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
      logInfo m!"frontx: {fn}: {M} variables (+{2 + mt.maxK} control), result in variable {out}, {st.nObl} obligations; translate + step proof {t1 - t0} ms, kernel check of step {t2 - t1} ms, induction {t3 - t2} ms, exec theorem {t4 - t3} ms"

/-- `frontx_compile f` or `frontx_compile f with inv` (`inv : params → Prop`, an extra precondition that the
recursive calls must preserve; needed for `Nat` arguments whose bounds are not implied by the tests) -/
elab "frontx_compile " f:ident : command => liftTermElabM (compileCmd f none)
elab "frontx_compile " f:ident " with " inv:term : command => liftTermElabM (compileCmd f (some inv))

end Proven.Frontx
