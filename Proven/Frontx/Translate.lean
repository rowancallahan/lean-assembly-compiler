/- `frontx_compile f`: translate a first-order tail-recursive Lean definition into a `Tree` and prove,
automatically, that the tree computes the function.  The translator is untrusted; what counts are the
kernel-checked theorems it adds:

* `f.tree : Tree`, `f.lay : Lay`
* `f.runs : ∀ args σ, (σ holds the arguments) → ∃ σ', f.tree.Runs σ (rep (f args)) σ'`
* `f.exec : ∀ args σ, … → ∃ σ', BExec (prog f.lay f.tree out) σ σ' ∧ σ'.env out = rep (f args) ∧ σ'.heap = σ.heap`

The definition is read through its unfolding equation (`f.eq_def`), never the compiler IR.  The proof of
`f.runs` is functional induction on `f` (so the recursion's own termination argument is reused; no measure is
ever stated): each case is one `Tree.step`, computed by `simp` with the lemma set of `Rep.lean`. -/
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

def MT.maxK : MT → Nat
  | .ret _ => 0
  | .call as => as.length
  | .ite _ t e => max t.maxK e.maxK
  | .let_ _ _ k | .load _ _ _ k => k.maxK

/-! ## translation -/

structure Ctx where
  fn : Name
  params : Array Expr
  /-- byte-array parameters: (the fvar, block index, length variable) -/
  blocks : List (Expr × Nat × Nat) := []

inductive Item where
  | load (v b : Nat) (i : ME)
  | let_ (v : Nat) (e : ME)

structure St where
  next : Nat
  /-- Lean scalar terms that already live in a variable -/
  memo : List (Expr × Nat) := []
  /-- loads and temporaries to emit before the node being translated -/
  pend : Array Item := #[]
  /-- helper definitions that were inlined (the proof unfolds them) -/
  unfolded : Array Name := #[]

abbrev TrM := StateRefT St MetaM

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
  | some ``GetElem?.getElem!, 9 => some (args[7]!, args[8]!)
  | some ``ByteArray.get!, 2 => some (args[0]!, args[1]!)
  | some ``ByteArray.get, 3 => some (args[0]!, args[1]!)
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

/-- a scalar term -/
partial def trE (ctx : Ctx) (e : Expr) : TrM ME := do
  let e := e.consumeMData.headBeta
  if let some v ← find? e then return .var v
  let some ty ← classify (← inferType e) | throwError "frontx: not a scalar:{indentExpr e}"
  if !e.hasFVar then return .const (← litBV (ty.rep e))
  let args := e.getAppArgs
  let bin (op : Name) (masked : Bool) : TrM ME := do
    let r := ME.bin op (← trE ctx args[4]!) (← trE ctx args[5]!)
    match (if masked then ty.mask else none) with
    | some m => return .bin ``Op.and r (.const (mkBV m))
    | none => return r
  let shift (op : Name) (masked : Bool) : TrM ME := do
    let a ← trE ctx args[4]!
    let b := args[5]!
    let amt ← (do
      let some bty ← classify (← inferType b) | throwError "frontx: shift amount{indentExpr b}"
      match ty.shMask with
      | some m =>
        if b.hasFVar then return ME.bin ``Op.and (← trE ctx b) (.const (mkBV m))
        else return ME.const (← litBV (← mkAppM ``HAnd.hAnd #[bty.rep b, mkBV m]))
      | none => trE ctx b : TrM ME)
    let r := ME.bin op a amt
    match (if masked then ty.mask else none) with
    | some m => return .bin ``Op.and r (.const (mkBV m))
    | none => return r
  let conv (m : Option Nat) : TrM ME := do
    let a ← trE ctx args[0]!
    match m with
    | some m => return .bin ``Op.and a (.const (mkBV m))
    | none => return a
  match e.getAppFn.constName?, args.size with
  | some ``HAdd.hAdd, 6 => bin ``Op.add true
  | some ``HSub.hSub, 6 => bin ``Op.sub true
  | some ``HAnd.hAnd, 6 => bin ``Op.and false
  | some ``HOr.hOr, 6 => bin ``Op.or false
  | some ``HXor.hXor, 6 => bin ``Op.xor false
  | some ``HShiftRight.hShiftRight, 6 => shift ``Op.lshr false
  | some ``HShiftLeft.hShiftLeft, 6 => shift ``Op.shl true
  | some ``ite, 5 => return .ite (← trC ctx args[1]!) (← trE ctx args[3]!) (← trE ctx args[4]!)
  | some ``UInt8.toUInt32, 1 | some ``UInt8.toUInt64, 1 | some ``UInt32.toUInt64, 1
  | some ``UInt8.toNat, 1 | some ``UInt32.toNat, 1 | some ``UInt64.toNat, 1 | some ``Nat.toUInt64, 1 => conv none
  | some ``UInt32.toUInt8, 1 | some ``UInt64.toUInt8, 1 | some ``Nat.toUInt8, 1 => conv (some 0xff)
  | some ``UInt64.toUInt32, 1 | some ``Nat.toUInt32, 1 => conv (some 0xffffffff)
  | some ``ByteArray.size, 1 =>
    match ctx.block? args[0]! with
    | some (_, len) => return .var len
    | none => throwError "frontx: size of an unknown array{indentExpr e}"
  | some c, _ =>
    if c == ctx.fn then throwError "frontx: recursive call not in tail position{indentExpr e}"
    if (read? e).isSome then throwError "frontx: array read not hoisted{indentExpr e}"
    -- a helper function: its compound scalar arguments go to temporaries, then it is inlined
    for a in args do
      if a.hasFVar && !a.isFVar && (← classify (← inferType a)).isSome && (← find? a).isNone then
        let m ← trE ctx a
        let v ← fresh
        modify fun s => { s with memo := (a, v) :: s.memo, pend := s.pend.push (.let_ v m) }
    match ← unfoldDefinition? e with
    | some e' =>
      modify fun s => if s.unfolded.contains c then s else { s with unfolded := s.unfolded.push c }
      trE ctx e'
    | none => throwError "frontx: unsupported term{indentExpr e}"
  | none, _ => throwError "frontx: unsupported term{indentExpr e}"

/-- a decidable proposition, as a `0`/`1` value -/
partial def trC (ctx : Ctx) (p : Expr) : TrM ME := do
  let p := p.consumeMData.headBeta
  let args := p.getAppArgs
  let cmp (a b : Expr) : TrM ME := return .bin ``Op.ult (← trE ctx a) (← trE ctx b)
  match p.getAppFn.constName?, args.size with
  | some ``Eq, 3 =>
    if args[0]!.isConstOf ``Bool then
      if args[2]!.isConstOf ``Bool.true then trB ctx args[1]!
      else if args[2]!.isConstOf ``Bool.false then return cNot (← trB ctx args[1]!)
      else throwError "frontx: unsupported condition{indentExpr p}"
    else return .bin ``Op.eq (← trE ctx args[1]!) (← trE ctx args[2]!)
  | some ``Ne, 3 => return cNot (.bin ``Op.eq (← trE ctx args[1]!) (← trE ctx args[2]!))
  | some ``Not, 1 => return cNot (← trC ctx args[0]!)
  | some ``LT.lt, 4 => cmp args[2]! args[3]!
  | some ``GT.gt, 4 => cmp args[3]! args[2]!
  | some ``LE.le, 4 => return cNot (← cmp args[3]! args[2]!)
  | some ``GE.ge, 4 => return cNot (← cmp args[2]! args[3]!)
  | some ``And, 2 => return .bin ``Op.and (← trC ctx args[0]!) (← trC ctx args[1]!)
  | some ``Or, 2 => return .bin ``Op.or (← trC ctx args[0]!) (← trC ctx args[1]!)
  | _, _ => throwError "frontx: unsupported condition{indentExpr p}"

/-- a `Bool`, as a `0`/`1` value -/
partial def trB (ctx : Ctx) (b : Expr) : TrM ME := do
  let b := b.consumeMData.headBeta
  let args := b.getAppArgs
  match b.getAppFn.constName?, args.size with
  | some ``BEq.beq, 4 => return .bin ``Op.eq (← trE ctx args[2]!) (← trE ctx args[3]!)
  | some ``bne, 4 => return cNot (.bin ``Op.eq (← trE ctx args[2]!) (← trE ctx args[3]!))
  | some ``and, 2 => return .bin ``Op.and (← trB ctx args[0]!) (← trB ctx args[1]!)
  | some ``or, 2 => return .bin ``Op.or (← trB ctx args[0]!) (← trB ctx args[1]!)
  | some ``not, 1 => return cNot (← trB ctx args[0]!)
  | some ``Decidable.decide, 2 => trC ctx args[0]!
  | _, _ => throwError "frontx: unsupported Bool{indentExpr b}"

end

/-- emit loads for the array reads of `e` that are not yet in a variable -/
def hoist (ctx : Ctx) (e : Expr) : TrM Unit := do
  for r in reads ctx e do
    if (← find? r).isSome then continue
    let some (xs, i) := read? r | unreachable!
    let some (b, _) := ctx.block? xs | unreachable!
    let idx ← trE ctx i
    let v ← fresh
    modify fun s => { s with memo := (r, v) :: s.memo, pend := s.pend.push (.load v b idx) }

/-- wrap the pending loads and temporaries around `k` -/
def flush (k : MT) : TrM MT := do
  let items := (← get).pend
  modify fun s => { s with pend := #[] }
  return items.foldr (fun it k => match it with
    | .load v b i => .load v b i k
    | .let_ v e => .let_ v e k) k

/-- run `x` and forget the variables it bound (a branch) -/
def inBranch (x : TrM MT) : TrM MT := do
  let memo := (← get).memo
  let r ← x
  modify fun s => { s with memo }
  return r

/-- a term in tail position -/
partial def trT (ctx : Ctx) (e : Expr) : TrM MT := do
  let e := e.consumeMData.headBeta
  if e.isLet then
    let v := e.letValue!
    if (← classify e.letType!).isSome && v.hasFVar && !v.isFVar && (← find? v).isNone then
      hoist ctx v
      let m ← trE ctx v
      let x ← fresh
      modify fun s => { s with memo := (v, x) :: s.memo, pend := s.pend.push (.let_ x m) }
    return ← trT ctx (e.letBody!.instantiate1 v)
  let args := e.getAppArgs
  if e.isAppOfArity ``ite 5 then
    hoist ctx args[1]!
    let c ← trC ctx args[1]!
    let pre ← flush (.ret (.var 0))
    let t ← inBranch (trT ctx args[3]!)
    let f ← inBranch (trT ctx args[4]!)
    return graft pre (.ite c t f)
  if e.isAppOfArity ``dite 5 then
    hoist ctx args[1]!
    let c ← trC ctx args[1]!
    let pre ← flush (.ret (.var 0))
    let t ← inBranch (withLocalDeclD `h args[1]! fun h => trT ctx (args[3]!.beta #[h]))
    let f ← inBranch (withLocalDeclD `h (mkNot args[1]!) fun h => trT ctx (args[4]!.beta #[h]))
    return graft pre (.ite c t f)
  if e.getAppFn.isConstOf ctx.fn && args.size == ctx.params.size then
    let mut as := #[]
    for j in [0:args.size] do
      let p := ctx.params[j]!
      if args[j]! == p then continue
      if (ctx.block? p).isSome then throwError "frontx: array argument changed in the call{indentExpr e}"
      let some v ← find? p | throwError "frontx: parameter without a variable{indentExpr p}"
      hoist ctx args[j]!
      as := as.push (v, ← trE ctx args[j]!)
    return ← flush (.call as.toList)
  hoist ctx e
  let r ← trE ctx e
  flush (.ret r)
where
  /-- replace the placeholder leaf of a chain of loads/lets by `k` -/
  graft : MT → MT → MT
    | .load v b i p, k => .load v b i (graft p k)
    | .let_ v e p, k => .let_ v e (graft p k)
    | _, k => k

/-! ## the generated proof -/

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

/-- the rewriting set: `Tree.step`, expression evaluation, and every supported operation pushed through its
representation function -/
def simpNames : Array Name :=
  #[``Tree.step, ``BExp.denote, ``Op.eval, ``parSet, ``BEnv.set,
    ``rd0, ``rd1, ``rd2, ``blk_get, ``r8_fold, ``ba_get!, ``c_not, ``c_and, ``c_or, ``c_eq0,
    ``rN_lit, ``r8_lit, ``r32_lit, ``r64_lit, ``rN_toNat, ``rN_add, ``rN_sub, ``rN_lt, ``rN_inj, ``rN_ite,
    ``r64_add, ``r64_sub, ``r64_and, ``r64_or, ``r64_xor, ``r64_ite, ``r64_eq', ``r64_lt', ``r64_le', ``r64_toNat, ``r64_ofNat,
    ``r32_add, ``r32_sub, ``r32_and, ``r32_or, ``r32_xor, ``r32_ite, ``r32_eq', ``r32_lt', ``r32_le', ``r32_toNat, ``r32_shr,
    ``r8_add, ``r8_sub, ``r8_and, ``r8_or, ``r8_xor, ``r8_ite, ``r8_eq', ``r8_lt', ``r8_le', ``r8_toNat,
    ``r32_of8, ``r64_of8, ``r64_of32, ``r8_of32, ``r32_of64, ``r8_of64, ``r8_ofNat, ``r32_ofNat]

macro "frontx_simp" "[" ts:ident,* "]" loc:(Lean.Parser.Tactic.location)? : tactic => do
  let ids := ts.getElems ++ simpNames.map mkIdent
  let ls ← ids.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:ident)
  if loc.isSome then `(tactic| simp +zetaDelta (disch := omega) [$ls,*] $[$loc]?)
  else `(tactic| simp +zetaDelta (disch := omega) [$ls,*, *])

/-- normalise the path conditions (every hypothesis that is not an induction hypothesis) with the same set,
so that they rewrite the tests of the tree -/
elab "frontx_hyps" "[" ts:ident,* "]" : tactic => withMainContext do
  let mut g ← getMainGoal
  let mut names := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isForall || !(← isProp ty) then continue
    let n := Name.mkSimple s!"fxh{names.size}"
    g ← g.rename d.fvarId n
    names := names.push (mkIdent n)
  replaceMainGoal [g]
  for n in names do
    evalTactic (← `(tactic| try frontx_simp [$ts,*] at $n:ident))

macro "frontx_side" "[" ts:ident,* "]" : tactic => `(tactic|
  first | done | omega | assumption | (frontx_simp [$ts,*] <;> first | done | omega))

/-- one case of the functional induction: a `ret` leaf or a `call` leaf -/
macro "frontx_case" "[" ts:ident,* "]" : tactic => `(tactic|
  first
  | (refine step_call ?s ?step ?rest
     case step => (frontx_simp [$ts,*] <;> first | done | rfl)
     case rest => (frontx_ih <;> frontx_side [$ts,*]))
  | (refine step_ret ?s ?step
     case step => (frontx_simp [$ts,*] <;> first | done | rfl)))

/-! ## the command -/

def addThm (name : Name) (type : Expr) (tac : TSyntax `tactic) : TermElabM Unit := do
  let type ← instantiateMVars type
  let pf ← elabTermEnsuringType (← `(by $tac:tactic)) type
  synthesizeSyntheticMVarsNoPostponing
  let pf ← instantiateMVars pf
  if pf.hasSorry || pf.hasMVar then throwError "frontx: could not prove {name}"
  addDecl (.thmDecl { name, levelParams := [], type, value := pf })

/-- `frontx_compile f` or `frontx_compile f with inv` (`inv : params → Prop`, an extra precondition that the
recursive calls must preserve; needed for `Nat` arguments whose bounds are not implied by the tests) -/
elab "frontx_compile " f:ident inv?:(" with " term)? : command => liftTermElabM do
  let t0 ← IO.monoMsNow
  let fn ← realizeGlobalConstNoOverloadWithInfo f
  let info ← getConstInfo fn
  let some eqn ← getUnfoldEqnFor? fn (nonRec := true) | throwError "frontx: no unfolding equation for {fn}"
  let eqnTy := (← getConstInfo eqn).type
  forallTelescope info.type fun xs resTy => do
    let some rty ← classify resTy | throwError "frontx: unsupported result type{indentExpr resTy}"
    let some (_, lhs, body) := (← instantiateForall eqnTy xs).eq? | throwError "frontx: bad equation"
    -- variables for the parameters
    let mut ctx : Ctx := { fn, params := xs }
    let mut next := 0
    let mut memo : List (Expr × Nat) := []
    let mut scal : Array (Expr × Ty × Nat) := #[]
    for x in xs do
      let xty ← inferType x
      if (← whnfR xty).isConstOf ``ByteArray then
        ctx := { ctx with blocks := ctx.blocks ++ [(x, ctx.blocks.length, next + 1)] }
        next := next + 2
      else
        let some ty ← classify xty | throwError "frontx: unsupported parameter type{indentExpr xty}"
        memo := (x, next) :: memo
        scal := scal.push (x, ty, next)
        next := next + 1
    let (mt, st) ← (trT ctx body).run { next, memo }
    let M := st.next
    let t1 ← IO.monoMsNow
    let treeN := fn ++ `tree
    let layN := fn ++ `lay
    let tree ← mt.toExpr
    addDecl (.defnDecl (mkDefinitionValEx treeN [] (mkConst ``Tree) tree .abbrev .safe [treeN]))
    addDecl (.defnDecl (mkDefinitionValEx layN [] (mkConst ``Lay)
      (mkApp2 (mkConst ``Lay.mk) (toExpr M) (toExpr mt.maxK)) .abbrev .safe [layN]))
    enableRealizationsForConst treeN
    enableRealizationsForConst layN
    -- hypotheses: σ holds the arguments
    let out : Nat := match scal[0]? with | some (_, _, v) => v | none => M
    let two64 ← mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr (64 : Nat)]
    withLocalDeclD `σ (mkConst ``BState) fun σ => do
      let env := mkApp (mkConst ``BState.env) σ
      let heap := mkApp (mkConst ``BState.heap) σ
      let mut hyps : Array Expr := #[]
      if !ctx.blocks.isEmpty then
        let bl ← mkListLit (← mkAppM ``List #[mkApp (mkConst ``BitVec) (toExpr (8 : Nat))])
          (ctx.blocks.map fun (x, _, _) => mkApp (mkConst ``blk) x)
        hyps := hyps.push (← mkEq heap bl)
      for (x, _, len) in ctx.blocks do
        let sz := mkApp (mkConst ``ByteArray.size) x
        hyps := hyps.push (← mkEq (mkApp env (toExpr len)) (mkApp (mkConst ``rN) sz))
        hyps := hyps.push (← mkAppM ``LT.lt #[sz, two64])
      for (x, ty, v) in scal do
        hyps := hyps.push (← mkEq (mkApp env (toExpr v)) (ty.rep x))
        if ty == .nat then hyps := hyps.push (← mkAppM ``LT.lt #[x, two64])
      if let some inv := inv? then
        let invE ← elabTerm inv.raw[1] (some (← mkForallFVars xs (mkSort 0)))
        hyps := hyps.push (mkAppN invE xs).headBeta
      let mkStmt (concl : Expr) : MetaM Expr := do
        let body ← hyps.foldrM (fun h acc => mkArrow h acc) concl
        mkForallFVars (xs.push σ) body
      -- f.runs
      let runsTy ← mkStmt (← withLocalDeclD `σ' (mkConst ``BState) fun σ' => do
        mkAppM ``Exists #[← mkLambdaFVars #[σ'] (mkApp4 (mkConst ``Tree.Runs) (mkConst treeN) σ (rty.rep lhs) σ')])
      let as := (List.range xs.size).toArray.map fun i => mkIdent (Name.mkSimple s!"a{i}")
      let hs := (List.range hyps.size).toArray.map fun i => mkIdent (Name.mkSimple s!"h{i}")
      let σi := mkIdent `σ
      let fI := mkIdent fn
      let tI := mkIdent treeN
      let lI := mkIdent layN
      let hus := st.unfolded.map mkIdent
      let us := #[tI] ++ hus
      -- on failure the tree stays defined (for inspection); no theorem is added
      try
        addThm (fn ++ `runs) runsTy (← `(tactic|
          (intro $as*; fun_induction $fI:ident $as* <;> frontx_hyps [$hus,*] <;>
            intro $σi:ident $hs* <;> frontx_case [$us,*])))
      catch e =>
        logError m!"frontx: equation proof failed for {fn}: {e.toMessageData}"
        return
      let t2 ← IO.monoMsNow
      -- f.exec
      let prog := mkApp3 (mkConst ``prog) (mkConst layN) (mkConst treeN) (toExpr out)
      let execTy ← mkStmt (← withLocalDeclD `σ' (mkConst ``BState) fun σ' => do
        let c1 := mkApp3 (mkConst ``BExec) prog σ σ'
        let c2 ← mkEq (mkApp (mkApp (mkConst ``BState.env) σ') (toExpr out)) (rty.rep lhs)
        let c3 ← mkEq (mkApp (mkConst ``BState.heap) σ') heap
        mkAppM ``Exists #[← mkLambdaFVars #[σ'] (mkAnd c1 (mkAnd c2 c3))])
      let runsI := mkIdent (fn ++ `runs)
      addThm (fn ++ `exec) execTy (← `(tactic|
        (intro $as* $σi:ident $hs*
         exact prog_ok_ro $lI (by simp [$tI:ident, $lI:ident, Tree.wf, BExp.vlt]) (by rfl) ($runsI:ident $as* $σi $hs*) _)))
      let t3 ← IO.monoMsNow
      logInfo m!"frontx: {fn}: {M} variables (+{2 + mt.maxK} control), result in variable {out}; translate {t1 - t0} ms, equation proof {t2 - t1} ms, exec theorem {t3 - t2} ms"

end Proven.Frontx
