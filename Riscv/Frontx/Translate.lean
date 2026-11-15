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
import Riscv.Frontx.Rep
import Riscv.Frontx.For
import Riscv.Frontx.Bytes

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
  | store (b : Nat) (i e : ME) (k : MT)
  | sub (p : Expr) (k : MT)
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
  | .store b i e k => return mkApp4 (mkConst ``Tree.store) (Lean.toExpr b) i.toExpr e.toExpr (← k.toExpr)
  | .sub p k => return mkApp2 (mkConst ``Tree.sub) p (← k.toExpr)

def MT.maxK : MT → Nat
  | .ret _ => 0
  | .call as => as.length
  | .ite _ t e => max t.maxK e.maxK
  | .let_ _ _ k | .load _ _ _ k | .cload _ _ _ _ _ k | .store _ _ _ k | .sub _ k => k.maxK

/-- nesting depth of the condition variables `comp` uses -/
def MT.cdepth : MT → Nat
  | .ret _ | .call _ => 0
  | .ite _ t e => 1 + max t.cdepth e.cdepth
  | .let_ _ _ k | .load _ _ _ k | .store _ _ _ k | .sub _ k => k.cdepth
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

/-- a function returning `List UInt8`, written to the output block from index `j` on -/
structure LCtx where
  /-- the current output index and output block (Lean terms), block 0 -/
  j : Expr
  O : Expr
  A0 : Expr
  /-- the parameters `j`, `O` -/
  jP : Expr
  OP : Expr
  /-- the capacity hypothesis `j + (f xs).length ≤ O.length` and the equation `f xs = body` -/
  hcap : Expr
  eq : Expr

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
  /-- user-supplied equations `g args = closed form` (`using`), applied instead of unfolding `g` -/
  lemmas : Array Name := #[]
  /-- accumulator mode (`f x = g + f x'`, not a tail call): the accumulator and its variable -/
  acc? : Option (Expr × Nat) := none
  /-- positions of the parameters that are data (not proofs); `Rep` and the argument tuples range over these -/
  dataIdx : Option (Array Nat) := none
  /-- a result with several components: the first projection, and for the others (projection, type, variable) -/
  res0 : Option Expr := none
  resExtra : Array (Expr × Ty × Nat) := #[]
  /-- list result written to the output block (block 1) -/
  lo? : Option LCtx := none

/-- a load or a temporary, emitted before the node being translated, with the Lean term it holds -/
inductive Item where
  | load (v b : Nat) (i : ME) (r : Expr) (idx : Expr) (temps : List Expr)
  | cload (v b : Nat) (i c d : ME) (r : Expr) (idx : Expr) (temps : List Expr)
  | let_ (v : Nat) (e : ME) (L L' : Expr) (ty : Ty) (temps : List Expr)
  /-- a temporary introduced only to keep expressions shallow: `v := e`, no Lean term attached -/
  | raw (v : Nat) (e : ME)
  /-- a call: the callee's program `P` renamed to base `b` (`n` temporaries), its `Rep` (name, data arguments),
  its `exec` applied to the arguments, and the result `r` (the callee's `rep` of the call) -/
  | sub (b n : Nat) (P : Expr) (repN : Name) (dargs : Array Expr) (exec : Expr) (r : Expr) (temps : List Expr)

structure TrSt where
  next : Nat
  /-- Lean scalar terms that already live in a variable (newest first) -/
  memo : List (Expr × Nat) := []
  /-- the Lean terms held in temporaries (newest first); generalised in every obligation -/
  temps : List Expr := []
  /-- a temporary's term with its helpers unfolded (when different): its `Nat` bounds for `omega` -/
  tempsU : List (Expr × Expr) := []
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

/-- a call to a translated function `c` (it has `c.exec` of the plain form, result in its variable 4): its
program, `Rep` name, number of slots, and per parameter whether it is data, a block, or its variable -/
structure CallInfo where
  P : Expr
  repN : Name
  slots : Nat
  /-- per parameter of `c.exec`: `none` = a proof, `some none` = a byte array (block 0), `some (some v)` = a scalar
  in variable `v` -/
  kinds : Array (Option (Option Nat))

def callInfo? (c : Name) : MetaM (Option CallInfo) := do
  let env ← getEnv
  unless env.contains (c ++ `exec) && env.contains (c ++ `slots) do return none
  let some sl := (← getConstInfo (c ++ `slots)).value? | return none
  let some slots := (← whnf sl).nat? <|> (← whnf sl).rawNatLit? | return none
  forallTelescope (← getConstInfo (c ++ `exec)).type fun ys concl => do
    unless ys.size ≥ 2 do return none
    let hR ← inferType ys.back!
    let some repN := hR.getAppFn.constName? | return none
    let .app (.app (.const ``Exists _) _) (.lam _ _ body _) := concl | return none
    -- `BExec P σ σ' ∧ σ'.env 4 = … ∧ σ'.heap = σ.heap`
    unless body.isAppOfArity ``And 2 do return none
    let bx := body.getArg! 0
    unless bx.isAppOfArity ``BExec 3 do return none
    let rest := body.getArg! 1
    unless rest.isAppOfArity ``And 2 && (rest.getArg! 1).isAppOfArity ``Eq 3 do return none
    let c2 := rest.getArg! 0
    let some (_, l2, _) := c2.eq? | return none
    let .app _ l2a := l2 | return none
    unless l2a.nat? == some 4 || l2a.rawNatLit? == some 4 do return none
    let P := bx.getArg! 0
    if P.hasLooseBVars then return none
    let mut kinds := #[]
    let mut nextV := 4
    for y in ys.pop.pop do
      let yty ← whnfR (← inferType y)
      if ← isProp yty then kinds := kinds.push none
      else if yty.isConstOf ``ByteArray then kinds := kinds.push (some none)
      else if (← classify yty).isSome then
        kinds := kinds.push (some (some nextV)); nextV := nextV + 1
      else return none
    -- at most one block, and it comes first
    if (kinds.filter (· == some none)).size > 1 then return none
    return some { P, repN, slots, kinds }

/-- `c` calls itself (its unfolding equation mentions it) -/
def isRecFn (c : Name) : MetaM Bool := do
  let some eqn ← (try getUnfoldEqnFor? c (nonRec := true) catch _ => pure none) | return false
  forallTelescope (← getConstInfo eqn).type fun _ ty => do
    let some (_, _, rhs) := ty.eq? | return false
    return (rhs.find? (·.isConstOf c)).isSome

/-- `e` rewritten by one of the user's equations whose left-hand side matches it -/
def userRw? (lemmas : Array Name) (e : Expr) : MetaM (Option (Name × Expr)) := do
  for l in lemmas do
    let s ← saveState
    let (_, _, ty) ← forallMetaTelescope (← getConstInfo l).type
    if let some (_, lhs, rhs) := ty.eq? then
      if ← isDefEq lhs e then
        let rhs ← instantiateMVars rhs
        unless rhs.hasMVar do return some (l, rhs)
    s.restore
  return none

def Ctx.data (ctx : Ctx) (as : Array Expr) : Array Expr :=
  match ctx.dataIdx with
  | some ix => ix.map (as[·]!)
  | none => as

def cNot (c : ME) : ME := .bin ``Op.xor c (.const (mkBV 1))

def addThm (name : Name) (type : Expr) (tac : TSyntax `tactic) : TermElabM Unit := do
  let type ← instantiateMVars type
  let pf ← elabTermEnsuringType (← `(by $tac:tactic)) type
  synthesizeSyntheticMVarsNoPostponing
  let pf ← instantiateMVars pf
  if pf.hasSorry || pf.hasMVar then throwError "frontx: could not prove {name}"
  addDecl (.thmDecl { name, levelParams := [], type, value := pf })
  unless (← getConstInfo name) matches .thmInfo _ do throwError "frontx: {name} was not added as a theorem"

/-- a constant defined in the user's files (not in `Init`, `Std`, `Lean`) -/
def userConst (c : Name) : MetaM Bool := do
  let env ← getEnv
  match env.getModuleIdxFor? c with
  | none => return true
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    return !(m.getRoot == `Init || m.getRoot == `Std || m.getRoot == `Lean)

/-- unfold user definitions and `let`s at the head until a constructor application shows (or nothing changes) -/
partial def ctorNorm (e : Expr) (fuel : Nat := 8) : MetaM Expr := do
  let e ← whnfR e
  if fuel == 0 || e.getAppFn.isConstOf ``Prod.mk || e.getAppFn.isConstOf ``MProd.mk then return e
  if e.isLet then return ← ctorNorm (e.letBody!.instantiate1 e.letValue!) (fuel - 1)
  let some c := e.getAppFn.constName? | return e
  unless (← getConstInfo c) matches .defnInfo _ do return e
  if (← getEnv).isProjectionFn c then return e
  match ← unfoldDefinition? e with
  | some u => ctorNorm u.headBeta (fuel - 1)
  | none => return e

mutual

/-- a scalar term `e`: its expression, and `e` with the inlined helpers unfolded (definitionally equal to `e`;
the terms held in temporaries occur in it syntactically) -/
partial def trE (ctx : Ctx) (e : Expr) : TrM (ME × Expr) := do
  let e := e.consumeMData.headBeta
  -- a raw projection `p.2` is written with its projection function (the form the variables are keyed by)
  let e ← match e with
    | .proj sn i s =>
      match (getStructureFields (← getEnv) sn)[i]? with
      | some fld => mkProjection s fld
      | none => pure e
    | _ => pure e
  if let some v ← find? e then return (.var v, e)
  -- a projection of a term that is not a variable component: reduce to the field when a constructor shows
  if let some c := e.getAppFn.constName? then
    if let some pi := (← getEnv).getProjectionFnInfo? c then
      if e.getAppNumArgs == pi.numParams + 1 && !pi.fromClass then
        let s := e.appArg!
        let s' ← ctorNorm s
        if s'.isApp && s'.getAppFn.isConst && (← getEnv).isConstructor s'.getAppFn.constName! then
          return ← trE ctx (s'.getArg! (pi.numParams + pi.i))
        unless s.isFVar || (← find? e).isSome do
          throwError "frontx: projection of a term that is not a constructor application{indentExpr e}"
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
  -- `x % c`, `x / c` with a literal (or constant) `c`: mask / shift for `c = 2^k`, else one conditional
  -- subtraction, which needs `x < 2 * c` from the context (checked here by `omega`)
  if (f.isConstOf ``HMod.hMod || f.isConstOf ``HDiv.hDiv) && args.size == 6 && ty == .nat && !args[5]!.hasFVar then
    let cv ← whnf args[5]!
    let some c := cv.rawNatLit? <|> cv.nat? | throwError "frontx: divisor is not a literal{indentExpr args[5]!}"
    if c == 0 then throwError "frontx: division by 0"
    let isMod := f.isConstOf ``HMod.hMod
    let x := args[4]!
    let k := Nat.log2 c
    let pow2 := 2 ^ k == c
    let lN := Name.mkStr `Proven.Frontx (s!"{if isMod then "mod" else "div"}Lit{if pow2 then "" else "2"}_{c}")
    unless (← getEnv).contains lN do
      let nat := Lean.mkConst ``Nat
      let cE := mkNatLit c
      let ty ← withLocalDeclD `x nat fun xv => do
        let lhs ← mkAppM (if isMod then ``HMod.hMod else ``HDiv.hDiv) #[xv, cE]
        if pow2 then
          let rhs ← if isMod then mkAppM ``HAnd.hAnd #[xv, mkNatLit (c - 1)]
            else mkAppM ``HShiftRight.hShiftRight #[xv, mkNatLit k]
          mkForallFVars #[xv] (← mkEq lhs rhs)
        else
          let lt ← mkAppM ``LT.lt #[xv, cE]
          let rhs ← if isMod then mkAppM ``ite #[lt, xv, ← mkAppM ``HSub.hSub #[xv, cE]]
            else mkAppM ``ite #[lt, mkNatLit 0, mkNatLit 1]
          mkForallFVars #[xv] (← mkArrow (← mkAppM ``LT.lt #[xv, mkNatLit (2 * c)]) (← mkEq lhs rhs))
      let tac ← if pow2 then
          if isMod then `(tactic| (intro x; rw [show ($(Lean.quote (c - 1)) : Nat) = 2 ^ $(Lean.quote k) - 1 from rfl,
            Nat.and_two_pow_sub_one_eq_mod]))
          else `(tactic| (intro x; rw [Nat.shiftRight_eq_div_pow]))
        else `(tactic| (intro x h; split <;> omega))
      withLCtx {} #[] (addThm lN ty tac)
    -- a named constant divisor (`MOD_ADLER`) is unfolded in the obligations
    if let some cn := args[5]!.getAppFn.constName? then
      if (← getConstInfo cn) matches .defnInfo _ then
        modify fun s => if s.unfolded.contains cn then s else { s with unfolded := s.unfolded.push cn }
    unless pow2 do
      -- closed `Nat` subterms as literals, for `omega`
      let xl ← Meta.transform x (pre := fun t => do
        if !t.hasFVar && !t.hasLooseBVars && t.getAppFn.isConst then
          if (← whnfR (← inferType t)).isConstOf ``Nat then
            let tv ← whnf t
            if let some n := tv.rawNatLit? <|> tv.nat? then return .done (mkNatLit n)
        return .continue)
      let bnd ← mkAppM ``LT.lt #[xl, mkNatLit (2 * c)]
      let ok ← (withoutModifyingState do
        try
          let mv ← mkFreshExprSyntheticOpaqueMVar bnd
          -- (`frontx_u8_facts` is defined below: parsed at run time)
          let .ok stx := Parser.runParserCategory (← getEnv) `tactic "first | omega | (frontx_u8_facts; omega)"
            | throwError "frontx: parse"
          let rest ← Tactic.run mv.mvarId! (Tactic.withoutRecover (Tactic.evalTactic stx))
          pure rest.isEmpty
        catch _ => pure false : TermElabM Bool)
      unless ok do throwError "frontx: `{e}` is translated by one conditional subtraction and needs{indentExpr bnd}\nfrom the context (a `with` invariant or `requires`)"
    modify fun s => if s.unfolded.contains lN then s else { s with unfolded := s.unfolded.push lN }
    let lty ← instantiateForall (← getConstInfo lN).type #[x]
    let lty := if lty.isArrow then lty.bindingBody! else lty
    let some (_, _, rhs) := lty.eq? | unreachable!
    let (m, _) ← trE ctx rhs
    -- the divisor as a literal in the unfolded form (so `omega` reads the bounds of temporaries)
    let (_, x') ← trE ctx x
    return (m, mkAppN f ((args.set! 4 x').set! 5 (mkNatLit c)))
  -- `c * x` / `x * c` with a `Nat` literal `c`: shifts and adds, through a proved equation `mulLit_c`
  if f.isConstOf ``HMul.hMul && args.size == 6 && ty == .nat then
    let lit? (t : Expr) : Option Nat := (t.nat?).orElse fun _ => t.rawNatLit?
    let (c?, x) := match lit? args[4]!, lit? args[5]! with
      | some c, _ => (some c, args[5]!)
      | none, some c => (some c, args[4]!)
      | none, none => (none, args[4]!)
    if let some c := c? then
      let left := lit? args[4]! |>.isSome
      let lN := Name.mkStr `Proven.Frontx (s!"mulLit{if left then "L" else "R"}_{c}")
      unless (← getEnv).contains lN do
        let nat := Lean.mkConst ``Nat
        let ty ← withLocalDeclD `x nat fun xv => do
          let cE := mkNatLit c
          let lhs ← if left then mkAppM ``HMul.hMul #[cE, xv] else mkAppM ``HMul.hMul #[xv, cE]
          let bits := (List.range (Nat.log2 c + 1)).filter fun k => c.testBit k
          let terms ← bits.mapM fun k => mkAppM ``HShiftLeft.hShiftLeft #[xv, mkNatLit k]
          let rhs ← match terms with
            | [] => pure (mkNatLit 0)
            | t :: ts => ts.foldlM (fun a b => mkAppM ``HAdd.hAdd #[a, b]) t
          mkForallFVars #[xv] (← mkEq lhs rhs)
        let tac ← `(tactic| (intro x; simp only [Nat.shiftLeft_eq]; omega))
        withLCtx {} #[] (addThm lN ty tac)
      modify fun s => if s.unfolded.contains lN then s else { s with unfolded := s.unfolded.push lN }
      let some (_, _, rhs) := (← instantiateForall (← getConstInfo lN).type #[x]).eq? | unreachable!
      let (m, _) ← trE ctx rhs
      return (m, e)
  match f.constName?, args.size with
  | some ``HAdd.hAdd, 6 => bin ``Op.add ty.mask
  | some ``HSub.hSub, 6 =>
    if ty == .nat then
      -- truncated subtraction: plain if `b ≤ a` follows from the context, else a select
      let (a, a') ← trE ctx args[4]!
      let (b, b') ← trE ctx args[5]!
      let e' := mkAppN f ((args.set! 4 a').set! 5 b')
      let le ← (withoutModifyingState do
        try
          let mv ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[args[5]!, args[4]!])
          let rest ← Tactic.run mv.mvarId! (Tactic.withoutRecover (Tactic.evalTactic (← `(tactic| omega))))
          pure rest.isEmpty
        catch _ => pure false : TermElabM Bool)
      if le then return (.bin ``Op.sub a b, e')
      else return (.ite (.bin ``Op.ult a b) (.const (mkBV 0)) (.bin ``Op.sub a b), e')
    else bin ``Op.sub ty.mask
  | some ``Nat.succ, 1 =>
    let (a, a') ← trE ctx args[0]!
    return (.bin ``Op.add a (.const (mkBV 1)), mkAppN f #[a'])
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
  | some ``UInt8.ofNat, 1 => conv (some 0xff)
  | some ``UInt32.ofNat, 1 => conv (some 0xffffffff)
  | some ``UInt64.ofNat, 1 => conv none
  | some ``ByteArray.size, 1 =>
    match ctx.block? args[0]! with
    | some (_, len) => return (.var len, e)
    | none => throwError "frontx: size of an unknown array{indentExpr e}"
  | some c, _ =>
    if c == ctx.fn then throwError "frontx: recursive call not in tail position{indentExpr e}"
    if let some (l, rhs) ← userRw? ctx.lemmas e then
      modify fun s => if s.unfolded.contains l then s else { s with unfolded := s.unfolded.push l }
      let (m, _) ← trE ctx rhs
      return (m, e)
    -- a recursive translated function: a call (no inlining attempt)
    if ← isRecFn c then
      if let some r ← trCall ctx e c args ty then return r
    -- a helper function: its compound scalar arguments go to temporaries, then it is inlined
    for a in args do
      if a.hasFVar && !a.isFVar && (← find? a).isNone then
        if let some aty ← classify (← inferType a) then
          let (m, a') ← trE ctx a
          let m ← fit m
          let v ← fresh
          modify fun s => { s with memo := (a, v) :: s.memo, temps := a :: s.temps,
                                   tempsU := if a' == a then s.tempsU else (a, a') :: s.tempsU,
                                   pend := s.pend.push (.let_ v m a a' aty s.temps) }
    let st0 ← get
    let ms ← (saveState : TermElabM Term.SavedState)
    try
      match ← unfoldDefinition? e with
      | some e' =>
        modify fun s => if s.unfolded.contains c then s else { s with unfolded := s.unfolded.push c }
        trE ctx e'
      | none => throwError "frontx: unsupported term{indentExpr e}"
    catch ex =>
      (ms.restore : TermElabM Unit)
      set st0
      match ← trCall ctx e c args ty with
      | some r => return r
      | none => throw ex
  | none, _ => throwError "frontx: unsupported term{indentExpr e}"

/-- a decidable proposition, as a `0`/`1` value; and the proposition with helpers unfolded -/
partial def trC (ctx : Ctx) (p : Expr) : TrM (ME × Expr) := do
  let p := p.consumeMData.headBeta
  let args := p.getAppArgs
  let f := p.getAppFn
  let cmp (i j : Nat) (neg : Bool) : TrM (ME × Expr) := do
    -- a compound `Nat` side goes to a temporary: the test is then between variables (and `omega` has its equation)
    for k in [i, j] do
      let x := args[k]!
      if x.hasFVar && !x.isFVar && !x.isAppOfArity ``ByteArray.size 1 && (← find? x).isNone &&
          (← whnfR (← inferType x)).isConstOf ``Nat then
        let (m, x') ← trE ctx x
        let m ← fit m
        let v ← fresh
        modify fun s => { s with memo := (x, v) :: s.memo, temps := x :: s.temps,
                                 pend := s.pend.push (.let_ v m x x' .nat s.temps) }
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
  if let some v ← find? b then return (.var v, b)
  if !b.hasFVar then return (.const (← litBV (mkApp (mkConst ``rB) b)), b)
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
  | some ``ite, 5 =>
    let (c, p') ← trC ctx args[1]!
    let (x, x') ← trB ctx args[3]!
    let (y, y') ← trB ctx args[4]!
    return (.ite c x y, ← mkAppOptM ``ite #[args[0]!, p', none, x', y'])
  | some ``Decidable.decide, 2 =>
    let (c, q) ← trC ctx args[0]!
    return (c, ← mkAppOptM ``Decidable.decide #[q, none])
  | some c, _ =>
    if let some v ← find? b then return (.var v, b)
    if c == ctx.fn then throwError "frontx: recursive call not in tail position{indentExpr b}"
    if let some (l, rhs) ← userRw? ctx.lemmas b then
      modify fun s => if s.unfolded.contains l then s else { s with unfolded := s.unfolded.push l }
      let (m, _) ← trB ctx rhs
      return (m, b)
    if ← isRecFn c then
      if let some r ← trCall ctx b c args .bool then return r
    for a in args do
      if a.hasFVar && !a.isFVar && (← find? a).isNone then
        if let some aty ← classify (← inferType a) then
          let (m, a') ← trE ctx a
          let m ← fit m
          let v ← fresh
          modify fun s => { s with memo := (a, v) :: s.memo, temps := a :: s.temps,
                                   tempsU := if a' == a then s.tempsU else (a, a') :: s.tempsU,
                                   pend := s.pend.push (.let_ v m a a' aty s.temps) }
    let st0 ← get
    let ms ← (saveState : TermElabM Term.SavedState)
    try
      match ← unfoldDefinition? b with
      | some b' =>
        modify fun s => if s.unfolded.contains c then s else { s with unfolded := s.unfolded.push c }
        trB ctx b'
      | none => throwError "frontx: unsupported Bool{indentExpr b}"
    catch ex =>
      (ms.restore : TermElabM Unit)
      set st0
      match ← trCall ctx b c args .bool with
      | some r => return r
      | none => throw ex
  | _, _ => throwError "frontx: unsupported Bool{indentExpr b}"


/-- a call to a translated function `c` (`e = c args`, scalar type `ty`): its program as a sub-program
(`Tree.sub`), the arguments assigned to the callee's variables, the result in a fresh variable -/
partial def trCall (ctx : Ctx) (e : Expr) (c : Name) (args : Array Expr) (ty : Ty) : TrM (Option (ME × Expr)) := do
    let some ci ← callInfo? c | return none
    unless args.size == ci.kinds.size && ctx.lo?.isNone do return none
    let n := ci.slots + 3
    -- the callee's range is `b .. b + n`; the temporaries of the arguments go into it, above its parameters
    let b := (← get).next
    let np := (ci.kinds.filter fun k => k matches some (some _)).size
    modify fun s => { s with next := b + np }
    let mut dargs := #[]
    let mut assigns := #[]
    for (a, k) in args.zip ci.kinds do
      match k with
      | none => pure ()
      | some none =>
        unless (ctx.block? a).map (·.1) == some 0 do
          throwError "frontx: a call whose array argument is not the first block{indentExpr e}"
        dargs := dargs.push a
      | some (some v) =>
        dargs := dargs.push a
        let some aty ← classify (← inferType a) | throwError "frontx: argument type{indentExpr a}"
        let (m, a') ← trE ctx a
        let m ← fit m
        assigns := assigns.push (b + (v - 4), m, a, a', aty)
    -- after the call, the range holds the result in `b`, zeros elsewhere: forget what was kept there
    modify fun s => { s with next := max s.next (b + n + 1),
                             memo := s.memo.filter fun (_, v) => v < b || b + n < v }
    for (v, m, a, a', aty) in assigns do
      modify fun s => { s with pend := s.pend.push (.let_ v m a a' aty s.temps) }
    let exec := mkAppN (mkConst (c ++ `exec)) args
    let isRec ← isRecFn c
    modify fun s => { s with memo := (e, b) :: s.memo,
                             pend := s.pend.push (.sub b n ci.P ci.repN dargs exec (ty.rep e) s.temps),
                             -- the obligations may unfold a non-recursive callee (facts about its result)
                             unfolded := if s.unfolded.contains c || isRec then s.unfolded else s.unfolded.push c }
    -- the variables of the callee's program (for `Tree.wf`, `simp`)
    let vN := c ++ `callvars
    unless (← getEnv).contains vN do
      let vty ← mkEq (mkApp2 (mkConst ``BStmt.vltF) (toExpr (5 + n)) ci.P) (mkConst ``Bool.true)
      let mv ← mkFreshExprSyntheticOpaqueMVar vty
      let rest ← Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic| decide)))
      unless rest.isEmpty do throwError "frontx: callee variables"
      addDecl (.thmDecl { name := vN, levelParams := [], type := vty, value := ← instantiateMVars mv })
      addSimpTheorem simpExtension vN (post := true) (inv := false) .global 1000
    return some (.var b, e)

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
  #[``Tree.step, ``denote_var, ``denote_const, ``denote_bin, ``denote_ite, ``sel_c, ``sel_c', ``Op.eval, ``parSet, ``BEnv.set,
    ``seqSet, ``rB_def, ``callEnv, ``rho, ``rd0, ``rd1, ``rd2, ``blk_get, ``r8_fold, ``ba_get!, ``c_not, ``c_and, ``c_or, ``c_eq0, ``c_not', ``c_and', ``c_or', ``c_eq0',
    ``rN_lit, ``r8_lit, ``r32_lit, ``r64_lit, ``rN_toNat, ``rN_add, ``r8_toNat_sub, ``r32_toNat_sub, ``rN_sub', ``nat_ite_lt_neg, ``rN_lt, ``rN_or, ``rN_and, ``rN_shl, ``rN_inj, ``rN_eq_lit, ``rN_lt_lit, ``rN_lit_lt, ``rN_ite,
    ``r64_add, ``r64_sub, ``r64_and, ``r64_or, ``r64_xor, ``r64_ite, ``r64_eq', ``r64_lt', ``r64_le', ``r64_toNat, ``r64_ofNat,
    ``r32_add, ``r32_sub, ``r32_and, ``r32_or, ``r32_xor, ``r32_ite, ``r32_eq', ``r32_lt', ``r32_le', ``r32_toNat, ``r32_shr,
    ``r8_add, ``r8_sub, ``r8_and, ``r8_or, ``r8_xor, ``r8_ite, ``r8_eq', ``r8_lt', ``r8_le', ``r8_toNat,
    ``r8_dite, ``r32_dite, ``r64_dite, ``rN_dite,
    ``r32_of8, ``r64_of8, ``r64_of32, ``r8_of32, ``r32_of64, ``r8_of64, ``r8_ofNat, ``r32_ofNat,
    ``r8_ofNatU, ``r32_ofNatU, ``r64_ofNatU, ``r32_shl, ``rN_shr]

/-- side conditions (bounds): `omega`, also through the defining equation of a temporary that is an `if` -/
elab "frontx_ite_facts" : tactic => withMainContext do
  let mut g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (α, lhs, _) := ty.eq? | continue
    unless α.isConstOf ``Nat && lhs.isAppOfArity ``ite 5 do continue
    let pf ← mkAppM ``ite_eq_or #[d.toExpr]
    let (_, g') ← (← g.assert `hite (← inferType pf) pf).intro1P
    g := g'
  replaceMainGoal [g]

/-- `x.toNat < 2 ^ 8` for the bytes `x` whose `toNat` occurs in the goal or the hypotheses -/
elab "frontx_u8_facts" : tactic => withMainContext do
  let mut g ← getMainGoal
  let mut seen : Array Expr := #[]
  let mut tys := #[← instantiateMVars (← g.getType)]
  for d in ← getLCtx do
    unless d.isImplementationDetail do tys := tys.push (← instantiateMVars d.type)
  let collect (e : Expr) (acc : Array Expr) : Array Expr := Id.run do
    let mut acc := acc
    let mut todo := #[e]
    while h : todo.size > 0 do
      let t := todo[todo.size - 1]
      todo := todo.pop
      if (t.isAppOfArity ``UInt8.toNat 1 || t.isAppOfArity ``UInt16.toNat 1 || t.isAppOfArity ``UInt32.toNat 1 ||
          t.isAppOfArity ``UInt64.toNat 1) && !t.hasLooseBVars && !acc.contains t then acc := acc.push t
      match t with
      | .app f x => todo := (todo.push f).push x
      | .lam _ d b _ | .forallE _ d b _ => todo := (todo.push d).push b
      | .letE _ d v b _ => todo := ((todo.push d).push v).push b
      | .mdata _ b | .proj _ _ b => todo := todo.push b
      | _ => pure ()
    return acc
  for ty in tys do seen := collect ty seen
  if seen.isEmpty then throwError "frontx_u8_facts: no byte"
  for t in seen do
    let x := t.appArg!
    let pf := match t.getAppFn.constName? with
      | some ``UInt16.toNat => mkApp (mkConst ``UInt16.toNat_lt) x
      | some ``UInt32.toNat => mkApp (mkConst ``UInt32.toNat_lt) x
      | some ``UInt64.toNat => mkApp (mkConst ``UInt64.toNat_lt) x
      | _ => mkApp (mkConst ``UInt8.toNat_lt) x
    let (_, g') ← (← g.assert `hu8 (← inferType pf) pf).intro1P
    g := g'
  replaceMainGoal [g]

macro "frontx_disch" : tactic =>
  `(tactic| first | omega | (frontx_ite_facts; omega) | (subst_vars; split; omega; omega) | (frontx_u8_facts; omega))

/-- expression evaluation, and every supported operation pushed through its representation function -/
macro "frontx_simp" "[" ts:ident,* "]" : tactic => do
  let ids := ts.getElems ++ simpNames.map mkIdent
  let ls ← ids.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:ident)
  `(tactic| simp +zetaDelta (disch := frontx_disch) [$ls,*, *, -String.toUTF8_eq_toByteArray, -String.size_toByteArray])

/-- prove one obligation: generalise the Lean terms held in temporaries, then `frontx_simp` / `omega` -/
def oblig (type : Expr) (temps? : Option (List Expr) := none) : TrM Expr := do
  let st ← get
  let temps := temps?.getD st.temps
  modify fun s => { s with nObl := s.nObl + 1 }
  let mv ← mkFreshExprSyntheticOpaqueMVar type
  let mut g := mv.mvarId!
  -- `Nat` temporaries defined by a helper: also their unfolded form (`L = L'`, definitional)
  for L in temps do
    if let some (_, L') := st.tempsU.find? (·.1 == L) then
      if (← whnfR (← inferType L)).isConstOf ``Nat then
        let ty ← mkEq L L'
        let pf ← mkExpectedTypeHint (← mkEqRefl L) ty
        let (_, g') ← (← g.assert (← mkFreshUserName `hu) ty pf).intro1P
        g := g'
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
      -- (a term under a proof whose type depends on it cannot be generalised: kept as it is)
      try
        let (_, g') ← g.generalize #[arg]
        g := g'
      catch _ => pure ()
  let us := st.unfolded.map mkIdent
  let usL ← us.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:ident)
  -- last resort: both sides are `if`s over equivalent (not identical) arithmetic conditions
  -- (a failing `rfl` at default transparency can take seconds on fixed-width terms: reducible first, full last)
  let tac ← `(tactic| first | with_reducible rfl | frontx_disch |
    (frontx_simp [$us,*] <;> (first | done | frontx_disch | rfl |
      (intro hq; frontx_simp [$us,*] <;> (first | done | frontx_disch | rfl)) |
      (split <;> split <;> (first | rfl | (exfalso; frontx_disch))))) |
    ((simp only [$usL,*] at *) <;> first | omega | (frontx_u8_facts; omega)) | rfl)
  let rest ← try Tactic.run g (Tactic.withoutRecover (Tactic.evalTactic tac)) catch e =>
    throwError "frontx: could not prove{indentExpr type}\ngoal: {MessageData.ofGoal g}\n{e.toMessageData}"
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

def mkConjPf : List Expr → List Expr → MetaM Expr
  | [_], [p] => pure p
  | c :: cs, p :: ps => do
    let q ← mkConjPf cs ps
    return mkApp4 (mkConst ``And.intro) c (← inferType q) p q
  | _, _ => pure (mkConst ``True.intro)

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
  | .sub b n P repN dargs exec r temps :: rest => do
    let bS := toExpr b
    let rhoE := mkApp (mkConst ``rho) bS
    let envG ← withLocalDeclD `v (mkConst ``Nat) fun v => mkLambdaFVars #[v] (mkApp env (mkApp rhoE v))
    let σg := mkApp2 (mkConst ``BState.mk) envG ctx.heap
    let some conj ← unfoldDefinition? (mkAppN (mkConst repN) (dargs.push σg))
      | throwError "frontx: cannot unfold {repN}"
    let conj := conj.headBeta
    let rec conjs (e : Expr) : List Expr :=
      if e.isAppOfArity ``And 2 then e.getArg! 0 :: conjs (e.getArg! 1) else [e]
    let cs := conjs conj
    let ps ← cs.mapM (oblig · temps)
    let hR ← mkConjPf cs ps
    let hg := mkApp2 exec σg hR
    let byDecide (ty : Expr) : TrM Expr := do
      let mv ← mkFreshExprSyntheticOpaqueMVar ty
      let rest ← Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic| decide)))
      unless rest.isEmpty do throwError "frontx: could not decide{indentExpr ty}"
      instantiateMVars mv
    let hb ← byDecide (← mkAppM ``LE.le #[toExpr (4 : Nat), bS])
    let hpv ← byDecide (← mkEq (mkApp2 (mkConst ``BStmt.vltF) (toExpr (5 + n)) P) (mkConst ``Bool.true))
    let hlow ← byDecide (← withLocalDeclD `v (mkConst ``Nat) fun v => do
      mkForallFVars #[v] (← mkArrow (← mkAppM ``Membership.mem #[mkApp (mkConst ``BStmt.assigns) P, v])
        (← mkAppM ``LE.le #[toExpr (4 : Nat), v])))
    let hx := mkAppN (mkConst ``callP_exec) #[P, bS, toExpr n, hb, hpv, hlow, env, ctx.heap, r, hg]
    let env' := mkApp4 (mkConst ``callEnv) env bS (toExpr n) r
    let (t, o, p) ← wrapItems ctx rest env' k
    let pE := mkApp3 (mkConst ``callP) P bS (toExpr n)
    return (.sub pE t, o, mkAppN (mkConst ``sim_sub)
      #[ctx.A, ctx.R, pE, ← t.toExpr, env, ctx.heap, env', o, hx, p])
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
  -- a tuple state (`foldl` over a pair): one local per component
  if S.isAppOfArity ``Prod 2 then return (← flattenS (S.getArg! 0)) ++ (← flattenS (S.getArg! 1))
  return [S]

/-- the components of a state term of type `S` -/
partial def stateComps (S s : Expr) : MetaM (List Expr) := do
  let S ← whnfR S
  if S.isAppOfArity ``MProd 2 then
    let s' ← whnfR s
    if s'.isAppOfArity ``MProd.mk 4 then return s'.getArg! 2 :: (← stateComps (S.getArg! 1) (s'.getArg! 3))
    return (← mkAppM ``MProd.fst #[s]) :: (← stateComps (S.getArg! 1) (← mkAppM ``MProd.snd #[s]))
  if S.isConstOf ``PUnit || S.isConstOf ``Unit then return []
  if S.isAppOfArity ``Prod 2 then
    let s' ← ctorNorm s
    if s'.isAppOfArity ``Prod.mk 4 then
      return (← stateComps (S.getArg! 0) (s'.getArg! 2)) ++ (← stateComps (S.getArg! 1) (s'.getArg! 3))
    return (← stateComps (S.getArg! 0) (← mkAppM ``Prod.fst #[s])) ++
      (← stateComps (S.getArg! 1) (← mkAppM ``Prod.snd #[s]))
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
  if S.isAppOfArity ``Prod 2 then
    let n := (← flattenS (S.getArg! 0)).length
    return ← mkAppM ``Prod.mk #[← mkState (S.getArg! 0) (xs.take n), ← mkState (S.getArg! 1) (xs.drop n)]
  match xs with
  | [x] => return x
  | _ => throwError "frontx: state arity"

/-- a value after the loop: beta, `Id`, `match` on the state tuple, `let` -/
partial def valNorm (v : Expr) (fuel : Nat := 16) : MetaM Expr := do
  let v ← idNorm v
  if fuel == 0 then return v
  if v.isAppOfArity ``ite 5 then
    let a := v.getAppArgs
    return mkAppN v.getAppFn #[a[0]!, a[1]!, a[2]!, ← valNorm a[3]! (fuel - 1), ← valNorm a[4]! (fuel - 1)]
  if v.isLet then return ← valNorm (v.letBody!.instantiate1 v.letValue!) (fuel - 1)
  if (← matchMatcherApp? v).isSome then
    let v' ← whnfCore v
    if v' != v then return ← valNorm v' (fuel - 1)
  return v

/-- the capacity side condition of a store or a call in a function writing its list result: from
`j + (f xs).length ≤ O.length`, the equation `f xs = body` and the path conditions -/
def capOblig (ctx : Ctx) (ty : Expr) : TrM Expr := do
  let some lo := ctx.lo? | throwError "frontx: not a list result"
  modify fun s => { s with nObl := s.nObl + 1 }
  let mv ← mkFreshExprSyntheticOpaqueMVar ty
  let hS ← Term.exprToSyntax lo.hcap
  let eS ← Term.exprToSyntax lo.eq
  let tac ← `(tactic|
    (have hc := ($hS:term)
     rw [$eS:term] at hc
     (try simp only [*, ↓reduceDIte, ↓reduceIte, dite_true, dite_false, ite_true, ite_false, eq_self_iff_true,
        not_true_eq_false, not_false_eq_true, Bool.false_eq_true, Bool.true_eq_false] at hc)
     (try simp only [List.length_set, List.length_cons, List.length_nil, List.length_append] at hc ⊢)
     first | omega | (frontx_simp [] <;> frontx_disch)))
  let rest ← try Tactic.run mv.mvarId! (Tactic.withoutRecover (Tactic.evalTactic tac)) catch e => do
    let mv' ← mkFreshExprSyntheticOpaqueMVar ty
    let gs ← try Tactic.run mv'.mvarId! (Tactic.evalTactic (← `(tactic|
      (have hc := ($hS:term)
       rw [$eS:term] at hc
       (try simp only [*, ↓reduceDIte, ↓reduceIte, dite_true, dite_false, ite_true, ite_false, eq_self_iff_true,
          not_true_eq_false, not_false_eq_true, Bool.false_eq_true, Bool.true_eq_false] at hc)
       (try simp only [List.length_set, List.length_cons, List.length_nil, List.length_append] at hc ⊢))))) catch _ => pure []
    throwError "frontx: could not prove the capacity condition{indentExpr ty}\n{e.toMessageData}\n{goalsToMessageData gs}"
  unless rest.isEmpty do throwError "frontx: could not prove the capacity condition{indentExpr ty}"
  instantiateMVars mv

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
    let some conj ← unfoldDefinition? (mkAppN (mkConst ctx.repN) ((ctx.data (repArgs vals)).push σ₁))
      | throwError "frontx: cannot unfold {ctx.repN}"
    let cs := splitAnd nconj conj.headBeta
    let ps ← cs.toArray.mapIdxM fun k c =>
      if ctx.lo?.isSome && k + 1 == nconj then capOblig ctx c
      else if ctx.lo?.isSome then (do try oblig c catch _ => capOblig ctx c) else oblig c
    let ps := ps.toList
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

/-- a `Nat` pattern: `(c, isVar)` for the literal `c` resp. `m + c` -/
partial def decPat (p : Expr) : Option (Nat × Bool) :=
  match p.nat? <|> p.rawNatLit? with
  | some c => some (c, false)
  | none =>
    if p.isConstOf ``Nat.zero then some (0, false)
    else if p.isAppOfArity ``Nat.succ 1 then (decPat p.appArg!).map fun (c, v) => (c + 1, v)
    else if p.isAppOfArity ``HAdd.hAdd 6 then
      match (p.getArg! 5).nat? <|> (p.getArg! 5).rawNatLit?, decPat (p.getArg! 4) with
      | some k, some (c, v) => some (c + k, v)
      | _, _ => none
    else if p.isFVar || p.isBVar then some (0, true)
    else none

/-- the patterns of a `match` on one `Nat`, per alternative -/
def natPats (ma : MatcherApp) : MetaM (Array (Nat × Bool)) := do
  let info ← getConstInfo ma.matcherName
  forallTelescope info.type fun args _ => do
    let first := ma.params.size + 1 + ma.discrs.size
    let mut out := #[]
    for i in [0:ma.alts.size] do
      let p ← forallTelescope (← inferType args[first + i]!) fun _ body => pure body.appArg!
      let some r := decPat p | throwError "frontx: unsupported pattern{indentExpr p}"
      out := out.push r
    return out

/-- `Prod.fst (a, b) ↦ a`, `(some v).isSome ↦ true`, `(some v).getD d ↦ v`, … -/
def projNorm (e : Expr) : MetaM Expr :=
  Meta.transform e.headBeta (post := fun e => do
    let e := e.headBeta
    if e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3 then
      let p ← whnfR e.appArg!
      if p.isAppOfArity ``Prod.mk 4 then
        return .done (if e.isAppOfArity ``Prod.fst 3 then p.getArg! 2 else p.getArg! 3)
    if let some c := e.getAppFn.constName? then
      if let some info ← getProjectionFnInfo? c then
        if e.getAppNumArgs == info.numParams + 1 then
          let sArg ← whnfR e.appArg!
          if sArg.isAppOf info.ctorName then return .done (← whnfR (mkApp e.appFn! sArg))
    if e.isAppOfArity ``Option.isSome 2 then
      let o ← whnfR e.appArg!
      if o.isAppOfArity ``Option.some 2 then return .done (mkConst ``Bool.true)
      if o.isAppOfArity ``Option.none 1 then return .done (mkConst ``Bool.false)
    if e.isAppOfArity ``Option.getD 3 then
      let o ← whnfR (e.getArg! 1)
      if o.isAppOfArity ``Option.some 2 then return .done o.appArg!
      if o.isAppOfArity ``Option.none 1 then return .done (e.getArg! 2)
    return .done e)

/-- the components of a result type: per component, the projection `fun x => …` and its scalar type -/
partial def resultComps (ty : Expr) : MetaM (Option (Array (Expr × Ty))) := do
  let ty ← whnfR ty
  if let some t ← classify ty then
    return some #[(← withLocalDeclD `x ty fun x => mkLambdaFVars #[x] x, t)]
  if ty.isAppOfArity ``Prod 2 then
    let some first ← resultComps (ty.getArg! 0) | return none
    let some rest ← resultComps (ty.getArg! 1) | return none
    let first' ← first.mapM fun (π, t) => do
      let l ← withLocalDeclD `p ty fun p => do mkLambdaFVars #[p] (mkApp π (← mkAppM ``Prod.fst #[p])).headBeta
      return (l, t)
    let rest' ← rest.mapM fun (π, t) => do
      let l ← withLocalDeclD `p ty fun p => do mkLambdaFVars #[p] (mkApp π (← mkAppM ``Prod.snd #[p])).headBeta
      return (l, t)
    return some (first' ++ rest')
  if let .const sn _ := ty.getAppFn then
    if isStructure (← getEnv) sn && sn != ``Prod then
      -- a structure: its fields, each a scalar or again such a structure
      let mut out := #[]
      for fld in getStructureFields (← getEnv) sn do
        let (fty, projL) ← withLocalDeclD `p ty fun p => do
          let pr ← mkProjection p fld
          return (← inferType pr, ← mkLambdaFVars #[p] pr)
        let some sub ← resultComps fty | return none
        for (π, t) in sub do
          let l ← withLocalDeclD `p ty fun p => do mkLambdaFVars #[p] (mkApp π (mkApp projL p).headBeta).headBeta
          out := out.push (l, t)
      return some out
  if ty.isAppOfArity ``Option 1 then
    let α := ty.appArg!
    let some ta ← classify α | return none
    let zero ← if ta == .bool then pure (Lean.mkConst ``Bool.false) else mkAppOptM ``OfNat.ofNat #[α, mkRawNatLit 0, none]
    let isS ← withLocalDeclD `o ty fun o => do mkLambdaFVars #[o] (← mkAppM ``Option.isSome #[o])
    let getL ← withLocalDeclD `o ty fun o => do mkLambdaFVars #[o] (← mkAppM ``Option.getD #[o, zero])
    return some #[(isS, .bool), (getL, ta)]
  return none

/-- the list `[(v, x), …]` of extra result variables and their values -/
def mkRs (rs : Array (Nat × Expr)) : MetaM Expr :=
  mkListLit (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) bv64)
    (rs.toList.map fun (v, x) => mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) bv64 (toExpr v) x)

/-- a `ret` leaf of a function whose result has several components -/
def retLeafM (ctx : Ctx) (env : Expr) (e : Expr) : TrM (MT × Expr × Expr) := do
  let e0 ← projNorm (mkApp ctx.res0.get! e)
  let mut rs := #[]
  for (π, ty, rv) in ctx.resExtra do
    let ej ← projNorm (mkApp π e)
    let (m, ej') ← trE ctx ej
    let m ← fit m
    modify fun s => { s with pend := s.pend.push (.let_ rv m ej ej' ty s.temps) }
    rs := rs.push (rv, ty.rep ej)
  let (m, e0') ← trE ctx e0
  let m ← fit m
  wrapItems ctx (← takePend) env fun env => do
    let h ← oblig (← mkEq (denoteE env m) (ctx.rty.rep e0'))
    let mut hr := mkApp (mkConst ``allEnv_nil) env
    let mut tail : Array (Nat × Expr) := #[]
    for (v, x) in rs.reverse do
      let hv ← oblig (← mkEq (mkApp env (toExpr v)) x)
      hr := mkAppN (mkConst ``allEnv_cons) #[env, toExpr v, x, ← mkRs tail.reverse, hv, hr]
      tail := tail.push (v, x)
    let r := ctx.rty.rep e0
    let rsE ← mkRs rs
    return (.ret m, mkApp3 (mkConst ``LOut.retm) ctx.A r rsE,
      mkAppN (mkConst ``sim_retm) #[ctx.A, ctx.R, m.toExpr, env, ctx.heap, r, rsE, h, hr])

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
                                 tempsU := if v' == v then s.tempsU else (v, v') :: s.tempsU,
                                 pend := s.pend.push (.let_ x m v v' ty s.temps) }
    return ← trT ctx nconj env (e.letBody!.instantiate1 v)
  let args := e.getAppArgs
  -- a two-way branch on `P`
  let branch (P inst : Expr) (kT kF : Expr → Expr → TrM (MT × Expr × Expr)) : TrM (MT × Expr × Expr) := do
    let (c, P') ← trC ctx P
    let c ← fit c
    wrapItems ctx (← takePend) env fun env => do
      let hc ← testOblig env c P'
      let br (hty : Expr) (k : Expr → Expr → TrM (MT × Expr × Expr)) : TrM (MT × Expr × Expr × Expr) := inBranch do
        withLocalDeclD `h hty fun h => do
          let (t, o, p) ← k env h
          let tail := if ctx.loop.isSome then o.appArg! else o
          return (t, ← mkLambdaFVars #[h] o, ← mkLambdaFVars #[h] p, ← mkLambdaFVars #[h] tail)
      let (t, o₁, p₁, x₁) ← br P kT
      let (f, o₂, p₂, x₂) ← br (mkNot P) kF
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
    return ← branch args[1]! args[2]! (fun env _ => trT ctx nconj env args[3]!) (fun env _ => trT ctx nconj env args[4]!)
  if e.isAppOfArity ``dite 5 then
    return ← branch args[1]! args[2]! (fun env h => trT ctx nconj env (args[3]!.beta #[h]))
      (fun env h => trT ctx nconj env (args[4]!.beta #[h]))
  -- `match n with | 0 => A | 1 => B | m + 2 => C` on a `Nat`: tests `n = 0`, `n = 1`, then `m := n - 2`
  if let some ma ← matchMatcherApp? e then
    if ma.discrs.size == 1 && ma.remaining.isEmpty then
      let n := ma.discrs[0]!
      if (← whnfR (← inferType n)).isConstOf ``Nat then
        let pats ← natPats ma
        let rec go (env : Expr) (i : Nat) : TrM (MT × Expr × Expr) := do
          let some (c, isVar) := pats[i]? | throwError "frontx: unsupported match{indentExpr e}"
          let alt := ma.alts[i]!
          if isVar then
            let arg ← if c == 0 then pure n else mkAppM ``HSub.hSub #[n, toExpr c]
            if i + 1 == pats.size || c == 0 then return ← trT ctx nconj env (alt.beta #[arg])
            let P ← mkAppM ``LE.le #[toExpr c, n]
            let inst ← synthInstance (mkApp (mkConst ``Decidable) P)
            branch P inst (fun env _ => trT ctx nconj env (alt.beta #[arg])) (fun env _ => go env (i + 1))
          else
            let body := if alt.isLambda then alt.beta #[mkConst ``Unit.unit] else alt
            if i + 1 == pats.size then return ← trT ctx nconj env body
            let P ← mkEq n (toExpr c)
            let inst ← synthInstance (mkApp (mkConst ``Decidable) P)
            branch P inst (fun env _ => trT ctx nconj env body) (fun env _ => go env (i + 1))
        return ← go env 0
    if ma.discrs.size == 1 && ma.remaining.isEmpty then
      let d := ma.discrs[0]!
      let dty ← whnfR (← inferType d)
      -- `match p with | ⟨a, b⟩ => B`: the fields of `p` (no test)
      if let .const sn _ := dty.getAppFn then
        if isStructure (← getEnv) sn && ma.alts.size == 1 then
          let flds ← (getStructureFields (← getEnv) sn).mapM fun f => mkProjection d f
          return ← trT ctx nconj env (ma.alts[0]!.beta flds)
      -- `match o with | none => A | some v => B v`: the test `o.isSome`, with `v := o.getD 0`
      if dty.isAppOfArity ``Option 1 && ma.alts.size == 2 then
        let α := dty.appArg!
        let (iN, iS) := if ma.altNumParams[0]! == 1 && ma.altNumParams[1]! != 1 then (1, 0) else (0, 1)
        let zero ← if (← whnfR α).isConstOf ``Bool then pure (Lean.mkConst ``Bool.false)
          else mkAppOptM ``OfNat.ofNat #[α, mkRawNatLit 0, none]
        let P ← mkEq (← mkAppM ``Option.isSome #[d]) (Lean.mkConst ``Bool.true)
        let inst ← synthInstance (mkApp (mkConst ``Decidable) P)
        let noneB := ma.alts[iN]!
        let noneB := if noneB.isLambda then noneB.beta #[mkConst ``Unit.unit] else noneB
        let someB := ma.alts[iS]!.beta #[← mkAppM ``Option.getD #[d, zero]]
        return ← branch P inst (fun env _ => trT ctx nconj env someB) (fun env _ => trT ctx nconj env noneB)
    throwError "frontx: unsupported match{indentExpr e}"
  if let some li := ctx.loop then
    -- the leaves of a loop body
    if e.isAppOfArity ``ForInStep.yield 2 then
      let s' := e.appArg!
      -- `yield (g …)` with a helper `g` returning the state (`foldl g`): unfold `g`, its `let`s go first
      if (← whnfR li.S).isAppOfArity ``Prod 2 && !(← whnfR s').isAppOfArity ``Prod.mk 4 then
        if let some c := s'.getAppFn.constName? then
          if c != ctx.fn && (← userConst c) && (← getConstInfo c) matches .defnInfo _ then
            if let some u ← unfoldDefinition? s' then
              let rec lift (u : Expr) : Expr :=
                match u.headBeta with
                | .letE n t v b nd => .letE n t v (lift b) nd
                | u => mkApp (e.appFn!) u
              modify fun st => if st.unfolded.contains c then st else { st with unfolded := st.unfolded.push c }
              return ← trT ctx nconj env (lift u)
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
      if ctx.res0.isSome then throwError "frontx: `break`/`return` in a loop with a result of several components"
      let s' := e.appArg!
      let v ← valNorm (mkApp li.postLean s')
      return ← retLeaf ctx env v (mkApp li.postBV s') (mkApp li.g e)
    throwError "frontx: unsupported term in a loop body{indentExpr e}"
  let callGen (args : Array Expr) : TrM (MT × Expr × Expr) := do
    let mut as := #[]
    let mut idx := #[]
    for j in [0:args.size] do
      let p := ctx.params[j]!
      if args[j]! == p || (← isProof p) || ctx.lo?.any (·.OP == p) then continue
      if (ctx.block? p).isSome then throwError "frontx: array argument changed in the call{indentExpr e}"
      match ← find? p with
      | some v =>
        as := as.push (v, args[j]!)
        idx := idx.push (some j)
      | none =>
        -- a parameter with several components: assign the components that change
        let some comps ← resultComps (← inferType p) | throwError "frontx: parameter without a variable{indentExpr p}"
        for (π, _) in comps do
          let old := (mkApp π p).headBeta
          let new ← projNorm (mkApp π args[j]!)
          if new == old then continue
          let some v ← find? old | throwError "frontx: parameter without a variable{indentExpr old}"
          as := as.push (v, new)
          idx := idx.push none
    let repArgs (vals : Array Expr) : Array Expr := Id.run do
      let mut r := args
      for (j?, k) in idx.zipIdx do
        if let some j := j? then r := r.set! j vals[k]!
      return r
    let (_, a) ← mkTuple (← (ctx.data args).toList.mapM fun x => do return (x, ← inferType x))
    return ← callLeaf ctx nconj env as repArgs a (mkApp2 (mkConst ``LOut.call) ctx.A a)
  if let some lo := ctx.lo? then
    let bv8L ← mkAppM ``List #[mkApp (mkConst ``BitVec) (toExpr (8 : Nat))]
    let heapE (O : Expr) : MetaM Expr := mkListLit bv8L [lo.A0, O]
    if e.isAppOfArity ``List.nil 1 then
      let r := mkApp (mkConst ``rN) lo.j
      let H ← heapE lo.O
      let (m, j') ← trE ctx lo.j
      let m ← fit m
      return ← wrapItems ctx (← takePend) env fun env => do
        let h ← oblig (← mkEq (denoteE env m) (mkApp (mkConst ``rN) j'))
        let hH ← oblig (← mkEq ctx.heap H)
        return (.ret m, mkApp3 (mkConst ``LOut.reth) ctx.A r H,
          mkAppN (mkConst ``sim_reth) #[ctx.A, ctx.R, m.toExpr, env, ctx.heap, r, H, h, hH])
    if e.isAppOfArity ``List.cons 3 then
      let y := e.getArg! 1
      let t := e.getArg! 2
      let (mi, j') ← trE ctx lo.j
      let mi ← fit mi
      let (my, y') ← trE ctx y
      let my ← fit my
      return ← wrapItems ctx (← takePend) env fun env => do
        let hH ← oblig (← mkEq ctx.heap (← heapE lo.O))
        let hjT ← mkEq (mkApp2 (mkConst ``BitVec.toNat) (toExpr (64 : Nat)) (denoteE env mi)) j'
        let hj ← try oblig hjT catch _ => capOblig ctx hjT
        let hlt ← capOblig ctx (← mkAppM ``LT.lt #[lo.j, ← mkAppM ``List.length #[lo.O]])
        let hy0 ← oblig (← mkEq (denoteE env my) (mkApp (mkConst ``r8) y'))
        let hy := mkApp3 (mkConst ``setw_of_r8) (denoteE env my) y hy0
        let O' ← mkAppM ``List.set #[lo.O, lo.j, mkApp (mkConst ``UInt8.toBitVec) y]
        let H' ← heapE O'
        let j1 ← mkAppM ``HAdd.hAdd #[lo.j, toExpr (1 : Nat)]
        let ctx' := { ctx with heap := H', lo? := some { lo with j := j1, O := O' } }
        let (k, o, p) ← trT ctx' nconj env t
        return (.store 1 mi my k, o, mkAppN (mkConst ``sim_store1)
          #[ctx.A, ctx.R, lo.A0, lo.O, mi.toExpr, my.toExpr, ← k.toExpr, env, ctx.heap, lo.j, y, o, hH, hj, hlt, hy, p])
    if e.getAppFn.isConstOf ctx.fn && args.size + 2 == ctx.params.size then
      return ← callGen (args ++ #[lo.j, lo.O])
    throwError "frontx: unsupported list result{indentExpr e}"
  if let some (acc, av) := ctx.acc? then
    let n0 := ctx.params.size - 1
    let call? := e.find? fun t => t.getAppFn.isConstOf ctx.fn && t.getAppNumArgs == n0
    match call? with
    | none =>
      let v ← mkAppM ``HAdd.hAdd #[acc, e]
      let r := mkApp (mkConst ``rN) v
      return ← retLeaf ctx env v r (mkApp2 (mkConst ``LOut.ret) ctx.A r)
    | some call =>
      -- `e = g + f x'` (checked by `omega` in the induction): continue with `acc + g`, where `g = e[f x' := 0]`
      let g0 := e.replace fun t => if t == call then some (toExpr (0 : Nat)) else none
      if (g0.find? (·.isConstOf ctx.fn)).isSome then throwError "frontx: more than one recursive call{indentExpr e}"
      let cargs := call.getAppArgs
      let mut as := #[]
      let mut idx := #[]
      for j in [0:n0] do
        let p := ctx.params[j]!
        if cargs[j]! == p || (← isProof p) then continue
        if (ctx.block? p).isSome then throwError "frontx: array argument changed in the call{indentExpr e}"
        let some v ← find? p | throwError "frontx: parameter without a variable{indentExpr p}"
        as := as.push (v, cargs[j]!)
        idx := idx.push j
      let newAcc ← if e == call then pure acc else mkAppM ``HAdd.hAdd #[acc, g0]
      let nas := as.size
      if e != call then as := as.push (av, newAcc)
      let full := cargs.push newAcc
      let repArgs (vals : Array Expr) : Array Expr := Id.run do
        let mut r := full
        for (j, k) in idx.zipIdx do
          r := r.set! j vals[k]!
        if e != call then r := r.set! n0 vals[nas]!
        return r
      let (_, a) ← mkTuple (← (ctx.data full).toList.mapM fun x => do return (x, ← inferType x))
      return ← callLeaf ctx nconj env as repArgs a (mkApp2 (mkConst ``LOut.call) ctx.A a)
  if e.getAppFn.isConstOf ctx.fn && args.size == ctx.params.size then
    return ← callGen args
  if ctx.res0.isSome then return ← retLeafM ctx env e
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

/-- accumulator mode: use the induction hypothesis at the new accumulator and reassociate (`omega`) -/
elab "frontx_ih_acc " h:ident : tactic => withMainContext do
  let hR := (← getLocalDeclFromUserName h.getId).toExpr
  let mut errs : MessageData := m!""
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless (← whnfR (← instantiateMVars d.type)).isForall do continue
    let s ← saveState
    try
      let (ms, _, _) ← forallMetaTelescope (← instantiateMVars d.type)
      unless ms.size ≥ 3 do throwError "arity"
      unless ← isDefEq (← inferType ms.back!) (← inferType hR) do throwError "no match"
      ms.back!.mvarId!.assign hR
      -- measure induction: the hypotheses `μ args' = m` (by `rfl`) and `m < n` (arithmetic)
      for m in ms.pop.reverse do
        if ← m.mvarId!.isAssigned then continue
        let mty ← instantiateMVars (← inferType m)
        unless ← isProp mty do continue
        if let some (_, x, _) := mty.eq? then
          unless ← isDefEq m (← mkEqRefl x) do throwError "measure equation"
        else
          let rest ← Tactic.run m.mvarId! (Tactic.withoutRecover (Tactic.evalTactic
            (← `(tactic| (subst_vars; dsimp only; omega)))))
          unless rest.isEmpty do throwError "measure does not decrease{indentExpr mty}"
      let pf ← instantiateMVars (mkAppN d.toExpr ms)
      if pf.hasMVar then throwError "unassigned"
      let g ← getMainGoal
      let (_, g) ← (← g.assert `ihx (← inferType pf) pf).intro1P
      replaceMainGoal [g]
      let ihxI := mkIdent `ihx
      evalTactic (← `(tactic| (obtain ⟨σ', hx⟩ := $ihxI:ident
                               exact ⟨σ', Tree.Runs.congr hx (by first | rfl | (congr 1; dsimp only; omega))⟩)))
      return
    catch e => s.restore; errs := errs ++ m!"\n{e.toMessageData}"
  throwError "frontx_ih_acc: no hypothesis applies{errs}"

/-- in `h : Sim R k σ (dite P o₁ o₂)`: case split on `P` (hypothesis `hc`), in both `h` and the goal; fails if the
outcome is not an `if` -/
elab "frontx_cases " h:ident : tactic => withMainContext do
  let hd ← getLocalDeclFromUserName h.getId
  let ty ← whnfR (← instantiateMVars hd.type)
  unless ty.isAppOfArity ``Sim 5 do throwError "frontx_cases: not a `Sim`"
  let a := ty.getAppArgs
  let o ← whnfR a[4]!
  unless o.isAppOfArity ``dite 5 do throwError "frontx_cases: not an `if`"
  let oa := o.getAppArgs
  let P := oa[1]!
  let (pos, neg) ← (← getMainGoal).byCases P `hc
  let hcI := mkIdent `hc
  let mut gs := []
  for (sub, lem, r1, r2) in [(pos, ``sim_pos, ``dif_pos, ``if_pos), (neg, ``sim_neg, ``dif_neg, ``if_neg)] do
    let g ← sub.mvarId.withContext do
      let pf := mkAppN (mkConst lem) #[a[0]!, a[1]!, a[2]!, a[3]!, P, oa[2]!, oa[3]!, oa[4]!, mkFVar sub.fvarId, hd.toExpr]
      let ty' ← whnfR (← inferType pf)
      let ty' := mkAppN ty'.getAppFn (ty'.getAppArgs.set! 4 (← whnfR ty'.getAppArgs[4]!))
      let (_, g) ← (← sub.mvarId.assert h.getId ty' pf).intro1P
      pure g
    let r1I := mkIdent r1; let r2I := mkIdent r2
    let hasCap := (← g.withContext do return (← getLCtx).findFromUserName? `hcap).isSome
    let rest ← Tactic.run g (do
      if hasCap then
        let capI := mkIdent `hcap
        evalTactic (← `(tactic| try simp only [$r1I:ident $hcI:ident, $r2I:ident $hcI:ident] at $capI:ident))
      evalTactic (← `(tactic| first | simp only [$r1I:ident $hcI:ident, $r2I:ident $hcI:ident] | skip)))
    gs := gs ++ rest
  replaceMainGoal gs

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

/-- fail unless `name` depends on the three standard axioms only -/
def checkAxioms (name : Name) : TermElabM Unit := do
  let axs ← Lean.collectAxioms name
  let bad := axs.filter fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
  unless bad.isEmpty do throwError "frontx: {name} depends on {bad}"

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

/-- the parameters with the first `ByteArray` moved to the front -/
def hoistBA (xs : Array Expr) : MetaM (Array Expr) := do
  for x in xs do
    if (← whnfR (← inferType x)).isConstOf ``ByteArray then return #[x] ++ xs.filter (· != x)
  return xs

/-- `frontx_compile` for a function whose body is `Id.run do <lets>; for i in [a:b] do <body>; <result>`:
the mutable locals and `i` become variables, the loop becomes the tree loop (`for_exec`). Adds `f.tree`, `f.lay`,
`f.slots`, `f.inits`, `f.Rep0` (the state holds the parameters), `f.Rep` (… and `i` and the locals), `f.step1`,
`f.exec`. -/
def compileLoop (fn : Name) (xs : Array Expr) (rty : Ty) (lhs forE : Expr) (post? : Option Expr)
    (inv? : Option Term) (lemmas : Array Name) (t0 : Nat) (eq? : Option Expr := none) (kind : String := "for loop")
    (pre? : Option Term := none) (resInfo : Array (Expr × Ty) := #[]) : TermElabM Unit := do
  -- a result with several components: the exit leaf also sets the extra result variables (`cvtM`, `for_execM`)
  let multi := resInfo.size > 1
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
  -- the first byte array is block 0 (length in variable 1) wherever it stands
  let xsO ← hoistBA xs
  for x in xsO do
    let xty ← inferType x
    if (← whnfR xty).isConstOf ``ByteArray then
      blocks := blocks ++ [(x, blocks.length, next + 1)]
      next := next + 2
    else if (← whnfR xty).isConstOf ``String then
      -- a `String` is the block of its UTF-8 bytes (`s.toUTF8`)
      blocks := blocks ++ [(mkApp (mkConst ``String.toUTF8) x, blocks.length, next + 1)]
      next := next + 2
    else
      -- a scalar, or a tuple / structure of scalars: one variable per component
      let some comps ← resultComps xty | throwError "frontx: unsupported parameter type{indentExpr xty}"
      if next < 4 then next := 4
      for (π, ty) in comps do
        let key := (mkApp π x).headBeta
        memo := (key, next) :: memo
        scal := scal.push (key, ty, next)
        next := next + 1
  if next < 4 then next := 4
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
  -- the extra result variables
  let mut resExtra : Array (Expr × Ty × Nat) := #[]
  for (π, t) in resInfo.extract 1 resInfo.size do
    resExtra := resExtra.push (π, t, next')
    next' := next' + 1
  if multi && ctyK.any (·.isNone) then throwError "frontx: `Option` locals with a result of several components"
  let preE? ← pre?.mapM fun pre => do
    let e ← elabTerm pre (some (← mkForallFVars xs (mkSort 0)))
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
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
    if let some preE := preE? then hyps := hyps.push (preE.beta xs)
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
        -- no bound for a `Nat` local: operations that need one get it from the invariant (`with`)
        hyps := hyps.push (← mkEq (mkApp env (toExpr v)) (ty.rep x))
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
  let postBV ← withLocalDeclD `s S fun s => do
    let v := (mkApp postLean s).headBeta
    mkLambdaFVars #[s] (rty.rep (if multi then (mkApp resInfo[0]!.1 v).headBeta else v))
  let bvL ← mkAppM ``List #[bv64]
  let vsE ← mkListLit (mkConst ``Nat) (resExtra.toList.map fun (_, _, v) => toExpr v)
  let wsE ← withLocalDeclD `s S fun s => do
    let v := (mkApp postLean s).headBeta
    mkLambdaFVars #[s] (← mkListLit bv64 (resExtra.toList.map fun (π, t, _) => t.rep (mkApp π v).headBeta))
  let _ := bvL
  -- `cvt post i` resp. `cvtM post vs ws i`
  let cvtE (i : Expr) : Expr := if multi then mkAppN (mkConst ``cvtM) #[S, postBV, vsE, wsE, i]
    else mkAppN (mkConst ``cvt) #[S, postBV, i]
  let exitOut (s : Expr) : MetaM Expr := if multi then do
      return mkApp3 (mkConst ``LOut.retm) A (mkApp postBV s) (← mkAppM ``List.zip #[vsE, mkApp wsE s])
    else pure (mkApp2 (mkConst ``LOut.ret) A (mkApp postBV s))
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
      let li : LoopInfo := { g := cvtE i, T, S, postBV, postLean, i, iv,
                             comps := cs.zip cvars }
      let ctx : Ctx := { fn, params := xs, blocks, A, R, heap := mkApp (mkConst ``BState.heap) σ, repN, rty,
                         loop := some li, lemmas, res0 := if multi then some resInfo[0]!.1 else none, resExtra }
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
              let frz := (cs.zip ctyK).filter (·.2.isNone) |>.map (·.1)
              let mut sN := sT
              let mut eqs := #[]
              for x in frz do
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
              let (t, o, p) ← if multi then retLeafM ctx env v
                else retLeaf ctx env v r (mkApp2 (mkConst ``LOut.ret) A r) fix
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
    let o₁ := Expr.lam `h Pi (mkApp (cvtE i) (mkApp2 F i s)) .default
    let o₂ := Expr.lam `h (mkNot Pi) (← exitOut s) .default
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
    let ctx : Ctx := { fn, params := xs, blocks, A, R, heap, repN, rty, lemmas }
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
      let pf ← if multi then do
          let hvs ← byTac (← mkEq (← mkAppM ``List.all #[vsE, ← withLocalDeclD `v (mkConst ``Nat) fun v => do
              mkLambdaFVars #[v] (← mkAppM ``and #[← mkDecide (← mkAppM ``LT.lt #[v,
                mkApp (mkConst ``Lay.M) (mkConst layN)]), ← mkAppM ``bne #[v, toExpr out]])]) (mkConst ``Bool.true))
            (← `(tactic| decide))
          pure (mkAppN (mkConst ``for_execM) #[S, mkConst layN, mkConst treeN, wfPf, roPf, R, F, postBV, vsE, wsE,
            a, b, init, mkConst initsN, toExpr out, hvs, mkAppN (mkConst stepN) xs, env0, heap, h0])
        else pure (mkAppN (mkConst ``for_exec) #[S, mkConst layN, mkConst treeN, wfPf, roPf, R, F, postBV, a, b, init,
          mkConst initsN, toExpr out, mkAppN (mkConst stepN) xs, env0, heap, h0])
      -- the function is the loop only up to a proved equation: transport the statement along it
      let pf ← match eq? with
        | none => pure pf
        | some eq => do
          let β ← inferType lhs
          let motive ← withLocalDeclD `v β fun v => do
            let progE := mkApp2 (mkConst ``initS) (mkConst initsN)
              (mkApp3 (mkConst ``prog) (mkConst layN) (mkConst treeN) (toExpr out))
            let c ← withLocalDeclD `σ' bstate fun σ' => do
              let c1 := mkApp3 (mkConst ``BExec) progE σ σ'
              let c2 ← mkEq (mkApp (mkApp (mkConst ``BState.env) σ') (toExpr out))
                (rty.rep (if multi then (mkApp resInfo[0]!.1 v).headBeta else v))
              let c3 ← mkEq (mkApp (mkConst ``BState.heap) σ') heap
              let c3 ← if multi then do
                  let ws := (← mkListLit bv64 (resExtra.toList.map fun (π, t, _) => t.rep (mkApp π v).headBeta))
                  pure (mkAnd c3 (mkApp2 (mkConst ``AllEnv) (mkApp (mkConst ``BState.env) σ') (← mkAppM ``List.zip #[vsE, ws])))
                else pure c3
              mkAppM ``Exists #[← mkLambdaFVars #[σ'] (mkAnd c1 (mkAnd c2 c3))]
            mkLambdaFVars #[v] c
          mkEqMPR (← mkCongrArg motive eq) pf
      return (← mkLambdaFVars hs pf, initsE, st'.nObl)
    addDef initsN (← mkAppM ``List #[pairTy]) initsE (compile := true)
    let prog := mkApp2 (mkConst ``initS) (mkConst initsN)
      (mkApp3 (mkConst ``prog) (mkConst layN) (mkConst treeN) (toExpr out))
    let concl ← withLocalDeclD `σ' bstate fun σ' => do
      let c1 := mkApp3 (mkConst ``BExec) prog σ σ'
      let c2 ← mkEq (mkApp (mkApp (mkConst ``BState.env) σ') (toExpr out))
        (rty.rep (if multi then (mkApp resInfo[0]!.1 lhs).headBeta else lhs))
      let c3 ← mkEq (mkApp (mkConst ``BState.heap) σ') heap
      let c3 ← if multi then do
          let ws := (← mkListLit bv64 (resExtra.toList.map fun (π, t, _) => t.rep (mkApp π lhs).headBeta))
          pure (mkAnd c3 (mkApp2 (mkConst ``AllEnv) (mkApp (mkConst ``BState.env) σ') (← mkAppM ``List.zip #[vsE, ws])))
        else pure c3
      mkAppM ``Exists #[← mkLambdaFVars #[σ'] (mkAnd c1 (mkAnd c2 c3))]
    let ty ← mkForallFVars (xs.push σ) (← mkArrow (mkAppN (mkConst rep0N) (xs.push σ)) concl)
    let pf ← withLocalDeclD `hR (mkConjE hyps) fun hR => do
      mkLambdaFVars (xs ++ #[σ, hR]) (mkAppN pfBody (← conjProjs n0 hR)).headBeta
    return (ty, pf, nObl)
  let execPf ← instantiateMVars execPf
  if execPf.hasSorry || execPf.hasMVar then throwError "frontx: exec proof incomplete"
  addDecl (.thmDecl { name := fn ++ `exec, levelParams := [], type := execTy, value := execPf })
  if multi then
    addDef (fn ++ `rvars) (← mkAppM ``List #[mkConst ``Nat]) vsE (compile := true)
  let t3 ← IO.monoMsNow
  logInfo m!"frontx: {fn} ({kind}): {nvars} variables ({M} user), {nvars - 8} slots, result in variable {out}, {st.nObl + nObl} obligations; translate + step proof {t1 - t0} ms, kernel check of step {t2 - t1} ms, init + exec theorem {t3 - t2} ms"


/-- `(position of k, b, h)` if the body is `match k with | 0 => b | k' + 1 => E` where every recursive call in `E`
is `f … k' …` with the other arguments unchanged; `h = fun k' acc => E[f … k' … := acc]` -/
def primRec? (fn : Name) (xs : Array Expr) (lhs body : Expr) : MetaM (Option (Nat × Expr × Expr)) := do
  let some ma ← matchMatcherApp? body | return none
  unless ma.discrs.size == 1 && ma.alts.size == 2 && ma.remaining.isEmpty do return none
  let some ki := xs.findIdx? (· == ma.discrs[0]!) | return none
  unless (← whnfR (← inferType xs[ki]!)).isConstOf ``Nat do return none
  let (iz, is) ←
    if ma.altNumParams[1]! == 1 && ma.altNumParams[0]! ≤ 1 then pure (0, 1)
    else if ma.altNumParams[0]! == 1 && ma.altNumParams[1]! ≤ 1 then pure (1, 0)
    else return none
  let zero := ma.alts[iz]!
  let zero := if zero.isLambda then zero.beta #[mkConst ``Unit.unit] else zero
  let β ← inferType lhs
  lambdaTelescope ma.alts[is]! fun ys E => do
    unless ys.size == 1 do return none
    let call := mkAppN lhs.getAppFn (xs.set! ki ys[0]!)
    withLocalDeclD `acc β fun acc => do
      let E' := E.replace fun e => if e == call then some acc else none
      if (E'.find? (·.isConstOf fn)).isSome || E' == acc || E' == E then return none
      return some (ki, zero, ← mkLambdaFVars #[ys[0]!, acc] E')

/-- `e` contains an `Array.foldl`, also inside the user definitions it uses (`fuel` levels) -/
partial def hasFold (e : Expr) (fuel : Nat := 3) : MetaM Bool := do
  if (e.find? (·.isConstOf ``Array.foldl)).isSome then return true
  if fuel == 0 then return false
  for c in e.getUsedConstants do
    if ← userConst c then
      if let some (.defnInfo d) := (← getEnv).find? c then
        if ← hasFold d.value (fuel - 1) then return true
  return false

/-- `(forIn …, post, proof of lhs = post (forIn …).run)` if `body` is `post (B.data.foldl g s)` for a byte-array
parameter `B`, after unfolding the user helpers that contain the fold (`bfoldl_forIn`) -/
def foldFor? (fn : Name) (xs : Array Expr) (lhs body eqPf : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  unless ← hasFold body do return none
  let e' ← Meta.transform body (pre := fun t => do
    if t.isAppOfArity ``Array.foldl 7 then return .done t
    if t.isLet then return .visit (t.letBody!.instantiate1 t.letValue!)
    if let some c := t.getAppFn.constName? then
      if c != fn && (← userConst c) then
        if let some (.defnInfo d) := (← getEnv).find? c then
          if ← hasFold d.value then
            if let some u ← unfoldDefinition? t then return .visit u.headBeta
    return .continue)
  let some foldT := e'.find? (·.isAppOfArity ``Array.foldl 7) | return none
  if ((e'.replace fun t => if t == foldT then some (mkConst ``True) else none).find?
      (·.isAppOfArity ``Array.foldl 7)).isSome then throwError "frontx: more than one `foldl`{indentExpr e'}"
  let fa := foldT.getAppArgs
  let arr := fa[4]!
  unless arr.isAppOfArity ``ByteArray.data 1 && xs.contains arr.appArg! do
    throwError "frontx: `foldl` over something else than the bytes of a parameter{indentExpr foldT}"
  let B := arr.appArg!
  let pf ← mkAppM ``bfoldl_forIn #[fa[2]!, fa[3]!, B]
  let some (_, l, r) := (← inferType pf).eq? | unreachable!
  unless ← isDefEq l foldT do throwError "frontx: `foldl` with a start or stop{indentExpr foldT}"
  let resTy ← inferType lhs
  let post ← withLocalDeclD `r fa[1]! fun rv => do
    mkLambdaFVars #[rv] (e'.replace fun t => if t == foldT then some rv else none)
  let eq ← mkEqTrans eqPf (← mkCongrArg post pf)
  let eq ← mkExpectedTypeHint eq (← mkEq lhs (mkApp post r))
  let _ := resTy
  return some (r.appArg!, post, eq)

def compileCmd (f : Ident) (inv? : Option Term) (lemmas : Array Name := #[]) (accMode := false)
    (pre? : Option Term := none) (from? : Option (Name × Term) := none) : TermElabM Unit := do
  let t0 ← IO.monoMsNow
  let fn ← realizeGlobalConstNoOverloadWithInfo f
  let info ← getConstInfo fn
  -- the equation `f xs = body`: the unfolding equation, or a proved one (`from`)
  let (eqnN, eqnTy) ← match from? with
    | some (e, _) => pure (e, (← getConstInfo e).type)
    | none =>
      let some eqn ← getUnfoldEqnFor? fn (nonRec := true) | throwError "frontx: no unfolding equation for {fn}"
      pure (eqn, (← getConstInfo eqn).type)
  let repN := fn ++ `Rep
  let treeN := fn ++ `tree
  let layN := fn ++ `lay
  let outN := fn ++ `out
  let stepN := fn ++ `step1
  let bstate := Lean.mkConst ``BState
  forallTelescope info.type fun xs resTy => do
    -- a `List UInt8` result: written to the output block (list mode)
    let resTyW ← whnfR resTy
    let listRes ← if resTyW.isAppOfArity ``List 1 then pure ((← whnfR resTyW.appArg!).isConstOf ``UInt8) else pure false
    let some resInfo ← (if listRes then pure (some #[(Lean.mkConst ``id, Ty.nat)]) else resultComps resTy)
      | throwError "frontx: unsupported result type{indentExpr resTy}"
    let rty := resInfo[0]!.2
    let multi := resInfo.size > 1
    let some (_, lhs, body) := (← instantiateForall eqnTy xs).eq? | throwError "frontx: bad equation"
    -- `… (B.data.foldl g s) …`: the `for` loop over the bytes of `B`, then the rest
    if !listRes then
      if let some (forE, post, eq) ← foldFor? fn xs lhs (stripPre body) (mkAppN (mkConst eqnN) xs) then
        return ← compileLoop fn xs rty lhs forE (some post) inv? lemmas t0 (eq? := some eq)
          (kind := "foldl as a for loop") (pre? := pre?) (resInfo := if multi then resInfo else #[])
    if let some (forE, post?) ← findFor fn (if listRes then Lean.mkConst ``True else stripPre body) then
      return ← compileLoop fn xs rty lhs forE post? inv? lemmas t0 (pre? := pre?)
        (resInfo := if multi then resInfo else #[])
    -- a test before the loop: `if c then v else loop` (or the other way round)
    let b0 := if listRes then Lean.mkConst ``True else stripPre body
    if b0.isAppOfArity ``ite 5 then
      let ba := b0.getAppArgs
      let pick ← (do
        if let some r ← findFor fn (stripPre ba[4]!) then pure (some (ba[1]!, ba[3]!, r))
        else if let some r ← findFor fn (stripPre ba[3]!) then pure (some (mkNot ba[1]!, ba[4]!, r))
        else pure none : TermElabM _)
      if let some (c, v, (forE, post?)) := pick then
        let fa := forE.getAppArgs
        let S := fa[4]!
        let range ← whnfR fa[5]!
        unless range.isAppOfArity ``Std.Legacy.Range.mk 4 do throwError "frontx: unsupported range{indentExpr range}"
        let a := range.getArg! 0
        let b := range.getArg! 1
        let inst ← synthInstance (mkApp (mkConst ``Decidable) c)
        let natE := Lean.mkConst ``Nat
        let b' := mkAppN (mkConst ``ite [levelOne]) #[natE, c, inst, a, b]
        let range' := mkAppN range.getAppFn #[a, b', range.getArg! 2, range.getArg! 3]
        let forE' := mkAppN forE.getAppFn (fa.set! 5 range')
        let postL ← match post? with
          | some p => pure p
          | none => withLocalDeclD `s S fun s => mkLambdaFVars #[s] s
        let post' ← withLocalDeclD `s S fun s => do
          mkLambdaFVars #[s] (mkAppN (mkConst ``ite [levelOne]) #[resTy, c, inst, v, (mkApp postL s).headBeta])
        let eq ← mkExpectedTypeHint (mkAppN (mkConst ``pretest_eq) #[S, resTy, c, inst, v, a, b, fa[6]!, fa[7]!, postL])
          (← mkEq lhs (mkApp post' (mkApp2 (mkConst ``Id.run [levelZero]) S forE')))
        return ← compileLoop fn xs rty lhs forE' (some post') inv? lemmas t0 (eq? := some eq)
          (kind := "test, then for loop") (pre? := pre?)
    -- primitive recursion on a `Nat` (recursive call not in tail position): the loop counting up
    if let some (ki, b, h) ← (if listRes then pure none else primRec? fn xs lhs body) then
      let k := xs[ki]!
      let β := resTy
      let nat := Lean.mkConst ``Nat
      let idM := Lean.mkConst ``Id [levelZero]
      let F ← withLocalDeclD `j nat fun j => withLocalDeclD `acc β fun acc => do
        let y := mkApp2 (mkConst ``ForInStep.yield [levelZero]) β (mkApp2 h j acc).headBeta
        mkLambdaFVars #[j, acc] (← mkAppOptM ``Pure.pure #[idM, none, none, y])
      let range := mkAppN (mkConst ``Std.Legacy.Range.mk) #[toExpr (0 : Nat), k, toExpr (1 : Nat), mkConst ``Nat.zero_lt_one]
      let forE ← mkAppOptM ``forIn #[idM, mkConst ``Std.Legacy.Range, nat, none, β, range, b, F]
      let fK ← mkLambdaFVars #[k] lhs
      let fI := mkIdent fn
      let hs ← withLocalDeclD `j nat fun j => do
        let ty ← mkEq (mkApp fK (← mkAppM ``HAdd.hAdd #[j, toExpr (1 : Nat)])).headBeta
          (mkApp2 h j (mkApp fK j).headBeta).headBeta
        mkLambdaFVars #[j] (← byTac ty (← `(tactic| first | rfl | simp only [$fI:ident] | (rw [$fI:ident]))))
      let eq := mkAppN (mkConst ``natRec_forIn) #[β, fK, h, hs, k]
      return ← compileLoop fn xs rty lhs forE none inv? lemmas t0 (eq? := some eq)
        (kind := "primitive recursion as a loop") (pre? := pre?)
    let xs0 := xs
    let restK (xs : Array Expr) (acc? : Option Expr) (lst? : Option (Expr × Expr) := none) : TermElabM Unit := do
      -- variables for the parameters
      let mut blocks : List (Expr × Nat × Nat) := []
      let mut next := 0
      let mut memo : List (Expr × Nat) := []
      let mut scal : Array (Expr × Ty × Nat) := #[]
      let mut dataIdx := #[]
      -- the first byte array is block 0 (length in variable 1) wherever it stands
      let ba0 := (← hoistBA xs)[0]?
      let ba0 ← match ba0 with
        | some b => if (← whnfR (← inferType b)).isConstOf ``ByteArray && xs[0]? != some b then pure (some b) else pure none
        | none => pure none
      if let some b := ba0 then
        blocks := [(b, 0, 1)]
        next := 2
      for (x, j) in xs.zipIdx do
        let xty ← inferType x
        if ← isProp xty then continue
        dataIdx := dataIdx.push j
        -- the output block: no variable (it is heap block 1)
        if lst?.any (·.2 == x) then continue
        if ba0 == some x then continue
        if (← whnfR xty).isConstOf ``ByteArray then
          blocks := blocks ++ [(x, blocks.length, next + 1)]
          next := next + 2
        else if (← whnfR xty).isConstOf ``String then
          blocks := blocks ++ [(mkApp (mkConst ``String.toUTF8) x, blocks.length, next + 1)]
          next := next + 2
        else
          -- a scalar, or a structure / tuple / `Option` of scalars: one variable per component
          let some comps ← resultComps xty | throwError "frontx: unsupported parameter type{indentExpr xty}"
          -- variables 2 and 3 stay free (work and output base in the `Implements1` calling convention)
          if next < 4 then next := 4
          for (π, ty) in comps do
            let key := (mkApp π x).headBeta
            memo := (key, next) :: memo
            scal := scal.push (key, ty, next)
            next := next + 1
      let xsD := dataIdx.map (xs[·]!)
      -- variables for the extra components of the result
      let mut resExtra : Array (Expr × Ty × Nat) := #[]
      if next < 4 then next := 4
      for (π, t) in resInfo.extract 1 resInfo.size do
        resExtra := resExtra.push (π, t, next)
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
            (blocks.map (fun (x, _, _) => mkApp (mkConst ``blk) x) ++ (lst?.map (·.2)).toList)
          hyps := hyps.push (← mkEq heap bl)
        for (x, _, len) in blocks do
          let sz := mkApp (mkConst ``ByteArray.size) x
          hyps := hyps.push (← mkEq (mkApp env (toExpr len)) (mkApp (mkConst ``rN) sz))
          hyps := hyps.push (← mkAppM ``LT.lt #[sz, two64])
        for (x, ty, v) in scal do
          hyps := hyps.push (← mkEq (mkApp env (toExpr v)) (ty.rep x))
          if ty == .nat && some x != acc? then hyps := hyps.push (← mkAppM ``LT.lt #[x, two64])
        for t? in [inv?, pre?] do
          if let some inv := t? then
            let invE ← elabTerm inv (some (← mkForallFVars xs0 (mkSort 0)))
            synthesizeSyntheticMVarsNoPostponing
            hyps := hyps.push (mkAppN (← instantiateMVars invE) xs0).headBeta
        -- list mode: the capacity of the output block, last
        if let some (j, O) := lst? then
          hyps := hyps.push (← mkAppM ``LT.lt #[← mkAppM ``List.length #[O], two64])
          hyps := hyps.push (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[j, ← mkAppM ``List.length #[lhs]],
            ← mkAppM ``List.length #[O]])
        if hyps.isEmpty then hyps := #[mkConst ``True]
        return hyps
      let mkConjE (hs : Array Expr) : Expr := hs.pop.foldr mkAnd hs.back!
      let nconj ← withLocalDeclD `σ bstate fun σ => do
        let hyps ← hypsOf σ
        addDef repN (← mkForallFVars (xsD.push σ) (mkSort 0)) (← mkLambdaFVars (xsD.push σ) (mkConjE hyps))
        return hyps.size
      -- argument tuples and the relation `R`
      let (A, _) ← mkTuple (← xsD.toList.mapM fun x => do return (x, ← inferType x))
      let R ← withLocalDeclD `a A fun a => withLocalDeclD `σ bstate fun σ => do
        let mut projs := #[]
        let mut cur := a
        for i in [0:xsD.size] do
          if i + 1 == xsD.size then projs := projs.push cur
          else
            projs := projs.push (← mkAppM ``Prod.fst #[cur])
            cur ← mkAppM ``Prod.snd #[cur]
        mkLambdaFVars #[a, σ] (mkAppN (mkConst repN) (projs.push σ))
      withLocalDeclD `σ bstate fun σ => do
        let hyps ← hypsOf σ
        let decls := hyps.mapIdx fun i h => (Name.mkSimple s!"h{i}", h)
        let ctx : Ctx := { fn, params := xs, blocks, A, R, heap := mkApp (mkConst ``BState.heap) σ, repN, rty, lemmas,
                           acc? := acc?.map fun acc => (acc, scal.back!.2.2), dataIdx := some dataIdx,
                           res0 := if multi then some resInfo[0]!.1 else none, resExtra }
        let ((mt, outE, proof), st) ← withLocalDeclsDND decls fun hs => do
          let ctx := match lst? with
            | none => ctx
            | some (j, O) =>
              { ctx with lo? := some { j, O, A0 := mkApp (mkConst ``blk) blocks.head!.1, jP := j, OP := O,
                                       hcap := hs.back!, eq := mkAppN (mkConst eqnN) xs0 } }
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
        let stepTy ← mkForallFVars (xs.push σ) (← mkArrow (mkAppN (mkConst repN) (xsD.push σ))
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
        if let some (j, O) := lst? then
          -- list mode: `runs` gives the result `j + (f xs).length` and the output block `wrO O j (f xs)`
          let some (_, μ0) := from? | throwError "frontx: a list result needs `from eq measure μ`"
          -- a named measure is unfolded (the decrease is checked by `omega`)
          let μ ← if !μ0.raw.isIdent then pure μ0 else do
            let e ← elabTerm μ0 none
            synthesizeSyntheticMVarsNoPostponing
            let e ← instantiateMVars e
            match e.getAppFn.constName? with
            | some c => if (← getConstInfo c).hasValue then
                Term.exprToSyntax (← deltaExpand e (· == c)) else pure μ0
            | none => pure μ0
          let some (_, _, jv) := scal.find? (·.1 == j) | throwError "frontx: no variable for the output index"
          let bv8L ← mkAppM ``List #[mkApp (mkConst ``BitVec) (toExpr (8 : Nat))]
          let A0 := mkApp (mkConst ``blk) blocks.head!.1
          let nP := xs0.size
          let as := (List.range xs.size).toArray.map fun i => mkIdent (Name.mkSimple s!"a{i}")
          let as0 := as.extract 0 nP
          let holes ← xs.mapM fun x => do if ← isProof x then `((by assumption)) else `(_)
          let us ← xs.mapM fun _ => `(_)
          let sI := mkIdent stepN
          let rI := mkIdent repN
          let eqI := mkIdent eqnN
          let runsTy ← mkForallFVars (xs.push σ) (← mkArrow (mkAppN (mkConst repN) (xsD.push σ))
            (← withLocalDeclD `σ' bstate fun σ' => do
              let r := mkApp (mkConst ``rN) (← mkAppM ``HAdd.hAdd #[j, ← mkAppM ``List.length #[lhs]])
              let H ← mkListLit bv8L [A0, ← mkAppM ``wrO #[O, j, lhs]]
              mkAppM ``Exists #[← mkLambdaFVars #[σ'] (mkAnd (mkApp4 (mkConst ``Tree.Runs) (mkConst treeN) σ r σ')
                (← mkEq (mkApp (mkConst ``BState.heap) σ') H))]))
          let hcapT ← (List.range (nconj - 1)).foldlM (fun (acc : Term) _ => `(And.right $acc)) (← `(hR))
          let hcapI := mkIdent `hcap
          addThm (fn ++ `runs) runsTy (← `(tactic|
            (intro $as*
             generalize hμ : ($μ $as0*) = n
             induction n using Nat.strongRecOn generalizing $as* with
             | _ n ih =>
               intro σ hR
               have $hcapI:ident := (by simp only [$rI:ident] at hR; exact $hcapT)
               rw [$eqI:ident $as0*] at $hcapI:ident ⊢
               have hs := $sI:ident $holes* σ hR
               (repeat' (frontx_cases hs)) <;>
               (try simp only [List.length_set, List.length_cons, List.length_nil, List.length_append] at $hcapI:ident) <;>
               first
               | (obtain ⟨σ₁, hs₁, hR₁⟩ := sim_call_elim _ hs
                  obtain ⟨σ', hx, hh⟩ := ih _ (by subst hμ; clear ih; first | (dsimp only; omega) | (simp_all only [↓reduceIte, Bool.false_eq_true, ite_true, ite_false]; omega) | (simp_all; omega)) $us* rfl _ hR₁
                  exact ⟨σ', .call hs₁ (hx.congr (by congr 1 <;> (try simp only [List.length_cons, List.length_append]) <;> omega)),
                    by rw [hh]; (try simp (disch := ((try simp only [List.length_set]); omega)) only [wrO_cons])⟩)
               | (obtain ⟨σ₁, hs₁, hh⟩ := sim_reth_elim _ hs
                  exact ⟨σ₁, Tree.Runs.congr (.ret hs₁) (by congr 1 <;> (try simp only [List.length_cons, List.length_nil]) <;> omega),
                    by rw [hh]; (try simp (disch := ((try simp only [List.length_set]); omega)) only [wrO_cons, wrO_nil])⟩))))
          let t3 ← IO.monoMsNow
          -- `Rep0`: `j = 0`, the capacity for the whole result
          let hyps0 := (hyps.filter fun h => !(h.find? (· == j)).isSome).push
            (← mkAppM ``LE.le #[← mkAppM ``List.length #[lhs], ← mkAppM ``List.length #[O]])
          let ps0 := xsD.filter (· != j)
          addDef (fn ++ `Rep0) (← mkForallFVars (ps0.push σ) (mkSort 0)) (← mkLambdaFVars (ps0.push σ) (mkConjE hyps0))
          let inits ← mkListLit pairTy [mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``BExp)
            (toExpr jv) (mkApp (mkConst ``BExp.const) (mkBV 0))]
          addDef (fn ++ `inits) (← mkAppM ``List #[pairTy]) inits (compile := true)
          let iI := mkIdent (fn ++ `inits)
          let tI := mkIdent treeN
          let lI := mkIdent layN
          let r0I := mkIdent (fn ++ `Rep0)
          let runsI := mkIdent (fn ++ `runs)
          let progE := mkApp2 (mkConst ``initS) (mkConst (fn ++ `inits))
            (mkApp3 (mkConst ``prog) (mkConst layN) (mkConst treeN) (toExpr out))
          let xsE := xs0 ++ #[O]
          let execTy ← mkForallFVars (xsE.push σ) (← mkArrow (mkAppN (mkConst (fn ++ `Rep0)) (ps0.push σ))
            (← withLocalDeclD `σ' bstate fun σ' => do
              let c1 := mkApp3 (mkConst ``BExec) progE σ σ'
              let c2 ← mkEq (mkApp (mkApp (mkConst ``BState.env) σ') (toExpr out))
                (mkApp (mkConst ``rN) (← mkAppM ``List.length #[lhs]))
              let c3 ← mkEq (mkApp (mkConst ``BState.heap) σ') (← mkListLit bv8L [A0, ← mkAppM ``wrO #[O, toExpr (0 : Nat), lhs]])
              mkAppM ``Exists #[← mkLambdaFVars #[σ'] (mkAnd c1 (mkAnd c2 c3))]))
          let outS := Syntax.mkNumLit (toString out)
          let aO := mkIdent `aO
          addThm (fn ++ `exec) execTy (← `(tactic|
            (intro $as0* $aO:ident σ hR
             have hr := $runsI:ident $as0* 0 $aO:ident ⟨seqSet σ.env $iI, σ.heap⟩
               (by simp only [$r0I:ident] at hR; simp [$rI:ident, $iI:ident, seqSet, BEnv.set, BExp.denote, rN, hR])
             rw [Nat.zero_add] at hr
             obtain ⟨σ', hx, hh⟩ := hr
             obtain ⟨τ', h1, h2, h3, _⟩ := prog_ok $lI (by simp [$tI:ident, $lI:ident, Tree.wf, BExp.vlt]) hx $outS _
               ⟨fun _ _ => rfl, rfl⟩
             exact ⟨τ', initS_exec _ _ h1, h2, h3.trans hh⟩)))
          checkAxioms (fn ++ `exec)
          let t4 ← IO.monoMsNow
          logInfo m!"frontx: {fn} (list result, output index in variable {jv}): {nvars} variables ({M} user), {nvars - 8} slots, length in variable {out}, {st.nObl} obligations; translate + step proof {t1 - t0} ms, kernel check of step {t2 - t1} ms, induction {t3 - t2} ms, exec theorem {t4 - t3} ms"
          return
        if let some acc := acc? then
          -- accumulator mode: `runs` is stated with `acc + f x`, `exec` starts with `acc := 0`
          let accv := scal.back!.2.2
          let as0 := (List.range xs0.size).toArray.map fun i => mkIdent (Name.mkSimple s!"a{i}")
          let holes0 ← xs0.mapM fun x => do if ← isProof x then `((by assumption)) else `(_)
          let fI := mkIdent fn
          let tI := mkIdent treeN
          let lI := mkIdent layN
          let sI := mkIdent stepN
          let rI := mkIdent repN
          let r0I := mkIdent (fn ++ `Rep0)
          let runsI := mkIdent (fn ++ `runs)
          let accLhs := mkApp (mkConst ``rN) (← mkAppM ``HAdd.hAdd #[acc, lhs])
          let runsTy ← mkForallFVars (xs.push σ) (← mkArrow (mkAppN (mkConst repN) (xsD.push σ))
            (← withLocalDeclD `σ' bstate fun σ' => do
              mkAppM ``Exists #[← mkLambdaFVars #[σ'] (mkApp4 (mkConst ``Tree.Runs) (mkConst treeN) σ accLhs σ')]))
          match from? with
          | none =>
            addThm (fn ++ `runs) runsTy (← `(tactic|
              (intro $as0*
               fun_induction $fI:ident $as0* <;> intro acc σ hR <;>
                (have hs := $sI:ident $holes0* acc σ hR
                 frontx_path hs
                 first
                 | (obtain ⟨σ₁, hs₁, hR₁⟩ := sim_call_elim _ hs
                    refine step_call σ₁ hs₁ ?_
                    frontx_ih_acc hR₁)
                 | (obtain ⟨σ₁, hs₁⟩ := sim_ret_elim _ hs
                    exact step_ret σ₁ hs₁)))))
          | some (eqN, μ) =>
            let eqI := mkIdent eqN
            addThm (fn ++ `runs) runsTy (← `(tactic|
              (intro $as0*
               generalize hμ : ($μ $as0*) = n
               induction n using Nat.strongRecOn generalizing $as0* with
               | _ n ih =>
                 intro acc σ hR
                 rw [$eqI:ident $as0*]
                 have hs := $sI:ident $holes0* acc σ hR
                 (repeat' (frontx_cases hs)) <;>
                 first
                 | (obtain ⟨σ₁, hs₁, hR₁⟩ := sim_call_elim _ hs
                    refine step_call σ₁ hs₁ ?_
                    frontx_ih_acc hR₁)
                 | (obtain ⟨σ₁, hs₁⟩ := sim_ret_elim _ hs
                    exact step_ret σ₁ hs₁))))
          let t3 ← IO.monoMsNow
          -- `Rep0`: the parameters only
          let hyps0 := hyps.filter fun h => !(h.find? (· == acc)).isSome
          addDef (fn ++ `Rep0) (← mkForallFVars (xsD.pop.push σ) (mkSort 0)) (← mkLambdaFVars (xsD.pop.push σ) (mkConjE hyps0))
          let inits ← mkListLit pairTy [mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``BExp)
            (toExpr accv) (mkApp (mkConst ``BExp.const) (mkBV 0))]
          addDef (fn ++ `inits) (← mkAppM ``List #[pairTy]) inits (compile := true)
          let iI := mkIdent (fn ++ `inits)
          let progE := mkApp2 (mkConst ``initS) (mkConst (fn ++ `inits))
            (mkApp3 (mkConst ``prog) (mkConst layN) (mkConst treeN) (toExpr out))
          let execTy ← mkForallFVars (xs0.push σ) (← mkArrow (mkAppN (mkConst (fn ++ `Rep0)) (xsD.pop.push σ))
            (← withLocalDeclD `σ' bstate fun σ' => do
              let c1 := mkApp3 (mkConst ``BExec) progE σ σ'
              let c2 ← mkEq (mkApp (mkApp (mkConst ``BState.env) σ') (toExpr out)) (rty.rep lhs)
              let c3 ← mkEq (mkApp (mkConst ``BState.heap) σ') (mkApp (mkConst ``BState.heap) σ)
              mkAppM ``Exists #[← mkLambdaFVars #[σ'] (mkAnd c1 (mkAnd c2 c3))]))
          let outS := Syntax.mkNumLit (toString out)
          addThm (fn ++ `exec) execTy (← `(tactic|
            (intro $as0* σ hR
             have hr := $runsI:ident $as0* 0 ⟨seqSet σ.env $iI, σ.heap⟩
               (by simp only [$r0I:ident] at hR; simp [$rI:ident, $iI:ident, seqSet, BEnv.set, BExp.denote, rN, hR])
             rw [Nat.zero_add] at hr
             obtain ⟨σ', h1, h2, h3⟩ := prog_ok_ro $lI (by simp [$tI:ident, $lI:ident, Tree.wf, BExp.vlt]) (by rfl) hr $outS
             exact ⟨σ', initS_exec _ _ h1, h2, h3⟩)))
          let t4 ← IO.monoMsNow
          logInfo m!"frontx: {fn} (accumulator introduced): {nvars} variables ({M} user), {nvars - 8} slots, result in variable {out}, {st.nObl} obligations; translate + step proof {t1 - t0} ms, kernel check of step {t2 - t1} ms, induction {t3 - t2} ms, exec theorem {t4 - t3} ms"
          return
        if multi then
          -- several result components: `runs`/`exec` also give the extra result variables
          addDef (fn ++ `rvars) (← mkAppM ``List #[mkConst ``Nat])
            (← mkListLit (mkConst ``Nat) (resExtra.toList.map fun (_, _, v) => toExpr v)) (compile := true)
          let as := (List.range xs.size).toArray.map fun i => mkIdent (Name.mkSimple s!"a{i}")
          let holes ← xs.mapM fun x => do if ← isProof x then `((by assumption)) else `(_)
          let fI := mkIdent fn
          let tI := mkIdent treeN
          let lI := mkIdent layN
          let sI := mkIdent stepN
          let runsI := mkIdent (fn ++ `runs)
          let r0 := rty.rep (mkApp resInfo[0]!.1 lhs).headBeta
          let rsL ← mkRs (resExtra.map fun (π, t, v) => (v, t.rep (mkApp π lhs).headBeta))
          let ind ← if (body.find? (·.isConstOf fn)).isSome then `(tactic| fun_induction $fI:ident $as*)
            else `(tactic| first | fun_cases $fI:ident $as* | unfold $fI:ident)
          let runsTy ← mkForallFVars (xs.push σ) (← mkArrow (mkAppN (mkConst repN) (xsD.push σ))
            (← withLocalDeclD `σ' bstate fun σ' => do
              mkAppM ``Exists #[← mkLambdaFVars #[σ'] (mkAnd (mkApp4 (mkConst ``Tree.Runs) (mkConst treeN) σ r0 σ')
                (mkApp2 (mkConst ``AllEnv) (mkApp (mkConst ``BState.env) σ') rsL))]))
          match from? with
          | none =>
            addThm (fn ++ `runs) runsTy (← `(tactic|
              (intro $as*
               $ind:tactic <;> intro σ hR <;>
                (have hs := $sI:ident $holes* σ hR
                 frontx_path hs
                 first
                 | (obtain ⟨σ₁, hs₁, hR₁⟩ := sim_call_elim _ hs
                    refine step_callQ σ₁ hs₁ ?_
                    frontx_ih
                    exact hR₁)
                 | (obtain ⟨σ₁, hs₁, hq⟩ := sim_retm_elim _ hs
                    exact step_retQ σ₁ hs₁ hq)))))
          | some (eqN, μ) =>
            let eqI := mkIdent eqN
            let us ← xs.mapM fun _ => `(_)
            addThm (fn ++ `runs) runsTy (← `(tactic|
              (intro $as*
               generalize hμ : ($μ $as*) = n
               induction n using Nat.strongRecOn generalizing $as* with
               | _ n ih =>
                 intro σ hR
                 rw [$eqI:ident $as*]
                 have hs := $sI:ident $holes* σ hR
                 (repeat' (frontx_cases hs)) <;>
                 first
                 | (obtain ⟨σ₁, hs₁, hR₁⟩ := sim_call_elim _ hs
                    refine step_callQ σ₁ hs₁ ?_
                    exact ih _ (by subst hμ; dsimp only; omega) $us* rfl _ hR₁)
                 | (obtain ⟨σ₁, hs₁, hq⟩ := sim_retm_elim _ hs
                    exact step_retQ σ₁ hs₁ hq))))
          let t3 ← IO.monoMsNow
          let progE := mkApp3 (mkConst ``prog) (mkConst layN) (mkConst treeN) (toExpr out)
          let execTy ← mkForallFVars (xs.push σ) (← mkArrow (mkAppN (mkConst repN) (xsD.push σ))
            (← withLocalDeclD `σ' bstate fun σ' => do
              let env' := mkApp (mkConst ``BState.env) σ'
              let c1 := mkApp3 (mkConst ``BExec) progE σ σ'
              let c2 ← mkEq (mkApp env' (toExpr out)) r0
              let c3 ← mkEq (mkApp (mkConst ``BState.heap) σ') (mkApp (mkConst ``BState.heap) σ)
              mkAppM ``Exists #[← mkLambdaFVars #[σ'] (mkAnd c1 (mkAnd c2 (mkAnd c3 (mkApp2 (mkConst ``AllEnv) env' rsL))))]))
          let outS := Syntax.mkNumLit (toString out)
          addThm (fn ++ `exec) execTy (← `(tactic|
            (intro $as* σ hR
             exact prog_okQ $lI (by simp [$tI:ident, $lI:ident, Tree.wf, BExp.vlt]) (by rfl) ($runsI:ident $as* σ hR) $outS
               (by simp [$lI:ident]))))
          let t4 ← IO.monoMsNow
          logInfo m!"frontx: {fn} ({resInfo.size} result components): {nvars} variables ({M} user), {nvars - 8} slots, results in variables {out}, {resExtra.map (·.2.2)}, {st.nObl} obligations; translate + step proof {t1 - t0} ms, kernel check of step {t2 - t1} ms, induction {t3 - t2} ms, exec theorem {t4 - t3} ms"
          return
        -- f.runs
        let mkStmt (concl : Expr) : MetaM Expr := do
          mkForallFVars (xs.push σ) (← mkArrow (mkAppN (mkConst repN) (xsD.push σ)) concl)
        let runsTy ← mkStmt (← withLocalDeclD `σ' bstate fun σ' => do
          mkAppM ``Exists #[← mkLambdaFVars #[σ'] (mkApp4 (mkConst ``Tree.Runs) (mkConst treeN) σ (rty.rep lhs) σ')])
        let as := (List.range xs.size).toArray.map fun i => mkIdent (Name.mkSimple s!"a{i}")
        let holes ← xs.mapM fun x => do if ← isProof x then `((by assumption)) else `(_)
        let σi := mkIdent `σ
        let fI := mkIdent fn
        let tI := mkIdent treeN
        let lI := mkIdent layN
        let sI := mkIdent stepN
        -- a function that does not call itself: case analysis instead of induction
        let ind ← if (body.find? (·.isConstOf fn)).isSome then `(tactic| fun_induction $fI:ident $as*)
          else `(tactic| first | fun_cases $fI:ident $as* | unfold $fI:ident)
        match from? with
        | none =>
          addThm (fn ++ `runs) runsTy (← `(tactic|
            (intro $as*
             $ind:tactic <;> intro $σi:ident hR <;>
              (have hs := $sI:ident $holes* $σi hR
               frontx_path hs
               first
               | (obtain ⟨σ₁, hs₁, hR₁⟩ := sim_call_elim _ hs
                  refine step_call σ₁ hs₁ ?_
                  frontx_ih
                  exact hR₁)
               | (obtain ⟨σ₁, hs₁⟩ := sim_ret_elim _ hs
                  exact step_ret σ₁ hs₁)))))
        | some (eqN, μ) =>
          -- a proved equation: well-founded induction on the measure `μ`, case analysis along the outcome
          let eqI := mkIdent eqN
          let us ← xs.mapM fun _ => `(_)
          addThm (fn ++ `runs) runsTy (← `(tactic|
            (intro $as*
             generalize hμ : ($μ $as*) = n
             induction n using Nat.strongRecOn generalizing $as* with
             | _ n ih =>
               intro $σi:ident hR
               rw [$eqI:ident $as*]
               have hs := $sI:ident $holes* $σi hR
               (repeat' (frontx_cases hs)) <;>
               first
               | (obtain ⟨σ₁, hs₁, hR₁⟩ := sim_call_elim _ hs
                  refine step_call σ₁ hs₁ ?_
                  exact ih _ (by subst hμ; dsimp only; omega) $us* rfl _ hR₁)
               | (obtain ⟨σ₁, hs₁⟩ := sim_ret_elim _ hs
                  exact step_ret σ₁ hs₁))))
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
    if listRes then
      withLocalDeclD `j (Lean.mkConst ``Nat) fun j => do
        let bv8L ← mkAppM ``List #[mkApp (mkConst ``BitVec) (toExpr (8 : Nat))]
        withLocalDeclD `O bv8L fun O => restK (xs.push j |>.push O) none (some (j, O))
    else if accMode then
      unless rty == .nat do throwError "frontx: recursive call not in tail position (accumulator mode needs a `Nat` result)"
      withLocalDeclD `acc (Lean.mkConst ``Nat) fun acc => restK (xs.push acc) (some acc)
    else restK xs none

/-- `frontx_compile f` or `frontx_compile f with inv` (`inv : params → Prop`, an extra precondition that the
recursive calls must preserve; needed for `Nat` arguments whose bounds are not implied by the tests) -/
syntax "frontx_compile " ident (" from " ident " measure " term)? (" requires " term)? (" with " term)?
  (" using " ident,+)? : command
elab_rules : command
  | `(frontx_compile $f:ident from $e:ident measure $μ:term $[requires $pre?]? $[with $inv?]? $[using $ls?,*]?) =>
    liftTermElabM do
    let lemmas ← match ls? with
      | some ls => ls.getElems.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
      | none => pure #[]
    let from? := some (← realizeGlobalConstNoOverloadWithInfo e, μ)
    let s ← saveState
    try compileCmd f inv? lemmas (pre? := pre?) (from? := from?)
    catch ex =>
      if ((← ex.toMessageData.toString).splitOn "not in tail position").length > 1 then
        s.restore
        compileCmd f inv? lemmas (accMode := true) (pre? := pre?) (from? := from?)
      else throw ex
    checkAxioms ((← realizeGlobalConstNoOverloadWithInfo f) ++ `exec)
  | `(frontx_compile $f:ident $[requires $pre?]? $[with $inv?]? $[using $ls?,*]?) => liftTermElabM do
    let lemmas ← match ls? with
      | some ls => ls.getElems.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
      | none => pure #[]
    let s ← saveState
    try compileCmd f inv? lemmas (pre? := pre?)
    catch e =>
      -- a recursive call that is not a tail call (and not primitive recursion): try an accumulator
      if ((← e.toMessageData.toString).splitOn "not in tail position").length > 1 then
        s.restore
        compileCmd f inv? lemmas (accMode := true) (pre? := pre?)
      else throw e
    checkAxioms ((← realizeGlobalConstNoOverloadWithInfo f) ++ `exec)

/-! ## List parameters as views of the input

`frontx_view f` for `f … (xs : List UInt8 | List Nat) … : T` defined by `match xs with | [] => a | x :: t => b`
(type parameters are instantiated with `UInt8`): adds

  `f.view B i … := f … (view B i) …`   and
  `f.view_eq : f.view B i … = if h : i < B.size then b[x := B[i], t := view B (i + 1)] else a`

with the recursive calls on `t` folded to `f.view B (i + 1) …`; then
`frontx_compile f.view from f.view_eq measure fun B i … => B.size - i`. -/

partial def viewTele {α : Type} (ty : Expr) (args others : Array Expr) (pos : Array Nat)
    (lst? : Option (Expr × Expr × Name × Nat))
    (k : Array Expr → Array Expr → Array Nat → Option (Expr × Expr × Name × Nat) → Expr → TermElabM α) :
    TermElabM α := do
  let ty ← whnf ty
  match ty with
  | .forallE n d b info =>
    let d' ← whnfR d
    if d'.isSort then
      viewTele (b.instantiate1 (mkConst ``UInt8)) (args.push (mkConst ``UInt8)) others pos lst? k
    else if info.isInstImplicit then
      let inst ← synthInstance d
      viewTele (b.instantiate1 inst) (args.push inst) others pos lst? k
    else if lst?.isSome && d'.isAppOfArity ``List 1 then
      -- a further list parameter: another view of the same block, with its own index
      let some (B, _, vw, _) := lst? | unreachable!
      withLocalDeclD `k (mkConst ``Nat) fun k2 => do
        let v := mkApp2 (mkConst vw) B k2
        viewTele (b.instantiate1 v) (args.push v) (others.push k2) (pos.push args.size) lst? k
    else if lst?.isNone && d'.isAppOfArity ``List 1 then
      let el ← whnfR d'.appArg!
      let vw ← if el.isConstOf ``UInt8 then pure ``view else if el.isConstOf ``Nat then pure ``viewN
        else throwError "frontx_view: unsupported element type{indentExpr el}"
      withLocalDeclD `B (mkConst ``ByteArray) fun B => withLocalDeclD `i (mkConst ``Nat) fun i => do
        let v := mkApp2 (mkConst vw) B i
        viewTele (b.instantiate1 v) (args.push v) others pos (some (B, i, vw, args.size)) k
    else
      withLocalDecl n info d fun x =>
        viewTele (b.instantiate1 x) (args.push x) (others.push x) (pos.push args.size) lst? k
  | _ => k args others pos lst? ty

/-! `frontx_spec g` for `def g ys := f a₁ … aₙ` (each `aⱼ` one of the `ys`, or a fixed term: a type, an instance,
a function): `g.eq : g ys = body of f`, the recursive calls with the same fixed arguments folded to `g`
(specialisation of polymorphic and higher-order definitions). -/
elab "frontx_spec " g:ident : command => liftTermElabM do
  let gN ← realizeGlobalConstNoOverloadWithInfo g
  let info ← getConstInfoDefn gN
  lambdaTelescope info.value fun ys body => do
    let body := body.headBeta
    let .const fN lvls := body.getAppFn | throwError "frontx_spec: the body must be an application of a definition"
    let args := body.getAppArgs
    let some eqn ← getUnfoldEqnFor? fN (nonRec := true) | throwError "frontx_spec: no unfolding equation for {fN}"
    let eqnInfo ← getConstInfo eqn
    let eqTy := eqnInfo.type.instantiateLevelParams eqnInfo.levelParams lvls
    let some (_, _, rhs) := (← instantiateForall eqTy args).eq? | throwError "frontx_spec: bad equation"
    let mut posOf : Array Nat := #[]
    for y in ys do
      let some j := args.findIdx? (· == y) | throwError "frontx_spec: parameter {y} is not passed on directly"
      posOf := posOf.push j
    let rhs' := rhs.replace fun e =>
      if e.isAppOfArity fN args.size then
        let ea := e.getAppArgs
        if (List.range args.size).all fun j => posOf.contains j || ea[j]! == args[j]! then
          some (mkAppN (mkConst gN) (posOf.map (ea[·]!)))
        else none
      else none
    let rhs' ← Core.betaReduce rhs'
    if (rhs'.find? (·.isConstOf fN)).isSome then
      throwError "frontx_spec: a recursive call changes a fixed argument{indentExpr rhs'}"
    let ty ← mkForallFVars ys (← mkEq (mkAppN (mkConst gN) ys) rhs')
    let pf ← mkLambdaFVars ys (mkAppN (mkConst eqn lvls) args)
    addDecl (.thmDecl { name := gN ++ `eq, levelParams := [], type := ty, value := pf })
    let eqName := gN ++ `eq
    logInfo m!"frontx: {eqName} : {ty}"

/-! General `match` shapes (several discriminants, nested list patterns such as `[y]`, `y₁ :: y₂ :: ys`): the
body of `f … (view B i) …` is normalised into a decision tree on `i < B.size`, `n = 0`, … (`vnorm`: a stuck
`match` is split on a discriminant and reduced), `B[k] :: view B (k + 1)` is folded back to `view B k`, and the
equation is proved by following the tests (`veqGo`). -/

/-- `view B k` / `viewN B k` occurrences -/
def isView (vw : Name) (B e : Expr) : Option Expr :=
  if e.isAppOfArity vw 2 && e.getArg! 0 == B then some (e.getArg! 1) else none

/-- split a stuck `match` and reduce: the decision tree of the body on the known parts of the list -/
partial def vnorm (vw : Name) (B : Expr) (e : Expr) (fuel : Nat := 32) : TermElabM Expr := do
  let e := e.headBeta
  if fuel == 0 then throwError "frontx_view: the match does not reduce{indentExpr e}"
  let some ma ← matchMatcherApp? e | return e
  match ← reduceMatcher? e with
  | .reduced e' => return ← vnorm vw B e' (fuel - 1)
  | _ => pure ()
  let ty ← inferType e
  let splitView (top : Bool) : TermElabM (Option Expr) := do
   for d in ma.discrs do
    let some v := (if top then (if (isView vw B d).isSome then some d else none) else d.find? (isView vw B · |>.isSome)) | continue
    let k := v.getArg! 1
    let P ← mkAppM ``LT.lt #[k, mkApp (mkConst ``ByteArray.size) B]
    let inst ← synthInstance (mkApp (mkConst ``Decidable) P)
    let k1 ← mkAppM ``HAdd.hAdd #[k, toExpr (1 : Nat)]
    let t ← withLocalDeclD `h P fun h => do
      let x ← Term.elabTerm (← `($(← Term.exprToSyntax B)[$(← Term.exprToSyntax k)]'$(← Term.exprToSyntax h))) none
      synthesizeSyntheticMVarsNoPostponing
      let x ← instantiateMVars x
      let x := if vw == ``viewN then mkApp (mkConst ``UInt8.toNat) x else x
      let c ← mkAppM ``List.cons #[x, mkApp2 (mkConst vw) B k1]
      mkLambdaFVars #[h] (← vnorm vw B (e.replace fun y => if y == v then some c else none) (fuel - 1))
    let f ← withLocalDeclD `h (mkNot P) fun h => do
      let nil ← mkAppOptM ``List.nil #[(← whnfR (← inferType v)).appArg!]
      mkLambdaFVars #[h] (← vnorm vw B (e.replace fun y => if y == v then some nil else none) (fuel - 1))
    return some (mkAppN (mkConst ``dite [← getLevel ty]) #[ty, P, inst, t, f])
   return none
  -- a view inside a discriminant
  if let some r ← splitView true then return r
  -- a `Nat` discriminant that is not a constructor
  for d in ma.discrs do
    let dty ← whnfR (← inferType d)
    if dty.isConstOf ``Nat then
      let d' ← whnfR d
      if d'.isAppOfArity ``Nat.succ 1 || d'.rawNatLit?.isSome || d'.nat?.isSome || d'.isConstOf ``Nat.zero then continue
      let P ← mkEq d (toExpr (0 : Nat))
      let inst ← synthInstance (mkApp (mkConst ``Decidable) P)
      let d1 := mkApp (mkConst ``Nat.succ) (← mkAppM ``HSub.hSub #[d, toExpr (1 : Nat)])
      let t ← withLocalDeclD `h P fun h => do
        mkLambdaFVars #[h] (← vnorm vw B (e.replace fun x => if x == d then some (toExpr (0 : Nat)) else none) (fuel - 1))
      let f ← withLocalDeclD `h (mkNot P) fun h => do
        mkLambdaFVars #[h] (← vnorm vw B (e.replace fun x => if x == d then some d1 else none) (fuel - 1))
      return mkAppN (mkConst ``dite [← getLevel ty]) #[ty, P, inst, t, f]
  if let some r ← splitView false then return r
  throwError "frontx_view: cannot reduce{indentExpr e}"

/-- fold `B[k] :: view B (k + 1)` back to `view B k` -/
def vfold (vw : Name) (B : Expr) (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun t => do
    if t.isAppOfArity ``List.cons 3 then
      if let some k1 := isView vw B (t.getArg! 2) then
        let hd := t.getArg! 1
        let hd := if vw == ``viewN && hd.isAppOfArity ``UInt8.toNat 1 then hd.appArg! else hd
        if let some (B', k) := read? hd then
          if B' == B then
            if ← isDefEq k1 (← mkAppM ``HAdd.hAdd #[k, toExpr (1 : Nat)]) then
              return .done (mkApp2 (mkConst vw) B k)
    return .continue)


/-- prove `f … (view B i) … = <decision tree>`: follow the tests of the right-hand side -/
partial def veqGo (f : Name) (vw : Name) (n : Nat := 0) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (_, _, rhs) := ty.eq? | throwError "frontx_view: not an equation"
  let fI := mkIdent f
  let vI := mkIdent (if vw == ``viewN then ``viewN_eq else ``view_eq)
  if rhs.isAppOfArity ``dite 5 then
    let c := rhs.getArg! 1
    let hc := mkIdent (Name.mkSimple s!"hc{n}")
    let cS ← Term.exprToSyntax c
    evalTactic (← `(tactic| by_cases $hc:ident : $cS))
    let gs ← getGoals
    let mut acc := []
    for (g', pos) in gs.zip [true, false] do
      setGoals [g']
      if pos then evalTactic (← `(tactic| rw [dif_pos $hc:ident]))
      else evalTactic (← `(tactic| rw [dif_neg $hc:ident]))
      if c.isAppOfArity ``LT.lt 4 then
        let kS ← Term.exprToSyntax (c.getArg! 2)
        let BS ← Term.exprToSyntax (c.getArg! 3).appArg!
        if pos then evalTactic (← `(tactic| try rw [$vI:ident $BS $kS, dif_pos $hc:ident]))
        else evalTactic (← `(tactic| try rw [$vI:ident $BS $kS, dif_neg $hc:ident]))
      else if c.isAppOfArity ``Eq 3 then
        if pos then evalTactic (← `(tactic| subst $hc:ident))
        else
          let m := mkIdent (Name.mkSimple s!"m{n}")
          evalTactic (← `(tactic| (obtain ⟨$m:ident, hm⟩ := Nat.exists_eq_succ_of_ne_zero $hc:ident; subst hm)))
      veqGo f vw (n + 1)
      acc := acc ++ (← getGoals)
    setGoals acc
  else
    let gl ← getMainGoal
    try evalTactic (← `(tactic| first | rfl | (simp only [$fI:ident]; done) | (rw [$fI:ident]; done) | (simp only [$fI:ident, Nat.add_sub_cancel]; done)))
    catch e => throwError "leaf {gl}: {e.toMessageData}"


syntax "frontx_view " ident (" from " ident)? : command
elab_rules : command
  | `(frontx_view $f:ident $[from $e?]?) => liftTermElabM do
  let fn ← realizeGlobalConstNoOverloadWithInfo f
  let info ← getConstInfo fn
  let eqn ← match e? with
    | some e => realizeGlobalConstNoOverloadWithInfo e
    | none =>
      let some eqn ← getUnfoldEqnFor? fn (nonRec := true) | throwError "frontx_view: no unfolding equation for {fn}"
      pure eqn
  let eqnInfo ← getConstInfo eqn
  let lvls := info.levelParams.map fun _ => levelZero
  let gN := fn ++ `view
  let fty := info.type.instantiateLevelParams info.levelParams lvls
  let eqnTy := eqnInfo.type.instantiateLevelParams eqnInfo.levelParams (eqnInfo.levelParams.map fun _ => levelZero)
  let vwEq ← viewTele fty #[] #[] #[] none fun args others pos lst? resTy => do
    let some (B, i, vw, lpos) := lst? | throwError "frontx_view: no list parameter"
    let ps := #[B, i] ++ others
    let fC := Lean.mkConst fn lvls
    let gTy ← mkForallFVars ps resTy
    let gVal ← mkLambdaFVars ps (mkAppN fC args)
    addAndCompile (.defnDecl (mkDefinitionValEx gN [] gTy gVal (.regular 1) .safe [gN]))
    enableRealizationsForConst gN
    let some (_, _, rhs) := (← instantiateForall eqnTy args).eq? | throwError "frontx_view: bad equation"
    let some ma ← matchMatcherApp? rhs | throwError "frontx_view: the body is not a `match`{indentExpr rhs}"
    let simple := pos.all (fun p => (isView vw B args[p]!).isNone) &&
      ma.discrs.size == 1 && ma.discrs[0]! == args[lpos]! && ma.alts.size == 2 && ma.remaining.isEmpty &&
      (ma.altNumParams[1]! == 2 || ma.altNumParams[0]! == 2)
    unless simple do
      -- the general path: decision tree, recursive calls folded
      let r ← vfold vw B (← vnorm vw B rhs)
      let isL (p : Nat) : Bool := (isView vw B args[p]!).isSome
      let r := r.replace fun e =>
        if e.isAppOfArity fn args.size then
          match isView vw B (e.getAppArgs[lpos]!) with
          | some k =>
            let rest := pos.map fun p =>
              if isL p then (isView vw B (e.getAppArgs[p]!)).getD (e.getAppArgs[p]!) else e.getAppArgs[p]!
            if (pos.zip rest).any fun (p, a) => isL p && a == e.getAppArgs[p]! && (isView vw B a).isNone then none
            else some (mkAppN (mkConst gN) (#[B, k] ++ rest))
          | none => none
        else none
      if (r.find? (·.isConstOf fn)).isSome then
        throwError "frontx_view: a recursive call that is not on a view of the list{indentExpr r}"
      let ty ← mkForallFVars ps (← mkEq (mkAppN (mkConst gN) ps) r)
      return (ty, vw, true)
    let (inil, icons) ← if ma.altNumParams[1]! == 2 then pure (0, 1) else pure (1, 0)
    let nilB := ma.alts[inil]!
    let nilB := if nilB.isLambda then nilB.beta #[mkConst ``Unit.unit] else nilB
    let nat := Lean.mkConst ``Nat
    let i1 ← mkAppM ``HAdd.hAdd #[i, toExpr (1 : Nat)]
    let tl := mkApp2 (mkConst vw) B i1
    let c ← mkAppM ``LT.lt #[i, mkApp (mkConst ``ByteArray.size) B]
    let inst ← synthInstance (mkApp (mkConst ``Decidable) c)
    let thenB ← withLocalDeclD `h c fun h => do
      let x ← Term.elabTerm (← `($(← Term.exprToSyntax B)[$(← Term.exprToSyntax i)]'$(← Term.exprToSyntax h))) none
      synthesizeSyntheticMVarsNoPostponing
      let x ← instantiateMVars x
      let x := if vw == ``viewN then mkApp (mkConst ``UInt8.toNat) x else x
      let body := (ma.alts[icons]!.beta #[x, tl])
      let body := body.replace fun e =>
        if e.isAppOfArity fn args.size && e.getAppArgs[lpos]! == tl then
          some (mkAppN (mkConst gN) (#[B, i1] ++ pos.map (e.getAppArgs[·]!)))
        else none
      if (body.find? (·.isConstOf fn)).isSome then
        throwError "frontx_view: a recursive call that is not on the tail of the list{indentExpr body}"
      mkLambdaFVars #[h] body
    let elseB ← withLocalDeclD `h (mkNot c) fun h => mkLambdaFVars #[h] nilB
    let rhs' := mkAppN (mkConst ``dite [levelOne]) #[resTy, c, inst, thenB, elseB]
    let ty ← mkForallFVars ps (← mkEq (mkAppN (mkConst gN) ps) rhs')
    pure (ty, vw, false)
  let (eqTy, vw, general) := vwEq
  let gI := mkIdent gN
  let fI := mkIdent fn
  let vI := mkIdent (if vw == ``viewN then ``viewN_eq else ``view_eq)
  let eI := mkIdent eqn
  if general then
    let eqTy ← instantiateMVars eqTy
    let mv ← mkFreshExprSyntheticOpaqueMVar eqTy
    let rest ← Tactic.run mv.mvarId! (do
      Tactic.evalTactic (← `(tactic| (intros; unfold $gI:ident)))
      veqGo fn vw)
    unless rest.isEmpty do throwError "frontx_view: could not prove the equation"
    let pf ← instantiateMVars mv
    if pf.hasSorry || pf.hasMVar then throwError "frontx_view: could not prove the equation"
    addDecl (.thmDecl { name := gN ++ `eq, levelParams := [], type := eqTy, value := pf })
    logInfo m!"frontx: {gN}, {gN ++ `eq} : {eqTy}"
    return
  addThm (gN ++ `eq) eqTy (← `(tactic|
    (intros
     unfold $gI:ident
     rw [$vI:ident]
     split <;> first | rfl | simp only [$fI:ident] | (rw [$fI:ident]) | (rw [$eI:ident]; rfl) | (rw [$eI:ident]))))
  let eqName := gN ++ `eq
  logInfo m!"frontx: {gN}, {eqName} : {eqTy}"

/-! ## Results that end with a view of the input: `frontx_tailcopy g measure μ`

For a list function `g B i …` (from `frontx_view`) whose result can be a view `view B k` (e.g. `drop`), adds
`g.cp B i … m k := bif m then view B k else g B i …`, its equation (the copy loop when `m`, else `g`'s body with
`view B k'` replaced by `g.cp … true k'` and the recursive calls by `g.cp … false k`), and the measure
`g.cp.μ` (`B.size - k` when copying, else `B.size + 1 + μ`); then `frontx_compile g.cp from g.cp.eq measure g.cp.μ`. -/

syntax "frontx_tailcopy " ident " measure " term : command
elab_rules : command
  | `(frontx_tailcopy $g:ident measure $μ:term) => liftTermElabM do
  let gN ← realizeGlobalConstNoOverloadWithInfo g
  let eqN := gN ++ `eq
  let cpN := gN ++ `cp
  let eqInfo ← getConstInfo eqN
  let ginfo ← getConstInfo gN
  let boolT := Lean.mkConst ``Bool
  let natT := Lean.mkConst ``Nat
  forallTelescope eqInfo.type fun ps ty => do
    let some (_, _, rhs) := ty.eq? | throwError "frontx_tailcopy: bad equation"
    let B := ps[0]!
    let resT ← inferType (mkAppN (mkConst gN) ps)
    -- g.cp
    let cpTy ← forallTelescope ginfo.type fun ys rT => do
      withLocalDeclD `m boolT fun m => withLocalDeclD `k natT fun k => mkForallFVars (ys ++ #[m, k]) rT
    let cpVal ← forallTelescope ginfo.type fun ys _ => do
      withLocalDeclD `m boolT fun m => withLocalDeclD `k natT fun k => do
        mkLambdaFVars (ys ++ #[m, k]) (← mkAppOptM ``cond #[resT, m, mkApp2 (mkConst ``view) ys[0]! k, mkAppN (mkConst gN) ys])
    addAndCompile (.defnDecl (mkDefinitionValEx cpN [] cpTy cpVal (.regular 1) .safe [cpN]))
    withLocalDeclD `m boolT fun m => withLocalDeclD `k natT fun k => do
      let cp (as : Array Expr) (m' k' : Expr) := mkAppN (mkConst cpN) (as ++ #[m', k'])
      let tru := Lean.mkConst ``Bool.true
      let fls := Lean.mkConst ``Bool.false
      let body' := rhs.replace fun e =>
        if e.isAppOfArity ``view 2 && e.getArg! 0 == B then some (cp ps tru (e.getArg! 1))
        else if e.isAppOfArity gN ps.size then some (cp e.getAppArgs fls k)
        else none
      let k1 ← mkAppM ``HAdd.hAdd #[k, toExpr (1 : Nat)]
      let c ← mkAppM ``LT.lt #[k, mkApp (mkConst ``ByteArray.size) B]
      let inst ← synthInstance (mkApp (mkConst ``Decidable) c)
      let copyB ← withLocalDeclD `h c fun h => do
        let x ← Term.elabTerm (← `($(← Term.exprToSyntax B)[$(← Term.exprToSyntax k)]'$(← Term.exprToSyntax h))) none
        synthesizeSyntheticMVarsNoPostponing
        mkLambdaFVars #[h] (← mkAppM ``List.cons #[← instantiateMVars x, cp ps tru k1])
      let nilB ← withLocalDeclD `h (mkNot c) fun h => do mkLambdaFVars #[h] (← mkAppOptM ``List.nil #[mkConst ``UInt8])
      let copyE := mkAppN (mkConst ``dite [levelOne]) #[resT, c, inst, copyB, nilB]
      let P ← mkEq m tru
      let instP ← synthInstance (mkApp (mkConst ``Decidable) P)
      let rhs' := mkAppN (mkConst ``ite [levelOne]) #[resT, P, instP, copyE, body']
      let eqTy ← mkForallFVars (ps ++ #[m, k]) (← mkEq (cp ps m k) rhs')
      let cpI := mkIdent cpN
      let eqI := mkIdent eqN
      addThm (cpN ++ `eq) eqTy (← `(tactic|
        (intros
         rename_i m k
         cases m
         · simp only [Bool.false_eq_true, ↓reduceIte]; exact $eqI:ident ..
         · simp only [↓reduceIte]; exact view_eq _ _)))
      -- the measure
      let μE ← elabTerm μ (some (← mkForallFVars ps natT))
      synthesizeSyntheticMVarsNoPostponing
      let μE ← instantiateMVars μE
      let sz := mkApp (mkConst ``ByteArray.size) B
      let μV ← mkLambdaFVars (ps ++ #[m, k]) (mkAppN (mkConst ``ite [levelOne]) #[natT, P, instP,
        ← mkAppM ``HSub.hSub #[sz, k], ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[sz, toExpr (1 : Nat)],
          (mkAppN μE ps).headBeta]])
      addDef (cpN ++ `μ) (← inferType μV) μV
      logInfo m!"frontx: {cpN}, {cpN ++ `eq} : {eqTy}"

/-! ## Entry points

`frontx_entry g` for `def g (xs : ByteArray) : T := f xs a₁ … aₙ`, `f` compiled by `frontx_compile` (first
parameter the byte array, the others scalars from variable 4 on), each `aᵢ` a closed term or `xs.size`.  Adds
`g.prog` (parameter initialisation, then `f`'s program), `g.slots` and

  `g.exec : ∀ xs env, env 1 = rN xs.size → xs.size < 2 ^ 32 → (∀ j, 8 ≤ j → env j = 0) →
     ∃ σ', BExec g.prog ⟨env, [blk xs]⟩ σ' ∧ σ'.env 4 = rep (g xs) ∧ σ'.heap = [blk xs]`,

the hypothesis of `implements1_of_frontx` (`Impl1.lean`). -/

def Ty.repName : Ty → Name
  | .bv => ``id | .u8 => ``r8 | .u32 => ``r32 | .u64 => ``r64 | .nat => ``rN | .bool => ``rB

syntax "frontx_entry " ident (" from " ident)? : command
elab_rules : command
  | `(frontx_entry $g:ident $[from $e?]?) => liftTermElabM do
  let gN ← realizeGlobalConstNoOverloadWithInfo g
  let info ← getConstInfoDefn gN
  -- `g xs = f xs a₁ … aₙ`: the definition of `g`, or a proved equation (`from`)
  let eqN? ← e?.mapM fun e => realizeGlobalConstNoOverloadWithInfo e
  let val ← match eqN? with
    | none => pure info.value
    | some eqN => forallTelescope (← getConstInfo eqN).type fun xs ty => do
        let some (_, _, rhs) := ty.eq? | throwError "frontx_entry: `from` needs an equation"
        mkLambdaFVars xs rhs
  let (fN, inits, rty, isList, isOpt, rcomps) ← lambdaTelescope val fun xs body => do
    unless xs.size == 1 && (← whnfR (← inferType xs[0]!)).isConstOf ``ByteArray do
      throwError "frontx_entry: expected one ByteArray parameter"
    let .const fN _ := body.getAppFn | throwError "frontx_entry: the body must be an application of a compiled function"
    let args := body.getAppArgs
    -- the byte array: an argument of `f` anywhere (it is `f`'s block 0)
    unless args.contains xs[0]! do throwError "frontx_entry: the byte array must be an argument"
    let args := #[xs[0]!] ++ args.filter (· != xs[0]!)
    let bty ← whnfR (← inferType body)
    let isList := bty.isAppOfArity ``List 1
    let isOpt ← if bty.isAppOfArity ``Option 1 then pure ((← whnfR bty.appArg!).isConstOf ``UInt8) else pure false
    -- a tuple / structure result: its components (written as bytes)
    let rcomps ← if isList || isOpt then pure #[] else
      match ← resultComps bty with
      | some cs => pure (if cs.size > 1 then cs else #[])
      | none => pure #[]
    let some rty ← (if isList || isOpt then pure (some Ty.nat) else if rcomps.size > 1 then pure (some rcomps[0]!.2)
        else classify bty)
      | throwError "frontx_entry: unsupported result type"
    let mut inits : Array Expr := #[]
    let mut next := 4
    for a in args.extract 1 args.size do
      let aty ← inferType a
      if ← isProp aty then continue
      -- a scalar, or a closed tuple / structure (one variable per component)
      let some acs ← resultComps aty | throwError "frontx_entry: unsupported argument type{indentExpr aty}"
      for (π, ty) in acs do
        let a' := (mkApp π a).headBeta
        let e ← if a'.isAppOfArity ``ByteArray.size 1 && a'.appArg! == xs[0]! then
            pure (mkApp (mkConst ``BExp.var) (toExpr (1 : Nat)))
          else
            if a'.hasFVar then throwError "frontx_entry: argument is neither closed nor `xs.size`{indentExpr a}"
            pure (mkApp (mkConst ``BExp.const) (ty.rep a'))
        inits := inits.push (← mkAppM ``Prod.mk #[toExpr next, e])
        next := next + 1
    return (fN, inits, rty, isList, isOpt, rcomps)
  let multi := rcomps.size > 1
  let env ← getEnv
  let hasInits := env.contains (fN ++ `inits)
  let base := mkAppN (mkConst ``prog) #[mkConst (fN ++ `lay), mkConst (fN ++ `tree), toExpr (4 : Nat)]
  let base := if hasInits then mkAppN (mkConst ``initS) #[mkConst (fN ++ `inits), base] else base
  -- an `Option UInt8` result: the two components (variables 4 and `v`) joined into variable 4 (`rOpt8`)
  let optV ← if isOpt then do
      let some rv := (← getConstInfo (fN ++ `rvars)).value? | throwError "frontx_entry: no result variables"
      let some [v] := (← whnf rv).listLit?.map (·.2.filterMap fun e => e.nat? <|> e.rawNatLit?) | throwError "frontx_entry: result variables{indentExpr rv}"
      pure (some v) else pure none
  let base := match optV with
    | some v => mkApp2 (mkConst ``BStmt.seq) base (mkApp2 (mkConst ``BStmt.assign) (toExpr (4 : Nat))
        (mkApp3 (mkConst ``BExp.bin) (mkConst ``Op.add) (mkApp (mkConst ``BExp.var) (toExpr (4 : Nat)))
          (mkApp3 (mkConst ``BExp.bin) (mkConst ``Op.shl) (mkApp (mkConst ``BExp.var) (toExpr v))
            (mkApp (mkConst ``BExp.const) (mkBV 8)))))
    | none => base
  let pairTy ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``BExp]
  -- several components: `g.comps` (variable, bytes, value), `g.enc`, and the stores after the program
  if multi then
    let rv ← if rcomps.size > 1 then do
        let some rv := (← getConstInfo (fN ++ `rvars)).value? | throwError "frontx_entry: no result variables"
        let some vs := (← whnf rv).listLit?.map (·.2.filterMap fun e => e.nat? <|> e.rawNatLit?)
          | throwError "frontx_entry: result variables{indentExpr rv}"
        pure vs.toArray else pure #[]
    unless rv.size + 1 == rcomps.size do throwError "frontx_entry: {rcomps.size} components, variables {rv}"
    let bty ← lambdaTelescope info.value fun _ b => inferType b
    let cty ← mkAppM ``Prod #[mkConst ``Nat, ← mkAppM ``Prod #[mkConst ``Nat, ← mkArrow bty bv64]]
    let cs ← (rcomps.zip (#[4] ++ rv)).mapM fun ((π, t), v) => do
      let k : Nat := match t with | .u8 | .bool => 1 | .u32 => 4 | _ => 8
      let r ← withLocalDeclD `b bty fun b => do mkLambdaFVars #[b] (t.rep (mkApp π b).headBeta)
      mkAppM ``Prod.mk #[toExpr v, ← mkAppM ``Prod.mk #[toExpr k, r]]
    addDef (gN ++ `comps) (← mkAppM ``List #[cty]) (← mkListLit cty cs.toList) (compile := true)
    addDef (gN ++ `enc) (← mkArrow bty (← mkAppM ``List #[mkConst ``UInt8]))
      (← mkAppOptM ``encC #[bty, mkConst (gN ++ `comps)]) (compile := true)
  let base := mkAppN (mkConst ``initS) #[← mkListLit pairTy inits.toList, base]
  let base ← if multi then do
      let cty := (← inferType (mkConst (gN ++ `comps))).appArg!
      let sel ← withLocalDeclD `c cty fun c => do
        mkLambdaFVars #[c] (← mkAppM ``Prod.mk #[← mkAppM ``Prod.fst #[c], ← mkAppM ``Prod.fst #[← mkAppM ``Prod.snd #[c]]])
      let st := mkApp2 (mkConst ``storeC) (← mkAppM ``List.map #[sel, mkConst (gN ++ `comps)]) (toExpr (0 : Nat))
      pure (mkApp2 (mkConst ``BStmt.seq) base st)
    else pure base
  addDef (gN ++ `prog) (mkConst ``BStmt) base (compile := true)
  addDef (gN ++ `slots) (mkConst ``Nat) (mkConst (fN ++ `slots)) (compile := true)
  let progI := mkIdent (gN ++ `prog)
  let gI := mkIdent gN
  let repI := mkIdent rty.repName
  let execI := mkIdent (fN ++ `exec)
  let repNI := mkIdent (fN ++ (if hasInits then `Rep0 else `Rep))
  let ty ← if isList then
      elabTerm (← `(∀ (xs : ByteArray) (out : List (BitVec 8)) (env : BEnv), env 1 = rN xs.size → xs.size < 2 ^ 32 →
        (∀ j, 8 ≤ j → env j = 0) → ($gI xs).length ≤ out.length → out.length < 2 ^ 32 →
        ∃ σ', BExec $progI ⟨env, [blk xs, out]⟩ σ' ∧ σ'.env 4 = rN ($gI xs).length ∧
          σ'.heap = [blk xs, wrO out 0 ($gI xs)])) none
    else if multi then
      let encI := mkIdent (gN ++ `enc)
      elabTerm (← `(∀ (xs : ByteArray) (out : List (BitVec 8)) (env : BEnv), env 1 = rN xs.size → xs.size < 2 ^ 32 →
        (∀ j, 8 ≤ j → env j = 0) → ($encI ($gI xs)).length ≤ out.length → out.length < 2 ^ 32 →
        ∃ σ', BExec $progI ⟨env, [blk xs, out]⟩ σ' ∧ σ'.heap = [blk xs, wrO out 0 ($encI ($gI xs))])) none
    else if isOpt then elabTerm (← `(∀ (xs : ByteArray) (env : BEnv), env 1 = rN xs.size → xs.size < 2 ^ 32 →
    (∀ j, 8 ≤ j → env j = 0) →
    ∃ σ', BExec $progI ⟨env, [blk xs]⟩ σ' ∧ σ'.env 4 = rOpt8 ($gI xs) ∧ σ'.heap = [blk xs])) none
    else elabTerm (← `(∀ (xs : ByteArray) (env : BEnv), env 1 = rN xs.size → xs.size < 2 ^ 32 →
    (∀ j, 8 ≤ j → env j = 0) →
    ∃ σ', BExec $progI ⟨env, [blk xs]⟩ σ' ∧ σ'.env 4 = $repI ($gI xs) ∧ σ'.heap = [blk xs])) none
  synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  if ty.hasMVar then throwError "frontx_entry: statement has metavariables{indentExpr ty}"
  let rwTac ← match eqN?, isList with
    | none, _ => `(tactic| skip)
    | some eqN, false => `(tactic| rw [$(mkIdent eqN):ident xs])
    | some eqN, true => `(tactic| rw [$(mkIdent eqN):ident xs] at hcap ⊢)
  let introTac ← if isList || multi then `(tactic| intro xs out env h1 hs h8 hcap hol) else `(tactic| intro xs env h1 hs h8)
  let joinTac ← if isOpt then `(tactic| refine opt_join ?_) else if multi then `(tactic| refine allEnv_res ?_)
    else `(tactic| skip)
  let rwTac ← if multi then `(tactic| skip) else pure rwTac
  let bytesTac ← if multi then
      let compsI := mkIdent (gN ++ `comps)
      let rwB ← match eqN? with
        | none => `(tactic| skip)
        | some eqN => `(tactic| rw [$(mkIdent eqN):ident xs])
      `(tactic| (refine entry_bytes $compsI ($gI xs) ?_ (by decide) hcap (by omega)
                 $rwB:tactic))
    else `(tactic| skip)
  addThm (gN ++ `exec) ty (← `(tactic| (
    $introTac:tactic
    $rwTac:tactic
    $bytesTac:tactic
    refine entry_exec ?_
    $joinTac:tactic
    apply $execI
    unfold $repNI
    and_intros <;> first
      | rfl
      | exact h1
      | omega
      | exact hcap
      | (simp [seqSet, BEnv.set, BExp.denote, h1]; done)
      | (simp [seqSet, BEnv.set, BExp.denote, h1]; omega))))
  checkAxioms (gN ++ `exec)
  logInfo m!"frontx: {gN}.prog, {gN}.exec"

end Proven.Frontx
