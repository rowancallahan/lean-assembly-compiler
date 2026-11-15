/- Word arrays (NOTES section 20): `wa_compile`, the reflection of a Lean definition into `WA` syntax
(`WaLang.lean`) and the generated proofs.  Untrusted: what counts is the kernel-checked `f.implements1`.

`wa_compile f` for `f : ByteArray → β` (β a scalar type with a `Res` instance) reads the body of `f`,
unfolds non-recursive helpers, and builds `f.wa : Pg [.ar .ba] (.sc t)`:
* `let`s of scalars become program `let`s, constant tables (top-level `Array` constants) and `xs.data` are
  hoisted to the front (`F.const`, `F.data`);
* `Array.foldl g init arr` (over an array of the environment) becomes a loop with state `(acc, i)`, its
  body read off `g acc arr[i]!` (the function `foldGo`, `foldl_foldGo`);
* the rest is the result expression.
Then `f.good : ∀ xs, xs.size < 2 ^ 32 → f.wa.Good (xs, ()) (f xs)` is proved stage by stage (per loop the
function `foldGo g arr`, the invariant `i ≤ arr.size`, the measure `arr.size - i`, `runs_of` with the loop's
equation, closed by `simp` over the meanings), and `f.code`, `f.implements1` follow from `implements1_wa`. -/
import Lean
import Riscv.Frontx.WaImpl

namespace Proven.WA
open Lean Meta Elab Term Command

/-! ## Folds as loops -/

def foldGo {α β : Type} [Inhabited α] (g : β → α → β) (a : Array α) (i : Nat) (acc : β) : β :=
  if i < a.size then foldGo g a (i + 1) (g acc a[i]!) else acc
termination_by a.size - i

theorem foldGo_eq {α β : Type} [Inhabited α] (g : β → α → β) (a : Array α) : ∀ i acc,
    foldGo g a i acc = (a.toList.drop i).foldl g acc := by
  intro i acc
  induction h : a.size - i generalizing i acc with
  | zero => rw [foldGo, if_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]; rfl
  | succ n ih =>
    rw [foldGo, if_pos (by omega), ih (i + 1) _ (by omega)]
    conv => rhs; rw [List.drop_eq_getElem_cons (by simp; omega)]
    rw [List.foldl_cons, getElem!_pos a i (by omega), Array.getElem_toList]

theorem foldl_foldGo {α β : Type} [Inhabited α] (g : β → α → β) (a : Array α) (s : β) :
    a.foldl g s = foldGo g a 0 s := by rw [foldGo_eq, List.drop_zero, Array.foldl_toList]

/-! ## Closing the side conditions -/

macro "wa_close" : tactic => `(tactic| (
  simp only [true_and, and_true, true_implies, Bool.false_eq_true, false_implies, decide_eq_true_eq, implies_true,
    and_self, ite_true, ite_false, Bool.true_eq_false] at ⊢
  repeat' (first | (apply And.intro) | split | intro)
  all_goals (first | trivial | assumption | omega | simp_all | skip)))

/-! ## Reflection -/

def tySyn : Ty → MetaM Term
  | .u8 => `(Ty.u8) | .u16 => `(Ty.u16) | .u32 => `(Ty.u32) | .u64 => `(Ty.u64) | .nat => `(Ty.nat)
  | .bool => `(Ty.bool)

def slSyn : Sl → MetaM Term
  | .sc t => do `(Sl.sc $(← tySyn t))
  | .ar .ba => `(Sl.ar AK.ba)
  | .ar (.arr t) => do `(Sl.ar (AK.arr $(← tySyn t)))

def ctxSyn (ctx : List Sl) : MetaM Term := do
  let xs ← ctx.toArray.mapM slSyn
  `([$xs,*])

def memSyn : Nat → MetaM Term
  | 0 => `(Mem.hd)
  | n + 1 => do `(Mem.tl $(← memSyn n))

def tyOf? (T : Expr) : MetaM (Option Ty) := do
  let T ← whnfR T
  if T.isConstOf ``UInt8 then return some .u8
  if T.isConstOf ``UInt16 then return some .u16
  if T.isConstOf ``UInt32 then return some .u32
  if T.isConstOf ``UInt64 then return some .u64
  if T.isConstOf ``Nat then return some .nat
  if T.isConstOf ``Bool then return some .bool
  return none

def slOf? (T : Expr) : MetaM (Option Sl) := do
  let T ← whnfR T
  if T.isConstOf ``ByteArray then return some (.ar .ba)
  if T.isAppOfArity ``Array 1 then
    if let some t ← tyOf? T.appArg! then return some (.ar (.arr t))
  return (← tyOf? T).map .sc

/-- an entry of the environment: the Lean term it stands for and its slot -/
structure Ent where
  key : Expr
  sl : Sl

/-- a term that must become a slot at the front of the program (a table, `xs.data`): raised by `arr` -/
initialize waHoistExc : Lean.InternalExceptionId ← Lean.registerInternalExceptionId `waHoist
initialize waHoistRef : IO.Ref (Option Expr) ← IO.mkRef none
/-- reads `a[i]!` known to be in range (the element of a fold) -/
initialize waSafeRef : IO.Ref (Array (Expr × Expr)) ← IO.mkRef #[]
/-- the stages of the program being reflected (for the proof) -/
inductive Stage | letS | loopS (k : Nat) (Δ : List Sl) | retS
initialize waStagesRef : IO.Ref (Array Stage) ← IO.mkRef #[]

def Ent.find? (ctx : List Ent) (e : Expr) : MetaM (Option (Nat × Sl)) := do
  for h : i in [0:ctx.length] do
    let en := ctx[i]
    if en.key == e then return some (i, en.sl)
  for h : i in [0:ctx.length] do
    let en := ctx[i]
    if ← withReducible (isDefEq en.key e) then return some (i, en.sl)
  return none

def binOps : List (Name × Name) :=
  [(``HAdd.hAdd, ``Op2.add), (``HSub.hSub, ``Op2.sub), (``HMul.hMul, ``Op2.mul), (``HDiv.hDiv, ``Op2.div),
   (``HMod.hMod, ``Op2.mod), (``HAnd.hAnd, ``Op2.and), (``HOr.hOr, ``Op2.or), (``HXor.hXor, ``Op2.xor),
   (``HShiftLeft.hShiftLeft, ``Op2.shl), (``HShiftRight.hShiftRight, ``Op2.shr)]

def castFns : List (Name × Ty) :=
  [(``UInt8.toNat, .nat), (``UInt16.toNat, .nat), (``UInt32.toNat, .nat), (``UInt64.toNat, .nat),
   (``UInt8.ofNat, .u8), (``UInt16.ofNat, .u16), (``UInt32.ofNat, .u32), (``UInt64.ofNat, .u64),
   (``UInt8.toUInt16, .u16), (``UInt8.toUInt32, .u32), (``UInt8.toUInt64, .u64),
   (``UInt16.toUInt8, .u8), (``UInt16.toUInt32, .u32), (``UInt16.toUInt64, .u64),
   (``UInt32.toUInt8, .u8), (``UInt32.toUInt16, .u16), (``UInt32.toUInt64, .u64),
   (``UInt64.toUInt8, .u8), (``UInt64.toUInt16, .u16), (``UInt64.toUInt32, .u32)]

/-- is `c` a definition we may unfold (not one of ours, not recursive) -/
def unfoldable (c : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo _) := env.find? c | return false
  if (`Proven).isPrefixOf c then return false
  if env.isProjectionFn c then return false
  -- library code of Lean itself (`Init`, `Std`, `Lean`) is a primitive here, never unfolded
  if let some idx := env.getModuleIdxFor? c then
    let m := env.header.moduleNames[idx.toNat]!
    if (`Init).isPrefixOf m || (`Std).isPrefixOf m || (`Lean).isPrefixOf m then return false
  -- structural / well-founded recursion leaves an equation mentioning the constant itself
  return !(← isRecursiveDefinition c)
where
  isRecursiveDefinition (c : Name) : MetaM Bool := do
    let some eqs ← getEqnsFor? c | return false
    for eq in eqs do
      let t ← inferType (mkConst eq ((← getConstInfo eq).levelParams.map Level.param))
      if t.find? (·.isConstOf c) |>.isSome then
        -- the left-hand side always mentions `c`; count occurrences
        let n := (t.foldConsts 0 fun c' n => if c' == c then n + 1 else n)
        if n > 1 then return true
    return false

partial def unfoldHead? (e : Expr) : MetaM (Option Expr) := do
  let some c := e.getAppFn.constName? | return none
  if !(← unfoldable c) then return none
  let some e' ← unfoldDefinition? e | return none
  return some e'.headBeta

mutual
partial def reifyE (ctx : List Ent) (e : Expr) : TermElabM (Term × Ty) := do
  let e ← instantiateMVars e
  let e := e.consumeMData
  let throwU {α : Type} (m : String) : TermElabM α := throwError "wa_compile: unsupported {m}: {e}"
  if let some (i, .sc t) ← Ent.find? ctx e then
    return (← `(E.var $(← memSyn i)), t)
  match e with
  | .letE _ _ v b _ => return ← reifyE ctx (b.instantiate1 v)
  | .lit (.natVal _) => return (← `(E.lit Ty.nat $(← exprToSyntax e)), .nat)
  | _ => pure ()
  let f := e.getAppFn
  let args := e.getAppArgs
  let some c := f.constName? | throwU "term"
  -- literals
  if c == ``OfNat.ofNat && args.size == 3 then
    if let some t ← tyOf? args[0]! then return (← `(E.lit $(← tySyn t) $(← exprToSyntax e)), t)
  if (c == ``Bool.true || c == ``Bool.false) && args.size == 0 then
    return (← `(E.lit Ty.bool $(← exprToSyntax e)), .bool)
  -- arithmetic
  if let some (_, op) := binOps.find? (·.1 == c) then
    if args.size == 6 then
      let (a, t) ← reifyE ctx args[4]!
      let (b, _) ← reifyE ctx args[5]!
      return (← `(E.bin $(mkIdent op) $a $b), t)
  if c == ``BEq.beq && args.size == 4 then
    let (a, _) ← reifyE ctx args[2]!; let (b, _) ← reifyE ctx args[3]!
    return (← `(E.cmp Cmp.eq $a $b), .bool)
  if c == ``bne && args.size == 4 then
    let (a, _) ← reifyE ctx args[2]!; let (b, _) ← reifyE ctx args[3]!
    return (← `(E.cmp Cmp.ne $a $b), .bool)
  if c == ``and && args.size == 2 then
    let (a, _) ← reifyE ctx args[0]!; let (b, _) ← reifyE ctx args[1]!
    return (← `(E.bin Op2.band $a $b), .bool)
  if c == ``or && args.size == 2 then
    let (a, _) ← reifyE ctx args[0]!; let (b, _) ← reifyE ctx args[1]!
    return (← `(E.bin Op2.bor $a $b), .bool)
  if c == ``not && args.size == 1 then
    let (a, _) ← reifyE ctx args[0]!
    return (← `(E.cast Ty.bool $a), .bool)
  if c == ``Decidable.decide && args.size == 2 then
    return (← reifyP ctx args[0]!, .bool)
  if let some (_, t) := castFns.find? (·.1 == c) then
    if args.size == 1 then
      let (a, _) ← reifyE ctx args[0]!
      return (← `(E.cast $(← tySyn t) $a), t)
  if c == ``Nat.toUInt32 && args.size == 1 then
    let (a, _) ← reifyE ctx args[0]!
    return (← `(E.cast Ty.u32 $a), .u32)
  -- conditionals
  if c == ``ite && args.size == 5 then
    let cnd ← reifyP ctx args[1]!
    let (a, t) ← reifyE ctx args[3]!; let (b, _) ← reifyE ctx args[4]!
    return (← `(E.ite $cnd $a $b), t)
  if c == ``dite && args.size == 5 then
    let cnd ← reifyP ctx args[1]!
    let (a, t) ← withLocalDeclD `h args[1]! fun h => reifyE ctx (args[3]!.beta #[h])
    let (b, _) ← withLocalDeclD `h (mkNot args[1]!) fun h => reifyE ctx (args[4]!.beta #[h])
    return (← `(E.ite $cnd $a $b), t)
  -- arrays
  if c == ``GetElem.getElem && args.size == 8 then
    return ← reifyGet ctx args[5]! args[6]! false
  if c == ``GetElem?.getElem! && args.size == 8 then
    return ← reifyGet ctx args[6]! args[7]! true
  if (c == ``Array.size && args.size == 2) || (c == ``ByteArray.size && args.size == 1) then
    let a := args.back!
    let (i, _) ← arr ctx a
    return (← `(E.size $(← memSyn i)), .nat)
  if let some e' ← unfoldHead? e then return ← reifyE ctx e'
  throwU "term"

partial def reifyGet (ctx : List Ent) (a i : Expr) (chk : Bool) : TermElabM (Term × Ty) := do
  let (m, sl) ← arr ctx a
  let (ix, _) ← reifyE ctx i
  let safe := (← waSafeRef.get).any fun (a', i') => a' == a && i' == i
  let ck ← if chk && !safe then `(true) else `(false)
  match sl with
  | .ar .ba => return (← `(E.getB $(← memSyn m) $ix $ck), .u8)
  | .ar (.arr t) => return (← `(E.getA $(← memSyn m) $ix $ck), t)
  | _ => throwError "wa_compile: not an array {a}"

/-- an array of the environment, or a request to hoist it -/
partial def arr (ctx : List Ent) (a : Expr) : TermElabM (Nat × Sl) := do
  let a := (← instantiateMVars a).consumeMData
  if let some r ← Ent.find? ctx a then return r
  if a.hasLooseBVars || a.hasFVar && !(a.isAppOfArity ``ByteArray.data 1) then
    throwError "wa_compile: array not in the environment {a}"
  waHoistRef.set (some a)
  throw (.internal waHoistExc)

partial def reifyP (ctx : List Ent) (p : Expr) : TermElabM Term := do
  let p := (← instantiateMVars p).consumeMData
  let f := p.getAppFn; let args := p.getAppArgs
  let some c := f.constName? | throwError "wa_compile: unsupported condition {p}"
  let two (k : Term → Term → MetaM Term) : TermElabM Term := do
    let (a, _) ← reifyE ctx args[2]!; let (b, _) ← reifyE ctx args[3]!; k a b
  if c == ``LT.lt && args.size == 4 then return ← two fun a b => `(E.cmp Cmp.lt $a $b)
  if c == ``LE.le && args.size == 4 then return ← two fun a b => `(E.cmp Cmp.le $a $b)
  if c == ``GT.gt && args.size == 4 then return ← two fun a b => `(E.cmp Cmp.lt $b $a)
  if c == ``GE.ge && args.size == 4 then return ← two fun a b => `(E.cmp Cmp.le $b $a)
  if c == ``Eq && args.size == 3 then
    if args[2]!.isConstOf ``Bool.true then return (← reifyE ctx args[1]!).1
    let (a, _) ← reifyE ctx args[1]!; let (b, _) ← reifyE ctx args[2]!
    return ← `(E.cmp Cmp.eq $a $b)
  if c == ``Ne && args.size == 3 then
    let (a, _) ← reifyE ctx args[1]!; let (b, _) ← reifyE ctx args[2]!
    return ← `(E.cmp Cmp.ne $a $b)
  if c == ``And && args.size == 2 then
    return ← `(E.bin Op2.band $(← reifyP ctx args[0]!) $(← reifyP ctx args[1]!))
  if c == ``Or && args.size == 2 then
    return ← `(E.bin Op2.bor $(← reifyP ctx args[0]!) $(← reifyP ctx args[1]!))
  if c == ``Not && args.size == 1 then
    return ← `(E.cast Ty.bool $(← reifyP ctx args[0]!))
  throwError "wa_compile: unsupported condition {p}"
end

/-! ## Bodies and programs -/

/-- `(fun x => b) a` as `let x := a; b` unless `a` is atomic -/
partial def letBeta (f : Expr) (args : List Expr) : Expr :=
  match f, args with
  | .lam n t b bi, a :: as =>
    if a.isFVar || a.isConst || a.isLit || a.isAppOfArity ``OfNat.ofNat 3 then letBeta (b.instantiate1 a) as
    else .letE n t a (letBeta b as) false
  | f, as => mkAppN f as.toArray

/-- unfold helpers at the head (keeping their arguments as `let`s) -/
partial def prepTop (e : Expr) (names : IO.Ref (Array Name)) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  let some c := e.getAppFn.constName? | return e
  if c == ``Array.foldl then return e
  if !(← unfoldable c) then return e
  let info ← getConstInfo c
  let some v := info.value? | return e
  names.modify (·.push c)
  let us := e.getAppFn.constLevels!
  prepTop (letBeta (v.instantiateLevelParams info.levelParams us) e.getAppArgs.toList) names

/-- hoist the `let`s of the call arguments, then the call -/
partial def reifyCall (ctx : List Ent) (Δ : List Sl) (args : List Expr) (names : IO.Ref (Array Name)) :
    TermElabM Term := do
  -- find the first argument that starts with a `let` after unfolding
  let rec go (pre : List Expr) : List Expr → TermElabM Term
    | [] => do
      let mut acc ← `(Args.nil)
      for (a, sl) in (pre.zip Δ).reverse do
        match sl with
        | .sc _ => let (t, _) ← reifyE ctx a; acc ← `(Args.cons $t $acc)
        | .ar _ =>
          let (m, _) ← arr ctx a
          acc ← `(Args.cons (A.var $(← memSyn m)) $acc)
      `(T.call $acc)
    | a :: rest => do
      let a' ← prepTop a names
      match a' with
      | .letE n t v b _ =>
        if let some (.sc ty) ← slOf? t then
          let (vt, _) ← reifyE ctx v
          withLocalDeclD n t fun x => do
            let ctx' := ⟨x, .sc ty⟩ :: ctx
            let k ← reifyCall ctx' Δ (pre ++ b.instantiate1 x :: rest) names
            `(T.let_ $vt $k)
        else go pre (b.instantiate1 v :: rest)
      | _ => go (pre ++ [a']) rest
  go [] args

/-- a recorded loop: the Lean function computing its result from the state, invariant, measure -/
structure LoopRec where
  g : Expr
  P : Expr
  μ : Expr
  Δ : List Sl
  deriving Inhabited

/-- the stages of a program -/
partial def reifyPg (ctx : List Ent) (e : Expr) (R : Sl) (names : IO.Ref (Array Name)) (loops : IO.Ref (Array LoopRec)) :
    TermElabM Term := do
  let e ← prepTop e names
  match e with
  | .letE n t v b _ =>
    let some sl ← slOf? t | throwError "wa_compile: unsupported let type {t}"
    let v' ← prepTop v names
    if v'.isAppOfArity ``Array.foldl 7 then
      withLocalDeclD n t fun x => do
        let lp ← reifyFold ctx v' names loops
        waStagesRef.modify (·.push (.loopS ((← loops.get).size - 1) [.sc .nat]))
        let k ← reifyPg (⟨x, sl⟩ :: ctx) (b.instantiate1 x) R names loops
        `($lp $k)
    else
      match sl with
      | .sc ty =>
        let (vt, _) ← reifyE ctx v
        waStagesRef.modify (·.push .letS)
        withLocalDeclD n t fun x => do
          let k ← reifyPg (⟨x, .sc ty⟩ :: ctx) (b.instantiate1 x) R names loops
          `(Pg.let_ (s := $(← slSyn sl)) $vt $k)
      | _ => throwError "wa_compile: unsupported array let {v}"
  | _ =>
    if e.isAppOfArity ``Array.foldl 7 then
      let lp ← reifyFold ctx e names loops
      waStagesRef.modify (·.push (.loopS ((← loops.get).size - 1) [.sc .nat]))
      waStagesRef.modify (·.push .retS)
      return ← `($lp (Pg.ret (E.var Mem.hd)))
    let (t, _) ← reifyE ctx e
    waStagesRef.modify (·.push .retS)
    `(Pg.ret $t)
where
  /-- `Array.foldl g init arr`: a loop over `(acc, i)`, returned as a function of the continuation -/
  reifyFold (ctx : List Ent) (e : Expr) (names : IO.Ref (Array Name)) (loops : IO.Ref (Array LoopRec)) :
      TermElabM Term := do
    let args := e.getAppArgs
    let (α, β, g, init, a) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
    let some (.sc tb) ← slOf? β | throwError "wa_compile: fold state {β}"
    let some (.sc _) ← slOf? α | throwError "wa_compile: fold element {α}"
    let (ma, _) ← arr ctx a
    let (it, _) ← reifyE ctx init
    let Δ : List Sl := [.sc tb, .sc .nat]
    let body ← withLocalDeclD `acc β fun acc => withLocalDeclD `i (mkConst ``Nat) fun i => do
      let ctx' := ⟨acc, .sc tb⟩ :: ⟨i, .sc .nat⟩ :: ctx
      let elt ← mkAppOptM ``getElem! #[none, none, none, none, none, none, a, i]
      waSafeRef.modify (·.push (a, i))
      let call ← reifyCall ctx' Δ [mkApp2 g acc elt, ← mkAppM ``HAdd.hAdd #[i, mkNatLit 1]] names
      `(T.ite (E.cmp Cmp.lt (E.var (Mem.tl Mem.hd)) (E.size $(← memSyn (ma + 2)))) $call (T.ret (E.var Mem.hd)))
    let sT ← mkAppM ``Vals #[← toListSl Δ]
    let gE ← withLocalDeclD `s sT fun s => do
      let i ← mkAppM ``Prod.fst #[← mkAppM ``Prod.snd #[s]]
      let accE ← mkAppM ``Prod.fst #[s]
      mkLambdaFVars #[s] (← mkAppOptM ``foldGo #[α, β, none, g, a, i, accE])
    let PE ← withLocalDeclD `s sT fun s => do
      let i ← mkAppM ``Prod.fst #[← mkAppM ``Prod.snd #[s]]
      mkLambdaFVars #[s] (← mkAppOptM ``LE.le #[mkConst ``Nat, none, i, ← mkAppM ``Array.size #[a]])
    let μE ← withLocalDeclD `s sT fun s => do
      let i ← mkAppM ``Prod.fst #[← mkAppM ``Prod.snd #[s]]
      mkLambdaFVars #[s] (← mkAppOptM ``HSub.hSub #[mkConst ``Nat, mkConst ``Nat, mkConst ``Nat, none,
        ← mkAppM ``Array.size #[a], i])
    loops.modify (·.push ⟨gE, PE, μE, Δ⟩)
    `(Pg.loop $(← ctxSyn Δ) $body (Inis.cons $it (Inis.cons (E.lit Ty.nat 0) Inis.nil)))
  toListSl (Δ : List Sl) : MetaM Expr := do
    let mut l ← mkAppOptM ``List.nil #[mkConst ``Sl]
    for s in Δ.reverse do
      let se ← match s with
        | .sc t => pure (mkApp (mkConst ``Sl.sc) (toTyE t))
        | .ar .ba => pure (mkApp (mkConst ``Sl.ar) (mkConst ``AK.ba))
        | .ar (.arr t) => pure (mkApp (mkConst ``Sl.ar) (mkApp (mkConst ``AK.arr) (toTyE t)))
      l ← mkAppM ``List.cons #[se, l]
    return l
  toTyE : Ty → Expr
    | .u8 => mkConst ``Ty.u8 | .u16 => mkConst ``Ty.u16 | .u32 => mkConst ``Ty.u32 | .u64 => mkConst ``Ty.u64
    | .nat => mkConst ``Ty.nat | .bool => mkConst ``Ty.bool

/-! ## The command -/

theorem u8_lt64 (x : UInt8) : x.toNat < 2 ^ 64 := by have := x.toNat_lt; omega
theorem u16_lt64 (x : UInt16) : x.toNat < 2 ^ 64 := by have := x.toNat_lt; omega
theorem u32_lt64 (x : UInt32) : x.toNat < 2 ^ 64 := by have := x.toNat_lt; omega
theorem u64_lt64 (x : UInt64) : x.toNat < 2 ^ 64 := x.toNat_lt
theorem u8_lt64' (x : UInt8) : x.toNat < 18446744073709551616 := u8_lt64 x
theorem u16_lt64' (x : UInt16) : x.toNat < 18446744073709551616 := u16_lt64 x
theorem u32_lt64' (x : UInt32) : x.toNat < 18446744073709551616 := u32_lt64 x
theorem u64_lt64' (x : UInt64) : x.toNat < 18446744073709551616 := u64_lt64 x

/-- the simp set of the meanings -/
macro "wa_dsimp" : tactic => `(tactic| simp only [T.ok, T.out, T.den, E.ok, E.den, A.den, Args.ok, Args.den, Arg.den,
  Ini.ok, Ini.den, Inis.ok, Inis.den, F.ok, F.den, Vals.app, Mem.get, AK.size, AK.get, Op2.den, Cmp.den, WA.cast,
  Ty.small, Op2.exact, decide_eq_true_eq, u8_lt64, u16_lt64, u32_lt64, u64_lt64, u8_lt64', u16_lt64', u32_lt64',
  u64_lt64'] at *)

macro "wa_okt" : tactic => `(tactic| (wa_dsimp <;> wa_close))

def tyTypeSyn : Ty → MetaM Term
  | .u8 => `(UInt8) | .u16 => `(UInt16) | .u32 => `(UInt32) | .u64 => `(UInt64) | .nat => `(Nat) | .bool => `(Bool)

/-- `rintro ⟨x0, x1, …, ⟨⟩⟩` with the components' types made explicit (for `omega`) -/
def introState (Δ : List Sl) (extra : Array Ident := #[]) : TermElabM (Array (TSyntax `tactic)) := do
  let names := (List.range Δ.length).map fun j => mkIdent (Name.mkSimple s!"x{j}")
  let mut pats : Array (TSyntax `rcasesPat) := #[]
  for nm in names do pats := pats.push (← `(rcasesPat| $nm:ident))
  pats := pats.push (← `(rcasesPat| ⟨⟩))
  let ex : Array (TSyntax `rcasesPat) ← extra.mapM fun e => `(rcasesPat| $e:ident)
  let mut tacs := #[← `(tactic| rintro ⟨$pats,*⟩ $ex*)]
  for (nm, sl) in names.zip Δ do
    match sl with
    | .sc t => tacs := tacs.push (← `(tactic| change $(← tyTypeSyn t) at $nm:ident))
    | _ => pure ()
  return tacs

syntax "wa_compile " ident : command

/-- reify the body of `fn`; `hoisted` are terms over the input (bound variable 0) placed in front -/
def reifyEntry (fn : Name) (t : Ty) (hoisted : Array Expr) (names : IO.Ref (Array Name))
    (loops : IO.Ref (Array LoopRec)) : TermElabM (Sum Expr (Term × Array LoopRec)) := do
  let info ← getConstInfo fn
  let ba := Lean.mkConst ``ByteArray
  waStagesRef.set #[]; waSafeRef.set #[]
  withLocalDeclD `xs ba fun x => do
    let hs' := hoisted.map (·.instantiate1 x)
    let mut ctx : List Ent := [⟨x, .ar .ba⟩]
    let mut fronts : Array (Term × Sl) := #[]
    for h in hs' do
      let ty ← inferType h
      let some sl ← slOf? ty | throwError "wa_compile: hoisted {h}"
      let fT ← if h.isAppOfArity ``ByteArray.data 1 then do
          let (m, _) ← arr ctx h.appArg!
          `(F.data $(← memSyn m))
        else `(F.const $(← exprToSyntax h))
      fronts := fronts.push (fT, sl)
      ctx := ⟨h, sl⟩ :: ctx
      waStagesRef.modify (·.push .letS)
    let body := (info.value!.instantiateLevelParams info.levelParams (info.levelParams.map Level.param)).beta #[x]
    try
      let mut prog ← reifyPg ctx body (.sc t) names loops
      for (fT, sl) in fronts.reverse do
        prog ← `(Pg.let_ (s := $(← slSyn sl)) $fT $prog)
      let ls ← (← loops.get).mapM fun l => do
        let ab (e : Expr) : MetaM Expr := do
          let e' ← mkLambdaFVars #[x] (← instantiateMVars e)
          if e'.hasFVar then throwError "wa_compile: a loop over a computed array is not supported yet"
          return e'
        return { l with g := ← ab l.g, P := ← ab l.P, μ := ← ab l.μ }
      return .inr (prog, ls)
    catch ex =>
      if let .internal id _ := ex then
        if id == waHoistExc then
          let some key ← waHoistRef.get | throw ex
          return .inl (key.abstract #[x])
      throw ex

def addFn (n : Name) (e : Expr) : TermElabM Unit := do
  let e ← instantiateMVars e
  let ty ← inferType e
  let d := Declaration.defnDecl (mkDefinitionValEx n [] ty e .abbrev .safe [n])
  if (← isProp ty) || (← isProp (← forallTelescope ty fun _ b => pure b)) then addDecl d else addAndCompile d
  enableRealizationsForConst n

set_option hygiene false in
macro "wa_step " P:ident μ:ident : tactic => `(tactic| (
  simp only [$P:ident, $μ:ident] at hP ⊢
  wa_dsimp
  split at h
  · injection h with h; subst h; wa_dsimp; omega
  · cases h))

def seqT (ts : Array (TSyntax `tactic)) : MacroM (TSyntax `tactic) := do
  let mut t ← `(tactic| skip)
  for x in ts.reverse do t ← `(tactic| ($x:tactic; $t:tactic))
  return t

set_option hygiene false in
elab_rules : command
  | `(wa_compile $f:ident) => do
    let fn ← liftCoreM <| realizeGlobalConstNoOverload f
    let (t, stages, ls, names) ← liftTermElabM do
      let info ← getConstInfo fn
      let ba := Lean.mkConst ``ByteArray
      let t ← forallTelescope info.type fun xs b => do
        unless xs.size == 1 && (← isDefEq (← inferType xs[0]!) ba) do
          throwError "wa_compile: expected a function of one ByteArray"
        let some t ← tyOf? b | throwError "wa_compile: result type {b} is not a scalar"
        return t
      let names ← IO.mkRef (#[] : Array Name)
      let loops ← IO.mkRef (#[] : Array LoopRec)
      let mut hoisted : Array Expr := #[]
      let mut res : Option (Term × Array LoopRec) := none
      for _ in [0:16] do
        names.set #[]; loops.set #[]
        match ← reifyEntry fn t hoisted names loops with
        | .inl k => hoisted := hoisted.push k
        | .inr p => res := some p; break
      let some (prog, ls) := res | throwError "wa_compile: too many hoisted arrays"
      let pty ← elabTerm (← `(Pg [Sl.ar AK.ba] (Sl.sc $(← tySyn t)))) none
      let progE ← elabTermEnsuringType prog pty
      synthesizeSyntheticMVarsNoPostponing
      addFn (fn ++ `wa) (← instantiateMVars progE)
      for h : k in [0:ls.size] do
        let l := ls[k]
        addFn (fn ++ Name.mkSimple s!"g{k}") l.g
        addFn (fn ++ Name.mkSimple s!"P{k}") l.P
        addFn (fn ++ Name.mkSimple s!"μ{k}") l.μ
      logInfo m!"wa_compile: {fn}: {hoisted.size} hoisted, {ls.size} loops, unfolded {← names.get}"
      return (t, ← waStagesRef.get, ls, ← names.get)
    let fI := mkIdent fn
    let wa := mkIdent (fn ++ `wa)
    let unf : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      (names.push fn).mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
    let xsI := mkIdent `xs
    -- the proof of `Good`, stage by stage
    let rec good : List Stage → CommandElabM Term
      | [] => throwError "wa_compile: no result"
      | .retS :: _ => `(⟨by simp only [$unf,*, foldl_foldGo]; wa_dsimp; try rfl, by wa_okt⟩)
      | .letS :: rest => do `(⟨by wa_okt, $(← good rest)⟩)
      | .loopS k _ :: rest => do
        let l := ls[k]!
        let g := mkIdent (fn ++ Name.mkSimple s!"g{k}")
        let P := mkIdent (fn ++ Name.mkSimple s!"P{k}")
        let μ := mkIdent (fn ++ Name.mkSimple s!"μ{k}")
        let st ← liftTermElabM (introState l.Δ #[mkIdent `hP])
        let st2 ← liftTermElabM (introState l.Δ #[mkIdent `s', mkIdent `hP, mkIdent `h])
        let st3 ← liftTermElabM (introState l.Δ #[mkIdent `hP])
        let okall ← `(tactic| ($(← liftMacroM (seqT st)); simp only [$P:ident] at hP; wa_dsimp; wa_close))
        let step ← `(tactic| ($(← liftMacroM (seqT st2)); wa_step $P $μ))
        let heq ← `(tactic| ($(← liftMacroM (seqT st3)); simp only [$g:ident]; rw [foldGo]; wa_dsimp; simp only [$g:ident, $unf,*, ← getElem!_pos, dite_eq_ite, decide_eq_true_eq]))
        let p0 ← `(tactic| (simp only [$P:ident]; wa_dsimp; omega))
        let sq (t : TSyntax `tactic) : CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) :=
          `(Lean.Parser.Tactic.tacticSeq| $t:tactic)
        `(⟨by wa_okt, _, $P $xsI, by $(← sq p0), by $(← sq okall), by $(← sq step),
            runs_of _ _ ($g $xsI) ($P $xsI) ($μ $xsI) (by $(← sq heq)) (by $(← sq step)) _ (by $(← sq p0)),
            $(← good rest)⟩)
    let pf ← good stages.toList
    let goodN := mkIdent (fn ++ `good)
    elabCommand (← `(set_option maxRecDepth 100000 in
      theorem $goodN:ident : ∀ (xs : ByteArray), xs.size < 2 ^ 32 → ($wa).Good (xs, ()) ($fI xs) := by
        intro xs hx
        have hds : xs.data.size = xs.size := rfl
        exact $pf))
    let βT ← liftTermElabM (tyTypeSyn t)
    let code := mkIdent (fn ++ `code)
    let impl := mkIdent (fn ++ `implements1)
    elabCommand (← `(def $code:ident : List (BitVec 32) := waCode $wa (Proven.Frontx.Res.k $βT)))
    elabCommand (← `(set_option maxRecDepth 100000 in
      theorem $impl:ident : Proven.Implements1With (fun xs : ByteArray => xs.data.toList) Proven.Frontx.Res.enc $code $fI
          (fun _ => 8 * wholeW $wa [inLoc] + 8 * (wholeN $wa (Proven.Frontx.Res.k $βT) + 1) + 7) :=
        implements1_wa (β := $βT) $fI $wa id (fun _ => rfl) (by decide) (by decide +kernel) (by decide +kernel)
          (by decide +kernel) (by decide +kernel) (fun xs hx => ⟨_, $goodN xs hx, rfl⟩)))

end Proven.WA
