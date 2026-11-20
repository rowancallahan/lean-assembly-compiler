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
import Legacy.Riscv.Frontx.WaImpl

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

/-! ## `a ++ b` as a loop of pushes (paged mode) -/

def appendGo (b : ByteArray) (i : Nat) (acc : ByteArray) : ByteArray :=
  if i < b.size then appendGo b (i + 1) (acc.push b[i]!) else acc
termination_by b.size - i

theorem appendGo_eq (b : ByteArray) : ∀ i acc, appendGo b i acc = acc ++ b.extract i b.size := by
  intro i acc
  induction h : b.size - i generalizing i acc with
  | zero =>
    rw [appendGo, if_neg (by omega)]
    apply ByteArray.ext; simp; omega
  | succ n ih =>
    rw [appendGo, if_pos (by omega), ih (i + 1) _ (by omega)]
    apply ByteArray.ext
    simp only [ByteArray.data_append, ByteArray.data_push, ByteArray.data_extract]
    rw [getElem!_pos b i (by omega)]
    apply Array.toList_inj.1
    simp only [Array.toList_append, Array.toList_push, Array.toList_extract, List.append_assoc,
      List.singleton_append]
    congr 1
    have hi : i < b.data.toList.length := by
      rw [Array.length_toList]; show i < b.size; omega
    simp only [List.extract_eq_take_drop]
    rw [List.drop_eq_getElem_cons hi]
    have e : b.size - i = (b.size - (i + 1)) + 1 := by omega
    rw [e, List.take_succ_cons]
    congr 1

/-- `a.push x` as a loop of one push (paged mode) -/
def pushGo (x : UInt8) (i : Nat) (acc : ByteArray) : ByteArray :=
  if i < 1 then pushGo x (i + 1) (acc.push x) else acc
termination_by 1 - i

theorem pushGo_eq (x : UInt8) (acc : ByteArray) : pushGo x 0 acc = acc.push x := by
  rw [pushGo, if_pos (by omega), pushGo, if_neg (by omega)]

/-- `a ++ b` is the loop from a copy of `a` -/
theorem append_appendGo (a b : ByteArray) : a ++ b = appendGo b 0 (a.extract 0 a.size) := by
  rw [appendGo_eq, ByteArray.extract_zero_size, ByteArray.extract_zero_size]

theorem ByteArray.get!_eq' (a : ByteArray) (i : Nat) : a.get! i = a[i]! := by
  cases a with
  | mk bs =>
    simp only [ByteArray.get!]
    by_cases h : i < bs.size
    · rw [getElem!_pos bs i h, getElem!_pos (ByteArray.mk bs) i (by simpa [ByteArray.size] using h)]; rfl
    · rw [getElem!_neg bs i h, getElem!_neg (ByteArray.mk bs) i (by simpa [ByteArray.size] using h)]

/-! ## Closing the side conditions -/

theorem wa_mul_lt64 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) : a * b < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) (by decide)
theorem wa_gcd_lt {a b B : Nat} (ha : a < B) (hb : b < B) : Nat.gcd a b < B := by
  by_cases h : a = 0
  · subst h; rw [Nat.gcd_zero_left]; exact hb
  · exact Nat.lt_of_le_of_lt (Nat.gcd_le_left b (Nat.pos_of_ne_zero h)) ha

open Lean Meta Elab Tactic in
/-- facts `omega` cannot find by itself: the bounds of `%` and `/` by a variable (`Nat`) and of `UInt8.toNat`;
`==` on `Nat` as `=` -/
elab "wa_facts" : tactic => withMainContext do
  let mut es : Array Expr := #[← getMainTarget]
  for d in ← getLCtx do
    if !d.isImplementationDetail then es := es.push (← instantiateMVars d.type)
  let mut mods : Array (Expr × Expr) := #[]
  let mut divs : Array (Expr × Expr) := #[]
  let mut u8s : Array Expr := #[]
  let mut muls : Array (Expr × Expr) := #[]
  let mut gcds : Array (Expr × Expr) := #[]
  let all ← es.foldlM (init := (#[] : Array Expr)) fun acc e => do
    let mut acc := acc
    let mut todo := #[e]
    while h : todo.size > 0 do
      let x := todo.back
      todo := todo.pop
      acc := acc.push x
      match x with
      | .app f a => todo := todo.push f |>.push a
      | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
      | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
      | .mdata _ b => todo := todo.push b
      | _ => pure ()
    return acc
  for x in all do
    if x.hasLooseBVars then continue
    if x.isAppOfArity ``HMod.hMod 6 && (x.getArg! 0).isConstOf ``Nat then
      unless mods.contains (x.getArg! 4, x.getArg! 5) do mods := mods.push (x.getArg! 4, x.getArg! 5)
    if x.isAppOfArity ``HDiv.hDiv 6 && (x.getArg! 0).isConstOf ``Nat then
      unless divs.contains (x.getArg! 4, x.getArg! 5) do divs := divs.push (x.getArg! 4, x.getArg! 5)
    if x.isAppOfArity ``UInt8.toNat 1 then
      unless u8s.contains (x.getArg! 0) do u8s := u8s.push (x.getArg! 0)
    if x.isAppOfArity ``HMul.hMul 6 && (x.getArg! 0).isConstOf ``Nat && !(x.getArg! 4).isAppOf ``OfNat.ofNat &&
        !(x.getArg! 5).isAppOf ``OfNat.ofNat then
      unless muls.contains (x.getArg! 4, x.getArg! 5) do muls := muls.push (x.getArg! 4, x.getArg! 5)
    if x.isAppOfArity ``Nat.gcd 2 then
      unless gcds.contains (x.getArg! 0, x.getArg! 1) do gcds := gcds.push (x.getArg! 0, x.getArg! 1)
  for (a, b) in mods do
    let (a, b) := (← Term.exprToSyntax a, ← Term.exprToSyntax b)
    evalTactic (← `(tactic| have := Nat.mod_le $a $b))
    evalTactic (← `(tactic| have := fun h : 0 < $b => Nat.mod_lt $a h))
  for (a, b) in divs do
    let (a, b) := (← Term.exprToSyntax a, ← Term.exprToSyntax b)
    evalTactic (← `(tactic| have := Nat.div_le_self $a $b))
  for a in u8s do
    let a ← Term.exprToSyntax a
    evalTactic (← `(tactic| have := UInt8.toNat_lt $a))
  evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only [beq_iff_eq, bne_iff_ne, ne_eq] at *))
  for (a, b) in muls do
    let (a, b) := (← Term.exprToSyntax a, ← Term.exprToSyntax b)
    evalTactic (← `(tactic| try have := wa_mul_lt64 (a := $a) (b := $b) (by omega) (by omega)))
  for (a, b) in gcds do
    let (a, b) := (← Term.exprToSyntax a, ← Term.exprToSyntax b)
    evalTactic (← `(tactic| try have := wa_gcd_lt (a := $a) (b := $b) (B := 2 ^ 64) (by omega) (by omega)))

macro "wa_close" : tactic => `(tactic| (
  simp (config := { failIfUnchanged := false }) only [true_and, and_true, true_implies, Bool.false_eq_true, false_implies, decide_eq_true_eq, implies_true,
    and_self, ite_true, ite_false, Bool.true_eq_false] at ⊢
  repeat' (first | (apply And.intro) | split | intro)
  all_goals (first | trivial | assumption | omega | (wa_facts; omega) | simp_all | skip)))

/-! ## Reflection -/

def tySyn : Ty → MetaM Term
  | .u8 => `(Ty.u8) | .u16 => `(Ty.u16) | .u32 => `(Ty.u32) | .u64 => `(Ty.u64) | .nat => `(Ty.nat)
  | .bool => `(Ty.bool) | .int => `(Ty.int)

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
  if T.isConstOf ``Int then return some .int
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
/-- paged mode (`wp_compile`, `WpCmd.lean`): loop states copied from a read-only array, `extract` and `++` stages -/
initialize waPagedRef : IO.Ref Bool ← IO.mkRef false
/-- the values of the program's `let`s (newest last), to state loop functions over the input only -/
initialize waLetValsRef : IO.Ref (Array (Expr × Expr)) ← IO.mkRef #[]

/-- replace the program's `let` variables by their values -/
def substLets (e : Expr) : MetaM Expr := do
  let mut e := e
  for (x, v) in (← waLetValsRef.get).reverse do
    e := e.replaceFVar x v
  return e

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

/-- core library functions compiled as code (unfolded / loops) rather than treated as primitives -/
def coreCode : List Name := [``Nat.gcd, ``Nat.lcm]

/-- is `c` a definition we may unfold (not one of ours, not recursive) -/
def unfoldable (c : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo _) := env.find? c | return false
  if (`Proven).isPrefixOf c then return false
  if env.isProjectionFn c then return false
  -- library code of Lean itself (`Init`, `Std`, `Lean`) is a primitive here, never unfolded
  if let some idx := env.getModuleIdxFor? c then
    let m := env.header.moduleNames[idx.toNat]!
    if ((`Init).isPrefixOf m || (`Std).isPrefixOf m || (`Lean).isPrefixOf m) && !coreCode.contains c then return false
  -- structural / well-founded recursion leaves an equation mentioning the constant itself
  if env.contains (c ++ `_unary) then return false
  if let some (.defnInfo d) := env.find? c then
    if (d.value.find? fun e => e.isConstOf ``WellFounded.fix || e.isConstOf ``WellFounded.Nat.fix ||
        (e.constName?.map (fun n => n.isStr && (n.getString! == "brecOn" || n.getString! == "rec"))).getD false).isSome then
      return false
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
  -- `Int`: `-x` is `0 - x`; `Int.ediv` / `Int.emod` are `/` / `%`; `Int.toNat`, `Nat` → `Int`
  if c == ``Neg.neg && args.size == 3 then
    let (a, t) ← reifyE ctx args[2]!
    if t == .int then return (← `(E.bin Op2.sub (E.lit Ty.int 0) $a), .int)
  if (c == ``Int.ediv || c == ``Int.emod) && args.size == 2 then
    let (a, _) ← reifyE ctx args[0]!; let (b, _) ← reifyE ctx args[1]!
    return (← if c == ``Int.ediv then `(E.bin Op2.div $a $b) else `(E.bin Op2.mod $a $b), .int)
  if c == ``Int.toNat && args.size == 1 then
    let (a, _) ← reifyE ctx args[0]!
    return (← `(E.cast Ty.nat $a), .nat)
  if (c == ``Int.ofNat && args.size == 1) || ((c == ``Nat.cast || c == ``NatCast.natCast) && args.size == 3 &&
      (← whnfR args[0]!).isConstOf ``Int) then
    let (a, _) ← reifyE ctx args.back!
    return (← `(E.cast Ty.int $a), .int)
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
  if c == ``ByteArray.get! && args.size == 2 then
    return ← reifyGet ctx args[0]! args[1]! true
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

/-- an in-place update of an array of the environment -/
partial def reifyA (ctx : List Ent) (e : Expr) : TermElabM Term := do
  let e := (← instantiateMVars e).consumeMData
  if let .letE _ _ v b _ := e then return ← reifyA ctx (b.instantiate1 v)
  if let some (i, .ar _) ← Ent.find? ctx e then return ← `(A.var $(← memSyn i))
  let f := e.getAppFn; let args := e.getAppArgs
  let some c := f.constName? | throwError "wa_compile: unsupported array update {e}"
  if (c == ``Array.set! && args.size == 4) || (c == ``ByteArray.set! && args.size == 3) then
    let n := args.size
    let a ← reifyA ctx args[n - 3]!
    let (i, _) ← reifyE ctx args[n - 2]!
    let (x, _) ← reifyE ctx args[n - 1]!
    return ← `(A.set $a $i $x)
  if (c == ``Array.push && args.size == 3) || (c == ``ByteArray.push && args.size == 2) then
    let n := args.size
    let a ← reifyA ctx args[n - 2]!
    let (x, _) ← reifyE ctx args[n - 1]!
    return ← `(A.push $a $x)
  if c == ``ite && args.size == 5 then
    return ← `(A.ite $(← reifyP ctx args[1]!) $(← reifyA ctx args[3]!) $(← reifyA ctx args[4]!))
  throwError "wa_compile: unsupported array update {e}"

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
          acc ← `(Args.cons $(← reifyA ctx a) $acc)
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
  /-- the function whose equation is the loop body -/
  un : Name := ``foldGo
  deriving Inhabited

/-- invariants and measures for the user loops (in order), as functions of the loop function's arguments -/
initialize waHintsRef : IO.Ref (Array (Expr × Expr)) ← IO.mkRef #[]

/-- a call of a recursive user definition (a loop) -/
def userLoop? (e : Expr) : MetaM (Option Name) := do
  let some c := e.getAppFn.constName? | return none
  if (`Proven).isPrefixOf c then return none
  let env ← getEnv
  let some (.defnInfo _) := env.find? c | return none
  if let some idx := env.getModuleIdxFor? c then
    let m := env.header.moduleNames[idx.toNat]!
    if ((`Init).isPrefixOf m || (`Std).isPrefixOf m || (`Lean).isPrefixOf m) && !coreCode.contains c then return none
  if ← unfoldable c then return none
  return some c

/-- a loop body: the right-hand side of the equation of `fn` -/
partial def reifyT (ctx : List Ent) (fn : Name) (Δ : List Sl) (R : Sl) (e : Expr) (names : IO.Ref (Array Name))
    (keep : Option (Array Nat) := none) : TermElabM Term := do
  let e ← prepTop e names
  match e with
  | .letE n t v b _ =>
    match ← slOf? t with
    | some (.sc ty) =>
      let (vt, _) ← reifyE ctx v
      withLocalDeclD n t fun x => do
        let k ← reifyT (⟨x, .sc ty⟩ :: ctx) fn Δ R (b.instantiate1 x) names keep
        `(T.let_ $vt $k)
    | _ => reifyT ctx fn Δ R (b.instantiate1 v) names keep
  | _ =>
    if e.isAppOf fn then
      let as := e.getAppArgs
      let as := match keep with | some ks => ks.toList.map (as[·]!) | none => as.toList
      return ← reifyCall ctx Δ as names
    let args := e.getAppArgs
    if e.isAppOfArity ``ite 5 then
      return ← `(T.ite $(← reifyP ctx args[1]!) $(← reifyT ctx fn Δ R args[3]! names keep) $(← reifyT ctx fn Δ R args[4]! names keep))
    if e.isAppOfArity ``dite 5 then
      let a ← withLocalDeclD `h args[1]! fun h => reifyT ctx fn Δ R (args[3]!.beta #[h]) names keep
      let b ← withLocalDeclD `h (mkNot args[1]!) fun h => reifyT ctx fn Δ R (args[4]!.beta #[h]) names keep
      return ← `(T.ite $(← reifyP ctx args[1]!) $a $b)
    match R with
    | .sc _ => let (t, _) ← reifyE ctx e; `(T.ret $t)
    | .ar _ => `(T.ret $(← reifyA ctx e))

/-- the initial value of an array slot of a loop -/
partial def reifyF (ctx : List Ent) (e : Expr) (modified : Bool := false) : TermElabM Term := do
  let e := (← instantiateMVars e).consumeMData
  if let some (i, .ar k) ← Ent.find? ctx e then
    -- paged: a `ByteArray` state that the loop changes starts as a copy (`xs.extract 0 xs.size = xs`)
    if (← waPagedRef.get) && modified && k == .ba then
      let m ← memSyn i
      return ← `(F.extract $m (E.lit Ty.nat 0) (E.size $m))
    return ← `(F.alias $(← memSyn i))
  let args := e.getAppArgs
  if e.isAppOfArity ``Array.replicate 3 then
    let (n, _) ← reifyE ctx args[1]!; let (x, _) ← reifyE ctx args[2]!
    return ← `(F.rep $n $x)
  if e.isAppOfArity ``ByteArray.data 1 then
    let (m, _) ← arr ctx args[0]!
    return ← `(F.data $(← memSyn m))
  let (m, sl) ← arr ctx e
  if (← waPagedRef.get) && modified && sl == .ar .ba then
    let mm ← memSyn m
    return ← `(F.extract $mm (E.lit Ty.nat 0) (E.size $mm))
  `(F.alias $(← memSyn m))

/-- `p.f` / `S.f p` of a constructor application `p = S.mk a…`: the field `a` -/
def projCtor? (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  let (i, np, s) ← match e with
    | .proj _ i s => pure (i, 0, s)
    | _ =>
      let some c := e.getAppFn.constName? | return none
      let some pi := (← getEnv).getProjectionFnInfo? c | return none
      if pi.fromClass || e.getAppNumArgs != pi.numParams + 1 then return none
      pure (pi.i, pi.numParams, e.appArg!)
  let s := s.consumeMData.headBeta
  let some c := s.getAppFn.constName? | return none
  let some (.ctorInfo ci) := (← getEnv).find? c | return none
  unless isStructure (← getEnv) ci.induct && s.getAppNumArgs == ci.numParams + ci.numFields do return none
  let _ := np
  return some (s.getArg! (ci.numParams + i))

/-- every projection of a constructor application in `e` reduced -/
def normPC (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun t => do
    if let some t' ← projCtor? t then return .visit t' else return .done t)

/-- `let x : S := S.mk a…; b` (S a structure): `let f₁ := a₁; …; b[x := S.mk f₁ …]`, projections reduced -/
def splitStructLet? (t v b : Expr) : MetaM (Option Expr) := do
  let some sn := (← whnfR t).getAppFn.constName? | return none
  unless isStructure (← getEnv) sn do return none
  let v := v.consumeMData.headBeta
  let some c := v.getAppFn.constName? | return none
  let some (.ctorInfo ci) := (← getEnv).find? c | return none
  unless ci.induct == sn && v.getAppNumArgs == ci.numParams + ci.numFields do return none
  let fields := (v.getAppArgs.extract ci.numParams v.getAppNumArgs)
  let names := getStructureFields (← getEnv) sn
  let rec go (i : Nat) (fs : Array Expr) : MetaM Expr := do
    if h : i < fields.size then
      let a := fields[i]
      let ty ← inferType a
      -- proofs and atoms are substituted, other fields get a `let`
      if (← isProof a) || a.isFVar || a.isConst || a.isLit then return ← go (i + 1) (fs.push a)
      withLetDecl (names[i]?.getD `f) ty a fun x => do
        let r ← go (i + 1) (fs.push x)
        mkLetFVars #[x] r (usedLetOnly := false)
    else
      normPC (b.instantiate1 (mkAppN v.getAppFn (v.getAppArgs.extract 0 ci.numParams ++ fs)))
  return some (← go 0 #[])

/-- paged: a loop call `fn … a …` with a computed `ByteArray` argument `a` becomes `let t := a; fn … t …` -/
def nameArrayArg? (ctx : List Ent) (e : Expr) : MetaM (Option Expr) := do
  let args := e.getAppArgs
  for h : j in [0:args.size] do
    let a := args[j]
    if a.hasLooseBVars then continue
    let ty ← inferType a
    unless (← whnfR ty).isConstOf ``ByteArray do continue
    if (← Ent.find? ctx a).isSome then continue
    if a.isFVar then continue
    let args' := args.mapIdx fun i x => if i == j then .bvar 0 else x.liftLooseBVars 0 1
    return some (.letE `t ty a (mkAppN e.getAppFn args') false)
  return none

/-- the stages of a program -/
partial def reifyPg (ctx : List Ent) (e : Expr) (R : Sl) (names : IO.Ref (Array Name)) (loops : IO.Ref (Array LoopRec)) :
    TermElabM Term := do
  let e ← prepTop e names
  match e with
  | .letE n t v b _ =>
    -- a structure built by its constructor: one `let` per field, the projections of the constructor reduce
    if let some e' ← splitStructLet? t (← prepTop v names) b then
      return ← reifyPg ctx e' R names loops
    let some sl ← slOf? t | throwError "wa_compile: unsupported let type {t}"
    let v' ← prepTop v names
    -- `let x := (let y := a; B); K` ⇒ `let y := a; let x := B; K` (a helper's arguments, then its loop)
    if let .letE n2 t2 v2 b2 _ := v' then
      return ← reifyPg ctx (.letE n2 t2 v2 (.letE n (t.liftLooseBVars 0 1) b2 (b.liftLooseBVars 1 1) false) false)
        R names loops
    if (← waPagedRef.get) && sl == .ar .ba then
      -- paged: `a ++ b` is a loop of pushes onto a copy of `a`; both arrays named first
      if v'.isAppOfArity ``HAppend.hAppend 6 then
        let a := v'.getArg! 4; let bb := v'.getArg! 5
        if (← Ent.find? ctx bb).isNone then
          return ← reifyPg ctx (.letE `t t bb (.letE n t (mkAppN v'.getAppFn ((v'.getAppArgs.extract 0 4).push
            (a.liftLooseBVars 0 1) |>.push (.bvar 0))) (b.liftLooseBVars 1 1) false) false) R names loops
        if (← Ent.find? ctx a).isNone then
          return ← reifyPg ctx (.letE `t t a (.letE n t (mkAppN v'.getAppFn ((v'.getAppArgs.extract 0 4).push
            (.bvar 0) |>.push (bb.liftLooseBVars 0 1))) (b.liftLooseBVars 1 1) false) false) R names loops
        let lp ← reifyAppend ctx a bb loops
        waStagesRef.modify (·.push (.loopS ((← loops.get).size - 1) [.sc .nat]))
        return ← withLocalDeclD n t fun x => do
          waLetValsRef.modify (·.push (x, v'))
          let k ← reifyPg (⟨x, sl⟩ :: ctx) (b.instantiate1 x) R names loops
          `($lp $k)
      -- `a.push x`: one push onto a copy of `a`
      if v'.isAppOfArity ``ByteArray.push 2 then
        let a := v'.getArg! 0
        if (← Ent.find? ctx a).isNone then
          return ← reifyPg ctx (.letE `t t a (.letE n t (mkApp2 v'.getAppFn (.bvar 0) ((v'.getArg! 1).liftLooseBVars 0 1))
            (b.liftLooseBVars 1 1) false) false) R names loops
        let lp ← reifyPushOnce ctx a (v'.getArg! 1) loops
        waStagesRef.modify (·.push (.loopS ((← loops.get).size - 1) [.sc .nat]))
        return ← withLocalDeclD n t fun x => do
          waLetValsRef.modify (·.push (x, v'))
          let k ← reifyPg (⟨x, sl⟩ :: ctx) (b.instantiate1 x) R names loops
          `($lp $k)
      -- `a.extract lo hi`: a fresh array
      if v'.isAppOfArity ``ByteArray.extract 3 then
        let (m, _) ← arr ctx (v'.getArg! 0)
        let (lo, _) ← reifyE ctx (v'.getArg! 1)
        let (hi, _) ← reifyE ctx (v'.getArg! 2)
        waStagesRef.modify (·.push .letS)
        return ← withLocalDeclD n t fun x => do
          waLetValsRef.modify (·.push (x, v'))
          let k ← reifyPg (⟨x, sl⟩ :: ctx) (b.instantiate1 x) R names loops
          `(Pg.let_ (s := Sl.ar AK.ba) (F.extract $(← memSyn m) $lo $hi) $k)
    if (← waPagedRef.get) && (← userLoop? v').isSome then
      if let some v2 ← nameArrayArg? ctx v' then
        return ← reifyPg ctx (.letE n t v2 b false) R names loops
    if v'.isAppOfArity ``Array.foldl 7 || (← userLoop? v').isSome then
      withLocalDeclD n t fun x => do
        let lp ← if v'.isAppOfArity ``Array.foldl 7 then reifyFold ctx v' names loops else reifyLoop ctx v' sl names loops
        waStagesRef.modify (·.push (.loopS ((← loops.get).size - 1) [.sc .nat]))
        waLetValsRef.modify (·.push (x, v'))
        let k ← reifyPg (⟨x, sl⟩ :: ctx) (b.instantiate1 x) R names loops
        `($lp $k)
    else
      match sl with
      | .sc ty =>
        let (vt, _) ← reifyE ctx v
        waStagesRef.modify (·.push .letS)
        withLocalDeclD n t fun x => do
          waLetValsRef.modify (·.push (x, v))
          let k ← reifyPg (⟨x, .sc ty⟩ :: ctx) (b.instantiate1 x) R names loops
          `(Pg.let_ (s := $(← slSyn sl)) $vt $k)
      | _ => reifyPg ctx (b.instantiate1 v) R names loops
  | _ =>
    if e.isAppOfArity ``Array.foldl 7 then
      let lp ← reifyFold ctx e names loops
      waStagesRef.modify (·.push (.loopS ((← loops.get).size - 1) [.sc .nat]))
      waStagesRef.modify (·.push .retS)
      return ← `($lp (Pg.ret (E.var Mem.hd)))
    if (← waPagedRef.get) && (← userLoop? e).isSome then
      if let some e2 ← nameArrayArg? ctx e then
        return ← reifyPg ctx e2 R names loops
    if (← userLoop? e).isSome then
      let lp ← reifyLoop ctx e R names loops
      waStagesRef.modify (·.push (.loopS ((← loops.get).size - 1) [.sc .nat]))
      waStagesRef.modify (·.push .retS)
      match R with
      | .sc _ => return ← `($lp (Pg.ret (E.var Mem.hd)))
      | .ar _ => return ← `($lp (Pg.ret (A.var Mem.hd)))
    if let .ar k := R then
      if let some (i, .ar _) ← Ent.find? ctx e then
        waStagesRef.modify (·.push .retS)
        return ← `(Pg.ret (A.var $(← memSyn i)))
      if (← waPagedRef.get) && k == .ba then
        -- a computed `ByteArray` result: named first
        return ← reifyPg ctx (.letE `r (← inferType e) e (.bvar 0) false) R names loops
    let (t, _) ← reifyE ctx e
    waStagesRef.modify (·.push .retS)
    `(Pg.ret $t)
where
  /-- `a.push x` (`a` of the environment): a loop over `(acc, i)` from a copy of `a`, one push of `x` -/
  reifyPushOnce (ctx : List Ent) (a xE : Expr) (loops : IO.Ref (Array LoopRec)) : TermElabM Term := do
    let (ma, _) ← arr ctx a
    let ma' ← memSyn ma
    let Δ : List Sl := [.ar .ba, .sc .nat]
    let body ← withLocalDeclD `acc (mkConst ``ByteArray) fun acc => withLocalDeclD `i (mkConst ``Nat) fun i => do
      let (xt, _) ← reifyE (⟨acc, .ar .ba⟩ :: ⟨i, .sc .nat⟩ :: ctx) xE
      `(T.ite (E.cmp Cmp.lt (E.var (Mem.tl Mem.hd)) (E.lit Ty.nat 1))
        (T.call (Args.cons (A.push (A.var Mem.hd) $xt)
          (Args.cons (E.bin Op2.add (E.var (Mem.tl Mem.hd)) (E.lit Ty.nat 1)) Args.nil)))
        (T.ret (A.var Mem.hd)))
    let init ← `(Inis.cons (F.extract $ma' (E.lit Ty.nat 0) (E.size $ma')) (Inis.cons (E.lit Ty.nat 0) Inis.nil))
    let sT ← mkAppM ``Vals #[← toListSl Δ]
    let xz ← substLets xE
    let az ← substLets a
    let iOf (s : Expr) : MetaM Expr := do mkAppM ``Prod.fst #[← mkAppM ``Prod.snd #[s]]
    let gE ← withLocalDeclD `s sT fun s => do
      mkLambdaFVars #[s] (← mkAppM ``pushGo #[xz, ← iOf s, ← mkAppM ``Prod.fst #[s]])
    let PE ← withLocalDeclD `s sT fun s => do
      let i ← iOf s
      let accs ← mkAppM ``ByteArray.size #[← mkAppM ``Prod.fst #[s]]
      let c1 ← mkAppM ``LE.le #[i, mkNatLit 1]
      let c2 ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[accs, ← mkAppM ``HSub.hSub #[mkNatLit 1, i]],
        ← mkAppM ``HAdd.hAdd #[← mkAppM ``ByteArray.size #[az], mkNatLit 1]]
      mkLambdaFVars #[s] (mkAnd c1 (mkAnd c2 (← mkAppM ``LE.le #[← mkAppM ``ByteArray.size #[az], mkNatLit 1048575])))
    let μE ← withLocalDeclD `s sT fun s => do
      mkLambdaFVars #[s] (← mkAppM ``HSub.hSub #[mkNatLit 1, ← iOf s])
    loops.modify (·.push ⟨gE, PE, μE, Δ, ``pushGo⟩)
    `(Pg.loop [Sl.ar AK.ba, Sl.sc Ty.nat] $body $init)
  /-- `a ++ b` (both arrays of the environment): a loop over `(acc, i)` from a copy of `a`, pushing `b[i]` -/
  reifyAppend (ctx : List Ent) (a bb : Expr) (loops : IO.Ref (Array LoopRec)) : TermElabM Term := do
    let (ma, _) ← arr ctx a
    let (mb, _) ← arr ctx bb
    let ma' ← memSyn ma
    let mb2 ← memSyn (mb + 2)
    let body ← `(T.ite (E.cmp Cmp.lt (E.var (Mem.tl Mem.hd)) (E.size $mb2))
      (T.call (Args.cons (A.push (A.var Mem.hd) (E.getB $mb2 (E.var (Mem.tl Mem.hd)) false))
        (Args.cons (E.bin Op2.add (E.var (Mem.tl Mem.hd)) (E.lit Ty.nat 1)) Args.nil)))
      (T.ret (A.var Mem.hd)))
    let init ← `(Inis.cons (F.extract $ma' (E.lit Ty.nat 0) (E.size $ma')) (Inis.cons (E.lit Ty.nat 0) Inis.nil))
    let Δ : List Sl := [.ar .ba, .sc .nat]
    let sT ← mkAppM ``Vals #[← toListSl Δ]
    let bz ← substLets bb
    let iOf (s : Expr) : MetaM Expr := do mkAppM ``Prod.fst #[← mkAppM ``Prod.snd #[s]]
    let gE ← withLocalDeclD `s sT fun s => do
      mkLambdaFVars #[s] (← mkAppM ``appendGo #[bz, ← iOf s, ← mkAppM ``Prod.fst #[s]])
    let PE ← withLocalDeclD `s sT fun s => do
      let i ← iOf s
      let bs ← mkAppM ``ByteArray.size #[bz]
      let accs ← mkAppM ``ByteArray.size #[← mkAppM ``Prod.fst #[s]]
      let c1 ← mkAppM ``LE.le #[i, bs]
      let c2 ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[accs, ← mkAppM ``HSub.hSub #[bs, i]], mkNatLit 1048576]
      mkLambdaFVars #[s] (mkAnd c1 c2)
    let μE ← withLocalDeclD `s sT fun s => do
      mkLambdaFVars #[s] (← mkAppM ``HSub.hSub #[← mkAppM ``ByteArray.size #[bz], ← iOf s])
    loops.modify (·.push ⟨gE, PE, μE, Δ, ``appendGo⟩)
    `(Pg.loop [Sl.ar AK.ba, Sl.sc Ty.nat] $body $init)
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
    loops.modify (·.push ⟨gE, PE, μE, Δ, ``foldGo⟩)
    `(Pg.loop $(← ctxSyn Δ) $body (Inis.cons $it (Inis.cons (E.lit Ty.nat 0) Inis.nil)))
  /-- a call of a recursive user definition `fn args`: a loop over its arguments -/
  reifyLoop (ctx : List Ent) (e : Expr) (R : Sl) (names : IO.Ref (Array Name)) (loops : IO.Ref (Array LoopRec)) :
      TermElabM Term := do
    let some fn ← userLoop? e | throwError "wa_compile: not a loop {e}"
    let args := e.getAppArgs
    let info ← getConstInfo fn
    let us := e.getAppFn.constLevels!
    let some eqn ← getUnfoldEqnFor? fn (nonRec := true) | throwError "wa_compile: no equation for {fn}"
    let eqT := (← getConstInfo eqn).instantiateTypeLevelParams us
    let hints ← waHintsRef.get
    -- the user's loops in order (the paged `++` / `push` loops have their own invariants)
    let k := ((← loops.get).filter fun l => l.un != ``appendGo && l.un != ``pushGo).size
    let some (Pu, μu) := hints[k]? | throwError "wa_compile: loop {k} ({fn}) needs `invariant … measure …`"
    forallTelescope eqT fun ps eq => do
      unless ps.size == args.size do throwError "wa_compile: {fn}: partial application"
      let some (_, _, rhs) := eq.eq? | throwError "wa_compile: equation of {fn}"
      -- `Prop` parameters (proofs) are not state: dropped from the loop, rebuilt in `g` from the invariant
      -- the parameters a recursive call changes
      let calls := collectApps fn rhs
      let modified (j : Nat) : Bool :=
        calls.any fun c => c.getAppNumArgs == ps.size && c.getAppArgs[j]? != some ps[j]!
      let mut Δ : List Sl := []
      let mut keep : Array Nat := #[]
      let mut props : Array Nat := #[]
      -- paged: an array parameter the loop never changes, given an array of the environment, is that array
      let mut dropped : Array Nat := #[]
      for h : j in [0:ps.size] do
        let p := ps[j]
        if ← isProp (← inferType p) then props := props.push j; continue
        let some sl ← slOf? (← inferType p) | throwError "wa_compile: {fn}: unsupported parameter {p}"
        if (← waPagedRef.get) && sl matches .ar _ && !modified j && (← Ent.find? ctx args[j]!).isSome then
          dropped := dropped.push j; continue
        Δ := Δ ++ [sl]; keep := keep.push j
      let rhs := rhs.replaceFVars (dropped.map (ps[·]!)) (dropped.map (args[·]!))
      -- initial values
      let mut init ← `(Inis.nil)
      for (j, sl) in (keep.toList.zip Δ).reverse do
        let a := args[j]!
        match sl with
        | .sc _ => let (t, _) ← reifyE ctx a; init ← `(Inis.cons $t $init)
        | .ar _ => init ← `(Inis.cons $(← reifyF ctx a (modified j)) $init)
      -- the body over the state (first parameter innermost)
      let kps := keep.map (ps[·]!)
      let ctx' := (kps.toList.zip Δ).map (fun (p, sl) => (⟨p, sl⟩ : Ent)) ++ ctx
      let body ← reifyT ctx' fn Δ R rhs names (some keep)
      -- the function, invariant and measure on `Vals Δ`
      let sT ← mkAppM ``Vals #[← toListSl Δ]
      let comps (s : Expr) : MetaM (Array Expr) := do
        let mut out := #[]; let mut cur := s
        for _ in kps do
          out := out.push (← mkAppM ``Prod.fst #[cur]); cur ← mkAppM ``Prod.snd #[cur]
        return out
      let gE ← withLocalDeclD `s sT fun s => do
        let cs ← comps s
        if props.isEmpty then
          let mut full : Array Expr := #[]
          let mut ki := 0
          for j in [0:ps.size] do
            if dropped.contains j then full := full.push args[j]!
            else full := full.push cs[ki]!; ki := ki + 1
          return ← mkLambdaFVars #[s] (mkAppN e.getAppFn full)
        -- `if h : T₁ ∧ … then fn … h.1 … else default`
        let pts ← props.mapM fun j => do
          return ((← inferType ps[j]!).replaceFVars kps cs).replaceFVars (dropped.map (ps[·]!)) (dropped.map (args[·]!))
        let C := pts.pop.foldr (fun t acc => mkAnd t acc) pts.back!
        let RT ← inferType e
        let yes ← withLocalDeclD `h C fun h => do
          let mut pf : Array Expr := #[]
          let mut cur := h
          for i in [0:pts.size] do
            if i + 1 == pts.size then pf := pf.push cur
            else
              pf := pf.push (mkProj ``And 0 cur); cur := mkProj ``And 1 cur
          let mut full : Array Expr := #[]
          let mut ki := 0; let mut pi := 0
          for j in [0:ps.size] do
            if props.contains j then full := full.push pf[pi]!; pi := pi + 1
            else if dropped.contains j then full := full.push args[j]!
            else full := full.push cs[ki]!; ki := ki + 1
          mkLambdaFVars #[h] (mkAppN e.getAppFn full)
        let no ← withLocalDeclD `h (mkNot C) fun h => do
          mkLambdaFVars #[h] (← mkAppOptM ``Inhabited.default #[RT, none])
        let dec ← try synthInstance (mkApp (mkConst ``Decidable) C) catch _ => pure (mkApp (mkConst ``Classical.propDecidable) C)
        mkLambdaFVars #[s] (mkApp5 (mkConst ``dite [← getLevel RT]) RT C dec yes no)
      let PE ← withLocalDeclD `s sT fun s => do
        let cs ← comps s
        let full := (Array.range ps.size).filterMap fun j => (keep.idxOf? j).map (cs[·]!)
        let _ := full
        let mut allArgs : Array Expr := #[]
        let mut ki := 0
        for j in [0:ps.size] do
          if props.contains j then continue
          if dropped.contains j then allArgs := allArgs.push args[j]!; continue
          allArgs := allArgs.push cs[ki]!; ki := ki + 1
        mkLambdaFVars #[s] ((mkAppN Pu allArgs).headBeta)
      let μE ← withLocalDeclD `s sT fun s => do
        let cs ← comps s
        let mut allArgs : Array Expr := #[]
        let mut ki := 0
        for j in [0:ps.size] do
          if props.contains j then continue
          if dropped.contains j then allArgs := allArgs.push args[j]!; continue
          allArgs := allArgs.push cs[ki]!; ki := ki + 1
        mkLambdaFVars #[s] ((mkAppN μu allArgs).headBeta)
      loops.modify (·.push ⟨← substLets gE, ← substLets PE, ← substLets μE, Δ, fn⟩)
      `(Pg.loop $(← ctxSyn Δ) $body $init)
  collectApps (fn : Name) (e : Expr) : Array Expr := Id.run do
    let mut out := #[]
    let mut todo := #[e]
    while h : todo.size > 0 do
      let x := todo.back
      todo := todo.pop
      if x.isAppOf fn then out := out.push x
      match x with
      | .app f a => todo := todo.push f |>.push a
      | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
      | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
      | .mdata _ b => todo := todo.push b
      | _ => pure ()
    return out
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
    | .nat => mkConst ``Ty.nat | .bool => mkConst ``Ty.bool | .int => mkConst ``Ty.int

/-! ## The command -/

theorem u8_lt64 (x : UInt8) : x.toNat < 2 ^ 64 := by have := x.toNat_lt; omega
theorem u16_lt64 (x : UInt16) : x.toNat < 2 ^ 64 := by have := x.toNat_lt; omega
theorem u32_lt64 (x : UInt32) : x.toNat < 2 ^ 64 := by have := x.toNat_lt; omega
theorem u64_lt64 (x : UInt64) : x.toNat < 2 ^ 64 := x.toNat_lt
theorem u8_lt64' (x : UInt8) : x.toNat < 18446744073709551616 := u8_lt64 x
theorem u16_lt64' (x : UInt16) : x.toNat < 18446744073709551616 := u16_lt64 x
theorem u32_lt64' (x : UInt32) : x.toNat < 18446744073709551616 := u32_lt64 x
theorem u64_lt64' (x : UInt64) : x.toNat < 18446744073709551616 := u64_lt64 x

theorem size_ite_set {α : Type} (c : Prop) [Decidable c] (a : Array α) (i : Nat) (x : α) :
    (if c then a.set! i x else a).size = a.size := by split <;> simp
theorem size_set' {α : Type} (a : Array α) (i : Nat) (x : α) : (a.set! i x).size = a.size := by simp

/-- the simp set of the meanings -/
macro "wa_dsimp" : tactic => `(tactic| simp (config := { failIfUnchanged := false }) only [T.ok, T.out, T.den, E.ok, E.den, A.den, A.ok, AK.set, AK.push, Args.ok, Args.den, Arg.den,
  Ini.ok, Ini.den, Inis.ok, Inis.den, F.ok, F.den, Vals.app, Mem.get, AK.size, AK.get, Op2.den, Cmp.den, WA.cast,
  Ty.small, Op2.exact, Op2.side, cast.side, Proven.Frontx.ediv_hdiv, Proven.Frontx.emod_hmod, Int.zero_sub, Int.ofNat_eq_natCast, decide_eq_true_eq, AK.el, size_ite_set, size_set', Array.size_replicate, u8_lt64, u16_lt64, u32_lt64, u64_lt64, u8_lt64', u16_lt64', u32_lt64',
  u64_lt64'] at *)

macro "wa_okt" : tactic => `(tactic| (wa_dsimp <;> wa_close))

def tyTypeSyn : Ty → MetaM Term
  | .u8 => `(UInt8) | .u16 => `(UInt16) | .u32 => `(UInt32) | .u64 => `(UInt64) | .nat => `(Nat) | .bool => `(Bool)
  | .int => `(Int)

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

unsafe def evalChoiceWU (stx : Syntax) : TermElabM (Option (List (Nat × Nat) × List Nat)) := do
  Term.evalTerm _ (← Term.elabType (← `(Option (List (Nat × Nat) × List Nat)))) stx
@[implemented_by evalChoiceWU] opaque evalChoiceW (stx : Syntax) : TermElabM (Option (List (Nat × Nat) × List Nat))
unsafe def evalBoolWU (stx : Syntax) : TermElabM Bool := do
  Term.evalTerm _ (← Term.elabType (← `(Bool))) stx
@[implemented_by evalBoolWU] opaque evalBoolW (stx : Syntax) : TermElabM Bool

syntax "wa_compile " ident (" invariant " term " measure " term)* : command

/-- reify the body of `fn`; `hoisted` are terms over the input (bound variable 0) placed in front -/
def reifyEntry (fn : Name) (R : Sl) (hoisted : Array Expr) (names : IO.Ref (Array Name))
    (loops : IO.Ref (Array LoopRec)) : TermElabM (Sum Expr (Term × Array LoopRec)) := do
  let info ← getConstInfo fn
  let ba := Lean.mkConst ``ByteArray
  waStagesRef.set #[]; waSafeRef.set #[]; waLetValsRef.set #[]
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
      let mut prog ← reifyPg ctx body R names loops
      for (fT, sl) in fronts.reverse do
        prog ← `(Pg.let_ (s := $(← slSyn sl)) $fT $prog)
      let ls ← (← loops.get).mapM fun l => do
        let ab (e : Expr) : MetaM Expr := do
          let e' ← mkLambdaFVars #[x] (← instantiateMVars e)
          if e'.hasFVar then throwError "wa_compile: a loop over a computed array is not supported yet: {e'}"
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
  split at h <;> first
    | (injection h with h; subst h; wa_dsimp; first | omega | (wa_facts; omega))
    | cases h))

def seqT (ts : Array (TSyntax `tactic)) : MacroM (TSyntax `tactic) := do
  let mut t ← `(tactic| skip)
  for x in ts.reverse do t ← `(tactic| ($x:tactic; $t:tactic))
  return t

set_option hygiene false in
elab_rules : command
  | `(wa_compile $f:ident $[invariant $Ps measure $μs]*) => do
    let fn ← liftCoreM <| realizeGlobalConstNoOverload f
    let (R, stages, ls, names) ← liftTermElabM do
      let info ← getConstInfo fn
      let ba := Lean.mkConst ``ByteArray
      let R ← forallTelescope info.type fun xs b => do
        unless xs.size == 1 && (← isDefEq (← inferType xs[0]!) ba) do
          throwError "wa_compile: expected a function of one ByteArray"
        let some R ← slOf? b | throwError "wa_compile: unsupported result type {b}"
        return R
      let mut hints := #[]
      for (P, μ) in Ps.zip μs do
        let Pe ← instantiateMVars (← elabTerm P none); let μe ← instantiateMVars (← elabTerm μ none)
        synthesizeSyntheticMVarsNoPostponing
        hints := hints.push (← instantiateMVars Pe, ← instantiateMVars μe)
      waHintsRef.set hints
      let names ← IO.mkRef (#[] : Array Name)
      let loops ← IO.mkRef (#[] : Array LoopRec)
      let mut hoisted : Array Expr := #[]
      let mut res : Option (Term × Array LoopRec) := none
      for _ in [0:16] do
        names.set #[]; loops.set #[]
        match ← reifyEntry fn R hoisted names loops with
        | .inl k => hoisted := hoisted.push k
        | .inr p => res := some p; break
      let some (prog, ls) := res | throwError "wa_compile: too many hoisted arrays"
      let pty ← elabTerm (← `(Pg [Sl.ar AK.ba] $(← slSyn R))) none
      let progE ← elabTermEnsuringType prog pty
      synthesizeSyntheticMVarsNoPostponing
      addFn (fn ++ `wa) (← instantiateMVars progE)
      for h : k in [0:ls.size] do
        let l := ls[k]
        addFn (fn ++ Name.mkSimple s!"g{k}") l.g
        addFn (fn ++ Name.mkSimple s!"P{k}") l.P
        addFn (fn ++ Name.mkSimple s!"μ{k}") l.μ
      logInfo m!"wa_compile: {fn}: {hoisted.size} hoisted, {ls.size} loops, unfolded {← names.get}"
      return (R, ← waStagesRef.get, ls, ← names.get)
    let fI := mkIdent fn
    let wa := mkIdent (fn ++ `wa)
    let unf : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      (names.push fn).mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
    let xsI := mkIdent `xs
    -- the proof of `Good`, stage by stage
    let rec good : List Stage → CommandElabM Term
      | [] => throwError "wa_compile: no result"
      | .retS :: _ => match R with
        | .sc _ => `(⟨by simp only [$unf,*, foldl_foldGo, ← getElem!_pos, dite_eq_ite]; wa_dsimp; try rfl, by wa_okt⟩)
        | .ar _ => `(by simp only [$unf,*, foldl_foldGo]; wa_dsimp; try rfl)
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
        let unI := mkIdent l.un
        let heq ← `(tactic| ($(← liftMacroM (seqT st3)); simp only [$g:ident]; rw [$unI:ident]; wa_dsimp; simp only [$g:ident, $unf,*, ← getElem!_pos, dite_eq_ite, decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq, bne_iff_ne]))
        let p0 ← `(tactic| (simp only [$P:ident]; wa_dsimp; wa_close))
        let sq (t : TSyntax `tactic) : CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) :=
          `(Lean.Parser.Tactic.tacticSeq| $t:tactic)
        `(⟨by wa_okt, _, $P $xsI, by $(← sq p0), by $(← sq okall), by $(← sq step),
            runs_of _ _ ($g $xsI) ($P $xsI) ($μ $xsI) (by $(← sq heq)) (by $(← sq step)) _ (by $(← sq p0)),
            $(← good rest)⟩)
    let pf ← good stages.toList
    let goodN := mkIdent (`_root_ ++ fn ++ `good)
    elabCommand (← `(set_option maxRecDepth 100000 in set_option backward.isDefEq.respectTransparency false in
      theorem $goodN:ident : ∀ (xs : ByteArray), xs.size < 2 ^ 32 → ($wa).Good (xs, ()) ($fI xs) := by
        intro xs hx
        have hds : xs.data.size = xs.size := rfl
        exact $pf))
    let code := mkIdent (`_root_ ++ fn ++ `code)
    let impl := mkIdent (`_root_ ++ fn ++ `implements1)
    let tblI := mkIdent (`_root_ ++ fn ++ `tbl)
    let splI := mkIdent (`_root_ ++ fn ++ `spl)
    let choice (pick : Term) : CommandElabM Unit := do
      let some (t, sp) ← liftTermElabM (evalChoiceW pick)
        | throwError "wa_compile: no register choice passed optB"
      let ts ← t.toArray.mapM fun (a, b) => `(($(quote a), $(quote b)))
      let ss : Array Term := sp.toArray.map fun j => quote j
      elabCommand (← `(def $tblI:ident : List (Nat × Nat) := [$ts,*]))
      elabCommand (← `(def $splI:ident : List Nat := [$ss,*]))
    match R with
    | .sc t =>
      let βT ← liftTermElabM (tyTypeSyn t)
      if ← liftTermElabM (evalBoolW (← `(MS.hasMop (wholeProg $wa (Proven.Frontx.Res.k $βT))))) then
        choice (← `(waPick $wa (Proven.Frontx.Res.k $βT)))
        elabCommand (← `(def $code:ident : List (BitVec 32) :=
          waCodeC $wa (Proven.Frontx.Res.k $βT) (waTbl $tblI) $splI))
        elabCommand (← `(set_option maxRecDepth 100000 in set_option backward.isDefEq.respectTransparency false in
          theorem $impl:ident : Proven.Implements1With (fun xs : ByteArray => xs.data.toList) Proven.Frontx.Res.enc $code
              $fI (fun _ => 8 * wholeW $wa [inLoc] + 8 * (wholeN $wa (Proven.Frontx.Res.k $βT) + 1) + 7) :=
            implements1_waC (β := $βT) $fI $wa id (fun _ => rfl) (by decide) (by decide +kernel) (by decide +kernel)
              (waTbl $tblI) $splI (by decide +kernel) (by decide +kernel) (fun xs hx => ⟨_, $goodN xs hx, rfl⟩)))
        return
      elabCommand (← `(def $code:ident : List (BitVec 32) := waCode $wa (Proven.Frontx.Res.k $βT)))
      elabCommand (← `(set_option maxRecDepth 100000 in set_option backward.isDefEq.respectTransparency false in
        theorem $impl:ident : Proven.Implements1With (fun xs : ByteArray => xs.data.toList) Proven.Frontx.Res.enc $code
            $fI (fun _ => 8 * wholeW $wa [inLoc] + 8 * (wholeN $wa (Proven.Frontx.Res.k $βT) + 1) + 7) :=
          implements1_wa (β := $βT) $fI $wa id (fun _ => rfl) (by decide) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (fun xs hx => ⟨_, $goodN xs hx, rfl⟩)))
    | .ar k =>
      let kT ← liftTermElabM (match k with | .ba => `(AK.ba) | .arr t => do `(AK.arr $(← tySyn t)))
      if ← liftTermElabM (evalBoolW (← `(MS.hasMop (wholeProgA $wa)))) then
        choice (← `(waPickA $wa))
        elabCommand (← `(def $code:ident : List (BitVec 32) := waCodeAC $wa (waTbl $tblI) $splI))
        elabCommand (← `(set_option maxRecDepth 100000 in set_option backward.isDefEq.respectTransparency false in
          theorem $impl:ident : Proven.Implements1With (fun xs : ByteArray => xs.data.toList) (encArr $kT) $code
              $fI (fun _ => 8 * wholeW $wa [inLoc] + 8 * (wholeNA $wa + 1) + 7) (retLen := true) :=
            implements1_waAC (k := $kT) $fI $wa (by decide) (by decide +kernel) (waTbl $tblI) $splI
              (by decide +kernel) (by decide +kernel) (by decide +kernel) $goodN))
        return
      elabCommand (← `(def $code:ident : List (BitVec 32) := waCodeA $wa))
      elabCommand (← `(set_option maxRecDepth 100000 in set_option backward.isDefEq.respectTransparency false in
        theorem $impl:ident : Proven.Implements1With (fun xs : ByteArray => xs.data.toList) (encArr $kT) $code
            $fI (fun _ => 8 * wholeW $wa [inLoc] + 8 * (wholeNA $wa + 1) + 7) (retLen := true) :=
          implements1_waA (k := $kT) $fI $wa (by decide) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel) $goodN))

end Proven.WA
