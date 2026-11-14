/- `compile% f`: turn an ordinary Lean function on `List UInt8` into a `Pipe`, compile it, and return a
`Compiled` value: the pipe, a kernel-checked proof that `f` equals the pipe's denotation, and a
kernel-checked proof that `compileP` accepts the pipe.  `Compiled.ok` is then the machine-code theorem for
`f` itself.  Anything the reifier or the compiler does not accept is an elaboration error naming the
subterm or the limit.  No `native_decide`: the proofs are `rfl`/`simp` and `decide +kernel`. -/
import Compiler.Front.PipeOk
import Lean

namespace Proven
open Lean Meta Elab Term

theorem compileP_of_toBool {p : Pipe} (h : (compileP p).toBool = true) :
    compileP p = .ok (compileAF [0, 3] (Pipe.prog p)) := by
  cases hc : compileP p with
  | error m => simp [hc, Except.toBool] at h
  | ok code => obtain ⟨-, -, rfl⟩ := compileP_inv hc; rfl

/-- result encodings: a list is itself, a byte is a one-byte list, a word is its 8 little-endian bytes -/
abbrev encL (l : List UInt8) : List UInt8 := l
abbrev enc1 (b : UInt8) : List UInt8 := [b]
abbrev enc8 (w : BitVec 64) : List UInt8 := leBytes w 8

/-- a compiled function: `pipe` denotes `f` (through `enc`), and `compileP pipe` succeeds -/
structure Compiled {α : Type} (enc : α → List UInt8) (f : List UInt8 → α) where
  pipe : Pipe
  denote : ∀ xs, enc (f xs) = Pipe.denote pipe xs
  check : (compileP pipe).toBool = true

namespace Compiled
variable {α : Type} {enc : α → List UInt8} {f : List UInt8 → α}

/-- the machine code -/
def code (c : Compiled enc f) : List (BitVec 32) := compileAF [0, 3] (Pipe.prog c.pipe)

theorem compiles (c : Compiled enc f) : compileP c.pipe = .ok c.code := compileP_of_toBool c.check

/-- the code implements the user's function (result encoded by `enc`) -/
theorem ok (c : Compiled enc f) : ImplementsPipe c.code (fun xs => enc (f xs)) (Pipe.space c.pipe) := by
  have : (fun xs => enc (f xs)) = Pipe.denote c.pipe := funext c.denote
  rw [this]; exact compileP_ok c.compiles

/-- `ImplementsMapped` form, when the pipe needs no more output space than its result -/
theorem mapped (c : Compiled enc f) (hs : ∀ n, Pipe.space c.pipe n ≤ Pipe.len c.pipe n) :
    ImplementsMapped c.code (fun xs => enc (f xs)) := by
  have : (fun xs => enc (f xs)) = Pipe.denote c.pipe := funext c.denote
  rw [this]; exact compileP_mapped c.compiles hs

/-- pipes of `map`/`take`/`drop`/`reverse` only: output block of exactly the result size -/
theorem mapped_view (c : Compiled enc f) (hv : c.pipe.all Stage.isView = true) :
    ImplementsMapped c.code (fun xs => enc (f xs)) := by
  have : (fun xs => enc (f xs)) = Pipe.denote c.pipe := funext c.denote
  rw [this]; exact compileP_view c.compiles hv

end Compiled

/-- list-valued functions: the statement is about `f` itself -/
theorem Compiled.implements {f : List UInt8 → List UInt8} (c : Compiled encL f) :
    ImplementsPipe c.code f (Pipe.space c.pipe) := c.ok

/-! ## Reification -/

def compileErr (p : Pipe) : Option String :=
  match compileP p with
  | .ok _ => none
  | .error m => some m

unsafe def evalErrUnsafe (e : Expr) : MetaM (Option String) :=
  evalExpr (Option String) (mkApp (mkConst ``Option [levelZero]) (mkConst ``String)) e

@[implemented_by evalErrUnsafe]
opaque evalErr (e : Expr) : MetaM (Option String)

def isTy (e : Expr) (ty : Expr) : MetaM Bool := do isDefEq (← inferType e) ty

def u8 : Expr := mkConst ``UInt8
def w64 : Expr := mkApp (mkConst ``BitVec) (mkNatLit 64)

/-- byte expression over the element `x` (and the accumulator `acc?`) -/
partial def reifyB (acc? : Option Expr) (x : Expr) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  unless ← isTy e u8 do throwError "compile%: expected a `UInt8` expression, got{indentExpr e}"
  if e == x then return mkConst ``BExp.x
  if acc? == some e then return mkConst ``BExp.acc
  if !e.hasFVar then return mkApp (mkConst ``BExp.lit) e
  let args := e.getAppArgs
  let r := reifyB acc? x
  let bin (op : Name) : MetaM Expr := do
    return mkApp3 (mkConst ``BExp.bin) (mkConst op) (← r args[4]!) (← r args[5]!)
  let ite (cmp : Name) (a b t f : Expr) : MetaM Expr := do
    return mkApp5 (mkConst ``BExp.ite) (mkConst cmp) (← r a) (← r b) (← r t) (← r f)
  match e.getAppFn.constName?, args.size with
  | some ``HAdd.hAdd, 6 => bin ``BOp.add
  | some ``HSub.hSub, 6 => bin ``BOp.sub
  | some ``HAnd.hAnd, 6 => bin ``BOp.and
  | some ``HOr.hOr, 6 => bin ``BOp.or
  | some ``HXor.hXor, 6 => bin ``BOp.xor
  | some ``ite, 5 =>
    let c := args[1]!; let t := args[3]!; let f := args[4]!
    let ca := c.getAppArgs
    match c.getAppFn.constName?, ca.size with
    | some ``LT.lt, 4 => ite ``BCmp.lt ca[2]! ca[3]! t f
    | some ``LE.le, 4 => ite ``BCmp.le ca[2]! ca[3]! t f
    | some ``GT.gt, 4 => ite ``BCmp.lt ca[3]! ca[2]! t f
    | some ``GE.ge, 4 => ite ``BCmp.le ca[3]! ca[2]! t f
    | some ``Eq, 3 => ite ``BCmp.eq ca[1]! ca[2]! t f
    | some ``Ne, 3 => ite ``BCmp.ne ca[1]! ca[2]! t f
    | _, _ => throwError "compile%: unsupported condition (use <, ≤, >, ≥, =, ≠ on bytes){indentExpr c}"
  | _, _ => throwError "compile%: unsupported byte expression (use + - &&& ||| ^^^, if-then-else, literals){indentExpr e}"

/-- `b` if `n` is `b.toNat % 64` -/
def modAmt64? (n : Expr) : Option Expr :=
  if n.isAppOfArity ``HMod.hMod 6 && n.appFn!.appArg!.isAppOfArity ``BitVec.toNat 2 &&
    n.appArg!.nat? == some 64 then n.appFn!.appArg!.appArg! else none

/-- word expression over the accumulator `acc : BitVec 64` and the element `x : UInt8`
(which may occur only as `x.toBitVec.setWidth 64`) -/
partial def reifyW (acc x : Expr) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  unless ← isTy e w64 do throwError "compile%: expected a `BitVec 64` expression, got{indentExpr e}"
  if e == acc then return mkConst ``WExp.acc
  if (e.isAppOfArity ``BitVec.setWidth 3 || e.isAppOfArity ``BitVec.zeroExtend 3) &&
      e.appArg!.isAppOfArity ``UInt8.toBitVec 1 && e.appArg!.appArg! == x then
    return mkConst ``WExp.x
  if !e.hasFVar then return mkApp (mkConst ``WExp.const) e
  let args := e.getAppArgs
  let r := reifyW acc x
  let bin (op : Name) (a b : Expr) : MetaM Expr := do
    return mkApp3 (mkConst ``WExp.bin) (mkConst op) (← r a) (← r b)
  match e.getAppFn.constName?, args.size with
  | some ``HAdd.hAdd, 6 => bin ``Op.add args[4]! args[5]!
  | some ``HSub.hSub, 6 => bin ``Op.sub args[4]! args[5]!
  | some ``HAnd.hAnd, 6 => bin ``Op.and args[4]! args[5]!
  | some ``HOr.hOr, 6 => bin ``Op.or args[4]! args[5]!
  | some ``HXor.hXor, 6 => bin ``Op.xor args[4]! args[5]!
  | some ``HShiftLeft.hShiftLeft, 6 =>
    if let some b := modAmt64? args[5]! then bin ``Op.shl args[4]! b
    else throwError "compile%: shift amount must be `b.toNat % 64`{indentExpr e}"
  | some ``HShiftRight.hShiftRight, 6 =>
    if let some b := modAmt64? args[5]! then bin ``Op.lshr args[4]! b
    else throwError "compile%: shift amount must be `b.toNat % 64`{indentExpr e}"
  | some ``ite, 5 =>
    let c := args[1]!; let t := args[3]!; let f := args[4]!
    if t.nat? == some 1 && f.nat? == some 0 then
      if c.isAppOfArity ``LT.lt 4 then return ← bin ``Op.ult c.appFn!.appArg! c.appArg!
      if c.isAppOfArity ``Eq 3 then return ← bin ``Op.eq c.appFn!.appArg! c.appArg!
    if c.isAppOfArity ``Eq 3 && c.appArg!.nat? == some 0 then
      return mkApp3 (mkConst ``WExp.ite) (← r c.appFn!.appArg!) (← r f) (← r t)
    throwError "compile%: unsupported word condition (use `if a < b then 1 else 0`, `if a = b then 1 else 0`, `if c = 0 then y else x`){indentExpr e}"
  | _, _ => throwError "compile%: unsupported word expression (the element must appear as `x.toBitVec.setWidth 64`){indentExpr e}"

/-- open a function of `n` arguments (a lambda, or a constant that unfolds to one) -/
def withFun {α : Type} (f : Expr) (n : Nat) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let f ← instantiateMVars f
  let f ← if f.isLambda then pure f else
    match ← unfoldDefinition? f with
    | some f' => pure f'
    | none => etaExpand f
  lambdaBoundedTelescope f n fun ys body => do
    unless ys.size == n do throwError "compile%: expected a function of {n} argument(s), got{indentExpr f}"
    k ys body

/-- the stages computing the list `e` from the argument `xs` -/
partial def reifyL (xs : Expr) (e : Expr) : MetaM (Array Expr) := do
  let e ← instantiateMVars e
  if e == xs then return #[]
  let args := e.getAppArgs
  let closedNat (n : Expr) (what : String) : MetaM Unit := do
    if n.hasFVar then throwError "compile%: the {what} count must not depend on the input:{indentExpr n}"
  match e.getAppFn.constName?, args.size with
  | some ``List.map, 4 =>
    let st ← withFun args[2]! 1 fun ys body => return mkApp (mkConst ``Stage.map) (← reifyB none ys[0]! body)
    return (← reifyL xs args[3]!).push st
  | some ``List.take, 3 =>
    closedNat args[1]! "take"
    return (← reifyL xs args[2]!).push (mkApp (mkConst ``Stage.take) args[1]!)
  | some ``List.drop, 3 =>
    closedNat args[1]! "drop"
    return (← reifyL xs args[2]!).push (mkApp (mkConst ``Stage.drop) args[1]!)
  | some ``List.reverse, 2 => return (← reifyL xs args[1]!).push (mkConst ``Stage.reverse)
  | some ``List.mergeSort, 3 =>
    unless ← isDefEq args[2]! (mkConst ``leU) do
      throwError "compile%: mergeSort is supported only with the default order `fun a b => a ≤ b`, got{indentExpr args[2]!}"
    return (← reifyL xs args[1]!).push (mkConst ``Stage.sort)
  | _, _ =>
    throwError "compile%: unsupported list expression (use map, take, drop, reverse, mergeSort, foldl on the argument){indentExpr e}"

/-- stages and result encoding for the body `e` of `fun xs => e` -/
def reifyTop (xs : Expr) (e : Expr) : MetaM (Array Expr × Name) := do
  let e ← instantiateMVars e
  let ty ← inferType e
  if ← isDefEq ty (mkApp (mkConst ``List [levelZero]) u8) then return (← reifyL xs e, ``encL)
  let args := e.getAppArgs
  unless e.isAppOfArity ``List.foldl 5 do
    throwError "compile%: a result of type{indentExpr ty}\nmust be a `List.foldl`, got{indentExpr e}"
  if args[3]!.hasFVar then throwError "compile%: the initial value must not depend on the input:{indentExpr args[3]!}"
  let pre ← reifyL xs args[4]!
  if ← isDefEq ty u8 then
    let st ← withFun args[2]! 2 fun ys body =>
      return mkApp2 (mkConst ``Stage.fold) (← reifyB (some ys[0]!) ys[1]! body) args[3]!
    return (pre.push st, ``enc1)
  if ← isDefEq ty w64 then
    let st ← withFun args[2]! 2 fun ys body =>
      return mkApp2 (mkConst ``Stage.foldW) (← reifyW ys[0]! ys[1]! body) args[3]!
    return (pre.push st, ``enc8)
  throwError "compile%: unsupported result type{indentExpr ty}\n(supported: List UInt8, UInt8, BitVec 64)"

/-- `compile% f`, for `f : List UInt8 → List UInt8` (or `→ UInt8`, `→ BitVec 64` for folds) written with
`List.map`, `take`, `drop`, `reverse`, `mergeSort`, `foldl`: a `Compiled enc f`. -/
elab "compile% " t:term : term => do
  let f ← instantiateMVars (← elabTerm t none)
  synthesizeSyntheticMVarsNoPostponing
  let f ← instantiateMVars f
  let (stages, enc) ← withFun f 1 fun ys body => reifyTop ys[0]! body
  let pipe ← mkListLit (mkConst ``Stage) stages.toList
  if let some m ← evalErr (mkApp (mkConst ``compileErr) pipe) then
    throwError "compile%: the pipe{indentExpr pipe}\nis rejected by compileP: {m}"
  let stx ← `(Compiled.mk (enc := $(mkIdent enc)) (f := $(← exprToSyntax f)) $(← exprToSyntax pipe)
    (by first
      | exact fun _ => rfl
      | (intro xs; simp [Pipe.denote, Stage.denote, BExp.denote, WExp.denote, BOp.eval, Op.eval,
          show leU = (fun a b => decide (a ≤ b)) from rfl])
      | fail "compile%: could not prove that the function equals the reified pipe")
    (by decide +kernel))
  elabTerm stx none

end Proven
