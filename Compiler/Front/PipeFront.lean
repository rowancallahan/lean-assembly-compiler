/- `compile% f`: turn an ordinary Lean function on `List UInt8` into a `Pipe`, compile it, and return a
`Compiled` value: the pipe, a kernel-checked proof that `f` equals the pipe's denotation, and a
kernel-checked proof that `compileP` accepts the pipe.  `Compiled.ok` is then the machine-code theorem for
`f` itself.  Anything the reifier or the compiler does not accept is an elaboration error naming the
subterm or the limit.  No `native_decide`: the proofs are `rfl`/`simp` and `decide +kernel`. -/
import Compiler.Front.PipeOk
import Compiler.Front.PipeStdMachine
import Lean

namespace Proven
open Lean Meta Elab Term

/-- the compiler used by `compile%` (`Compiler/Front/PipeStdMachine.lean`) -/
abbrev compileX := compileXA
abbrev codeX (p : XPipe) : List (BitVec 32) := compileAF [0, 3] (XPipe.prog p)

theorem compileX_of_toBool {p : XPipe} (h : (compileX p).toBool = true) : compileX p = .ok (codeX p) := by
  cases hc : compileX p with
  | error m => simp [hc, Except.toBool] at h
  | ok code => obtain ⟨-, -, rfl⟩ := compileXA_inv hc; rfl

/-- result encodings: a list is itself, a byte is a one-byte list, everything else the `Bytes` encoding of
`Spec/Encode.lean` (`BitVec 64`: 8 bytes little-endian; `Bool`: one byte 0/1; `Option UInt8`: tag byte, value) -/
abbrev encL (l : List UInt8) : List UInt8 := l
abbrev enc1 (b : UInt8) : List UInt8 := [b]
abbrev enc8 (w : BitVec 64) : List UInt8 := enc w
abbrev encB (b : Bool) : List UInt8 := enc b
abbrev encO (o : Option UInt8) : List UInt8 := enc o

/-- a compiled function: `pipe` denotes `f` (through `enc`), and the compiler accepts the pipe -/
structure Compiled {α : Type} (enc : α → List UInt8) (f : List UInt8 → α) where
  pipe : XPipe
  denote : ∀ xs, enc (f xs) = XPipe.denote pipe xs
  check : (compileX pipe).toBool = true

namespace Compiled
variable {α : Type} {enc : α → List UInt8} {f : List UInt8 → α}

/-- the machine code -/
def code (c : Compiled enc f) : List (BitVec 32) := codeX c.pipe

theorem compiles (c : Compiled enc f) : compileX c.pipe = .ok c.code := compileX_of_toBool c.check

/-- the code implements the user's function (result encoded by `enc`), and returns the result length in `a1` -/
theorem okLen (c : Compiled enc f) : ImplementsPipeLen c.code (fun xs => enc (f xs)) (XPipe.space c.pipe) := by
  have : (fun xs => enc (f xs)) = XPipe.denote c.pipe := funext c.denote
  rw [this]; exact compileXA_ok c.compiles

/-- the code implements the user's function (result encoded by `enc`) -/
theorem ok (c : Compiled enc f) : ImplementsPipe c.code (fun xs => enc (f xs)) (XPipe.space c.pipe) := c.okLen.toPipe

/-- `ImplementsMapped` form, when the output block needs no more than the result -/
theorem mapped (c : Compiled enc f) (hs : ∀ x : List UInt8, XPipe.space c.pipe x.length ≤ (enc (f x)).length) :
    ImplementsMapped c.code (fun xs => enc (f xs)) := c.ok.mapped hs

end Compiled

/-- list-valued functions: the statement is about `f` itself -/
theorem Compiled.implements {f : List UInt8 → List UInt8} (c : Compiled encL f) :
    ImplementsPipe c.code f (XPipe.space c.pipe) := c.ok

/-- list-valued functions with the length in `a1` (for data-dependent lengths: `filter`, `takeWhile`, ...) -/
theorem Compiled.implementsLen {f : List UInt8 → List UInt8} (c : Compiled encL f) :
    ImplementsPipeLen c.code f (XPipe.space c.pipe) := c.okLen

/-! ## Reification -/

def compileErr (p : XPipe) : Option String :=
  match compileX p with
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
  if e == x then return mkConst ``ByteExp.x
  if acc? == some e then return mkConst ``ByteExp.acc
  if !e.hasFVar then return mkApp (mkConst ``ByteExp.lit) e
  let args := e.getAppArgs
  let r := reifyB acc? x
  let bin (op : Name) : MetaM Expr := do
    return mkApp3 (mkConst ``ByteExp.bin) (mkConst op) (← r args[4]!) (← r args[5]!)
  let ite (cmp : Name) (a b t f : Expr) : MetaM Expr := do
    return mkApp5 (mkConst ``ByteExp.ite) (mkConst cmp) (← r a) (← r b) (← r t) (← r f)
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

/-- a Boolean condition on the element `x` -/
partial def reifyP (x : Expr) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let r := reifyP x
  let rb := reifyB none x
  let args := e.getAppArgs
  let cmp (c : Name) (a b : Expr) : MetaM Expr := do
    return mkApp3 (mkConst ``BPred.cmp) (mkConst c) (← rb a) (← rb b)
  match e.getAppFn.constName?, args.size with
  | some ``Bool.true, 0 => return mkConst ``BPred.tt
  | some ``Bool.false, 0 => return mkConst ``BPred.ff
  | some ``and, 2 => return mkApp2 (mkConst ``BPred.and) (← r args[0]!) (← r args[1]!)
  | some ``or, 2 => return mkApp2 (mkConst ``BPred.or) (← r args[0]!) (← r args[1]!)
  | some ``not, 1 => return mkApp (mkConst ``BPred.not) (← r args[0]!)
  | some ``BEq.beq, 4 => cmp ``BCmp.eq args[2]! args[3]!
  | some ``bne, 4 => return mkApp (mkConst ``BPred.not) (← cmp ``BCmp.eq args[2]! args[3]!)
  | some ``Decidable.decide, 2 =>
    let c := args[0]!
    let ca := c.getAppArgs
    match c.getAppFn.constName?, ca.size with
    | some ``LT.lt, 4 => cmp ``BCmp.lt ca[2]! ca[3]!
    | some ``LE.le, 4 => cmp ``BCmp.le ca[2]! ca[3]!
    | some ``GT.gt, 4 => cmp ``BCmp.lt ca[3]! ca[2]!
    | some ``GE.ge, 4 => cmp ``BCmp.le ca[3]! ca[2]!
    | some ``Eq, 3 => cmp ``BCmp.eq ca[1]! ca[2]!
    | some ``Ne, 3 => cmp ``BCmp.ne ca[1]! ca[2]!
    | _, _ => throwError "compile%: unsupported condition (use <, ≤, >, ≥, =, ≠ on bytes){indentExpr c}"
  | _, _ => throwError "compile%: unsupported predicate (use comparisons, ==, !=, &&, ||, !){indentExpr e}"

def closedChk (e : Expr) (what : String) : MetaM Unit := do
  if e.hasFVar then throwError "compile%: the {what} must not depend on the input:{indentExpr e}"

/-- the stages computing the list `e` from the argument `xs` -/
partial def reifyL (xs : Expr) (e : Expr) : MetaM (Array Expr) := do
  let e ← instantiateMVars e
  if e == xs then return #[]
  let args := e.getAppArgs
  let base (st : Expr) : Expr := mkApp (mkConst ``XStage.base) st
  let pred (f : Expr) : MetaM Expr := withFun f 1 fun ys body => reifyP ys[0]! body
  match e.getAppFn.constName?, args.size with
  | some ``List.map, 4 =>
    let st ← withFun args[2]! 1 fun ys body => return mkApp (mkConst ``Stage.map) (← reifyB none ys[0]! body)
    return (← reifyL xs args[3]!).push (base st)
  | some ``List.take, 3 =>
    closedChk args[1]! "take count"
    return (← reifyL xs args[2]!).push (base (mkApp (mkConst ``Stage.take) args[1]!))
  | some ``List.drop, 3 =>
    closedChk args[1]! "drop count"
    return (← reifyL xs args[2]!).push (base (mkApp (mkConst ``Stage.drop) args[1]!))
  | some ``List.reverse, 2 => return (← reifyL xs args[1]!).push (base (mkConst ``Stage.reverse))
  | some ``List.mergeSort, 3 =>
    unless ← isDefEq args[2]! (mkConst ``leU) do
      throwError "compile%: mergeSort is supported only with the default order `fun a b => a ≤ b`, got{indentExpr args[2]!}"
    return (← reifyL xs args[1]!).push (base (mkConst ``Stage.sort))
  | some ``List.filter, 3 => return (← reifyL xs args[2]!).push (mkApp (mkConst ``XStage.filter) (← pred args[1]!))
  | some ``List.takeWhile, 3 =>
    return (← reifyL xs args[2]!).push (mkApp (mkConst ``XStage.takeWhile) (← pred args[1]!))
  | some ``List.dropWhile, 3 =>
    return (← reifyL xs args[2]!).push (mkApp (mkConst ``XStage.dropWhile) (← pred args[1]!))
  | some ``HAppend.hAppend, 6 =>
    let l := args[4]!; let c := args[5]!
    if !c.hasFVar then return (← reifyL xs l).push (mkApp (mkConst ``XStage.appendC) c)
    if !l.hasFVar then
      -- `c ++ ys = (ys.reverse ++ c.reverse).reverse`
      let rv := base (mkConst ``Stage.reverse)
      return ((← reifyL xs c).push rv |>.push (mkApp (mkConst ``XStage.appendC)
        (mkApp2 (mkConst ``List.reverse [levelZero]) u8 l))).push rv
    throwError "compile%: `++` is supported with one constant side only{indentExpr e}"
  | _, _ =>
    throwError "compile%: unsupported list expression (use map, take, drop, reverse, mergeSort, filter, takeWhile, dropWhile, ++ a constant list, foldl on the argument){indentExpr e}"

def red (r : Expr) : Expr := mkApp (mkConst ``XStage.red) r

/-- `n : Nat` as a reduction of a list (`length`, `countP`, `count`, `findIdx`, `idxOf`, the `Nat` sum) -/
def reifyNat (xs : Expr) (n : Expr) : MetaM (Array Expr) := do
  let n ← instantiateMVars n
  let args := n.getAppArgs
  let pred (f : Expr) : MetaM Expr := withFun f 1 fun ys body => reifyP ys[0]! body
  match n.getAppFn.constName?, args.size with
  | some ``List.length, 2 => return (← reifyL xs args[1]!).push (red (mkConst ``Red.length))
  | some ``List.countP, 3 =>
    return (← reifyL xs args[2]!).push (red (mkApp (mkConst ``Red.countP) (← pred args[1]!)))
  | some ``List.count, 4 =>
    closedChk args[2]! "counted byte"
    return (← reifyL xs args[3]!).push (red (mkApp (mkConst ``Red.count) args[2]!))
  | some ``List.findIdx, 3 =>
    return (← reifyL xs args[2]!).push (red (mkApp (mkConst ``Red.findIdx) (← pred args[1]!)))
  | some ``List.idxOf, 4 =>
    closedChk args[2]! "searched byte"
    return (← reifyL xs args[3]!).push (red (mkApp (mkConst ``Red.idxOf) args[2]!))
  | some ``List.sum, 4 =>
    let l := args[3]!
    unless l.isAppOfArity ``List.map 4 && (← isDefEq l.getAppArgs[2]! (mkConst ``UInt8.toNat)) do
      throwError "compile%: a `Nat` sum must be `(l.map UInt8.toNat).sum`{indentExpr n}"
    return (← reifyL xs l.getAppArgs[3]!).push (red (mkConst ``Red.sum64))
  | _, _ => throwError "compile%: unsupported natural number (use length, count, countP, findIdx, idxOf, (l.map UInt8.toNat).sum){indentExpr n}"

/-- stages and result encoding for the body `e` of `fun xs => e` -/
def reifyTop (xs : Expr) (e : Expr) : MetaM (Array Expr × Name) := do
  let e ← instantiateMVars e
  let ty ← inferType e
  if ← isDefEq ty (mkApp (mkConst ``List [levelZero]) u8) then return (← reifyL xs e, ``encL)
  let args := e.getAppArgs
  let pred (f : Expr) : MetaM Expr := withFun f 1 fun ys body => reifyP ys[0]! body
  if ← isDefEq ty u8 then
    if e.isAppOfArity ``List.sum 4 then return ((← reifyL xs args[3]!).push (red (mkConst ``Red.sum8)), ``enc1)
    unless e.isAppOfArity ``List.foldl 5 do
      throwError "compile%: a `UInt8` result must be a `List.foldl` or `List.sum`, got{indentExpr e}"
    closedChk args[3]! "initial value"
    let pre ← reifyL xs args[4]!
    let st ← withFun args[2]! 2 fun ys body =>
      return mkApp2 (mkConst ``Stage.fold) (← reifyB (some ys[0]!) ys[1]! body) args[3]!
    return (pre.push (mkApp (mkConst ``XStage.base) st), ``enc1)
  if ← isDefEq ty w64 then
    if (e.isAppOfArity ``BitVec.ofNat 2 && args[0]!.nat? == some 64) then return (← reifyNat xs args[1]!, ``enc8)
    if e.isAppOfArity ``Nat.cast 3 then return (← reifyNat xs args[2]!, ``enc8)
    unless e.isAppOfArity ``List.foldl 5 do
      throwError "compile%: a `BitVec 64` result must be a `List.foldl` or `BitVec.ofNat 64 n`, got{indentExpr e}"
    closedChk args[3]! "initial value"
    let pre ← reifyL xs args[4]!
    let st ← withFun args[2]! 2 fun ys body =>
      return mkApp2 (mkConst ``Stage.foldW) (← reifyW ys[0]! ys[1]! body) args[3]!
    return (pre.push (mkApp (mkConst ``XStage.base) st), ``enc8)
  if ← isDefEq ty (mkConst ``Bool) then
    match e.getAppFn.constName?, args.size with
    | some ``List.any, 3 => return ((← reifyL xs args[1]!).push (red (mkApp (mkConst ``Red.any) (← pred args[2]!))), ``encB)
    | some ``List.all, 3 => return ((← reifyL xs args[1]!).push (red (mkApp (mkConst ``Red.all) (← pred args[2]!))), ``encB)
    | some ``List.contains, 4 =>
      closedChk args[3]! "searched byte"
      return ((← reifyL xs args[2]!).push (red (mkApp (mkConst ``Red.contains) args[3]!)), ``encB)
    | some ``List.elem, 4 =>
      closedChk args[2]! "searched byte"
      return ((← reifyL xs args[3]!).push (red (mkApp (mkConst ``Red.contains) args[2]!)), ``encB)
    | some ``List.isEmpty, 2 => return ((← reifyL xs args[1]!).push (red (mkConst ``Red.isEmpty)), ``encB)
    | _, _ => throwError "compile%: a `Bool` result must be any, all, contains, elem or isEmpty, got{indentExpr e}"
  if ← isDefEq ty (mkApp (mkConst ``Option [levelZero]) u8) then
    match e.getAppFn.constName?, args.size with
    | some ``List.head?, 2 => return ((← reifyL xs args[1]!).push (red (mkConst ``Red.head)), ``encO)
    | some ``List.getLast?, 2 => return ((← reifyL xs args[1]!).push (red (mkConst ``Red.getLast)), ``encO)
    | some ``List.find?, 3 =>
      return ((← reifyL xs args[2]!).push (red (mkApp (mkConst ``Red.find) (← pred args[1]!))), ``encO)
    | some ``List.min?, 3 => return ((← reifyL xs args[2]!).push (red (mkConst ``Red.min)), ``encO)
    | some ``List.max?, 3 => return ((← reifyL xs args[2]!).push (red (mkConst ``Red.max)), ``encO)
    | some ``GetElem?.getElem?, 7 =>
      closedChk args[6]! "index"
      return ((← reifyL xs args[5]!).push (mkApp (mkConst ``XStage.base) (mkApp (mkConst ``Stage.drop) args[6]!))
        |>.push (red (mkConst ``Red.head)), ``encO)
    | _, _ => throwError "compile%: an `Option UInt8` result must be head?, getLast?, find?, min?, max? or l[i]?, got{indentExpr e}"
  throwError "compile%: unsupported result type{indentExpr ty}\n(supported: List UInt8, UInt8, BitVec 64, Bool, Option UInt8)"

/-- `compile% f`, for `f : List UInt8 → α` written with the list functions above: a `Compiled enc f`. -/
elab "compile% " t:term : term => do
  let f ← instantiateMVars (← elabTerm t none)
  synthesizeSyntheticMVarsNoPostponing
  let f ← instantiateMVars f
  let (stages, enc) ← withFun f 1 fun ys body => reifyTop ys[0]! body
  let pipe ← mkListLit (mkConst ``XStage) stages.toList
  if let some m ← evalErr (mkApp (mkConst ``compileErr) pipe) then
    throwError "compile%: the pipe{indentExpr pipe}\nis rejected by the compiler: {m}"
  let stx ← `(Compiled.mk (enc := $(mkIdent enc)) (f := $(← exprToSyntax f)) $(← exprToSyntax pipe)
    (by first
      | exact fun _ => rfl
      | exact fun _ => (leBytes_eq_enc _).symm
      | (intro xs; simp [XPipe.denote, XStage.denote, Red.denote, Stage.denote, ByteExp.denote, WExp.denote, BOp.eval,
          Op.eval, List.head?_drop, List.reverse_append, show leU = (fun a b => decide (a ≤ b)) from rfl])
      | fail "compile%: could not prove that the function equals the reified pipe")
    (by decide +kernel))
  elabTerm stx none

end Proven
