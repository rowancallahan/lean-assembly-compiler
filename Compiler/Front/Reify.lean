/- `reify%`: turn a Lean function built from `BitVec 64` primitives into an `Exp`, and an example
of compiling one end to end. -/
import Riscv.Direct.Compiler

namespace Proven
open Lean Meta Elab Term

/-- `n` if `e` is the numeral `n` -/
def lit? (e : Expr) : Option Nat :=
  if e.isAppOfArity ``OfNat.ofNat 3 then e.appFn!.appArg!.rawNatLit? else none

/-- `b` if `n` is `b.toNat % 64` -/
def modAmt? (n : Expr) : Option Expr :=
  if n.isAppOfArity ``HMod.hMod 6 && n.appFn!.appArg!.isAppOfArity ``BitVec.toNat 2 && lit? n.appArg! == some 64
  then n.appFn!.appArg!.appArg! else none

/-- `Exp` syntax for `e`, whose free variables are among the arguments `xs` -/
partial def reifyGo (xs : Array Expr) (e : Expr) : TermElabM Term := do
  unless ← isDefEq (← inferType e) (mkApp (mkConst ``BitVec) (mkNatLit 64)) do
    throwError "reify%: not a `BitVec 64`{indentExpr e}"
  if let some i := xs.idxOf? e then
    return ← `(Exp.var $(Syntax.mkNumLit (toString i)))
  let bin (op : Name) (a b : Expr) : TermElabM Term := do
    `(Exp.bin $(mkIdent op) $(← reifyGo xs a) $(← reifyGo xs b))
  let op? : Option Name := match e.getAppFn.constName?, e.getAppNumArgs with
    | some ``HAdd.hAdd, 6 => some ``Op.add | some ``HSub.hSub, 6 => some ``Op.sub
    | some ``HAnd.hAnd, 6 => some ``Op.and | some ``HOr.hOr, 6 => some ``Op.or
    | some ``HXor.hXor, 6 => some ``Op.xor | _, _ => none
  if let some op := op? then
    return ← bin op e.appFn!.appArg! e.appArg!
  -- shifts by `b.toNat % 64`
  let sh? : Option Name := match e.getAppFn.constName?, e.getAppNumArgs with
    | some ``HShiftLeft.hShiftLeft, 6 => some ``Op.shl | some ``HShiftRight.hShiftRight, 6 => some ``Op.lshr
    | some ``BitVec.sshiftRight, 3 => some ``Op.ashr | _, _ => none
  if let some op := sh? then
    if let some b := modAmt? e.appArg! then return ← bin op e.appFn!.appArg! b
  -- `if p then x else y`
  if e.isAppOfArity ``ite 5 then
    let args := e.getAppArgs
    let (p, x, y) := (args[1]!, args[3]!, args[4]!)
    if lit? x == some 1 && lit? y == some 0 then
      if p.isAppOfArity ``LT.lt 4 then return ← bin ``Op.ult p.appFn!.appArg! p.appArg!
      if p.isAppOfArity ``Eq 3 && p.appFn!.appArg!.isAppOfArity ``BitVec.slt 3 then
        let c := p.appFn!.appArg!
        return ← bin ``Op.slt c.appFn!.appArg! c.appArg!
      if p.isAppOfArity ``Eq 3 && !(p.appFn!.appArg!.isAppOfArity ``BitVec.slt 3) then
        return ← bin ``Op.eq p.appFn!.appArg! p.appArg!
    if p.isAppOfArity ``Eq 3 && lit? p.appArg! == some 0 then
      return ← `(Exp.ite $(← reifyGo xs p.appFn!.appArg!) $(← reifyGo xs y) $(← reifyGo xs x))
  if e.hasFVar then throwError "reify%: unsupported subterm{indentExpr e}"
  `(Exp.const $(← exprToSyntax e))

/-- `reify% f` for `f : BitVec 64 → … → BitVec 64` (at most 4 arguments) built from
`+ - &&& ||| ^^^`, `a <<< (b.toNat % 64)`, `a >>> (b.toNat % 64)`, `a.sshiftRight (b.toNat % 64)`,
`if a < b then 1 else 0`, `if a.slt b then 1 else 0`, `if a = b then 1 else 0`, `if c = 0 then y else x`
and closed constants: the `Exp` `e` with `e.denote env = f (env 0) …` by `rfl`.
Anything else is an error. -/
elab "reify% " t:term : term => do
  let f ← instantiateMVars (← elabTerm t none)
  let f ← if f.isLambda then pure f else
    match ← unfoldDefinition? f with
    | some f' => pure f'
    | none => throwError "reify%: expected a lambda or a definition, got{indentExpr f}"
  lambdaTelescope f fun xs body => do
    unless xs.size ≤ 4 do throwError "reify%: at most 4 arguments"
    elabTerm (← reifyGo xs body) (some (mkConst ``Exp))

/-! ## Example -/

def demo (a b c d : BitVec 64) : BitVec 64 := ((a + b) ^^^ (c &&& 0xff)) - (d ||| 0x1234)

def demoE : Exp := reify% demo

theorem demoE_denote (env : Fin 4 → BitVec 64) : demoE.denote env = demo (env 0) (env 1) (env 2) (env 3) :=
  rfl

/-- `compile demoE` run on the Sail model computes `demo a0 a1 a2 a3` into `a0` and returns. -/
theorem demo_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compile demoE)) (hok : codeOK pc (compile demoE).length)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      getX s' 10 = demo (getX s 10) (getX s 11) (getX s 12) (getX s 13) ∧ Cfg s' ∧ s'.mem = s.mem ∧
      calleeSavedKept s s' :=
  compile_ok demoE (by unfold demoE; decide) h hpc hc hok hra

/-- an example using every new operator -/
def demo2 (a b c d : BitVec 64) : BitVec 64 :=
  if ((if a < b then 1 else 0) ^^^ (if a.slt c then 1 else 0) : BitVec 64) = 0 then
    (a <<< (d.toNat % 64)) + (b >>> (c.toNat % 64)) else
    (if c = d then 1 else 0) - c.sshiftRight (a.toNat % 64)

def demo2E : Exp := reify% demo2

theorem demo2E_denote (env : Fin 4 → BitVec 64) :
    demo2E.denote env = demo2 (env 0) (env 1) (env 2) (env 3) := rfl

theorem demo2_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compile demo2E)) (hok : codeOK pc (compile demo2E).length)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      getX s' 10 = demo2 (getX s 10) (getX s 11) (getX s 12) (getX s 13) ∧ Cfg s' ∧ s'.mem = s.mem ∧
      calleeSavedKept s s' :=
  compile_ok demo2E (by unfold demo2E; decide) h hpc hc hok hra

end Proven
