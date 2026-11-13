/- `reify%`: turn a Lean function built from `BitVec 64` primitives into an `Exp`, and an example
of compiling one end to end. -/
import Proven.Compiler

namespace Proven
open Lean Meta Elab Term

/-- `Exp` syntax for `e`, whose free variables are among the arguments `xs` -/
partial def reifyGo (xs : Array Expr) (e : Expr) : TermElabM Term := do
  if let some i := xs.idxOf? e then
    return ← `(Exp.var $(Syntax.mkNumLit (toString i)))
  let op? : Option Name := match e.getAppFn.constName?, e.getAppNumArgs with
    | some ``HAdd.hAdd, 6 => some ``Op.add | some ``HSub.hSub, 6 => some ``Op.sub
    | some ``HAnd.hAnd, 6 => some ``Op.and | some ``HOr.hOr, 6 => some ``Op.or
    | some ``HXor.hXor, 6 => some ``Op.xor | _, _ => none
  if let some op := op? then
    return ← `(Exp.bin $(mkIdent op) $(← reifyGo xs e.appFn!.appArg!) $(← reifyGo xs e.appArg!))
  if e.hasFVar then throwError "reify%: unsupported subterm{indentExpr e}"
  `(Exp.const $(← exprToSyntax e))

/-- `reify% f` for `f : BitVec 64 → … → BitVec 64` (at most 4 arguments) built from
`+ - &&& ||| ^^^` and closed constants: the `Exp` `e` with `e.denote env = f (env 0) …` by `rfl`.
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

end Proven
