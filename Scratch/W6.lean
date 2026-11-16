import Riscv.Frontx.ExprExamples
open Lean Meta Elab
namespace ConLeche
def boolTrueName : Name := (Name.str .anonymous "Bool").str "true"
end ConLeche
#eval show MetaM Unit from do
  let c ← mkFreshExprMVar (some (mkConst ``ConLeche.Name))
  let e ← mkAppM ``BEq.beq #[c, mkConst ``ConLeche.boolTrueName]
  let e' ← withTransparency .instances (whnf e)
  logInfo m!"{e'}"
  let some u ← unfoldDefinition? e' | return
  logInfo m!"{u}"
  let u := u.headBeta
  let inst := u.getArg! 1
  logInfo m!"{inst}  ==> {← withTransparency .instances (whnf inst)}"
