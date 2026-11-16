import Riscv.Frontx.ExprExamples
open Proven.Frontx.ExprEx
namespace ConLeche
namespace Cached
def isStuckHeadC : Expr → Bool
  | .sort _ | .fvar .. | .forallE .. | .const .. | .lit _ => true
  | _ => false
end Cached
def Expr.headIsProj (e : Expr) : Bool :=
  match e.getAppFn with
  | .proj _ _ _ => true
  | _ => false
def Expr.getAppArgs : Expr → List Expr
  | .app f a => getAppArgs f ++ [a]
  | _ => []
end ConLeche
namespace Proven.Frontx.ExprEx
frontx_ind ConLeche.Cached.isStuckHeadC on TExpr
set_option maxHeartbeats 8000000 in
frontx_ind ConLeche.Expr.headIsProj on TExpr
end Proven.Frontx.ExprEx
