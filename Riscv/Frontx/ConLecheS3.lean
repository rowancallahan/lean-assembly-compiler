import Riscv.Frontx.ExprExamples
import Riscv.Frontx.IndGate
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet
set_option maxErrors 100000

-- batchB.lean block: ConLeche/Kernel/Inductives/GenRec.lean:107
section
namespace ConLeche
/-- The binder of an opened variable (the motive types' binders: their
codomains are sorts, never zero). -/
def classBinder (x : Expr) : Expr := x.fvarTypeD
end ConLeche
end
-- frontx_ind classBinder on TExpr


-- batchB.lean block: ConLeche/Cached/CoreC.lean:322
section
namespace ConLeche.Cached
open ConLeche
variable {m : Type → Type}
/-- **`whnf`'s easy cases** (official `whnf`, "Do not cache easy
cases"): sorts, free variables, Π-types and literals, which neither
head-normalize, reduce as literals nor unfold.  A constant or a
lambda-expression still goes through the memo, as in official `whnf`. -/
@[inline] def whnfEasy : Expr → Bool
  | .sort _ | .fvar .. | .forallE .. | .lit _ => true
  | _ => false
end ConLeche.Cached
end
-- frontx_ind Cached.whnfEasy on TExpr


namespace Proven.Frontx.ExprEx
-- #19 Expr.sizeF (already in ExprEx: test there)
frontx_ind_gate ConLeche.Expr.sizeF on TExpr
-- #23 Expr.getAppFn (already in ExprEx: test there)
frontx_ind_gate ConLeche.Expr.getAppFn on TExpr
-- #27 Expr.fvarTypeD (already in ExprEx: test there)
frontx_ind_gate ConLeche.Expr.fvarTypeD on TExpr
-- #115 Expr.isLit (already in ExprEx: test there)
frontx_ind_gate ConLeche.Expr.isLit on TExpr
-- #171 classBinder
frontx_ind_gate ConLeche.classBinder on TExpr
frontx_ind ConLeche.classBinder on TExpr
-- #247 Cached.whnfEasy
frontx_ind_gate ConLeche.Cached.whnfEasy on TExpr
frontx_ind ConLeche.Cached.whnfEasy on TExpr
end Proven.Frontx.ExprEx
