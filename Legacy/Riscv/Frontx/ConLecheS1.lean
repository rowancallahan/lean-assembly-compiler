import Legacy.Riscv.Frontx.IndGate
import Legacy.Riscv.Frontx.ExprExamples
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet
set_option maxErrors 100000
open Proven.Frontx.ExprEx



namespace ConLeche
namespace Expr
/-- Is the expression an application?  The spine test of `beqGoX`. -/
@[inline] def beqIsApp : Expr → Bool
  | .app .. => true
  | _ => false
end Expr
end ConLeche

section
namespace ConLeche.Cached
open ConLeche
variable {m : Type → Type}
/-- **`whnfCore`'s easy cases** (official `whnf_core`, "handle easy
cases"): the kinds that are their own head normal form
(`whnfCoreStepI`'s `.done e` arm).  The loop returns them before the
memo, at every step: no lookup, no insert.  A free variable is never a
let-variable here (lets are ζ-reduced by instantiation), so it is easy,
as official's non-let `FVar`. -/
@[inline] def whnfCoreEasy : Expr → Bool
  | .sort _ | .fvar .. | .forallE .. | .lam .. | .const .. | .lit _ => true
  | _ => false
end ConLeche.Cached
end

frontx_ind_gate ConLeche.Expr.beqIsApp on TExpr
frontx_ind ConLeche.Expr.beqIsApp on TExpr

frontx_ind_gate ConLeche.Cached.whnfCoreEasy on TExpr
frontx_ind ConLeche.Cached.whnfCoreEasy on TExpr
