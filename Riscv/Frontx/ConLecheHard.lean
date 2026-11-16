/- con-leche hard blockers (NOTES section 36): specialisation of a constant scalar parameter, wildcard patterns
inside nested patterns and in called functions, matches on two arguments.  con-leche @6810492c1, verbatim
(file:line per block). -/
import Riscv.Frontx.ExprExamples
import Riscv.Frontx.ConLecheBlk

set_option linter.unusedVariables false

namespace ConLeche.Expr

-- Kernel/ExprOps.lean:677-692
def liftLooseBVars (amount : Nat) : (cutoff : Nat) → Expr → Expr
  | c, .bvar i => if i ≥ c then .bvar (i + amount) else .bvar i
  | _, .fvar i ty => .fvar i ty
  | _, .sort u => .sort u
  | _, .const n us => .const n us
  | c, .app a b => .app (liftLooseBVars amount c a) (liftLooseBVars amount c b)
  | c, .lam ty body =>
    .lam (liftLooseBVars amount c ty) (liftLooseBVars amount (c + 1) body)
  | c, .forallE ty body =>
    .forallE (liftLooseBVars amount c ty) (liftLooseBVars amount (c + 1) body)
  | c, .letE ty v body =>
    .letE (liftLooseBVars amount c ty) (liftLooseBVars amount c v)
      (liftLooseBVars amount (c + 1) body)
  | _, .lit l => .lit l
  | c, .proj s i e => .proj s i (liftLooseBVars amount c e)

end ConLeche.Expr

namespace Proven.Frontx.ConLecheHard
open Proven.Frontx.ExprEx

/-- entry: lift the loose bound variables at or above the cutoff (from the input) by one -/
def lift1 (e : ConLeche.Expr) (c : Nat) : ConLeche.Expr := ConLeche.Expr.liftLooseBVars 1 c e
frontx_ind lift1 on TExpr

end Proven.Frontx.ConLecheHard
