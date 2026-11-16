import Riscv.Frontx.ExprExamples
import Riscv.Frontx.IndGate
set_option maxErrors 100000
open Proven.Frontx.ExprEx

-- Testing/conleche-batches/batchB.lean:58-72 (= ConLeche/Kernel/Env.lean:385, verbatim)
section
namespace ConLeche
def Expr.piSortTeleLen? : Expr → Option Nat
  | .forallE _ body => (Expr.piSortTeleLen? body).map (· + 1)
  | .sort _ => some 0
  | _ => none
end ConLeche
end
frontx_ind_gate ConLeche.Expr.piSortTeleLen? on TExpr
