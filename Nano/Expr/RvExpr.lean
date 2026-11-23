/- Nano/Expr/RvExpr: **RISC-V (Sail model)**: for every accepted program, C's RISC-V code computes the value `Ev` of
the program's emitted Expr (`expr_rv`), and for C itself (`self_expr_rv`; also `NanoMain.self_expr_C`). -/
import Nano.Expr.SelfSrc
import Nano.Main.RvTop
namespace ExprSpec
open NanoMain Proven.Top LeanRV64D

theorem expr_rv : ExprCorrect riscv compileC := correct_expr C_correctLO
theorem self_expr_rv : SelfExpr riscv compileC := self_expr C_correctLO

end ExprSpec
