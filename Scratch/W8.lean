import Riscv.Frontx.ExprExamples
namespace ConLeche
def Name.beq2 (a b : Name) : Bool := decide (a = b)
end ConLeche
namespace Proven.Frontx.ExprEx
frontx_ind ConLeche.Name.beq2 on TExpr
end Proven.Frontx.ExprEx
