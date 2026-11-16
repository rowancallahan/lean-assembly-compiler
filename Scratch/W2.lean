import Riscv.Frontx.ExprExamples
namespace ConLeche
open Name (anonymous)
def natName : Name := anonymous |>.str "Nat"
def natAddName : Name := natName.str "add"
def falseName : Name := anonymous |>.str "False"
end ConLeche
namespace Proven.Frontx.ExprEx
frontx_ind ConLeche.falseName on TExpr
frontx_ind ConLeche.natAddName on TExpr
end Proven.Frontx.ExprEx
