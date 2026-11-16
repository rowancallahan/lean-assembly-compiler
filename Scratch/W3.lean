import Riscv.Frontx.ExprExamples
namespace ConLeche
open Name (anonymous)
def natName : Name := anonymous |>.str "Nat"
def bn (s : String) : Name := .str .anonymous s
def natPredName : Name := natName.str "pred"
def natLandName : Name := natName.str "land"
end ConLeche
namespace Proven.Frontx.ExprEx
frontx_ind ConLeche.natPredName on TExpr
frontx_ind ConLeche.natLandName on TExpr
end Proven.Frontx.ExprEx
