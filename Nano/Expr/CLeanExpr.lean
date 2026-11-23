/- Nano/Expr/CLeanExpr: `C_lean` (C's emitted Expr = Lean's) with `C_expr`: the value of Lean's own Expr of C is `mC`. -/
import Nano.Expr.CLean
set_option maxHeartbeats 400000
namespace ExprSpec
open NanoMain

/-- **Lean's own Expr of C means `mC`**: whenever C's meaning on `inp` has a result, the value `Ev` of Lean's
elaborated Expr of C's `m` (the table `ExprLeanC.defs`) applied to `inp` is `mC inp`, the Lean function -/
theorem C_lean_expr (inp : List UInt8) (hin : inp.length < 2 ^ 64) (hs : Sem κC Cert.PC.all inp = .ok (mC inp)) :
    Ev (progOf ExprLeanC.defs) [.l inp] (.app (.c "m" []) (.bv 0)) (.l (mC inp)) :=
  (congrArg (fun o => Ev (progOf o) [.l inp] (.app (.c "m" []) (.bv 0)) (.l (mC inp))) C_lean).mp (C_expr inp hin hs)

end ExprSpec
