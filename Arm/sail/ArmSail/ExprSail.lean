/- **Native ARM (the Sail ARM v9.4-A model)**: for every accepted program, the native code computes the value `Ev` of the
program's emitted Expr (`expr_armSail`), and for C itself (`self_expr_armSail`): `C_correct_native_release_armSail`
composed with Nano/Expr/MachExpr.lean / SelfSrc.lean. -/
import ArmSail.TopN
import Nano.Expr.SelfSrc
namespace ArmSail
open Proven.Top NanoMain ExprSpec

theorem expr_armSail : ExprCorrect Proven.Top.armSail compileNano := correct_expr C_correct_native_release_armSail
theorem self_expr_armSail : SelfExpr Proven.Top.armSail compileNano := self_expr C_correct_native_release_armSail

end ArmSail
