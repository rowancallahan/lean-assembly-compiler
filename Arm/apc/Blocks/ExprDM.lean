/- **Native ARM (DeepMind's AArch64 model)**: for every accepted program, the native code computes the value `Ev` of the
program's emitted Expr (`expr_armDM`), and for C itself (`self_expr_armDM`): `C_correct_native_release_armDM` composed
with Nano/Expr/MachExpr.lean / SelfSrc.lean. -/
import Blocks.ArmDMRelease
import Nano.Expr.SelfSrc
namespace Proven.Apc.Blocks
open Proven.Top NanoMain ExprSpec

theorem expr_armDM : ExprCorrectLoaded Proven.Top.armDM ArmDMExecutable ArmDMWritable compileNano :=
  correct_expr_loaded C_correct_native_release_armDM
theorem self_expr_armDM : SelfExprLoaded Proven.Top.armDM ArmDMExecutable ArmDMWritable compileNano :=
  self_expr_loaded C_correct_native_release_armDM

end Proven.Apc.Blocks
