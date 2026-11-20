import Lean
/- **The inliner compiled through S3** (`Testing/notes/NANO_PARSE_S3.md`): `inlBS` (= `inlB` on every input,
`Nano.IS.inlBS_eq`) compiled by the S3 front end (`s3_compileB`), then the ONE S3 compiler theorem through the
adapter (`Nano.S3Stage.stage`): the machine theorem in the linker's form, `inlS3_implements`. -/
import Legacy.Compiler.S3.Front
import Legacy.Nano.InlS3
import Legacy.Nano.S3Stage

namespace Nano.IS
open Proven Proven.S3 Nano.S3Stage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option s3.depth 4 in
s3_compileB InlS3 := inlBS

set_option maxRecDepth 100000 in
theorem inlS3_small : smallB InlS3.P.S = true := by decide +kernel

theorem inlS3_main : (InlS3.P.S.fn InlS3.P.main).1.length = 1 := by decide

end Nano.IS
open Proven Proven.Ir
deriving instance Lean.ToExpr for Proven.Op
deriving instance Lean.ToExpr for Proven.Mach.MOp
deriving instance Lean.ToExpr for Proven.Mach.Cond
deriving instance Lean.ToExpr for Proven.Ir.Arg
deriving instance Lean.ToExpr for Proven.Ir.Rhs
deriving instance Lean.ToExpr for Proven.Ir.Tst
deriving instance Lean.ToExpr for Proven.Ir.Inst
deriving instance Lean.ToExpr for Proven.Ir.Term
deriving instance Lean.ToExpr for Proven.Ir.Block
deriving instance Lean.ToExpr for Proven.Ir.Func
deriving instance Lean.ToExpr for Proven.Ir.Prog
deriving instance DecidableEq for Proven.Ir.Arg
deriving instance DecidableEq for Proven.Ir.Rhs
deriving instance DecidableEq for Proven.Ir.Tst
deriving instance DecidableEq for Proven.Ir.Inst
deriving instance DecidableEq for Proven.Ir.Term
deriving instance DecidableEq for Proven.Ir.Block
deriving instance DecidableEq for Proven.Ir.Func
deriving instance DecidableEq for Proven.Ir.Prog
open Lean Elab Term Meta in
elab "irLit% " t:term : term => do
  let ty := mkApp (mkConst ``Proven.Ir.Prog) (mkConst ``Nat)
  let e ← elabTerm t (some ty)
  let e ← instantiateMVars e
  let v ← unsafe evalExpr (Proven.Ir.Prog Nat) ty e
  return toExpr v
def Qlit : Ir.Prog Nat := irLit% ((Ir.alloc (S3.lowerP Nano.IS.InlS3.P)).getD ⟨[], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hQ : Ir.alloc (S3.lowerP Nano.IS.InlS3.P) = some Qlit := by decide +kernel
