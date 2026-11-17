/- Stage 2b, kernel checks part 2b: the allocation of function 18 (the largest; Nano/ParseS3BStage.lean), on its
lowered literal (Nano/ParseS3BLow18.lean). -/
import Nano.ParseS3BLow18

namespace Nano.PS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
/-- function 18, allocated (literal) -/
def stage2B_F18 : Ir.Func Nat := funcLit% ((Func.alloc1 stage2B_G18).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a18' : Func.alloc1 stage2B_G18 = some stage2B_F18 := by decide +kernel
theorem stage2B_a18 : Func.alloc1 (lowFn Stage2B.P ⟨18, by decide⟩) = some stage2B_F18 := by
  rw [stage2B_g18]; exact stage2B_a18'

end Nano.PS
