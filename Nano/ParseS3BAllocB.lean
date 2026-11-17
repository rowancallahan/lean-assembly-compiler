/- Stage 2b, kernel checks part 2: the allocation of function 18 (the largest; Nano/ParseS3BStage.lean). -/
import Nano.ParseS3BAllocA

namespace Nano.PS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
/-- function 18, allocated (literal) -/
def stage2B_F18 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨18, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a18 : Func.alloc1 (lowFn Stage2B.P ⟨18, by decide⟩) = some stage2B_F18 := by decide +kernel

end Nano.PS
