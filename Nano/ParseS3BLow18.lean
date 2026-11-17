/- Stage 2b, kernel checks part 2a: the lowering of function 18 (the largest) as a literal, checked here; its
allocation in Nano/ParseS3BAllocB.lean (split in two files to keep each build's memory down). -/
import Nano.ParseS3BAllocA

namespace Nano.PS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
/-- function 18, lowered (literal) -/
def stage2B_G18 : Ir.Func Nat := funcLit% (lowFn Stage2B.P ⟨18, by decide⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_g18 : lowFn Stage2B.P ⟨18, by decide⟩ = stage2B_G18 := by decide +kernel

end Nano.PS
