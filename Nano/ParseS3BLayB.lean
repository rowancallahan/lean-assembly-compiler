/- Stage 2b, kernel checks part 4 (Nano/ParseS3BStage.lean): the layout fixpoint `stage2B_fix`, the rounds bound
`stage2B_hm` and the layout `stage2B_hL`. -/
import Nano.ParseS3BLayA

set_option Elab.async false

namespace Nano.PS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_fix : rvT.layStep stage2B_Q stage2B_L2 = stage2B_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_hm : 2 ≤ Target.rounds stage2B_Q := by decide +kernel
theorem stage2B_hL : rvT.layout stage2B_Q 2 ⟨[], [], 0⟩ = stage2B_L2 := by
  simp only [Target.layout, stage2B_h1, stage2B_h2]
end Nano.PS
