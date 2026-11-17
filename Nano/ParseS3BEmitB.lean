/- Stage 2b, kernel checks part 6 (Nano/ParseS3BStage.lean): the emission of function 18 (the largest,
17754 words). -/
import Nano.ParseS3BEmitA

set_option Elab.async false

namespace Nano.PS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_eB : rvT.emitFsQ stage2B_Q stage2B_L2 18 12585 [stage2B_F18] = some 30339 := by decide +kernel

end Nano.PS
