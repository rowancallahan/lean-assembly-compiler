/- Stage 2b, kernel checks part 5 (Nano/ParseS3BStage.lean): the emission of functions 0 .. 17
(`Proven.Ir.Target.emitFsQ`, Nano/EmitSplit.lean). -/
import Legacy.Nano.ParseS3BLayB
import Legacy.Nano.EmitSplit

set_option Elab.async false


namespace Nano.PS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_eA : rvT.emitFsQ stage2B_Q stage2B_L2 0 44 [stage2B_F0, stage2B_F1, stage2B_F2, stage2B_F3, stage2B_F4, stage2B_F5, stage2B_F6, stage2B_F7, stage2B_F8, stage2B_F9, stage2B_F10, stage2B_F11, stage2B_F12, stage2B_F13, stage2B_F14, stage2B_F15, stage2B_F16, stage2B_F17] = some 12585 := by decide +kernel

end Nano.PS
