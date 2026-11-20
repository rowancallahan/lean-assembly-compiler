/- Stage 2b (the parser machine on the tag format) through S3: the machine theorem, from the S3 program `Stage2B` (`Nano.ParseS3BSelf.lean`, the S3 compile with its
certificates) through the adapter (`Nano.S3Stage.stage`). The IR compiler's acceptance and the code length are
kernel-checked on literals (`irLit%`, `layLit%`: the allocated program and the layout, elaborated by evaluation and
checked by the kernel; see Nano/S3Stage.lean). -/
import Legacy.Nano.ParseS3BSelf

namespace Nano.PS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
theorem stage2B_small : smallB Stage2B.P.S = true := by decide +kernel

theorem stage2B_main : (Stage2B.P.S.fn Stage2B.P.main).1.length = 1 := by decide

/-- the allocated program (literal) -/
def stage2B_Q : Ir.Prog Nat := irLit% ((Ir.alloc (lowerP Stage2B.P)).getD ⟨[], 0⟩)
end Nano.PS
