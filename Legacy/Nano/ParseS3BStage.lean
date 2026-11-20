/- **Stage 2b (the parser machine on the tag format) through S3: the machine theorem.** From the S3 program
`Stage2B` (Nano/ParseS3BSelf.lean: S3 compile, certificates, `computes`) through the adapter (`Nano.S3Stage.stage`).
The IR compiler's acceptance and the code length are kernel-checked on literals: the allocation per function
(Nano/ParseS3BAllocA.lean, Nano/ParseS3BAllocB.lean), the layout to its fixpoint (Nano/ParseS3BLayA.lean,
Nano/ParseS3BLayB.lean) and the emission (Nano/ParseS3BEmitA.lean, Nano/ParseS3BEmitB.lean and here, in pieces by
Nano/EmitSplit.lean; `compiles_len`). Split in eight files to keep each build ≤ 5 min. -/
import Legacy.Nano.ParseS3BEmitB

set_option Elab.async false

namespace Nano.PS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_eC : rvT.emitFsQ stage2B_Q stage2B_L2 19 30339 [stage2B_F19, stage2B_F20, stage2B_F21, stage2B_F22, stage2B_F23, stage2B_F24, stage2B_F25, stage2B_F26, stage2B_F27, stage2B_F28, stage2B_F29, stage2B_F30, stage2B_F31, stage2B_F32, stage2B_F33, stage2B_F34, stage2B_F35, stage2B_F36, stage2B_F37, stage2B_F38, stage2B_F39, stage2B_F40, stage2B_F41] = some stage2B_L2.ex := by decide +kernel

set_option maxRecDepth 100000 in
theorem stage2B_eQ : rvT.emitFsQ stage2B_Q stage2B_L2 0 44 stage2B_Q.funcs = some stage2B_L2.ex :=
  (congrArg (rvT.emitFsQ stage2B_Q stage2B_L2 0 44)
    (rfl : stage2B_Q.funcs = [stage2B_F0, stage2B_F1, stage2B_F2, stage2B_F3, stage2B_F4, stage2B_F5, stage2B_F6, stage2B_F7, stage2B_F8, stage2B_F9, stage2B_F10, stage2B_F11, stage2B_F12, stage2B_F13, stage2B_F14, stage2B_F15, stage2B_F16, stage2B_F17] ++ ([stage2B_F18] ++ [stage2B_F19, stage2B_F20, stage2B_F21, stage2B_F22, stage2B_F23, stage2B_F24, stage2B_F25, stage2B_F26, stage2B_F27, stage2B_F28, stage2B_F29, stage2B_F30, stage2B_F31, stage2B_F32, stage2B_F33, stage2B_F34, stage2B_F35, stage2B_F36, stage2B_F37, stage2B_F38, stage2B_F39, stage2B_F40, stage2B_F41]))).trans
  ((Target.emitFsQ_append_of rvT _ _ _ _ stage2B_eA rfl).trans
  ((Target.emitFsQ_append_of rvT _ _ _ _ stage2B_eB rfl).trans stage2B_eC))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_hE :
    ((rvT.emitP stage2B_Q stage2B_L2).map fun c => decide ((rvT.words c).length < 2 ^ 17)) = some true :=
  Target.emitP_lt rvT stage2B_Q stage2B_L2 44 (by decide +kernel) (by decide +kernel) stage2B_eQ (by decide +kernel)

theorem stage2B_cl : (Ir.compileW (lowerP Stage2B.P)).isSome = true ∧ (S3.words Stage2B.P).length < 2 ^ 17 :=
  compiles_len 2 stage2B_hQ stage2B_hm stage2B_hL stage2B_fix stage2B_hE

/-- the IR compiler accepts the program -/
theorem stage2B_compiles : (Ir.compileW (lowerP Stage2B.P)).isSome = true := stage2B_cl.1

theorem stage2B_code_len : (S3.words Stage2B.P).length < 2 ^ 17 := stage2B_cl.2

/-- **the machine theorem of stage 2b, route S3** (Sail axioms only) -/
theorem stage2B_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words Stage2B.P)
      (fun xs => stage2b xs.data.toList) (spaceP Stage2B.P) (2 ^ 20) true :=
  stage Stage2B.computes stage2B_small stage2B_main stage2B_compiles

/-- the compiled stage after stage 2a computes `stage2` on every input -/
theorem stage2B_f (x : List UInt8) :
    (fun xs : ByteArray => stage2b xs.data.toList) (Nano.Link.ofL (stage2a x)) = PB.stage2 x :=
  stage2b_stage2a x

end Nano.PS
