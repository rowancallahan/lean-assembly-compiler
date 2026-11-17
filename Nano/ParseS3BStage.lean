/- Stage 2b (the parser machine on the tag format) through S3: the machine theorem, from the S3 program `Stage2B` (`Nano.ParseS3BSelf.lean`, the S3 compile with its
certificates) through the adapter (`Nano.S3Stage.stage`). The IR compiler's acceptance and the code length are
kernel-checked on literals (`irLit%`, `layLit%`: the allocated program and the layout, elaborated by evaluation and
checked by the kernel; see Nano/S3Stage.lean). -/
import Nano.ParseS3BSelf

namespace Nano.PS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
theorem stage2B_small : smallB Stage2B.P.S = true := by decide +kernel

theorem stage2B_main : (Stage2B.P.S.fn Stage2B.P.main).1.length = 1 := by decide

/-- the allocated program (literal) -/
def stage2B_Q : Ir.Prog Nat := irLit% ((Ir.alloc (lowerP Stage2B.P)).getD ⟨[], 0⟩)
/-- the layout after one and two rounds (literals) -/
def stage2B_L1 : Lay := layLit% (rvT.layStep stage2B_Q ⟨[], [], 0⟩)
def stage2B_L2 : Lay := layLit% (rvT.layStep stage2B_Q stage2B_L1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_hQ : Ir.alloc (lowerP Stage2B.P) = some stage2B_Q := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_h1 : rvT.layStep stage2B_Q ⟨[], [], 0⟩ = stage2B_L1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_h2 : rvT.layStep stage2B_Q stage2B_L1 = stage2B_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_fix : rvT.layStep stage2B_Q stage2B_L2 = stage2B_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_hm : 2 ≤ Target.rounds stage2B_Q := by decide +kernel
theorem stage2B_hL : rvT.layout stage2B_Q 2 ⟨[], [], 0⟩ = stage2B_L2 := by
  simp only [Target.layout, stage2B_h1, stage2B_h2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_hE : (rvT.emitP stage2B_Q stage2B_L2).isSome = true := by decide +kernel

/-- the IR compiler accepts the program -/
theorem stage2B_compiles : (Ir.compileW (lowerP Stage2B.P)).isSome = true :=
  compileW_isSome 2 stage2B_hQ stage2B_hm stage2B_hL stage2B_fix stage2B_hE

/-- **the machine theorem of stage2, route S3** (Sail axioms only) -/
theorem stage2B_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words Stage2B.P)
      (fun xs => stage2b xs.data.toList) (spaceP Stage2B.P) (2 ^ 20) true :=
  stage Stage2B.computes stage2B_small stage2B_main stage2B_compiles

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_code_len' : (((rvT.emitP stage2B_Q stage2B_L2).map rvT.words).getD []).length < 2 ^ 17 := by
  decide +kernel

theorem stage2B_code_len : (S3.words Stage2B.P).length < 2 ^ 17 := by
  rw [words_eq' 2 stage2B_hQ stage2B_hm stage2B_hL stage2B_fix]; exact stage2B_code_len'

/-- the compiled stage after stage 2a computes `stage2` on every input -/
theorem stage2B_f (x : List UInt8) :
    (fun xs : ByteArray => stage2b xs.data.toList) (Nano.Link.ofL (stage2a x)) = PB.stage2 x :=
  stage2b_stage2a x

end Nano.PS
