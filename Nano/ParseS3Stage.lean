/- Stage 2 (the parser) through S3: the machine theorem, from the S3 program `Stage2S3` (`Nano/ParseS3Self.lean`, the S3 compile with its
certificates) through the adapter (`Nano.S3Stage.stage`). The IR compiler's acceptance and the code length are
kernel-checked on literals (`irLit%`, `layLit%`: the allocated program and the layout, elaborated by evaluation and
checked by the kernel; see Nano/S3Stage.lean). -/
import Nano.ParseS3Self

namespace Nano.PS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
theorem stage2S3_small : smallB Stage2S3.P.S = true := by decide +kernel

theorem stage2S3_main : (Stage2S3.P.S.fn Stage2S3.P.main).1.length = 1 := by decide

/-- the allocated program (literal) -/
def stage2S3_Q : Ir.Prog Nat := irLit% ((Ir.alloc (lowerP Stage2S3.P)).getD ⟨[], 0⟩)
/-- the layout after one and two rounds (literals) -/
def stage2S3_L1 : Lay := layLit% (rvT.layStep stage2S3_Q ⟨[], [], 0⟩)
def stage2S3_L2 : Lay := layLit% (rvT.layStep stage2S3_Q stage2S3_L1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2S3_hQ : Ir.alloc (lowerP Stage2S3.P) = some stage2S3_Q := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2S3_h1 : rvT.layStep stage2S3_Q ⟨[], [], 0⟩ = stage2S3_L1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2S3_h2 : rvT.layStep stage2S3_Q stage2S3_L1 = stage2S3_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2S3_fix : rvT.layStep stage2S3_Q stage2S3_L2 = stage2S3_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2S3_hm : 2 ≤ Target.rounds stage2S3_Q := by decide +kernel
theorem stage2S3_hL : rvT.layout stage2S3_Q 2 ⟨[], [], 0⟩ = stage2S3_L2 := by
  simp only [Target.layout, stage2S3_h1, stage2S3_h2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2S3_hE : (rvT.emitP stage2S3_Q stage2S3_L2).isSome = true := by decide +kernel

/-- the IR compiler accepts the program -/
theorem stage2S3_compiles : (Ir.compileW (lowerP Stage2S3.P)).isSome = true :=
  compileW_isSome 2 stage2S3_hQ stage2S3_hm stage2S3_hL stage2S3_fix stage2S3_hE

/-- **the machine theorem of stage2, route S3** (Sail axioms only) -/
theorem stage2S3_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words Stage2S3.P)
      (fun xs => stage2S xs.data.toList) (spaceP Stage2S3.P) (2 ^ 20) true :=
  stage Stage2S3.computes stage2S3_small stage2S3_main stage2S3_compiles

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2S3_code_len' : (((rvT.emitP stage2S3_Q stage2S3_L2).map rvT.words).getD []).length < 2 ^ 17 := by
  decide +kernel

theorem stage2S3_code_len : (S3.words Stage2S3.P).length < 2 ^ 17 := by
  rw [words_eq' 2 stage2S3_hQ stage2S3_hm stage2S3_hL stage2S3_fix]; exact stage2S3_code_len'

/-- the compiled stage computes `stage2` on every input -/
theorem stage2S3_f (x : List UInt8) : (fun xs : ByteArray => stage2S xs.data.toList) (Nano.Link.ofL x) = PB.stage2 x :=
  stage2S_eq x

end Nano.PS
