/- The assembler `asm` through S3 (branch nano-s3-all): the machine theorem, from the S3 program `AsmS3` (`Nano/AsmS3Self.lean`, `asmS`, the S3 compile with its
certificates) through the adapter (`Nano.S3Stage.stage`). The IR compiler's acceptance and the code length are
kernel-checked on literals (`irLit%`, `layLit%`: the allocated program and the layout, elaborated by evaluation and
checked by the kernel; see Nano/S3Stage.lean). -/
import Legacy.Nano.AsmS3Self

namespace Nano.AS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
theorem asmS3_small : smallB AsmS3.P.S = true := by decide +kernel

theorem asmS3_main : (AsmS3.P.S.fn AsmS3.P.main).1.length = 1 := by decide

/-- the allocated program (literal) -/
def asmS3_Q : Ir.Prog Nat := irLit% ((Ir.alloc (lowerP AsmS3.P)).getD ⟨[], 0⟩)
/-- the layout after one and two rounds (literals) -/
def asmS3_L1 : Lay := layLit% (rvT.layStep asmS3_Q ⟨[], [], 0⟩)
def asmS3_L2 : Lay := layLit% (rvT.layStep asmS3_Q asmS3_L1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asmS3_hQ : Ir.alloc (lowerP AsmS3.P) = some asmS3_Q := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asmS3_h1 : rvT.layStep asmS3_Q ⟨[], [], 0⟩ = asmS3_L1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asmS3_h2 : rvT.layStep asmS3_Q asmS3_L1 = asmS3_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asmS3_fix : rvT.layStep asmS3_Q asmS3_L2 = asmS3_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asmS3_hm : 2 ≤ Target.rounds asmS3_Q := by decide +kernel
theorem asmS3_hL : rvT.layout asmS3_Q 2 ⟨[], [], 0⟩ = asmS3_L2 := by
  simp only [Target.layout, asmS3_h1, asmS3_h2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asmS3_hE : (rvT.emitP asmS3_Q asmS3_L2).isSome = true := by decide +kernel

/-- the IR compiler accepts the program -/
theorem asmS3_compiles : (Ir.compileW (lowerP AsmS3.P)).isSome = true :=
  compileW_isSome 2 asmS3_hQ asmS3_hm asmS3_hL asmS3_fix asmS3_hE

/-- **the machine theorem of the assembler `asm`, route S3** (Sail axioms only) -/
theorem asmS3_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words AsmS3.P)
      (fun xs => asmS xs.data.toList) (spaceP AsmS3.P) (2 ^ 20) true :=
  stage AsmS3.computes asmS3_small asmS3_main asmS3_compiles

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asmS3_code_len' : (((rvT.emitP asmS3_Q asmS3_L2).map rvT.words).getD []).length < 2 ^ 17 := by
  decide +kernel

theorem asmS3_code_len : (S3.words AsmS3.P).length < 2 ^ 17 := by
  rw [words_eq' 2 asmS3_hQ asmS3_hm asmS3_hL asmS3_fix]; exact asmS3_code_len'

/-- the compiled stage computes `Nano.asm` on every input -/
theorem asmS3_f (x : List UInt8) : (fun xs : ByteArray => asmS xs.data.toList) (Nano.Link.ofL x) = Nano.asm x :=
  asmS_eq x

end Nano.AS
