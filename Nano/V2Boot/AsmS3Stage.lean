/- B₁: the machine theorem of the v2 stage `Nano.V2S.asmV`, from the S3 program `AsmB` (Nano/V2Boot/AsmS3Self.lean)
through the adapter `Nano.S3Stage.stage`; IR acceptance and code length kernel-checked on literals (ExpS3Stage
pattern). -/
import Nano.V2Boot.AsmS3Self
import Nano.V2Boot.Stage

namespace Nano.V2B
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
theorem asmB_small : smallB AsmB.P.S = true := by decide +kernel

theorem asmB_main : (AsmB.P.S.fn AsmB.P.main).1.length = 1 := by decide

/-- the allocated program (literal) -/
def asmB_Q : Ir.Prog Nat := irLit% ((Ir.alloc (lowerP AsmB.P)).getD ⟨[], 0⟩)
/-- the layout after one and two rounds (literals) -/
def asmB_L1 : Lay := layLit% (rvT.layStep asmB_Q ⟨[], [], 0⟩)
def asmB_L2 : Lay := layLit% (rvT.layStep asmB_Q asmB_L1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asmB_hQ : Ir.alloc (lowerP AsmB.P) = some asmB_Q := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asmB_h1 : rvT.layStep asmB_Q ⟨[], [], 0⟩ = asmB_L1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asmB_h2 : rvT.layStep asmB_Q asmB_L1 = asmB_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asmB_fix : rvT.layStep asmB_Q asmB_L2 = asmB_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asmB_hm : 2 ≤ Target.rounds asmB_Q := by decide +kernel
theorem asmB_hL : rvT.layout asmB_Q 2 ⟨[], [], 0⟩ = asmB_L2 := by
  simp only [Target.layout, asmB_h1, asmB_h2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asmB_hE : (rvT.emitP asmB_Q asmB_L2).isSome = true := by decide +kernel

/-- the IR compiler accepts the program -/
theorem asmB_compiles : (Ir.compileW (lowerP AsmB.P)).isSome = true :=
  compileW_isSome 2 asmB_hQ asmB_hm asmB_hL asmB_fix asmB_hE

/-- the machine theorem of the S3 twin `asmVS` (Sail axioms only) -/
theorem asmB_implementsS :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words AsmB.P)
      (fun xs => asmVS xs.data.toList) (spaceP AsmB.P) (2 ^ 20) true :=
  stage AsmB.computes asmB_small asmB_main asmB_compiles

/-- **the machine theorem of the v2 stage `Nano.V2S.asmV`** (inputs ≤ 2^20 bytes; bridge `asmVS_eq`) -/
theorem asmB_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words AsmB.P)
      (fun xs => Nano.V2S.asmV xs.data.toList) (spaceP AsmB.P) (2 ^ 20) true :=
  implements_congr (fun _ h => asmVS_eq _ (by omega)) asmB_implementsS

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asmB_code_len' : (((rvT.emitP asmB_Q asmB_L2).map rvT.words).getD []).length < 2 ^ 17 := by
  decide +kernel

theorem asmB_code_len : (S3.words AsmB.P).length < 2 ^ 17 := by
  rw [words_eq' 2 asmB_hQ asmB_hm asmB_hL asmB_fix]; exact asmB_code_len'

end Nano.V2B
