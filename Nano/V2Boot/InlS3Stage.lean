/- B₁: the machine theorem of the v2 stage `Nano.V2.inlV`, from the S3 program `InlB` (Nano/V2Boot/InlS3Self.lean)
through the adapter `Nano.S3Stage.stage`; IR acceptance and code length kernel-checked on literals (ExpS3Stage
pattern). -/
import Nano.V2Boot.InlS3Self
import Nano.V2Boot.Stage

namespace Nano.V2B
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
theorem inlB_small : smallB InlB.P.S = true := by decide +kernel

theorem inlB_main : (InlB.P.S.fn InlB.P.main).1.length = 1 := by decide

/-- the allocated program (literal) -/
def inlB_Q : Ir.Prog Nat := irLit% ((Ir.alloc (lowerP InlB.P)).getD ⟨[], 0⟩)
/-- the layout after one and two rounds (literals) -/
def inlB_L1 : Lay := layLit% (rvT.layStep inlB_Q ⟨[], [], 0⟩)
def inlB_L2 : Lay := layLit% (rvT.layStep inlB_Q inlB_L1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlB_hQ : Ir.alloc (lowerP InlB.P) = some inlB_Q := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlB_h1 : rvT.layStep inlB_Q ⟨[], [], 0⟩ = inlB_L1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlB_h2 : rvT.layStep inlB_Q inlB_L1 = inlB_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlB_fix : rvT.layStep inlB_Q inlB_L2 = inlB_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlB_hm : 2 ≤ Target.rounds inlB_Q := by decide +kernel
theorem inlB_hL : rvT.layout inlB_Q 2 ⟨[], [], 0⟩ = inlB_L2 := by
  simp only [Target.layout, inlB_h1, inlB_h2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlB_hE : (rvT.emitP inlB_Q inlB_L2).isSome = true := by decide +kernel

/-- the IR compiler accepts the program -/
theorem inlB_compiles : (Ir.compileW (lowerP InlB.P)).isSome = true :=
  compileW_isSome 2 inlB_hQ inlB_hm inlB_hL inlB_fix inlB_hE

/-- the machine theorem of the S3 twin `inlVS` (Sail axioms only) -/
theorem inlB_implementsS :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words InlB.P)
      (fun xs => inlVS xs.data.toList) (spaceP InlB.P) (2 ^ 20) true :=
  stage InlB.computes inlB_small inlB_main inlB_compiles

/-- **the machine theorem of the v2 stage `Nano.V2.inlV`** (inputs ≤ 2^20 bytes; bridge `inlVS_eq`) -/
theorem inlB_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words InlB.P)
      (fun xs => Nano.V2.inlV xs.data.toList) (spaceP InlB.P) (2 ^ 20) true :=
  implements_congr (fun _ h => inlVS_eq _ (by omega)) inlB_implementsS

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlB_code_len' : (((rvT.emitP inlB_Q inlB_L2).map rvT.words).getD []).length < 2 ^ 17 := by
  decide +kernel

theorem inlB_code_len : (S3.words InlB.P).length < 2 ^ 17 := by
  rw [words_eq' 2 inlB_hQ inlB_hm inlB_hL inlB_fix]; exact inlB_code_len'

end Nano.V2B
