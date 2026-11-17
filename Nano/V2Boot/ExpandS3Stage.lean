/- B₁: the machine theorem of the v2 stage `Nano.V2.mexpV`, from the S3 program `ExpB` (Nano/V2Boot/ExpandS3Self.lean)
through the adapter `Nano.S3Stage.stage`; IR acceptance and code length kernel-checked on literals (ExpS3Stage
pattern). -/
import Nano.V2Boot.ExpandS3Self
import Nano.V2Boot.Stage

namespace Nano.V2B
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
theorem expB_small : smallB ExpB.P.S = true := by decide +kernel

theorem expB_main : (ExpB.P.S.fn ExpB.P.main).1.length = 1 := by decide

/-- the allocated program (literal) -/
def expB_Q : Ir.Prog Nat := irLit% ((Ir.alloc (lowerP ExpB.P)).getD ⟨[], 0⟩)
/-- the layout after one and two rounds (literals) -/
def expB_L1 : Lay := layLit% (rvT.layStep expB_Q ⟨[], [], 0⟩)
def expB_L2 : Lay := layLit% (rvT.layStep expB_Q expB_L1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem expB_hQ : Ir.alloc (lowerP ExpB.P) = some expB_Q := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem expB_h1 : rvT.layStep expB_Q ⟨[], [], 0⟩ = expB_L1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem expB_h2 : rvT.layStep expB_Q expB_L1 = expB_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem expB_fix : rvT.layStep expB_Q expB_L2 = expB_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem expB_hm : 2 ≤ Target.rounds expB_Q := by decide +kernel
theorem expB_hL : rvT.layout expB_Q 2 ⟨[], [], 0⟩ = expB_L2 := by
  simp only [Target.layout, expB_h1, expB_h2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem expB_hE : (rvT.emitP expB_Q expB_L2).isSome = true := by decide +kernel

/-- the IR compiler accepts the program -/
theorem expB_compiles : (Ir.compileW (lowerP ExpB.P)).isSome = true :=
  compileW_isSome 2 expB_hQ expB_hm expB_hL expB_fix expB_hE

/-- the machine theorem of the S3 twin `mexpVS` (Sail axioms only) -/
theorem expB_implementsS :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words ExpB.P)
      (fun xs => mexpVS xs.data.toList) (spaceP ExpB.P) (2 ^ 20) true :=
  stage ExpB.computes expB_small expB_main expB_compiles

/-- **the machine theorem of the v2 stage `Nano.V2.mexpV`** (inputs ≤ 2^20 bytes; bridge `mexpVS_eq`) -/
theorem expB_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words ExpB.P)
      (fun xs => Nano.V2.mexpV xs.data.toList) (spaceP ExpB.P) (2 ^ 20) true :=
  implements_congr (fun _ h => mexpVS_eq _ (by omega)) expB_implementsS

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem expB_code_len' : (((rvT.emitP expB_Q expB_L2).map rvT.words).getD []).length < 2 ^ 17 := by
  decide +kernel

theorem expB_code_len : (S3.words ExpB.P).length < 2 ^ 17 := by
  rw [words_eq' 2 expB_hQ expB_hm expB_hL expB_fix]; exact expB_code_len'

end Nano.V2B
