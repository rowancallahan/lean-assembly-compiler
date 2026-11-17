/- B₁: the machine theorem of the v2 stage `Nano.V2S.lexV`, from the S3 program `LexB` (Nano/V2Boot/LexS3Self.lean)
through the adapter `Nano.S3Stage.stage`; IR acceptance and code length kernel-checked on literals (ExpS3Stage
pattern). -/
import Nano.V2Boot.LexS3Self
import Nano.V2Boot.Stage

namespace Nano.V2B
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
theorem lexB_small : smallB LexB.P.S = true := by decide +kernel

theorem lexB_main : (LexB.P.S.fn LexB.P.main).1.length = 1 := by decide

/-- the allocated program (literal) -/
def lexB_Q : Ir.Prog Nat := irLit% ((Ir.alloc (lowerP LexB.P)).getD ⟨[], 0⟩)
/-- the layout after one and two rounds (literals) -/
def lexB_L1 : Lay := layLit% (rvT.layStep lexB_Q ⟨[], [], 0⟩)
def lexB_L2 : Lay := layLit% (rvT.layStep lexB_Q lexB_L1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lexB_hQ : Ir.alloc (lowerP LexB.P) = some lexB_Q := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lexB_h1 : rvT.layStep lexB_Q ⟨[], [], 0⟩ = lexB_L1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lexB_h2 : rvT.layStep lexB_Q lexB_L1 = lexB_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lexB_fix : rvT.layStep lexB_Q lexB_L2 = lexB_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lexB_hm : 2 ≤ Target.rounds lexB_Q := by decide +kernel
theorem lexB_hL : rvT.layout lexB_Q 2 ⟨[], [], 0⟩ = lexB_L2 := by
  simp only [Target.layout, lexB_h1, lexB_h2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lexB_hE : (rvT.emitP lexB_Q lexB_L2).isSome = true := by decide +kernel

/-- the IR compiler accepts the program -/
theorem lexB_compiles : (Ir.compileW (lowerP LexB.P)).isSome = true :=
  compileW_isSome 2 lexB_hQ lexB_hm lexB_hL lexB_fix lexB_hE

/-- the machine theorem of the S3 twin `lexVS` (Sail axioms only) -/
theorem lexB_implementsS :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words LexB.P)
      (fun xs => lexVS xs.data.toList) (spaceP LexB.P) (2 ^ 20) true :=
  stage LexB.computes lexB_small lexB_main lexB_compiles

/-- **the machine theorem of the v2 stage `Nano.V2S.lexV`** (inputs ≤ 2^20 bytes; bridge `lexVS_eq`) -/
theorem lexB_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words LexB.P)
      (fun xs => Nano.V2S.lexV xs.data.toList) (spaceP LexB.P) (2 ^ 20) true :=
  implements_congr (fun _ h => lexVS_eq _ (by omega)) lexB_implementsS

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lexB_code_len' : (((rvT.emitP lexB_Q lexB_L2).map rvT.words).getD []).length < 2 ^ 17 := by
  decide +kernel

theorem lexB_code_len : (S3.words LexB.P).length < 2 ^ 17 := by
  rw [words_eq' 2 lexB_hQ lexB_hm lexB_hL lexB_fix]; exact lexB_code_len'

end Nano.V2B
