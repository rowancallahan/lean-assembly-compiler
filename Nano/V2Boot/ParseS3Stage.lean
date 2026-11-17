/- B₁: the machine theorem of the v2 stage `Nano.V2S.p2bV`, from the S3 program `ParseB` (Nano/V2Boot/ParseS3Self.lean)
through the adapter `Nano.S3Stage.stage`; IR acceptance and code length kernel-checked on literals (ExpS3Stage
pattern). -/
import Nano.V2Boot.ParseS3Self
import Nano.V2Boot.Stage

namespace Nano.V2B
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
theorem parseB_small : smallB ParseB.P.S = true := by decide +kernel

theorem parseB_main : (ParseB.P.S.fn ParseB.P.main).1.length = 1 := by decide

/-- the allocated program (literal) -/
def parseB_Q : Ir.Prog Nat := irLit% ((Ir.alloc (lowerP ParseB.P)).getD ⟨[], 0⟩)
/-- the layout after one and two rounds (literals) -/
def parseB_L1 : Lay := layLit% (rvT.layStep parseB_Q ⟨[], [], 0⟩)
def parseB_L2 : Lay := layLit% (rvT.layStep parseB_Q parseB_L1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem parseB_hQ : Ir.alloc (lowerP ParseB.P) = some parseB_Q := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem parseB_h1 : rvT.layStep parseB_Q ⟨[], [], 0⟩ = parseB_L1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem parseB_h2 : rvT.layStep parseB_Q parseB_L1 = parseB_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem parseB_fix : rvT.layStep parseB_Q parseB_L2 = parseB_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem parseB_hm : 2 ≤ Target.rounds parseB_Q := by decide +kernel
theorem parseB_hL : rvT.layout parseB_Q 2 ⟨[], [], 0⟩ = parseB_L2 := by
  simp only [Target.layout, parseB_h1, parseB_h2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem parseB_hE : (rvT.emitP parseB_Q parseB_L2).isSome = true := by decide +kernel

/-- the IR compiler accepts the program -/
theorem parseB_compiles : (Ir.compileW (lowerP ParseB.P)).isSome = true :=
  compileW_isSome 2 parseB_hQ parseB_hm parseB_hL parseB_fix parseB_hE

/-- the machine theorem of the S3 twin `p2bVS` (Sail axioms only) -/
theorem parseB_implementsS :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words ParseB.P)
      (fun xs => p2bVS xs.data.toList) (spaceP ParseB.P) (2 ^ 20) true :=
  stage ParseB.computes parseB_small parseB_main parseB_compiles

/-- **the machine theorem of the v2 stage `Nano.V2S.p2bV`** (inputs ≤ 2^20 bytes; bridge `p2bVS_eq`) -/
theorem parseB_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words ParseB.P)
      (fun xs => Nano.V2S.p2bV xs.data.toList) (spaceP ParseB.P) (2 ^ 20) true :=
  implements_congr (fun _ h => p2bVS_eq _ (by omega)) parseB_implementsS

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem parseB_code_len' : (((rvT.emitP parseB_Q parseB_L2).map rvT.words).getD []).length < 2 ^ 17 := by
  decide +kernel

theorem parseB_code_len : (S3.words ParseB.P).length < 2 ^ 17 := by
  rw [words_eq' 2 parseB_hQ parseB_hm parseB_hL parseB_fix]; exact parseB_code_len'

end Nano.V2B
