import Nano.V2.Flat
import Riscv.Steps.GenALU
import Riscv.Steps.GenMem
import Riscv.Steps.GenBranch
import Riscv.Steps.GenMul
/- nano v2 small backend, proof layer 4a: the encoder `I.enc` (Nano/V2/Gen.lean) produces, for every encodable
instruction (`I.wf`), exactly the word the Sail step lemmas (`Proven.G.step_*`, Riscv/Steps) are stated for. -/
namespace Nano.V2B
open Proven

theorem bits_nat (u k : Nat) (h : u < 2 ^ k) : bits (u : Int) k = u := by
  unfold bits; rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast h)]; simp

theorem bits_lt (x : Int) (k : Nat) : bits x k < 2 ^ k := by
  unfold bits
  have e : ((2 : Int) ^ k) = ((2 ^ k : Nat) : Int) := by push_cast; rfl
  have h1 : (0 : Int) < ((2 ^ k : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos k
  have h2 := Int.emod_lt_of_pos x h1
  have h3 := Int.emod_nonneg x (Int.ne_of_gt h1)
  rw [e]; omega

/-- one 32-bit word, bit by bit -/
macro "encbits" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [G.encS, Proven.wB, Proven.immB, Proven.wJ, Proven.immJ, BitVec.getLsbD_ofNat, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_and, BitVec.getLsbD_ofFin]
  iterate 32 (rcases i with _ | i; · simp (config := {decide := true}) [Nat.testBit_eq_decide_div_mod_eq] <;>
    (try simp only [← Bool.decide_or, ← Bool.decide_and, decide_eq_decide]) <;> omega)
  omega))

set_option maxRecDepth 100000

theorem encSt_eq (f3 : Nat) (hf : f3 < 8) (rs2 rs1 : Fin 32) (u : Nat) (hu : u < 4096) :
    BitVec.ofNat 32 (encSt f3 rs2.val rs1.val (u : Int)) = G.encS (BitVec.ofNat 3 f3) (BitVec.ofNat 12 u) rs2 rs1 := by
  unfold encSt; rw [bits_nat u 12 hu]; encbits

theorem encBt8_eq (f3 : Nat) (hf : f3 < 8) (rs1 rs2 : Fin 32) :
    BitVec.ofNat 32 (encBt f3 rs1.val rs2.val 8) = wB (BitVec.ofNat 3 f3) (.ofFin rs1) (.ofFin rs2) 4#12 := by
  unfold encBt; rw [show bits (8 : Int) 13 = 8 from rfl]; encbits

theorem encJt_eq (v : Nat) (hv : v < 2 ^ 20) :
    BitVec.ofNat 32 (encJt ((2 * v : Nat) : Int)) = wJ (.ofFin (0 : Fin 32)) (BitVec.ofNat 20 v) := by
  unfold encJt; rw [bits_nat (2 * v) 21 (by omega)]; encbits

end Nano.V2B
