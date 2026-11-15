/- Register-generic step lemmas for the RV64 M extension: `mul`, `mulhu`, `divu`, `remu`
(machinery: `Riscv/Steps/GenTac.lean`, as `GenALU.lean`).

M extension: `Cfg` (`Riscv/Steps/Step.lean`) fixes `misa = 0x800000000014112F`, whose bit 12 (`M`) is set, and the
bare-metal boot path establishes `Cfg` (`Riscv/Back/BootReset.lean`: the model's reset value of `misa` differs
only in `V`, which the stub clears), so no extra hypothesis is needed: the words below decode and execute in
every `Cfg` state.  Semantics checked against the model (`LeanRV64D/InstsEnd.lean`, `execute_MUL`,
`execute_DIV`, `execute_REM`; `mult_to_bits_half` in `Arithmetic.lean`):
* `mul`: low 64 bits of the product (signed × signed, whose low half is the unsigned one) = `a * b`;
* `mulhu`: high 64 bits of the unsigned 128-bit product;
* `divu`: `a / b`, and all ones when `b = 0` (Lean's `BitVec` / `UInt64` / `Nat` give `0`: callers guard);
* `remu`: `a % b`, and `a` when `b = 0` (= Lean's `x % 0 = x`). -/
import Riscv.Steps.GenALU
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Proven
namespace G

/-! ## The model's arithmetic as `BitVec` operations -/

theorem toInt_emod64 (a : BitVec 64) : a.toInt % ((18446744073709551616 : Nat) : Int) = (a.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := a.isLt
  split <;> omega

@[simp] theorem mul_low (a b : BitVec 64) :
    mult_to_bits_half Signedness.Signed Signedness.Signed a b VectorHalf.Low = a * b := by
  simp only [mult_to_bits_half, to_bits_truncate, Sail.get_slice_int, Sail.BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, BitVec.extractLsb_toNat, BitVec.toNat_mul]
  have h1 : (0:Int) ≤ a.toInt * b.toInt % 680564733841876926926749214863536422912 := Int.emod_nonneg _ (by decide)
  apply Int.ofNat_inj.1
  rw [Int.natCast_emod, Int.toNat_of_nonneg h1, Int.emod_emod_of_dvd _ (by decide), Int.natCast_emod, Int.natCast_mul,
    Int.mul_emod, toInt_emod64, toInt_emod64]

@[simp] theorem mul_low_x (a b : BitVec 64) :
    mult_to_bits_half (l := LeanRV64D.Functions.xlen) Signedness.Signed Signedness.Signed a b VectorHalf.Low = a * b := mul_low a b

/-- what `divu` writes: all ones for a zero divisor -/
def divu (a b : BitVec 64) : BitVec 64 := if b = 0 then BitVec.allOnes 64 else a / b

theorem tbt_nat (n : Nat) : (to_bits_truncate (l := 64) (n : Int)) = BitVec.ofNat 64 n := by
  simp only [to_bits_truncate, Sail.get_slice_int]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat]

@[simp] theorem divu_eq (a b : BitVec 64) :
    to_bits_truncate (l := 64) (if b.toNat = 0 then -1 else (a.toNat : Int) / (b.toNat : Int)) = divu a b := by
  unfold divu
  by_cases hb : b = 0
  · subst hb; simp [to_bits_truncate, Sail.get_slice_int]
  · have hb' : b.toNat ≠ 0 := fun e => hb (BitVec.eq_of_toNat_eq (by simpa using e))
    rw [if_neg hb', if_neg hb, ← Int.natCast_ediv, tbt_nat]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_udiv]
    have := Nat.div_le_self a.toNat b.toNat; have := a.isLt; omega

@[simp] theorem remu_eq (a b : BitVec 64) :
    to_bits_truncate (l := 64) (if b.toNat = 0 then (a.toNat : Int) else (a.toNat : Int).tmod (b.toNat : Int)) = a % b := by
  by_cases hb : b.toNat = 0
  · rw [if_pos hb, tbt_nat]
    have : b = 0 := BitVec.eq_of_toNat_eq (by simpa using hb)
    subst this; simp
  · rw [if_neg hb, ← Int.ofNat_tmod, tbt_nat]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_umod]
    have := Nat.mod_le a.toNat b.toNat; have := a.isLt; omega

/-! ## Step lemmas -/

variable {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
include h hpc hok

theorem step_mul (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 1 0 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 * getX s rs2) s.mem := by genc; gstep
theorem step_divu (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 1 5 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (divu (getX s rs1) (getX s rs2)) s.mem := by genc; gstep
theorem step_remu (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 1 7 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 % getX s rs2) s.mem := by genc; gstep

end G
end Proven
