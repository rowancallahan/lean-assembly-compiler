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
import Compiler.MOp
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

theorem tbt_int (z : Int) : (to_bits_truncate (l := 64) z) = BitVec.ofInt 64 z := by
  simp only [to_bits_truncate, Sail.get_slice_int]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt]
  omega

/-- signed `div`: the model's overflow clamp (`-2^63 / -1`) is the wrap of the true quotient `2^63` -/
@[simp] theorem div_eq (a b : BitVec 64) :
    to_bits_truncate (l := 64) (if (2 : Int) ^ (63 : Int) ≤ (if b.toInt = 0 then -1 else a.toInt.tdiv b.toInt) then -9223372036854775808
      else if b.toInt = 0 then -1 else a.toInt.tdiv b.toInt) = Mach.MOp.eval .div a b := by
  have p63 : (2 : Int) ^ (63 : Int) = 9223372036854775808 := by decide
  simp only [Mach.MOp.eval, tbt_int, p63]
  by_cases hb : b = 0
  · subst hb; simp
  · have hb' : b.toInt ≠ 0 := fun e => hb (BitVec.eq_of_toInt_eq (by simpa using e))
    simp only [if_neg hb', if_neg hb]
    split
    · have h1 : (a.toInt.tdiv b.toInt).natAbs = a.toInt.natAbs / b.toInt.natAbs := Int.natAbs_tdiv _ _
      have h2 := Nat.div_le_self a.toInt.natAbs b.toInt.natAbs
      have h3 := BitVec.toInt_lt (x := a); have h4 := BitVec.le_toInt (x := a)
      have e : a.toInt.tdiv b.toInt = 9223372036854775808 := by simp at h3 h4; omega
      rw [e]; decide
    · rfl

@[simp] theorem rem_eq (a b : BitVec 64) :
    to_bits_truncate (l := 64) (if b.toInt = 0 then a.toInt else a.toInt.tmod b.toInt) = Mach.MOp.eval .rem a b := by
  simp only [Mach.MOp.eval, tbt_int]
  split
  · next h => rw [h, Int.tmod_zero]
  · rfl

/-! ## Step lemmas -/

variable {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
include h hpc hok

theorem step_mul (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 1 0 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 * getX s rs2) s.mem := by genc; gstep
theorem step_divu (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 1 5 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (divu (getX s rs1) (getX s rs2)) s.mem := by genc; gstep
theorem step_remu (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 1 7 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 % getX s rs2) s.mem := by genc; gstep
/-- the model's signed quotient as `execute_DIV` writes it -/

theorem step_div0 (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 1 4 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (to_bits_truncate (l := 64)
      (if (2 : Int) ^ (63 : Int) ≤ (if (getX s rs2).toInt = 0 then -1 else (getX s rs1).toInt.tdiv (getX s rs2).toInt)
        then -9223372036854775808 else if (getX s rs2).toInt = 0 then -1 else (getX s rs1).toInt.tdiv (getX s rs2).toInt))
      s.mem := by genc; gstep
theorem step_div (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 1 4 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (Mach.MOp.eval .div (getX s rs1) (getX s rs2)) s.mem := by
  have := step_div0 h hpc hok rd rs1 rs2 hi; rwa [div_eq] at this
theorem step_rem (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 1 6 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (Mach.MOp.eval .rem (getX s rs1) (getX s rs2)) s.mem := by genc; gstep

end G
end Proven
