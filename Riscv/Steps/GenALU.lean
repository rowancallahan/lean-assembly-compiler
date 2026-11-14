/- Register-generic step lemmas for the RV64I integer ALU: R-type `add sub and or xor sll srl sra slt sltu`,
I-type `addi andi ori xori slti sltiu`, shifts `slli srli srai`, and `lui` — ONE lemma per form, with the
register numbers and the immediate as variables (machinery: `Riscv/Steps/GenTac.lean`). -/
import Riscv.Steps.GenTac
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Proven
namespace G

/-! ## Encodings as `concrete ||| symbolic fields` -/

theorem fin32_tb (r : Fin 32) {i : Nat} (h : 5 ≤ i) : r.val.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show r.val < 2 ^ 5 from r.isLt) (Nat.pow_le_pow_right (by decide) h))
theorem bv_tb {w : Nat} (x : BitVec w) {i : Nat} (h : w ≤ i) : x.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h))

theorem tb_lt128 {opc : Nat} (h : opc < 128) {i : Nat} (hi : 7 ≤ i) : opc.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hi))

/-- one bit: through appends and slices, then Boolean normalisation -/
macro "enc_bit1" : tactic => `(tactic| (
  repeat (first | rw [BitVec.getLsbD_append] | rw [BitVec.getLsbD_extractLsb'])
  simp (config := {decide := true}) [fin32_tb, bv_tb, BitVec.getLsbD, Bool.or_assoc, Bool.or_comm, tb_lt128, *]))
macro "enc_bits" : tactic => `(tactic| (
  revert i
  repeat (first | exact fa_zero | refine fa_succ (by enc_bit1) ?_)))

theorem encR_eq (f7 f3 : Nat) (rd rs1 rs2 : Fin 32) :
    encR f7 f3 rd rs1 rs2 = BitVec.ofNat 32 (f7 <<< 25 ||| f3 <<< 12 ||| 0x33) ||| fR rd rs1 rs2 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [encR, fR, BitVec.getLsbD_ofNat, BitVec.getLsbD_or, Nat.testBit_or, Nat.testBit_shiftLeft]
  enc_bits

theorem encI_eq (f3 : Nat) (imm : BitVec 12) (rd rs1 : Fin 32) :
    encI f3 imm.toNat rd rs1 = BitVec.ofNat 32 (f3 <<< 12 ||| 0x13) ||| fI rd rs1 imm := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [encI, fI, BitVec.getLsbD_ofNat, BitVec.getLsbD_or, Nat.testBit_or, Nat.testBit_shiftLeft]
  enc_bits

/-- RV64 shift-immediate: `imm = f6 <<< 6 ||| shamt` -/
theorem encSh_eq (f3 f6 : Nat) (sh : BitVec 6) (rd rs1 : Fin 32) :
    encI f3 (f6 <<< 6 ||| sh.toNat) rd rs1 = BitVec.ofNat 32 (f6 <<< 26 ||| f3 <<< 12 ||| 0x13) ||| fSh rd rs1 sh := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [encI, fSh, BitVec.getLsbD_ofNat, BitVec.getLsbD_or, Nat.testBit_or, Nat.testBit_shiftLeft]
  enc_bits

/-- U-type: `imm` is bits 31..12 of the word -/
def encU (opc : Nat) (rd : Fin 32) (imm : BitVec 20) : BitVec 32 :=
  BitVec.ofNat 32 (imm.toNat <<< 12 ||| rd.val <<< 7 ||| opc)

theorem encU_eq (opc : Nat) (h : opc < 128) (rd : Fin 32) (imm : BitVec 20) :
    encU opc rd imm = BitVec.ofNat 32 opc ||| fU rd imm := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [encU, fU, BitVec.getLsbD_ofNat, BitVec.getLsbD_or, Nat.testBit_or, Nat.testBit_shiftLeft]
  enc_bits

/-! ## R-type -/

variable {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
include h hpc hok

set_option hygiene false in
macro "genc" : tactic => `(tactic| (
  first | rw [Proven.G.encR_eq] at hi | rw [Proven.G.encI_eq] at hi | rw [Proven.G.encSh_eq] at hi |
    rw [Proven.G.encU_eq _ (by decide)] at hi
  simp only [Nat.reduceShiftLeft, Nat.reduceOr, Nat.reduceMod] at hi))

/-- `add rd, rs1, rs2` (`rd ≠ 0`: `add x0, x0, x2..x5` decode as the `ntl.*` hints) -/
theorem step_add (rd rs1 rs2 : Fin 32) (hrd : rd ≠ 0) (hi : instrAt s pc (encR 0 0 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 + getX s rs2) s.mem := by genc; gstep
theorem step_sub (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 0x20 0 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 - getX s rs2) s.mem := by genc; gstep
theorem step_and (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 0 7 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 &&& getX s rs2) s.mem := by genc; gstep
theorem step_or (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 0 6 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 ||| getX s rs2) s.mem := by genc; gstep
theorem step_xor (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 0 4 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 ^^^ getX s rs2) s.mem := by genc; gstep
theorem step_sll (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 0 1 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 <<< ((getX s rs2).toNat % 64)) s.mem := by genc; gstep
theorem step_srl (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 0 5 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 >>> ((getX s rs2).toNat % 64)) s.mem := by genc; gstep
theorem step_sra (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 0x20 5 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd ((getX s rs1).sshiftRight ((getX s rs2).toNat % 64)) s.mem := by genc; gstep
theorem step_slt (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 0 2 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (if (getX s rs1).slt (getX s rs2) then 1 else 0) s.mem := by genc; gstep
theorem step_sltu (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (encR 0 3 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (if getX s rs1 < getX s rs2 then 1 else 0) s.mem := by genc; gstep

/-! ## I-type -/

/-- `addi rd, rs1, imm` (`imm` sign-extended) -/
theorem step_addi (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encI 0 imm.toNat rd rs1)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 + imm.signExtend 64) s.mem := by genc; gstep
theorem step_andi (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encI 7 imm.toNat rd rs1)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 &&& imm.signExtend 64) s.mem := by genc; gstep
theorem step_ori (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encI 6 imm.toNat rd rs1)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 ||| imm.signExtend 64) s.mem := by genc; gstep
theorem step_xori (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encI 4 imm.toNat rd rs1)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 ^^^ imm.signExtend 64) s.mem := by genc; gstep
theorem step_slti (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encI 2 imm.toNat rd rs1)) :
    ∃ s', Next s s' (pc + 4) rd (if (getX s rs1).slt (imm.signExtend 64) then 1 else 0) s.mem := by genc; gstep
theorem step_sltiu (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encI 3 imm.toNat rd rs1)) :
    ∃ s', Next s s' (pc + 4) rd (if getX s rs1 < imm.signExtend 64 then 1 else 0) s.mem := by genc; gstep

/-! ## Shifts by an immediate (6-bit `shamt`) -/

theorem step_slli (rd rs1 : Fin 32) (sh : BitVec 6) (hi : instrAt s pc (encI 1 (0 <<< 6 ||| sh.toNat) rd rs1)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 <<< sh.toNat) s.mem := by genc; gstep
theorem step_srli (rd rs1 : Fin 32) (sh : BitVec 6) (hi : instrAt s pc (encI 5 (0 <<< 6 ||| sh.toNat) rd rs1)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 >>> sh.toNat) s.mem := by genc; gstep
theorem step_srai (rd rs1 : Fin 32) (sh : BitVec 6) (hi : instrAt s pc (encI 5 (0x10 <<< 6 ||| sh.toNat) rd rs1)) :
    ∃ s', Next s s' (pc + 4) rd ((getX s rs1).sshiftRight sh.toNat) s.mem := by genc; gstep

/-! ## `lui` -/

theorem step_lui (rd : Fin 32) (imm : BitVec 20) (hi : instrAt s pc (encU 0x37 rd imm)) :
    ∃ s', Next s s' (pc + 4) rd ((imm ++ 0#12).signExtend 64) s.mem := by genc; gstep

end G
end Proven
