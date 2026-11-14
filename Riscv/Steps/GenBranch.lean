/- Register-generic step lemmas for branches and jumps: `beq bne blt bge bltu bgeu rs1, rs2, off` with
arbitrary `rs1 rs2` and symbolic offset, `jal rd, off` with arbitrary `rd`, `jalr rd, imm(rs1)` (machinery:
`Riscv/Steps/GenTac.lean`; words `wB` / `wJ` of `Riscv/Steps/Branch.lean`, `encI` of `Spec/Code.lean`). -/
import Riscv.Steps.GenALU
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Proven
namespace G

theorem wB_eq (f3 : BitVec 3) (rs1 rs2 : Fin 32) (o : BitVec 12) :
    wB f3 (BitVec.ofFin rs1) (BitVec.ofFin rs2) o =
      ((0#17 : BitVec 17) +++ f3 +++ (0#5 : BitVec 5) +++ (0x63#7 : BitVec 7)) ||| fB rs1 rs2 o := by
  simp only [wB, immB, fB]; bits
theorem wJ_eq (rd : Fin 32) (o : BitVec 20) : wJ (BitVec.ofFin rd) o = 0x6f#32 ||| fJ rd o := by
  simp only [wJ, immJ, fJ]; bits

theorem slt_iff (a b : BitVec 64) : a.slt b = true ↔ a.toInt < b.toInt := by simp [BitVec.slt_iff_toInt_lt]
theorem ult_iff (a b : BitVec 64) : a.ult b = true ↔ a.toNat < b.toNat := by simp [BitVec.ult_iff_lt, BitVec.lt_def]

variable {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
include h hpc hok

set_option hygiene false in
macro "genb" : tactic => `(tactic| (
  first | rw [Proven.G.wB_eq] at hi | rw [Proven.G.wJ_eq] at hi | rw [Proven.G.encI_eq] at hi
  try simp only [Nat.reduceShiftLeft, Nat.reduceOr, BitVec.reduceAppend] at hi))

/-! ## Conditional branches: taken / not taken -/

theorem beq_t (rs1 rs2 : Fin 32) (o : BitVec 12) (hi : instrAt s pc (wB 0 (.ofFin rs1) (.ofFin rs2) o))
    (hc : getX s rs1 = getX s rs2) : ∃ s', Next s s' (pc + boff o) 0 0 s.mem := by genb; gstep
theorem beq_n (rs1 rs2 : Fin 32) (o : BitVec 12) (hi : instrAt s pc (wB 0 (.ofFin rs1) (.ofFin rs2) o))
    (hc : ¬getX s rs1 = getX s rs2) : ∃ s', Next s s' (pc + 4) 0 0 s.mem := by genb; gstep
theorem bne_t (rs1 rs2 : Fin 32) (o : BitVec 12) (hi : instrAt s pc (wB 1 (.ofFin rs1) (.ofFin rs2) o))
    (hc : ¬getX s rs1 = getX s rs2) : ∃ s', Next s s' (pc + boff o) 0 0 s.mem := by genb; gstep
theorem bne_n (rs1 rs2 : Fin 32) (o : BitVec 12) (hi : instrAt s pc (wB 1 (.ofFin rs1) (.ofFin rs2) o))
    (hc : getX s rs1 = getX s rs2) : ∃ s', Next s s' (pc + 4) 0 0 s.mem := by genb; gstep
theorem blt_t (rs1 rs2 : Fin 32) (o : BitVec 12) (hi : instrAt s pc (wB 4 (.ofFin rs1) (.ofFin rs2) o))
    (hc : (getX s rs1).toInt < (getX s rs2).toInt) : ∃ s', Next s s' (pc + boff o) 0 0 s.mem := by genb; gstep
theorem blt_n (rs1 rs2 : Fin 32) (o : BitVec 12) (hi : instrAt s pc (wB 4 (.ofFin rs1) (.ofFin rs2) o))
    (hc : ¬(getX s rs1).toInt < (getX s rs2).toInt) : ∃ s', Next s s' (pc + 4) 0 0 s.mem := by genb; gstep
theorem bge_t (rs1 rs2 : Fin 32) (o : BitVec 12) (hi : instrAt s pc (wB 5 (.ofFin rs1) (.ofFin rs2) o))
    (hc : ¬(getX s rs1).toInt < (getX s rs2).toInt) : ∃ s', Next s s' (pc + boff o) 0 0 s.mem := by genb; gstep
theorem bge_n (rs1 rs2 : Fin 32) (o : BitVec 12) (hi : instrAt s pc (wB 5 (.ofFin rs1) (.ofFin rs2) o))
    (hc : (getX s rs1).toInt < (getX s rs2).toInt) : ∃ s', Next s s' (pc + 4) 0 0 s.mem := by genb; gstep
theorem bltu_t (rs1 rs2 : Fin 32) (o : BitVec 12) (hi : instrAt s pc (wB 6 (.ofFin rs1) (.ofFin rs2) o))
    (hc : (getX s rs1).toNat < (getX s rs2).toNat) : ∃ s', Next s s' (pc + boff o) 0 0 s.mem := by genb; gstep
theorem bltu_n (rs1 rs2 : Fin 32) (o : BitVec 12) (hi : instrAt s pc (wB 6 (.ofFin rs1) (.ofFin rs2) o))
    (hc : ¬(getX s rs1).toNat < (getX s rs2).toNat) : ∃ s', Next s s' (pc + 4) 0 0 s.mem := by genb; gstep
theorem bgeu_t (rs1 rs2 : Fin 32) (o : BitVec 12) (hi : instrAt s pc (wB 7 (.ofFin rs1) (.ofFin rs2) o))
    (hc : ¬(getX s rs1).toNat < (getX s rs2).toNat) : ∃ s', Next s s' (pc + boff o) 0 0 s.mem := by genb; gstep
theorem bgeu_n (rs1 rs2 : Fin 32) (o : BitVec 12) (hi : instrAt s pc (wB 7 (.ofFin rs1) (.ofFin rs2) o))
    (hc : (getX s rs1).toNat < (getX s rs2).toNat) : ∃ s', Next s s' (pc + 4) 0 0 s.mem := by genb; gstep

/-! ## Jumps -/

/-- `jal rd, 2*o`: `x[rd] := pc + 4` -/
theorem step_jal (rd : Fin 32) (o : BitVec 20) (hi : instrAt s pc (wJ (.ofFin rd) o)) :
    ∃ s', Next s s' (pc + joff o) rd (pc + 4) s.mem := by genb; gstep

/-- `jalr rd, imm(rs1)` to an even target (`x[rd] := pc + 4`; `rd = rs1` is fine: `rs1` is read first) -/
theorem step_jalr (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (BitVec.ofNat 32 (imm.toNat <<< 20 |||
    rs1.val <<< 15 ||| rd.val <<< 7 ||| 0x67)))
    (he : (getX s rs1 + imm.signExtend 64).toNat % 2 = 0) :
    ∃ s', Next s s' (getX s rs1 + imm.signExtend 64) rd (pc + 4) s.mem := by
  have e : BitVec.ofNat 32 (imm.toNat <<< 20 ||| rs1.val <<< 15 ||| rd.val <<< 7 ||| 0x67) =
      0x67#32 ||| fI rd rs1 imm := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [fI, BitVec.getLsbD_ofNat, BitVec.getLsbD_or, Nat.testBit_or, Nat.testBit_shiftLeft]
    enc_bits
  rw [e] at hi; gstep

end G
end Proven
