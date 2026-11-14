/- The register-generic step lemmas (`Riscv/Steps/Gen*.lean`) subsume the generated ones: a sample of
generated lemmas and the `mov` interface law of `Riscv/Back/Iface.lean`, re-derived WITHOUT their
register restrictions (`MovOK`, `memD`/`memB`, fixed register lists), and nothing here unfolds the model. -/
import Riscv.Steps.GenMem
import Riscv.Back.Iface
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven
namespace G

@[simp] theorem getX_zero (s : St) : getX s 0 = 0 := rfl
@[simp] theorem xval_zero (m : Regs) : xval m 0 = 0 := rfl

/-- with `rd = x0` the written value is irrelevant -/
theorem Next.rd0 {s s' : St} {pc : BitVec 64} {v v' : BitVec 64} {m} (hn : Next s s' pc 0 v m) :
    Next s s' pc 0 v' m :=
  ⟨hn.ret, hn.cfg, hn.pc, fun j => by rw [hn.x j]; simp, hn.mem⟩

variable {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
include h hpc hok

/-- every R-type `Op` (`eq` is two words) in one lemma -/
theorem step_rop (op : Op) (hop : op ≠ .eq) (rd rs1 rs2 : Fin 32) (hrd : rd ≠ 0)
    (hi : instrAt s pc (encR op.f7 op.f3 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (Op.eval op (getX s rs1) (getX s rs2)) s.mem := by
  cases op <;> simp only [Op.f7, Op.f3] at hi <;> simp only [Op.eval]
  · exact step_add h hpc hok rd rs1 rs2 hrd hi
  · exact step_sub h hpc hok rd rs1 rs2 hi
  · exact step_and h hpc hok rd rs1 rs2 hi
  · exact step_or h hpc hok rd rs1 rs2 hi
  · exact step_xor h hpc hok rd rs1 rs2 hi
  · exact step_sll h hpc hok rd rs1 rs2 hi
  · exact step_srl h hpc hok rd rs1 rs2 hi
  · exact step_sra h hpc hok rd rs1 rs2 hi
  · exact step_sltu h hpc hok rd rs1 rs2 hi
  · exact step_slt h hpc hok rd rs1 rs2 hi
  · exact absurd rfl hop

/-- `mv rd, rs` (`add rd, x0, rs`) for ANY registers (the generated `step_var`/`step_var8`/`step_mv8`
cover `T k ← A i`, `T k ← A8 i`, `A8 v ← t0` only) -/
theorem step_mv (rd rs : Fin 32) (hrd : rd ≠ 0) (hi : instrAt s pc (encR 0 0 rd 0 rs)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs) s.mem := by
  have := step_add h hpc hok rd 0 rs hrd hi; simpa using this

/-- = `Words.step_res` -/
theorem step_res' (hi : instrAt s pc iRes) : ∃ s', Next s s' (pc + 4) 10 (getX s 5) s.mem :=
  step_mv h hpc hok 10 5 (by decide) hi

/-- = `Words.step_ret` -/
theorem step_ret' (hi : instrAt s pc iRet) (he : (getX s 1).toNat % 2 = 0) :
    ∃ s', Next s s' (getX s 1) 0 0 s.mem := by
  rw [show iRet = BitVec.ofNat 32 ((0#12 : BitVec 12).toNat <<< 20 ||| (1 : Fin 32).val <<< 15 |||
    (0 : Fin 32).val <<< 7 ||| 0x67) by decide] at hi
  obtain ⟨s', hn⟩ := step_jalr h hpc hok 0 1 0 hi (by simpa using he)
  exact ⟨s', by simpa using (Next.rd0 hn)⟩

/-- = `Words.W.inc_*` (`addi tk, tk, 1`), any register -/
theorem step_inc (rd : Fin 32) (hi : instrAt s pc (encI 0 1 rd rd)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rd + 1) s.mem := by
  have := step_addi h hpc hok rd rd 1 hi; simpa using this

/-- = `BranchWords.beq_5_6_t` -/
theorem beq_5_6_t' (o : BitVec 12) (hi : instrAt s pc (wB 0 5 6 o)) (hc : getX s 5 = getX s 6) :
    ∃ s', Next s s' (pc + boff o) 0 0 s.mem := beq_t h hpc hok 5 6 o hi hc

/-- = `BranchWords.step_jal_0` -/
theorem step_jal_0' (o : BitVec 20) (hi : instrAt s pc (wJ 0 o)) :
    ∃ s', Next s s' (pc + joff o) 0 (pc + 4) s.mem := step_jal h hpc hok 0 o hi

/-- = `MemSteps.step_ld` without `rd ∈ memD`, `rs1 ∈ memB` -/
theorem step_ld0 (rd rs1 : Fin 32) (hi : instrAt s pc (iLd rd rs1))
    (ha : 0x80000000 ≤ (getX s rs1).toNat ∧ (getX s rs1).toNat + 8 ≤ 0x100000000)
    (hal : (getX s rs1).toNat % 8 = 0) {v : BitVec 64} (hv : bytesAt s (getX s rs1).toNat 8 = (le8 v).map some) :
    ∃ s', Next s s' (pc + 4) rd v s.mem := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bytesAt_le8 hv
  rw [show iLd rd rs1 = encL 3 0 rd rs1 by simp [iLd, encL]] at hi
  have := step_ld h hpc hok rd rs1 0 hi (by simp) ha hal h0 h1 h2 h3 h4 h5 h6 h7
  rwa [le8_cat] at this

/-- = `MemSteps.step_sd` without `rs2 ∈ memD`, `rs1 ∈ memB` -/
theorem step_sd0 (rs2 rs1 : Fin 32) (hi : instrAt s pc (iSd rs2 rs1))
    (ha : 0x80000000 ≤ (getX s rs1).toNat ∧ (getX s rs1).toNat + 8 ≤ 0x100000000)
    (hal : (getX s rs1).toNat % 8 = 0) :
    ∃ s', Next s s' (pc + 4) 0 0 (storeBytes s.mem (getX s rs1).toNat (le8 (getX s rs2))) := by
  rw [show iSd rs2 rs1 = encS 3 0 rs2 rs1 by
    rw [encS_eq]; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [iSd, fS, BitVec.getLsbD_ofNat, BitVec.getLsbD_or, Nat.testBit_or, Nat.testBit_shiftLeft]
    enc_bits] at hi
  exact step_sd h hpc hok rs2 rs1 0 hi (by simp) ha hal

/-- = `MemSteps.step_lbu` without register restrictions -/
theorem step_lbu0 (rd rs1 : Fin 32) (hi : instrAt s pc (iLbu rd rs1))
    (ha : 0x80000000 ≤ (getX s rs1).toNat ∧ (getX s rs1).toNat + 1 ≤ 0x100000000) {b : BitVec 8}
    (hv : s.mem[(getX s rs1).toNat]? = some b) : ∃ s', Next s s' (pc + 4) rd (b.setWidth 64) s.mem := by
  rw [show iLbu rd rs1 = encL 4 0 rd rs1 by simp [iLbu, encL]] at hi
  exact step_lbu h hpc hok rd rs1 0 hi (by simp) ha hv

omit h hpc hok

/-- the `mov` interface law (`Riscv/Back/Iface.lean`) for ANY two distinct-or-equal abstract registers,
without `MovOK` -/
theorem law_mov_any {d a : Mach.Reg} {s : St} {pc : BitVec 64}
    (hA : Mach.Riscv.core.At s pc (Mach.Riscv.enc (.mov d a))) :
    Mach.Riscv.core.runsTo s fun s' => Mach.Riscv.core.Done s s' (Mach.next pc (Mach.Riscv.enc (.mov d a)).length) ∧
      Mach.Riscv.core.Set1 s s' d (Mach.Riscv.core.get s a) ∧ Mach.Riscv.core.mem s' = Mach.Riscv.core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := Mach.Riscv.first1 hA
  obtain ⟨s', hn⟩ := step_mv h hpc hok (Mach.Riscv.phys d) (Mach.Riscv.phys a) (Mach.Riscv.phys_ne0 d) hi
  exact Mach.Riscv.run1 hn ⟨Mach.Riscv.ofNext hn (.inr ⟨d, rfl⟩), Mach.Riscv.set1Of hn, Mach.Riscv.memOf hn⟩

end G
end Proven
