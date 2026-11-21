/- The register-generic step lemmas (`Riscv/Steps/Gen*.lean`) subsume the generated ones: a sample of
generated lemmas and the `mov` interface law of `Riscv/Back/Iface.lean`, re-derived WITHOUT their
register restrictions (`MovOK`, `memD`/`memB`, fixed register lists), and nothing here unfolds the model. -/
import Nano.Base.Riscv.Steps.GenMem
import Nano.Base.Riscv.Back.Iface
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven
namespace G

@[simp] theorem getX_zero (s : St) : getX s 0 = 0 := rfl
@[simp] theorem xval_zero (m : Regs) : xval m 0 = 0 := rfl


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



/-- = `Words.W.inc_*` (`addi tk, tk, 1`), any register -/
theorem step_inc (rd : Fin 32) (hi : instrAt s pc (encI 0 1 rd rd)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rd + 1) s.mem := by
  have := step_addi h hpc hok rd rd 1 hi; simpa using this


/-- = `BranchWords.step_jal_0` -/
theorem step_jal_0' (o : BitVec 20) (hi : instrAt s pc (wJ 0 o)) :
    ∃ s', Next s s' (pc + joff o) 0 (pc + 4) s.mem := step_jal h hpc hok 0 o hi




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
