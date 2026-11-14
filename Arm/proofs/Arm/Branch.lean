/- F3 (partial): branch instructions at the decode+execute layer. -/
import Arm.Machine
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.all false
set_option pp.deepTerms false
set_option pp.maxSteps 3000

namespace ArmProof

section
variable {s : St} (hc : Pins s.regs)
include hc

/-- the registers a taken direct branch to `t` writes -/
def takenRegs (m : Regs) (t : BitVec 64) : Regs :=
  ((m.insert .Branchtypetaken .BranchType_DIR).insert ._PC t).insert .__BranchTaken true

theorem b_exec (imm26 : BitVec 26) {pc : BitVec 64} (hpc : s.regs.get? ._PC = some pc) :
    decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 0#1 s =
      .ok () { s with regs := takenRegs s.regs (pc + sign_extend (imm26 +++ 0#2) 64) } := by
  have hr := retcfg_of hc
  obtain ⟨p, hp, hrw, hel⟩ := hr.p
  obtain ⟨fi, hfi, hgcs, hbrbe, hspe, hpac, hvhe, ha64⟩ := hr.fi
  obtain ⟨scr, hscr⟩ := hr.scr
  simp only [decode_b_uncond_aarch64_instrs_branch_unconditional_immediate,
    execute_aarch64_instrs_branch_unconditional_immediate, PC_read, takenRegs]
  rcases hel with ⟨hel3, tcr, htcr, htbi⟩ | ⟨hel1, -⟩
  · ret_simp
  · obtain ⟨q, hq, h3, -⟩ := hc.ps; rw [hp] at hq; cases hq; rw [hel1] at h3; cases h3

/-- `cbnz xt, imm` with `x ≠ 0`: taken -/
theorem cbnz_taken (t : Nat) (ht : t < 31) (imm19 : BitVec 19) {pc x : BitVec 64}
    (hpc : s.regs.get? ._PC = some pc) (hx : xget s.regs t = some x) (hz : x ≠ 0) :
    decode_cbz_aarch64_instrs_branch_conditional_compare (BitVec.ofNat 5 t) imm19 1#1 1#1 s =
      .ok () { s with regs := takenRegs s.regs (pc + sign_extend (imm19 +++ 0#2) 64) } := by
  have hr := retcfg_of hc
  obtain ⟨p, hp, hrw, hel⟩ := hr.p
  obtain ⟨fi, hfi, hgcs, hbrbe, hspe, hpac, hvhe, ha64⟩ := hr.fi
  obtain ⟨scr, hscr⟩ := hr.scr
  idx t
  have hz' : IsZero x = false := by simpa [IsZero, BitVec.zero] using hz
  simp only [decode_cbz_aarch64_instrs_branch_conditional_compare,
    execute_aarch64_instrs_branch_conditional_compare, PC_read, takenRegs, BranchNotTaken]
  rcases hel with ⟨hel3, tcr, htcr, htbi⟩ | ⟨hel1, -⟩
  · ret_simp
  · obtain ⟨q, hq, h3, -⟩ := hc.ps; rw [hp] at hq; cases hq; rw [hel1] at h3; cases h3

/-- `cbnz xt, imm` with `x = 0`: falls through -/
theorem cbnz_not (t : Nat) (ht : t < 31) (imm19 : BitVec 19) {pc x : BitVec 64}
    (hpc : s.regs.get? ._PC = some pc) (hx : xget s.regs t = some x) (hz : x = 0) :
    decode_cbz_aarch64_instrs_branch_conditional_compare (BitVec.ofNat 5 t) imm19 1#1 1#1 s =
      .ok () s := by
  have hr := retcfg_of hc
  obtain ⟨p, hp, hrw, hel⟩ := hr.p
  obtain ⟨fi, hfi, hgcs, hbrbe, hspe, hpac, hvhe, ha64⟩ := hr.fi
  obtain ⟨scr, hscr⟩ := hr.scr
  idx t
  have hz' : IsZero x = true := by subst hz; rfl
  simp only [decode_cbz_aarch64_instrs_branch_conditional_compare,
    execute_aarch64_instrs_branch_conditional_compare, PC_read, takenRegs, BranchNotTaken]
  rcases hel with ⟨hel3, tcr, htcr, htbi⟩ | ⟨hel1, -⟩
  · ret_simp
  · obtain ⟨q, hq, h3, -⟩ := hc.ps; rw [hp] at hq; cases hq; rw [hel1] at h3; cases h3

/-- `cbz xt, imm` with `x = 0`: taken -/
theorem cbz_taken (t : Nat) (ht : t < 31) (imm19 : BitVec 19) {pc x : BitVec 64}
    (hpc : s.regs.get? ._PC = some pc) (hx : xget s.regs t = some x) (hz : x = 0) :
    decode_cbz_aarch64_instrs_branch_conditional_compare (BitVec.ofNat 5 t) imm19 0#1 1#1 s =
      .ok () { s with regs := takenRegs s.regs (pc + sign_extend (imm19 +++ 0#2) 64) } := by
  have hr := retcfg_of hc
  obtain ⟨p, hp, hrw, hel⟩ := hr.p
  obtain ⟨fi, hfi, hgcs, hbrbe, hspe, hpac, hvhe, ha64⟩ := hr.fi
  obtain ⟨scr, hscr⟩ := hr.scr
  idx t
  have hz' : IsZero x = true := by subst hz; rfl
  simp only [decode_cbz_aarch64_instrs_branch_conditional_compare,
    execute_aarch64_instrs_branch_conditional_compare, PC_read, takenRegs, BranchNotTaken]
  rcases hel with ⟨hel3, tcr, htcr, htbi⟩ | ⟨hel1, -⟩
  · ret_simp
  · obtain ⟨q, hq, h3, -⟩ := hc.ps; rw [hp] at hq; cases hq; rw [hel1] at h3; cases h3

/-- `cbz xt, imm` with `x ≠ 0`: falls through -/
theorem cbz_not (t : Nat) (ht : t < 31) (imm19 : BitVec 19) {pc x : BitVec 64}
    (hpc : s.regs.get? ._PC = some pc) (hx : xget s.regs t = some x) (hz : x ≠ 0) :
    decode_cbz_aarch64_instrs_branch_conditional_compare (BitVec.ofNat 5 t) imm19 0#1 1#1 s =
      .ok () s := by
  have hr := retcfg_of hc
  obtain ⟨p, hp, hrw, hel⟩ := hr.p
  obtain ⟨fi, hfi, hgcs, hbrbe, hspe, hpac, hvhe, ha64⟩ := hr.fi
  obtain ⟨scr, hscr⟩ := hr.scr
  idx t
  have hz' : IsZero x = false := by simpa [IsZero, BitVec.zero] using hz
  simp only [decode_cbz_aarch64_instrs_branch_conditional_compare,
    execute_aarch64_instrs_branch_conditional_compare, PC_read, takenRegs, BranchNotTaken]
  rcases hel with ⟨hel3, tcr, htcr, htbi⟩ | ⟨hel1, -⟩
  · ret_simp
  · obtain ⟨q, hq, h3, -⟩ := hc.ps; rw [hp] at hq; cases hq; rw [hel1] at h3; cases h3

end
end ArmProof
