/- Full-step machinery, part 2: address translation (MMU off at EL3) and the instruction fetch. -/
import Arm.Hooks
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.all false
set_option pp.deepTerms false
set_option pp.maxSteps 3000

namespace ArmProof

set_option hygiene false in
macro "pins'" : tactic => `(tactic| (obtain ⟨⟨p, hp, hel, hrw⟩, hfe, hscr, hed, hmdcc, hos, hmd3, hgic, hmp3, hmp2, hpa, htcr, hsct, hmair, hmdscr, hspe⟩ := id hc))

section
variable {s : St} (hc : Pins s.regs)
include hc

theorem s1off_ok (va : BitVec 64) (fault : FaultRecord) (hfs : fault.statuscode = .Fault_None) (hva : va.toNat < 2 ^ 48) :
    ∃ r, AArch64_S1DisabledOutput fault .Regime_EL3 va accIF true s = .ok r { s with regs := s.regs.insert .InGuardedPage false } ∧
      r.1.statuscode = .Fault_None ∧ r.2.fault.statuscode = .Fault_None ∧ r.2.paddress.address = va.setWidth 56 := by
  have := walk_ok hc va; have := iz48 va hva; have hpm := @pamax_ok; pins'
  simp only [AArch64_S1DisabledOutput, SetInGuardedPage, AArch64_S1ICacheEnabled, AArch64_AddrTop,
    AArch64_S1HasAlignmentFault, CreateAddressDescriptor, AArch64_S1DisabledOutputMECID, NoFault, accIF, wp3]
  gsimp

theorem s1en_ok (acc : AccessType) : AArch64_S1Enabled .Regime_EL3 acc s = .ok false s := by
  pins'; simp only [AArch64_S1Enabled]; gsimp

theorem s1t_ok (va : BitVec 64) (fault : FaultRecord) (hfs : fault.statuscode = .Fault_None) (hva : va.toNat < 2 ^ 48) :
    ∃ r, AArch64_S1Translate fault .Regime_EL3 va true accIF s = .ok r { s with regs := s.regs.insert .InGuardedPage false } ∧
      r.1.statuscode = .Fault_None ∧ r.2.fault.statuscode = .Fault_None ∧ r.2.paddress.address = va.setWidth 56 := by
  obtain ⟨r, hr, h⟩ := s1off_ok hc va { fault with secondstage := false, s2fs1walk := false } hfs hva
  refine ⟨r, ?_, h⟩
  unfold AArch64_S1Translate
  rw [run_bind _ (uad_ok s), run_bind _ (ub_ok s), run_bind _ (ub_ok s), run_bind _ (u_TLBLine s)]
  dsimp only
  rw [run_bind _ (s1en_ok hc _)]
  simp only [Bool.not_false, if_true, run_lift]
  exact hr

end
end ArmProof
