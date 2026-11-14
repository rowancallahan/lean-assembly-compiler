/- Full-step machinery, part 3: the hooks around decode+execute in `__InstructionExecute`/`__TopLevel`/`__CycleEnd`. -/
import Arm.Fetch
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.all false
set_option pp.deepTerms false
set_option pp.maxSteps 3000

namespace ArmProof

/-- one machine step, as the model's `elfmain.sail` defines it (`step_model`: `SEE = -1; __TopLevel(); __CycleEnd()`);
the Lean model in use was generated without `elfmain.sail`, so it is restated here verbatim -/
def stepModel : SailM Unit := do
  writeReg Register.SEE (-1 : Int)
  __TopLevel ()
  __CycleEnd ()

/-- the registers `__InstructionExecute` has written when it reaches decode (word `w`, fetched at the PC) -/
def preRegs (m : Regs) (w : BitVec 32) : Regs :=
  (((((((((m.insert .ShouldAdvanceIT false).insert .ShouldAdvanceSS true).insert .BTypeCompatible false).insert
    .__InstructionStep false).insert .InGuardedPage false).insert .__BranchTaken false).insert
    .__ExclusiveMonitorSet false).insert .__ThisInstrEnc .__A64).insert .__ThisInstr w).insert .__currentCond 14#4

/-- what `__InstructionExecute` writes after decode+execute: `InGuardedPage := false`, `PSTATE.BTYPE := BTypeNext`,
and, unless a branch was taken, `_PC := _PC + 4` -/
def postRegs (m : Regs) (p1 : ProcState) (btn : BitVec 2) (bt : Bool) (pc1 : BitVec 64) : Regs :=
  let m' := (m.insert .InGuardedPage false).insert .PSTATE { p1 with BTYPE := btn }
  if bt then m' else m'.insert ._PC (pc1 + 4)

theorem addInt4 (x : BitVec 64) : BitVec.addInt x (fdiv_int 32 8) = x + 4 := rfl

section
variable {s : St} (hc : Pins s.regs)
include hc

theorem pmu_ok (e : BitVec 16) : PMUEvent e s = .ok () s := by
  pins; simp only [PMUEvent, PMUEvent__1]; gsimp

theorem spepre_ok : SPEPreExecution () s = .ok () s := by
  have := using32_ok hc; pins
  simp only [SPEPreExecution, StatisticalProfilingEnabled, StatisticalProfilingEnabled__1]; gsimp

theorem spepost_ok : SPEPostExecution () s = .ok () s := by
  pins; simp only [SPEPostExecution]; gsimp

theorem emu_ok (enc : __InstrEnc) (w : BitVec 32) : __CheckForEmulatorTermination enc w s = .ok () s := by
  pins; simp only [__CheckForEmulatorTermination]; gsimp

theorem ssadv_ok : SSAdvance () s = .ok () s := by
  have := dtarget_ok hc; have := el32_ok hc; pins; simp only [SSAdvance]; gsimp

theorem timers_ok : AArch64_CheckTimerConditions () s = .ok () s := by
  have := ss_el3 hc; have hi := @insert_self; pins
  simp only [AArch64_CheckTimerConditions, CurrentSecurityState, IsTimerConditionMet, PhysicalCountInt, SetInterruptRequestLevel]
  gsimp

theorem cycleEnd_ok {c : Int} (h : s.regs.get? .__cycle_count = some c) :
    __CycleEnd () s = .ok () { s with regs := s.regs.insert .__cycle_count (c + 1) } := by
  have := timers_ok hc; have := using32_ok hc; have := aa64_ok hc; have := el32_ok hc; have := ss_el3 hc; pins
  simp only [__CycleEnd, SPECycle, __UpdateSystemCounter, GenericCounterTick, AArch64_PMUCycle, ShouldBRBEFreeze,
    BranchRecordAllowed, CurrentSecurityState, __EndCycle]
  gsimp

theorem ie_ok (pc : BitVec 64) (w : BitVec 32) (hpc : s.regs.get? ._PC = some pc) (hlt : pc.toNat < 2 ^ 29)
    (hal : pc.toNat % 4 = 0) (hw : MemWord s.mem pc.toNat w) (s1 : St)
    (hdec : __DecodeA64 pc.toNat w { s with regs := preRegs s.regs w } = .ok () s1) (hc1 : Pins s1.regs)
    {p1 : ProcState} {bt : Bool} {pc1 : BitVec 64} {btn : BitVec 2}
    (hp1 : s1.regs.get? .PSTATE = some p1) (hbt : s1.regs.get? .__BranchTaken = some bt)
    (hpc1 : s1.regs.get? ._PC = some pc1) (hbtn : s1.regs.get? .BTypeNext = some btn)
    (hti : s1.regs.get? .__ThisInstr = some w) (hte : s1.regs.get? .__ThisInstrEnc = some .__A64)
    (hsi : s1.regs.get? .ShouldAdvanceIT = some false) (hss : s1.regs.get? .ShouldAdvanceSS = some true)
    (heret : BitVec.ofNat 20 (w.toNat >>> 12) ≠ 879088#20) :
    __InstructionExecute () s = .ok () { s1 with regs := postRegs s1.regs p1 btn bt pc1 } := by
  have hq : p1.EL = 3#2 ∧ p1.nRW = 0#1 ∧ p1.IL = 0#1 := by
    obtain ⟨q, hq, h⟩ := hc1.ps; rw [hp1] at hq; cases hq; exact h
  have hc2 : Pins ((s1.regs.insert .InGuardedPage false).insert .PSTATE { p1 with BTYPE := btn }) :=
    pins_pstate _ hq ((pins_insert _ rfl).2 hc1)
  have hs1 := ssadv_ok (s := { s1 with regs := (s1.regs.insert .InGuardedPage false).insert .PSTATE { p1 with BTYPE := btn } }) hc2
  have hs2 := ssadv_ok (s := { s1 with regs := ((s1.regs.insert .InGuardedPage false).insert .PSTATE { p1 with BTYPE := btn }).insert ._PC (pc1 + 4) })
    ((pins_insert _ rfl).2 hc2)
  simp only [choice_unit] at hs1 hs2
  clear hq hc2
  have hc1 : Pins ((s.regs.insert .ShouldAdvanceIT false).insert .ShouldAdvanceSS true) :=
    (pins_insert _ rfl).2 ((pins_insert _ rfl).2 hc)
  have hf := fetch_ok (s := { s with regs := (s.regs.insert .ShouldAdvanceIT false).insert .ShouldAdvanceSS true }) hc1 pc w
    (by simpa [Std.ExtDHashMap.get?_insert] using hpc) hlt hal hw pc
  simp only [choice_unit] at hf
  simp only [preRegs, choice_unit] at hdec
  have := @pmu_ok; have := @spepre_ok; have := @spepost_ok; have := @emu_ok; have := @ssadv_ok
  have := @halted_ok; have hi := @insert_self; have := u_InstrEnc; pins
  simp only [__InstructionExecute, EDSCR_write, EDSCR_read, _update_EDSCR_Type_PipeAdv, edscrV, __SetThisInstrDetails,
    __DefaultCond, __DecodeExecute, __TryDecodeExecute, ExecuteA64, ThisInstrAddr, AArch64_ExecutingERETInstr,
    ThisInstr, ThisInstrLength]
  cases bt <;> gsimp <;> simp only [addInt4, postRegs, ite_true, ite_false, Bool.false_eq_true] <;> first | exact hs1 | exact hs2

end
end ArmProof
