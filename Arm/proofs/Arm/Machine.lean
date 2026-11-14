/- F2: `ret` as a full step, runs of full steps, and `compile_ok` at the machine-step level. -/
import Arm.Full
import Arm.Ret
import Arm.Compiler
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.all false

namespace ArmProof
open Proven

theorem retcfg_of {s : St} (hc : Pins s.regs) : RetCfg s := by
  obtain ⟨p, hp, hel, hrw, -⟩ := hc.ps
  refine ⟨⟨p, hp, hrw, .inl ⟨hel, 0, hc.tcr3, by decide⟩⟩, ⟨featV, hc.feat, ?_⟩, ⟨0, hc.scr⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- **F2a: `ret` as a full machine step**: PC := x30, nothing else visible changes. -/
theorem full_ret {s : St} {a : AState} (hf : ArmFull s) (ha : Abs s a)
    {pc : BitVec 64} (hpc : s.regs.get? ._PC = some pc) (hlt : pc.toNat < 2 ^ 29) (hal : pc.toNat % 4 = 0)
    (hm : MemWord s.mem pc.toNat Arm.iRet) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFull s' ∧ s'.regs.get? ._PC = some (a.x 30) ∧ s'.mem = s.mem := by
  obtain ⟨b, hb, hbr⟩ := hf.bt
  obtain ⟨c, hcc⟩ := hf.cc
  let s0 : St := { s with regs := preRegs (s.regs.insert .SEE (-1 : Int)) Arm.iRet }
  have hc0 : Pins s0.regs := by
    show Pins (preRegs (s.regs.insert .SEE (-1 : Int)) Arm.iRet)
    unfold preRegs; simp [pins_insert, NotPinned, hf.pins]
  have hsee : s0.regs.get? .SEE = some (-1 : Int) := by simp [s0, preRegs, Std.ExtDHashMap.get?_insert]
  have h30 : xget s0.regs 30 = some (a.x 30) := by
    rw [← ha.x 30 (by decide)]
    show xget (preRegs (s.regs.insert .SEE (-1 : Int)) Arm.iRet) 30 = _
    have e : ∀ (r : Register) (v : RegisterType r) (m' : Regs), (r.ctorIdx < 1059 ∨ 1089 < r.ctorIdx) →
        xget (m'.insert r v) 30 = xget m' 30 := fun r v m' h => xget_insert _ r v (xreg_ne' h) 30
    simp only [preRegs]
    repeat rw [e _ _ _ (by decide)]
  have hd := ret_word s0 pc.toNat (-1) (by decide) hsee (retcfg_of hc0) h30
  obtain ⟨p, hp, -⟩ := hf.pins.ps
  let m1 := ((((s0.regs.insert .SEE (94 : Int)).insert .BTypeNext 0#2).insert .Branchtypetaken .BranchType_RET).insert
    ._PC (a.x 30)).insert .__BranchTaken true
  have hpins1 : Pins m1 := by simp [m1, pins_insert, NotPinned, hc0]
  have gg : ∀ r : Register, r ≠ .SEE ∧ r ≠ .BTypeNext ∧ r ≠ .Branchtypetaken ∧ r ≠ ._PC ∧ r ≠ .__BranchTaken →
      m1.get? r = s0.regs.get? r := fun r ⟨h1, h2, h3, h4, h5⟩ => by
    simp [m1, Std.ExtDHashMap.get?_insert, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
  have pg : ∀ r : Register, r ≠ .SEE → r ≠ .ShouldAdvanceIT ∧ r ≠ .ShouldAdvanceSS ∧ r ≠ .BTypeCompatible ∧
      r ≠ .__InstructionStep ∧ r ≠ .InGuardedPage ∧ r ≠ .__BranchTaken ∧ r ≠ .__ExclusiveMonitorSet ∧
      r ≠ .__ThisInstrEnc ∧ r ≠ .__ThisInstr ∧ r ≠ .__currentCond → s0.regs.get? r = s.regs.get? r := fun r h1 h2 => by
    show (preRegs _ _).get? r = _; rw [preRegs_get _ _ _ h2]; simp [Std.ExtDHashMap.get?_insert, Ne.symm h1]
  have hst := step_ok hf.pins pc Arm.iRet hpc hlt hal hm hb hbr { s0 with regs := m1 } hd hpins1
    (p1 := p) (bt := true) (pc1 := a.x 30) (btn := 0) (c := c)
    (by rw [gg _ (by decide), pg _ (by decide) (by decide)]; exact hp)
    (by simp [m1, Std.ExtDHashMap.get?_insert])
    (by simp [m1, Std.ExtDHashMap.get?_insert])
    (by simp [m1, Std.ExtDHashMap.get?_insert])
    (by rw [gg _ (by decide)]; simp [s0, preRegs, Std.ExtDHashMap.get?_insert])
    (by rw [gg _ (by decide)]; simp [s0, preRegs, Std.ExtDHashMap.get?_insert])
    (by rw [gg _ (by decide)]; simp [s0, preRegs, Std.ExtDHashMap.get?_insert])
    (by rw [gg _ (by decide)]; simp [s0, preRegs, Std.ExtDHashMap.get?_insert])
    (by rw [gg _ (by decide), pg _ (by decide) (by decide)]; exact hcc)
    (by decide)
  have ha0 : Abs s0 a := by
    have := pre_abs (s := { s with regs := s.regs.insert .SEE (-1 : Int) }) (ha.insert .SEE _ (xreg_ne' (by decide)) (by decide)) Arm.iRet
    exact this
  have ha1 : Abs { s0 with regs := m1 } a := by
    have n : ∀ r : Register, (r.ctorIdx < 1059 ∨ 1089 < r.ctorIdx) → r ≠ .PSTATE → ∀ v (s' : St), Abs s' a →
        Abs { s' with regs := s'.regs.insert r v } a := fun r h1 h2 v s' h => h.insert r v (xreg_ne' h1) h2
    exact n _ (by decide) (by decide) _ _ <| n _ (by decide) (by decide) _ _ <| n _ (by decide) (by decide) _ _ <|
      n _ (by decide) (by decide) _ _ <| n _ (by decide) (by decide) _ _ ha0
  have hp1 : m1.get? .PSTATE = some p := by rw [gg _ (by decide), pg _ (by decide) (by decide)]; exact hp
  have hx1 : ∀ i < 31, (xget m1 i).isSome := fun i hi => by rw [ha1.x i hi]; rfl
  refine ⟨_, hst, abs_post ha1 hp1 _ _ _ _, full_post (s1 := { s0 with regs := m1 }) (b := .BranchType_RET) hpins1 hp1
    (by simp [m1, Std.ExtDHashMap.get?_insert]) (by decide) (by simp [m1, Std.ExtDHashMap.get?_insert]) hx1 _ _ _ _,
    ?_, rfl⟩
  show ((postRegs m1 p 0 true (a.x 30)).insert .__cycle_count (c + 1)).get? ._PC = _
  simp [postRegs, m1, Std.ExtDHashMap.get?_insert]

end ArmProof
