/- F1/F2: full machine steps (`stepModel`) for every emitted word and for `ret`, and the backend theorem
`compile_ok` at the level of machine steps. -/
import Arm.Step
import Arm.Words
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.all false

namespace ArmProof

/-- **The configuration for full steps.** `Pins` (the pinned system registers: EL3, AArch64, MMU off, interrupts
not pending, debug/PMU/SPE/timers off, the feature set `featOn`, see `gen/pins.py`), plus the branch bookkeeping
the step reads: `Branchtypetaken ≠ RESET`, `BTypeNext = 0`, a cycle counter, and every `X` register present. -/
structure ArmFull (s : St) : Prop where
  pins : Pins s.regs
  bt : ∃ b, s.regs.get? .Branchtypetaken = some b ∧ (b == .BranchType_RESET) = false
  btn : s.regs.get? .BTypeNext = some 0
  cc : ∃ c, s.regs.get? .__cycle_count = some c
  x : ∀ i < 31, (xget s.regs i).isSome

theorem ins_swap {m : Regs} {a b : Register} {x : RegisterType a} {y : RegisterType b} (h : a ≠ b) :
    (m.insert a x).insert b y = (m.insert b y).insert a x :=
  Std.ExtDHashMap.ext_get? fun k => by
    simp only [Std.ExtDHashMap.get?_insert]
    by_cases ha : (a == k) = true <;> by_cases hb : (b == k) = true
    · exact absurd ((eq_of_beq ha).trans (eq_of_beq hb).symm) h
    all_goals simp [ha, hb]

theorem preRegs_see (m : Regs) (w : BitVec 32) (v : Int) :
    (preRegs m w).insert .SEE v = preRegs (m.insert .SEE v) w := by
  simp only [preRegs]; rw [ins_swap (a := .__currentCond) (b := .SEE) (by decide), ins_swap (a := .__ThisInstr) (b := .SEE) (by decide), ins_swap (a := .__ThisInstrEnc) (b := .SEE) (by decide), ins_swap (a := .__ExclusiveMonitorSet) (b := .SEE) (by decide), ins_swap (a := .__BranchTaken) (b := .SEE) (by decide), ins_swap (a := .InGuardedPage) (b := .SEE) (by decide), ins_swap (a := .__InstructionStep) (b := .SEE) (by decide), ins_swap (a := .BTypeCompatible) (b := .SEE) (by decide), ins_swap (a := .ShouldAdvanceSS) (b := .SEE) (by decide), ins_swap (a := .ShouldAdvanceIT) (b := .SEE) (by decide)]

theorem preRegs_get (m : Regs) (w : BitVec 32) (r : Register)
    (h : r ≠ .ShouldAdvanceIT ∧ r ≠ .ShouldAdvanceSS ∧ r ≠ .BTypeCompatible ∧ r ≠ .__InstructionStep ∧
      r ≠ .InGuardedPage ∧ r ≠ .__BranchTaken ∧ r ≠ .__ExclusiveMonitorSet ∧ r ≠ .__ThisInstrEnc ∧
      r ≠ .__ThisInstr ∧ r ≠ .__currentCond) : (preRegs m w).get? r = m.get? r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp [preRegs, Std.ExtDHashMap.get?_insert, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5,
    Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10]

theorem pre_abs {s : St} {a : AState} (ha : Abs s a) (w : BitVec 32) : Abs { s with regs := preRegs s.regs w } a := by
  have n : ∀ r : Register, (r.ctorIdx < 1059 ∨ 1089 < r.ctorIdx) → r ≠ .PSTATE → ∀ v (s' : St), Abs s' a →
      Abs { s' with regs := s'.regs.insert r v } a := fun r h1 h2 v s' h => h.insert r v (xreg_ne' h1) h2
  unfold preRegs
  exact n _ (by decide) (by decide) _ _ <| n _ (by decide) (by decide) _ _ <| n _ (by decide) (by decide) _ _ <|
    n _ (by decide) (by decide) _ _ <| n _ (by decide) (by decide) _ _ <| n _ (by decide) (by decide) _ _ <|
    n _ (by decide) (by decide) _ _ <| n _ (by decide) (by decide) _ _ <| n _ (by decide) (by decide) _ _ <|
    n _ (by decide) (by decide) _ _ ha

/-- emitted words are not `eret` (`__InstructionExecute` tests this before copying `BTypeNext`) -/
theorem not_eret_b : emitted.all (fun w => w.toNat / 4096 != 879088) = true := by decide +kernel
theorem not_eret : ∀ w ∈ emitted, BitVec.ofNat 20 (w.toNat >>> 12) ≠ 879088#20 := by
  intro w hw e
  have h1 := List.all_eq_true.mp not_eret_b w hw
  have h2 := congrArg BitVec.toNat e
  have h3 := w.isLt
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at h2
  simp at h1
  omega

theorem post_get (m : Regs) (q : ProcState) (btn : BitVec 2) (bt : Bool) (pc1 : BitVec 64) (c : Int) (r : Register)
    (h : r ≠ .InGuardedPage ∧ r ≠ .PSTATE ∧ r ≠ ._PC ∧ r ≠ .__cycle_count) :
    ((postRegs m q btn bt pc1).insert .__cycle_count c).get? r = m.get? r := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold postRegs; split <;> simp [Std.ExtDHashMap.get?_insert, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]

theorem post_ps (m : Regs) (q : ProcState) (btn : BitVec 2) (bt : Bool) (pc1 : BitVec 64) (c : Int) :
    ((postRegs m q btn bt pc1).insert .__cycle_count c).get? .PSTATE = some { q with BTYPE := btn } := by
  unfold postRegs; split <;> simp [Std.ExtDHashMap.get?_insert]

theorem post_xget (m : Regs) (q : ProcState) (btn : BitVec 2) (bt : Bool) (pc1 : BitVec 64) (c : Int) (i : Nat) :
    xget ((postRegs m q btn bt pc1).insert .__cycle_count c) i = xget m i := by
  have e : ∀ (r : Register) (v : RegisterType r) (m' : Regs), (r.ctorIdx < 1059 ∨ 1089 < r.ctorIdx) →
      xget (m'.insert r v) i = xget m' i := fun r v m' h => xget_insert _ r v (xreg_ne' h) i
  unfold postRegs; split
  · rw [e _ _ _ (by decide), e _ _ _ (by decide), e _ _ _ (by decide)]
  · rw [e _ _ _ (by decide), e _ _ _ (by decide), e _ _ _ (by decide), e _ _ _ (by decide)]

theorem abs_post {s1 : St} {a : AState} (ha : Abs s1 a) {q : ProcState} (hq : s1.regs.get? .PSTATE = some q)
    (btn : BitVec 2) (bt : Bool) (pc1 : BitVec 64) (c : Int) :
    Abs { s1 with regs := (postRegs s1.regs q btn bt pc1).insert .__cycle_count c } a := by
  obtain ⟨p, hp, hN, hZ, hC, hV⟩ := ha.p
  rw [hq] at hp; cases hp
  exact ⟨fun i hi => by rw [post_xget]; exact ha.x i hi, _, post_ps .., hN, hZ, hC, hV⟩

theorem full_post {s1 : St} (hc : Pins s1.regs) {q : ProcState} (hq : s1.regs.get? .PSTATE = some q)
    {b : BranchType} (hb : s1.regs.get? .Branchtypetaken = some b) (hbr : (b == .BranchType_RESET) = false)
    (hbn : s1.regs.get? .BTypeNext = some 0) (hx : ∀ i < 31, (xget s1.regs i).isSome)
    (btn : BitVec 2) (bt : Bool) (pc1 : BitVec 64) (c : Int) :
    ArmFull { s1 with regs := (postRegs s1.regs q btn bt pc1).insert .__cycle_count c } := by
  have hq3 : q.EL = 3#2 ∧ q.nRW = 0#1 ∧ q.IL = 0#1 := by
    obtain ⟨q', hq', h⟩ := hc.ps; rw [hq] at hq'; cases hq'; exact h
  have h1 := pins_pstate { q with BTYPE := btn } hq3 ((pins_insert (r := .InGuardedPage) (m := s1.regs) false rfl).2 hc)
  refine ⟨?_, ⟨b, by rw [post_get _ _ _ _ _ _ _ (by decide)]; exact hb, hbr⟩,
    by rw [post_get _ _ _ _ _ _ _ (by decide)]; exact hbn, ⟨c, by simp [Std.ExtDHashMap.get?_insert]⟩,
    fun i hi => by rw [post_xget]; exact hx i hi⟩
  show Pins ((postRegs s1.regs q btn bt pc1).insert .__cycle_count c)
  apply (pins_insert (r := .__cycle_count) _ rfl).2
  unfold postRegs; split
  · exact h1
  · exact (pins_insert (r := ._PC) _ rfl).2 h1

/-- **F1: a full machine step on an emitted word.** Under `ArmFull`, with the PC 4-aligned below `2^29` and the
word `w` stored little-endian at the PC, `stepModel` succeeds; the new state is abstracted by `armStep w a`,
satisfies `ArmFull` again, has `PC + 4` in the PC, and the same memory. -/
theorem full_word {w : BitVec 32} (hw : w ∈ emitted) {s : St} {a : AState} (hf : ArmFull s) (ha : Abs s a)
    {pc : BitVec 64} (hpc : s.regs.get? ._PC = some pc) (hlt : pc.toNat < 2 ^ 29) (hal : pc.toNat % 4 = 0)
    (hm : MemWord s.mem pc.toNat w) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' (armStep w a) ∧ ArmFull s' ∧ s'.regs.get? ._PC = some (pc + 4) ∧
      s'.mem = s.mem := by
  obtain ⟨b, hb, hbr⟩ := hf.bt
  obtain ⟨c, hcc⟩ := hf.cc
  let s0 : St := { s with regs := preRegs s.regs w }
  have hcfg0 : ArmCfg s0 := by
    show (preRegs s.regs w).get? .SPESampleInFlight = some false
    rw [preRegs_get _ _ _ (by decide)]; exact hf.pins.spe
  obtain ⟨s1, hdec, ha1, hc1, hfr⟩ := armStep_ok hw pc.toNat s0 a hcfg0 (pre_abs ha w)
  have hdec' : __DecodeA64 pc.toNat w { s with regs := preRegs (s.regs.insert .SEE (-1 : Int)) w } = .ok () s1 := by
    rw [← preRegs_see]; exact hdec
  have hfr1 : ∀ r : Register, (∀ i < 31, xreg i ≠ r) → r ≠ .PSTATE → r ≠ .SEE → s1.regs.get? r = s0.regs.get? r :=
    hfr.2.1
  have g : ∀ r : Register, (r.ctorIdx < 1059 ∨ 1089 < r.ctorIdx) → r ≠ .PSTATE → r ≠ .SEE →
      s1.regs.get? r = s0.regs.get? r := fun r h1 h2 h3 => hfr1 r (xreg_ne' h1) h2 h3
  obtain ⟨p, hp, -⟩ := hf.pins.ps
  have hp0 : s0.regs.get? .PSTATE = some p := by
    show (preRegs s.regs w).get? .PSTATE = some p; rw [preRegs_get _ _ _ (by decide)]; exact hp
  obtain ⟨q, hq, hpq⟩ := hfr.2.2 p hp0
  have hc0 : Pins s0.regs := by
    show Pins (preRegs s.regs w)
    unfold preRegs; simp [pins_insert, NotPinned, hf.pins]
  have hpins1 : Pins s1.regs := pins_frame hc0 hfr1 fun p' hp' => by
    rw [hp0] at hp'; cases hp'
    exact ⟨q, hq, by rw [← hpq], by rw [← hpq], by rw [← hpq]⟩
  have v0 : ∀ r : Register, (r.ctorIdx < 1059 ∨ 1089 < r.ctorIdx) → r ≠ .PSTATE → r ≠ .SEE →
      (∀ v, (preRegs s.regs w).get? r = some v → s1.regs.get? r = some v) := fun r h1 h2 h3 v h => (g r h1 h2 h3).trans h
  have hst := step_ok hf.pins pc w hpc hlt hal hm hb hbr s1 hdec' hpins1 hq
    (v0 .__BranchTaken (by decide) (by decide) (by decide) false (by simp [preRegs, Std.ExtDHashMap.get?_insert]))
    (v0 ._PC (by decide) (by decide) (by decide) pc (by rw [preRegs_get _ _ _ (by decide)]; exact hpc))
    (v0 .BTypeNext (by decide) (by decide) (by decide) 0 (by rw [preRegs_get _ _ _ (by decide)]; exact hf.btn))
    (v0 .__ThisInstr (by decide) (by decide) (by decide) w (by simp [preRegs, Std.ExtDHashMap.get?_insert]))
    (v0 .__ThisInstrEnc (by decide) (by decide) (by decide) .__A64 (by simp [preRegs, Std.ExtDHashMap.get?_insert]))
    (v0 .ShouldAdvanceIT (by decide) (by decide) (by decide) false (by simp [preRegs, Std.ExtDHashMap.get?_insert]))
    (v0 .ShouldAdvanceSS (by decide) (by decide) (by decide) true (by simp [preRegs, Std.ExtDHashMap.get?_insert]))
    (v0 .__cycle_count (by decide) (by decide) (by decide) c (by rw [preRegs_get _ _ _ (by decide)]; exact hcc))
    (not_eret w hw)
  have hx1 : ∀ i < 31, (xget s1.regs i).isSome := fun i hi => by rw [ha1.x i hi]; rfl
  refine ⟨_, hst, abs_post ha1 hq _ _ _ _, full_post hpins1 hq ?_ hbr ?_ hx1 _ _ _ _, ?_, ?_⟩
  · rw [g _ (by decide) (by decide) (by decide)]; show (preRegs s.regs w).get? _ = _
    rw [preRegs_get _ _ _ (by decide)]; exact hb
  · rw [g _ (by decide) (by decide) (by decide)]; show (preRegs s.regs w).get? _ = _
    rw [preRegs_get _ _ _ (by decide)]; exact hf.btn
  · simp [postRegs, Std.ExtDHashMap.get?_insert]
  · exact hfr.1

end ArmProof
