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

/-! ## Runs of full machine steps -/

/-- `n` full machine steps (`stepModel`) from `s` to `s'` -/
def ArmSteps : Nat → St → St → Prop
  | 0, s, s' => s' = s
  | n + 1, s, s' => ∃ s₁, stepModel s = .ok () s₁ ∧ ArmSteps n s₁ s'

/-- the machine reaches a state satisfying `P` (the ARM analogue of the RISC-V `runsTo`) -/
def armRunsTo (s : St) (P : St → Prop) : Prop := ∃ n s', ArmSteps n s s' ∧ P s'

theorem ArmSteps.append : ∀ {m n : Nat} {s₁ s₂ s₃ : St}, ArmSteps m s₁ s₂ → ArmSteps n s₂ s₃ → ArmSteps (m + n) s₁ s₃
  | 0, n, s₁, s₂, s₃, h₁, h₂ => by cases h₁; simpa using h₂
  | m + 1, n, s₁, s₂, s₃, ⟨t, ht, h₁⟩, h₂ => by
    rw [show m + 1 + n = (m + n) + 1 by omega]; exact ⟨t, ht, ArmSteps.append h₁ h₂⟩

/-- the words `ws` sit at consecutive word addresses from byte address `a` -/
def CodeAt (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (ws : List (BitVec 32)) : Prop :=
  ∀ i (h : i < ws.length), MemWord m (a + 4 * i) ws[i]

theorem pc_add (pc : BitVec 64) (k : Nat) : pc + 4 + BitVec.ofNat 64 (4 * k) = pc + BitVec.ofNat 64 (4 * (k + 1)) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

/-- **simulation by full steps**: on emitted words laid out from the PC, the machine follows the small machine -/
theorem run_full : ∀ (ws : List (BitVec 32)) (s : St) (a : AState) (pc : BitVec 64), (∀ w ∈ ws, w ∈ emitted) →
    ArmFull s → Abs s a → s.regs.get? ._PC = some pc → pc.toNat % 4 = 0 → pc.toNat + 4 * ws.length < 2 ^ 29 →
    CodeAt s.mem pc.toNat ws →
    ∃ s', ArmSteps ws.length s s' ∧ Abs s' (runA ws a) ∧ ArmFull s' ∧
      s'.regs.get? ._PC = some (pc + BitVec.ofNat 64 (4 * ws.length)) ∧ s'.mem = s.mem
  | [], s, a, pc, _, hf, ha, hpc, _, _, _ => ⟨s, rfl, ha, hf, by simpa using hpc, rfl⟩
  | w :: ws, s, a, pc, hw, hf, ha, hpc, hal, hlt, hcode => by
    have h0 : MemWord s.mem pc.toNat w := by have := hcode 0 (by simp); simpa using this
    obtain ⟨s₁, h₁, ha₁, hf₁, hpc₁, hm₁⟩ :=
      full_word (hw w (List.mem_cons_self ..)) hf ha hpc (by simp at hlt; omega) hal h0
    have e : (pc + 4).toNat = pc.toNat + 4 := by simp [BitVec.toNat_add]; simp at hlt; omega
    obtain ⟨s₂, h₂, ha₂, hf₂, hpc₂, hm₂⟩ := run_full ws s₁ (armStep w a) (pc + 4)
      (fun w' h => hw w' (List.mem_cons_of_mem _ h)) hf₁ ha₁ hpc₁ (by omega) (by simp at hlt; omega)
      (fun i hi => by rw [hm₁, e, show pc.toNat + 4 + 4 * i = pc.toNat + 4 * (i + 1) by omega]
                      exact hcode (i + 1) (by simp; omega))
    refine ⟨s₂, ⟨s₁, h₁, h₂⟩, ha₂, hf₂, ?_, hm₂.trans hm₁⟩
    rw [hpc₂, pc_add]; rfl

theorem T30 : ∀ i < 11, (30 : Nat) ≠ Arm.T i := by decide

/-- the value of `X[i]` in a state (`0` if missing) -/
def xv (s : St) (i : Nat) : BitVec 64 := (xget s.regs i).getD 0

/-- **F2: the AArch64 backend is correct at the level of full machine steps.** From a state satisfying `ArmFull`
whose memory holds `Arm.compile e` (little-endian words) at the 4-aligned PC (code below `2^29`), the machine reaches
`PC = x30` with `x0 = e.denote` of the inputs `x0..x3`, `ArmFull` again, memory unchanged, and every `X` register other
than `x0` and the backend's temporaries unchanged. The ARM analogue of the RISC-V `compile_ok`. -/
theorem compile_ok (e : Exp) (he : e.depth < 11) {s : St} (hf : ArmFull s) {pc : BitVec 64}
    (hpc : s.regs.get? ._PC = some pc) (hal : pc.toNat % 4 = 0) (hlt : pc.toNat + 4 * (Arm.compile e).length < 2 ^ 29)
    (hcode : CodeAt s.mem pc.toNat (Arm.compile e)) :
    armRunsTo s fun s' => s'.regs.get? ._PC = some (xv s 30) ∧
      xget s'.regs 0 = some (e.denote (fun i => xv s i)) ∧ ArmFull s' ∧ s'.mem = s.mem ∧
      (∀ j < 31, (∀ i < 11, j ≠ Arm.T i) → j ≠ 0 → xget s'.regs j = xget s.regs j) := by
  obtain ⟨p, hp, -⟩ := hf.pins.ps
  let env : Fin 4 → BitVec 64 := fun i => xv s i
  let a : AState := ⟨fun i => xv s i, p.N == 1#1, p.Z == 1#1, p.C == 1#1, p.V == 1#1⟩
  have hxa : ∀ i < 31, xget s.regs i = some (a.x i) := fun i hi => by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hf.x i hi); simp [a, xv, hv]
  have ha : Abs s a := ⟨hxa, p, hp, (ofBool_beq_one _).symm, (ofBool_beq_one _).symm, (ofBool_beq_one _).symm,
    (ofBool_beq_one _).symm⟩
  let ws := Arm.gen e 0 ++ [Arm.iRes]
  have hc : Arm.compile e = ws ++ [Arm.iRet] := by simp [ws, Arm.compile]
  have hmem : ∀ w ∈ ws, w ∈ emitted := fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · exact gen_mem e 0 (by omega) w hw
    · rw [List.mem_singleton.mp hw]; exact res_mem
  have hlen : (Arm.compile e).length = ws.length + 1 := by rw [hc]; simp
  obtain ⟨s₁, h₁, ha₁, hf₁, hpc₁, hm₁⟩ := run_full ws s a pc hmem hf ha hpc hal (by omega)
    (fun i hi => by have := hcode i (by omega); rwa [List.getElem_of_eq hc, List.getElem_append_left hi] at this)
  have e1 : (pc + BitVec.ofNat 64 (4 * ws.length)).toNat = pc.toNat + 4 * ws.length := by
    simp [BitVec.toNat_add]; omega
  obtain ⟨s₂, h₂, ha₂, hf₂, hpc₂, hm₂⟩ := full_ret hf₁ ha₁ hpc₁ (by omega) (by omega) (by
    rw [hm₁, e1]; have := hcode ws.length (by omega)
    rw [List.getElem_of_eq hc, List.getElem_append_right (by omega)] at this; simpa using this)
  have henv' : ∀ i : Fin 4, a.x i = env i := fun i => rfl
  obtain ⟨v, kp⟩ := gen_small env e 0 a (by omega) henv'
  have hres := res_small (runA (Arm.gen e 0) a)
  have hra : runA ws a = runA [Arm.iRes] (runA (Arm.gen e 0) a) := runA_append _ _ _
  refine ⟨ws.length + 1, s₂, ArmSteps.append h₁ ⟨s₂, h₂, rfl⟩, ?_, ?_, hf₂, hm₂.trans hm₁, fun j hj hT h0 => ?_⟩
  · rw [hpc₂, hra, hres, if_neg (by decide), kp 30 (fun i _ hi => T30 i hi)]
  · rw [ha₂.x 0 (by decide), hra, hres, if_pos rfl, show (9 : Nat) = Arm.T 0 from rfl, v]
  · rw [ha₂.x j hj, hra, hres, if_neg h0, kp j (fun i _ hi h => hT i hi h), hxa j hj]

end ArmProof
