/- Full machine steps (`stepModel`, under `ArmFull`) for the words the DeepMind-model compiler emits beyond the 216
expression words: `b`, `bl`, `cbz`/`cbnz`, `b.cond`, `movz`/`movk`, `add`/`sub` immediate, with symbolic fields. -/
import Arm.SymDec
import Arm.Branch
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.all false
set_option pp.deepTerms false
set_option pp.maxSteps 3000

namespace ArmProof

theorem pkeep_el {p q : ProcState} (h : PKeep p q) : q.EL = p.EL ∧ q.nRW = p.nRW ∧ q.IL = p.IL := by
  unfold PKeep at h
  rw [← h]; exact ⟨rfl, rfl, rfl⟩

/-- **generic full step**: any decode+execute result `s1` that changes only `X`, NZCV, SEE and the branch
bookkeeping (`_PC`, `__BranchTaken`, `Branchtypetaken` ≠ RESET, `BTypeNext` = 0) is one full `stepModel` step. -/
theorem full_gen {w : BitVec 32} {s : St} {a : AState} (hf : ArmFull s) {pc : BitVec 64}
    (hpc : s.regs.get? ._PC = some pc) (hlt : pc.toNat < 2 ^ 29) (hal : pc.toNat % 4 = 0)
    (hm : MemWord s.mem pc.toNat w) (heret : BitVec.ofNat 20 (w.toNat >>> 12) ≠ 879088#20) {s1 : St}
    (hdec : __DecodeA64 pc.toNat w { s with regs := preRegs (s.regs.insert .SEE (-1 : Int)) w } = .ok () s1)
    (hfr : ∀ r : Register, (∀ i < 31, xreg i ≠ r) → r ≠ .PSTATE → r ≠ .SEE → r ≠ ._PC → r ≠ .__BranchTaken →
      r ≠ .Branchtypetaken → r ≠ .BTypeNext → s1.regs.get? r = (preRegs (s.regs.insert .SEE (-1 : Int)) w).get? r)
    (hps : ∀ p, s.regs.get? .PSTATE = some p → ∃ q, s1.regs.get? .PSTATE = some q ∧ PKeep p q)
    {bt : Bool} {pc1 : BitVec 64} {b : BranchType}
    (hbt : s1.regs.get? .__BranchTaken = some bt) (hpc1 : s1.regs.get? ._PC = some pc1)
    (hb : s1.regs.get? .Branchtypetaken = some b) (hbr : (b == .BranchType_RESET) = false)
    (hbtn : s1.regs.get? .BTypeNext = some 0) (ha1 : Abs s1 a) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFull s' ∧
      s'.regs.get? ._PC = some (if bt then pc1 else pc1 + 4) ∧ s'.mem = s1.mem := by
  obtain ⟨b0, hb0, hbr0⟩ := hf.bt
  obtain ⟨c, hcc⟩ := hf.cc
  let m0 := preRegs (s.regs.insert .SEE (-1 : Int)) w
  have pg : ∀ r : Register, r ≠ .SEE → r ≠ .ShouldAdvanceIT ∧ r ≠ .ShouldAdvanceSS ∧ r ≠ .BTypeCompatible ∧
      r ≠ .__InstructionStep ∧ r ≠ .InGuardedPage ∧ r ≠ .__BranchTaken ∧ r ≠ .__ExclusiveMonitorSet ∧
      r ≠ .__ThisInstrEnc ∧ r ≠ .__ThisInstr ∧ r ≠ .__currentCond → m0.get? r = s.regs.get? r := fun r h1 h2 => by
    show (preRegs _ _).get? r = _; rw [preRegs_get _ _ _ h2]; simp [Std.ExtDHashMap.get?_insert, Ne.symm h1]
  have hc0 : Pins m0 := by
    show Pins (preRegs (s.regs.insert .SEE (-1 : Int)) w)
    unfold preRegs; simp [pins_insert, NotPinned, hf.pins]
  obtain ⟨p, hp, -⟩ := hf.pins.ps
  obtain ⟨q, hq, hpq⟩ := hps p hp
  let m1 := (((m0.insert ._PC pc1).insert .__BranchTaken bt).insert .Branchtypetaken b).insert .BTypeNext 0
  have hm1 : Pins m1 := by simp [m1, pins_insert, NotPinned, hc0]
  have hfr1 : ∀ r : Register, (∀ i < 31, xreg i ≠ r) → r ≠ .PSTATE → r ≠ .SEE → s1.regs.get? r = m1.get? r := by
    intro r h1 h2 h3
    by_cases e1 : r = ._PC; · subst e1; simp [m1, Std.ExtDHashMap.get?_insert, hpc1]
    by_cases e2 : r = .__BranchTaken; · subst e2; simp [m1, Std.ExtDHashMap.get?_insert, hbt]
    by_cases e3 : r = .Branchtypetaken; · subst e3; simp [m1, Std.ExtDHashMap.get?_insert, hb]
    by_cases e4 : r = .BTypeNext; · subst e4; simp [m1, Std.ExtDHashMap.get?_insert, hbtn]
    rw [hfr r h1 h2 h3 e1 e2 e3 e4]
    simp [m1, m0, Std.ExtDHashMap.get?_insert, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4]
  have hp0 : m1.get? .PSTATE = some p := by
    simp only [m1, Std.ExtDHashMap.get?_insert]; simp; exact (pg _ (by decide) (by decide)).trans hp
  have hpins1 : Pins s1.regs := pins_frame hm1 hfr1 fun p' hp' => by
    rw [hp0] at hp'; cases hp'; exact ⟨q, hq, pkeep_el hpq⟩
  have g : ∀ r : Register, (r.ctorIdx < 1059 ∨ 1089 < r.ctorIdx) → r ≠ .PSTATE → r ≠ .SEE → r ≠ ._PC →
      r ≠ .__BranchTaken → r ≠ .Branchtypetaken → r ≠ .BTypeNext → s1.regs.get? r = m0.get? r :=
    fun r h1 h2 h3 h4 h5 h6 h7 => hfr r (xreg_ne' h1) h2 h3 h4 h5 h6 h7
  have hst := step_ok hf.pins pc w hpc hlt hal hm hb0 hbr0 s1 hdec hpins1 hq hbt hpc1 hbtn
    (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [m0, preRegs, Std.ExtDHashMap.get?_insert])
    (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [m0, preRegs, Std.ExtDHashMap.get?_insert])
    (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [m0, preRegs, Std.ExtDHashMap.get?_insert])
    (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [m0, preRegs, Std.ExtDHashMap.get?_insert])
    (c := c) (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        pg _ (by decide) (by decide)]; exact hcc)
    heret
  have hx1 : ∀ i < 31, (xget s1.regs i).isSome := fun i hi => by rw [ha1.x i hi]; rfl
  refine ⟨_, hst, abs_post ha1 hq _ _ _ _, full_post hpins1 hq hb hbr hbtn hx1 _ _ _ _, ?_, rfl⟩
  unfold postRegs; cases bt <;> simp [Std.ExtDHashMap.get?_insert, hpc1]

/-! ## decode+execute with symbolic fields -/
section
variable {s : St} {d n : Nat} {a : BitVec 64}
theorem hw4 (hw : BitVec 2) : (hw +++ 0#4).toNat = hw.toNat * 16 := by
  rw [BitVec.toNat_append]; simp [Nat.shiftLeft_eq]
theorem sw2 (imm : BitVec 16) (m : Nat) (hm : 16 ≤ m) : BitVec.setWidth 64 (BitVec.setWidth m imm) = BitVec.setWidth 64 imm := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]
  have h1 := imm.isLt; have h2 := Nat.pow_le_pow_right (show 0 < 2 by decide) hm
  rw [Nat.mod_eq_of_lt (show imm.toNat < 2 ^ m by omega), Nat.mod_eq_of_lt (show imm.toNat < 2 ^ 64 by omega)]
theorem ao16 (m : Nat) (hm : m = 16) : BitVec.setWidth 64 (BitVec.allOnes m) = 0xFFFF#64 := by subst hm; decide
theorem wid (k : Nat) : ((k : Int) + 15).toNat - k + 1 = 16 := by omega
theorem movk_exec' (hd : d < 31) (imm : BitVec 16) (hw : BitVec 2) (ha : xget s.regs d = some a) :
    decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide (BitVec.ofNat 5 d) imm hw 3#2 1#1 s =
      .ok () { s with regs := xset s.regs d (~~~(0xFFFF#64 <<< (hw.toNat * 16)) &&& a ||| imm.setWidth 64 <<< (hw.toNat * 16)) } := by
  idx d
  have := hw.isLt
  dsimp only [decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide]; dsimp
  exec_simp
  rw [hw4] at *
  simp only [show ((hw.toNat * 16 : Nat) : Int) + 15 < 64 by omega, ite_true, EStateM.pure]
  rw [ao16 _ (wid _), sw2 _ _ (by rw [wid]; decide)]
theorem movz_exec' (hd : d < 31) (imm : BitVec 16) (hw : BitVec 2) :
    decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide (BitVec.ofNat 5 d) imm hw 2#2 1#1 s =
      .ok () { s with regs := xset s.regs d (imm.setWidth 64 <<< (hw.toNat * 16)) } := by
  idx d
  have := hw.isLt
  dsimp only [decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide]; dsimp
  exec_simp
  rw [hw4] at *
  simp only [show ((hw.toNat * 16 : Nat) : Int) + 15 < 64 by omega, ite_true, EStateM.pure]
  rw [sw2 _ _ (by rw [wid]; decide)]
theorem addi_exec (hd : d < 31) (hn : n < 31) (ha : xget s.regs n = some a) (imm : BitVec 12) :
    decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) imm 0#1 0#1 0#1 1#1 s =
      .ok () { s with regs := xset s.regs d (a + imm.setWidth 64) } := by
  idx d; idx n
  dsimp only [decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate]; dsimp
  exec_simp
theorem subi_exec (hd : d < 31) (hn : n < 31) (ha : xget s.regs n = some a) (imm : BitVec 12) :
    decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) imm 0#1 0#1 1#1 1#1 s =
      .ok () { s with regs := xset s.regs d (a - imm.setWidth 64) } := by
  idx d; idx n
  dsimp only [decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate]; dsimp
  exec_simp
/-- the condition test of `ConditionHolds` on PSTATE `p` -/
def condP (c : BitVec 4) (p : ProcState) : Bool :=
  let r : Bool := match (c.extractLsb' 1 3).toNat with
    | 0 => p.Z == 1#1 | 1 => p.C == 1#1 | 2 => p.N == 1#1 | 3 => p.V == 1#1
    | 4 => p.C == 1#1 && p.Z == 0#1 | 5 => p.N == p.V | 6 => p.N == p.V && p.Z == 0#1 | _ => true
  if c.getLsbD 0 && c != 15#4 then !r else r
theorem bv4 : ∀ c : BitVec 4, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨
    c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 := by decide
theorem cond_ok (c : BitVec 4) {p : ProcState} (hp : s.regs.get? .PSTATE = some p) :
    ConditionHolds c s = .ok (condP c p) s := by
  rcases bv4 c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) [ConditionHolds, condP, PreSail.undefined_bool, PreSail.internal_pick, choose_ok,
    PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hp, andM,
    ToBool.toBool, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', Sail.BitVec.access, BitVec.access]
  all_goals (rcases Bool.eq_false_or_eq_true (p.C == 1#1) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (p.N == p.V) with h2 | h2 <;>
    simp [h1, h2, EStateM.get, EStateM.bind, EStateM.pure, hp])
section
variable {s : St} (hc : Pins s.regs)
include hc
theorem bl_exec (imm26 : BitVec 26) {pc : BitVec 64} (hpc : s.regs.get? ._PC = some pc) :
    decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1 s =
      .ok () { s with regs := ((((s.regs.insert .R30 (pc + 4)).insert .Branchtypetaken .BranchType_DIRCALL).insert ._PC
        (pc + sign_extend (imm26 +++ 0#2) 64)).insert .__BranchTaken true) } := by
  have hr := retcfg_of hc
  obtain ⟨p, hp, hrw, hel⟩ := hr.p
  obtain ⟨fi, hfi, hgcs, hbrbe, hspe, hpac, hvhe, ha64⟩ := hr.fi
  obtain ⟨scr, hscr⟩ := hr.scr
  have hx : ∀ s' : St, X_set 30 64 (BitVec.addInt pc 4) s' = .ok () { s' with regs := s'.regs.insert .R30 (pc + 4) } := by
    intro s'; have := write_gpr_ok (s := s') (d := 30) (by decide) (pc + 4)
    simp only [X_set, set_R, addInt4] at *; simp (config := {decide := true}) [bind, pure, EStateM.bind, EStateM.pure, this]; rfl
  simp only [decode_bl_aarch64_instrs_branch_unconditional_immediate,
    execute_aarch64_instrs_branch_unconditional_immediate, PC_read]
  rcases hel with ⟨hel3, tcr, htcr, htbi⟩ | ⟨hel1, -⟩
  · ret_simp
  · obtain ⟨q, hq, h3, -⟩ := hc.ps; rw [hp] at hq; cases hq; rw [hel1] at h3; cases h3
theorem bc_taken (c : BitVec 4) (imm19 : BitVec 19) {pc : BitVec 64} (hpc : s.regs.get? ._PC = some pc)
    {p : ProcState} (hp : s.regs.get? .PSTATE = some p) (hcond : condP c p = true) :
    decode_b_cond_aarch64_instrs_branch_conditional_cond c imm19 s =
      .ok () { s with regs := takenRegs s.regs (pc + sign_extend (imm19 +++ 0#2) 64) } := by
  have hr := retcfg_of hc
  obtain ⟨p', hp', hrw, hel⟩ := hr.p
  rw [hp] at hp'; cases hp'
  obtain ⟨fi, hfi, hgcs, hbrbe, hspe, hpac, hvhe, ha64⟩ := hr.fi
  obtain ⟨scr, hscr⟩ := hr.scr
  have hco := cond_ok (s := s) c hp
  simp only [decode_b_cond_aarch64_instrs_branch_conditional_cond,
    execute_aarch64_instrs_branch_conditional_cond, PC_read, takenRegs, BranchNotTaken]
  rcases hel with ⟨hel3, tcr, htcr, htbi⟩ | ⟨hel1, -⟩
  · ret_simp
  · obtain ⟨q, hq, h3, -⟩ := hc.ps; rw [hp] at hq; cases hq; rw [hel1] at h3; cases h3
theorem bc_not (c : BitVec 4) (imm19 : BitVec 19) {pc : BitVec 64} (hpc : s.regs.get? ._PC = some pc)
    {p : ProcState} (hp : s.regs.get? .PSTATE = some p) (hcond : condP c p = false) :
    decode_b_cond_aarch64_instrs_branch_conditional_cond c imm19 s = .ok () s := by
  have hr := retcfg_of hc
  obtain ⟨p', hp', hrw, hel⟩ := hr.p
  rw [hp] at hp'; cases hp'
  obtain ⟨fi, hfi, hgcs, hbrbe, hspe, hpac, hvhe, ha64⟩ := hr.fi
  obtain ⟨scr, hscr⟩ := hr.scr
  have hco := cond_ok (s := s) c hp
  simp only [decode_b_cond_aarch64_instrs_branch_conditional_cond,
    execute_aarch64_instrs_branch_conditional_cond, PC_read, takenRegs, BranchNotTaken]
  rcases hel with ⟨hel3, tcr, htcr, htbi⟩ | ⟨hel1, -⟩
  · ret_simp
  · obtain ⟨q, hq, h3, -⟩ := hc.ps; rw [hp] at hq; cases hq; rw [hel1] at h3; cases h3
end
end

theorem noteret {w K T : BitVec 32} (hK : w &&& K = T) (i : Nat) (hi : 12 ≤ i) (hk : K.getLsbD i = true)
    (hne : (T.getLsbD i == Nat.testBit 879088 (i - 12)) = false) : BitVec.ofNat 20 (w.toNat >>> 12) ≠ 879088#20 := by
  intro e
  have h1 : w.toNat >>> 12 = 879088 := by
    have := congrArg BitVec.toNat e; have := w.isLt
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at *; omega
  have h2 : w.getLsbD i = Nat.testBit 879088 (i - 12) := by
    rw [BitVec.getLsbD, ← h1, Nat.testBit_shiftRight]; congr 1; omega
  have h3 : w.getLsbD i = T.getLsbD i := by rw [← hK, BitVec.getLsbD_and, hk, Bool.and_true]
  rw [← h3, h2] at hne; simp at hne

/-- inserting a register that is neither an `X` register nor PSTATE keeps `Abs` -/
theorem abs_ins {s : St} {a : AState} (h : Abs s a) (r : Register) (h1 : r.ctorIdx < 1059 ∨ 1089 < r.ctorIdx)
    (h2 : r ≠ .PSTATE) (v : RegisterType r) : Abs { s with regs := s.regs.insert r v } a := h.insert r v (xreg_ne' h1) h2

/-- the state decode starts from -/
def s0of (s : St) (w : BitVec 32) : St := { s with regs := preRegs (s.regs.insert .SEE (-1 : Int)) w }

theorem s0_see (s : St) (w : BitVec 32) : (s0of s w).regs.get? .SEE = some (-1 : Int) := by
  simp [s0of, preRegs, Std.ExtDHashMap.get?_insert]

theorem s0_get (s : St) (w : BitVec 32) (r : Register) (h1 : r ≠ .SEE) (h2 : r ≠ .ShouldAdvanceIT ∧ r ≠ .ShouldAdvanceSS ∧
    r ≠ .BTypeCompatible ∧ r ≠ .__InstructionStep ∧ r ≠ .InGuardedPage ∧ r ≠ .__BranchTaken ∧
    r ≠ .__ExclusiveMonitorSet ∧ r ≠ .__ThisInstrEnc ∧ r ≠ .__ThisInstr ∧ r ≠ .__currentCond) :
    (s0of s w).regs.get? r = s.regs.get? r := by
  show (preRegs _ _).get? r = _; rw [preRegs_get _ _ _ h2]; simp [Std.ExtDHashMap.get?_insert, Ne.symm h1]

theorem s0_pins {s : St} (hf : ArmFull s) (w : BitVec 32) : Pins (s0of s w).regs := by
  show Pins (preRegs (s.regs.insert .SEE (-1 : Int)) w)
  unfold preRegs; simp [pins_insert, NotPinned, hf.pins]

theorem s0_abs {s : St} {a : AState} (ha : Abs s a) (w : BitVec 32) : Abs (s0of s w) a :=
  pre_abs (s := { s with regs := s.regs.insert .SEE (-1 : Int) }) (abs_ins ha .SEE (by decide) (by decide) _) w

theorem s0_x {s : St} (w : BitVec 32) (i : Nat) : xget (s0of s w).regs i = xget s.regs i := by
  have e : ∀ (r : Register) (v : RegisterType r) (m' : Regs), (r.ctorIdx < 1059 ∨ 1089 < r.ctorIdx) →
      xget (m'.insert r v) i = xget m' i := fun r v m' h => xget_insert _ r v (xreg_ne' h) i
  show xget (preRegs _ _) i = _
  simp only [preRegs]
  repeat rw [e _ _ _ (by decide)]

theorem pkeep_refl (p : ProcState) : PKeep p p := rfl

section
variable {w : BitVec 32} {s : St} {a : AState} (hf : ArmFull s) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : pc.toNat < 2 ^ 29) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
  (heret : BitVec.ofNat 20 (w.toNat >>> 12) ≠ 879088#20)
include hf ha hpc hlt hal hm heret

theorem s0_ps : ∀ p, s.regs.get? .PSTATE = some p → (s0of s w).regs.get? .PSTATE = some p :=
  fun _ hp => (s0_get _ _ _ (by decide) (by decide)).trans hp

/-- full step for a decode+execute that writes one `X` register -/
theorem full_x {k : Int} {d : Nat} (hd : d < 31) {v : BitVec 64}
    (hdec : __DecodeA64 pc.toNat w (s0of s w) = .ok () { s0of s w with regs := xset ((s0of s w).regs.insert .SEE k) d v }) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' (a.setX d v) ∧ ArmFull s' ∧ s'.regs.get? ._PC = some (pc + 4) ∧
      s'.mem = s.mem := by
  obtain ⟨b0, hb0, hbr0⟩ := hf.bt
  have hx : ∀ r : Register, (∀ i < 31, xreg i ≠ r) → r ≠ .SEE →
      (xset ((s0of s w).regs.insert .SEE k) d v).get? r = (s0of s w).regs.get? r := fun r h1 h2 => by
    rw [xset_get_ne _ _ _ _ h1]; simp [Std.ExtDHashMap.get?_insert, Ne.symm h2]
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_gen hf hpc hlt hal hm heret hdec (bt := false) (pc1 := pc) (b := b0)
    (fun r h1 h2 h3 _ _ _ _ => hx r h1 h3)
    (fun p hp => ⟨p, by rw [hx _ (xreg_ne' (by decide)) (by decide)]; exact s0_ps hf ha hpc hlt hal hm heret p hp, pkeep_refl p⟩)
    (by rw [hx _ (xreg_ne' (by decide)) (by decide)]; simp [s0of, preRegs, Std.ExtDHashMap.get?_insert])
    (by rw [hx _ (xreg_ne' (by decide)) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hpc)
    (by rw [hx _ (xreg_ne' (by decide)) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hb0) hbr0
    (by rw [hx _ (xreg_ne' (by decide)) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hf.btn)
    (Abs.xset (abs_ins (s0_abs ha w) .SEE (by decide) (by decide) k) hd v)
  exact ⟨s', h1, h2, h3, by simpa using h4, h5⟩

/-- full step for a taken branch (`takenRegs`) -/
theorem full_tk {k : Int} {t : BitVec 64}
    (hdec : __DecodeA64 pc.toNat w (s0of s w) = .ok () { s0of s w with regs := takenRegs ((s0of s w).regs.insert .SEE k) t }) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFull s' ∧ s'.regs.get? ._PC = some t ∧ s'.mem = s.mem := by
  have hx : ∀ r : Register, r ≠ .SEE → r ≠ ._PC → r ≠ .__BranchTaken → r ≠ .Branchtypetaken →
      (takenRegs ((s0of s w).regs.insert .SEE k) t).get? r = (s0of s w).regs.get? r := fun r h1 h2 h3 h4 => by
    simp [takenRegs, Std.ExtDHashMap.get?_insert, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_gen hf hpc hlt hal hm heret hdec (bt := true) (pc1 := t) (b := .BranchType_DIR)
    (fun r _ _ h3 h4 h5 h6 _ => hx r h3 h4 h5 h6)
    (fun p hp => ⟨p, by rw [hx _ (by decide) (by decide) (by decide) (by decide)]; exact s0_ps hf ha hpc hlt hal hm heret p hp, pkeep_refl p⟩)
    (by simp [takenRegs, Std.ExtDHashMap.get?_insert]) (by simp [takenRegs, Std.ExtDHashMap.get?_insert])
    (by simp [takenRegs, Std.ExtDHashMap.get?_insert]) (by decide)
    (by rw [hx _ (by decide) (by decide) (by decide) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hf.btn)
    (by
      have := abs_ins (abs_ins (s0_abs ha w) .SEE (by decide) (by decide) k) .Branchtypetaken (by decide) (by decide) .BranchType_DIR
      exact abs_ins (abs_ins this ._PC (by decide) (by decide) t) .__BranchTaken (by decide) (by decide) true)
  exact ⟨s', h1, h2, h3, h4, h5⟩

/-- full step for a branch not taken (decode+execute writes only SEE) -/
theorem full_nt {k : Int}
    (hdec : __DecodeA64 pc.toNat w (s0of s w) = .ok () { s0of s w with regs := (s0of s w).regs.insert .SEE k }) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFull s' ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  obtain ⟨b0, hb0, hbr0⟩ := hf.bt
  have hx : ∀ r : Register, r ≠ .SEE → ((s0of s w).regs.insert .SEE k).get? r = (s0of s w).regs.get? r :=
    fun r h1 => by simp [Std.ExtDHashMap.get?_insert, Ne.symm h1]
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_gen hf hpc hlt hal hm heret hdec (bt := false) (pc1 := pc) (b := b0)
    (fun r _ _ h3 _ _ _ _ => hx r h3)
    (fun p hp => ⟨p, by rw [hx _ (by decide)]; exact s0_ps hf ha hpc hlt hal hm heret p hp, pkeep_refl p⟩)
    (by rw [hx _ (by decide)]; simp [s0of, preRegs, Std.ExtDHashMap.get?_insert])
    (by rw [hx _ (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hpc)
    (by rw [hx _ (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hb0) hbr0
    (by rw [hx _ (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hf.btn)
    (abs_ins (s0_abs ha w) .SEE (by decide) (by decide) k)
  exact ⟨s', h1, h2, h3, by simpa using h4, h5⟩

end

theorem s0_pc {s : St} {pc : BitVec 64} (hpc : s.regs.get? ._PC = some pc) (w : BitVec 32) (k : Int) :
    ((s0of s w).regs.insert .SEE k).get? ._PC = some pc := by
  simp only [Std.ExtDHashMap.get?_insert]; simp; exact (s0_get _ _ _ (by decide) (by decide)).trans hpc

theorem s0_pins' {s : St} (hf : ArmFull s) (w : BitVec 32) (k : Int) : Pins ((s0of s w).regs.insert .SEE k) :=
  (pins_insert _ rfl).2 (s0_pins hf w)

theorem s0_xk {s : St} {a : AState} (ha : Abs s a) (w : BitVec 32) (k : Int) {i : Nat} (hi : i < 31) :
    xget ((s0of s w).regs.insert .SEE k) i = some (a.x i) :=
  (xget_insert _ .SEE _ (xreg_ne' (by decide)) i).trans ((s0_x w i).trans (ha.x i hi))

theorem cbnz_eq_cbz : decode_cbnz_aarch64_instrs_branch_conditional_compare = decode_cbz_aarch64_instrs_branch_conditional_compare := rfl

theorem xset30 (m : Regs) (v : BitVec 64) : xset m 30 v = m.insert .R30 v := rfl

/-- the register number of a 5-bit field -/
theorem ofNat_toNat5 (r : BitVec 5) : BitVec.ofNat 5 r.toNat = r := by simp

section
variable {w : BitVec 32} {s : St} {a : AState} (hf : ArmFull s) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : pc.toNat < 2 ^ 29) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
include hf ha hpc hlt hal hm

/-- **`b`** (any 26-bit offset) as a full step: PC := PC + offset, nothing else visible changes -/
theorem full_b (hK : w &&& 0xFC000000#32 = 0x14000000#32) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFull s' ∧
      s'.regs.get? ._PC = some (pc + sign_extend (Sail.BitVec.slice w 0 26 +++ 0#2) 64) ∧ s'.mem = s.mem := by
  have hd := dec_bsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [b_exec (s0_pins' hf w _) _ (s0_pc hpc w _)] at hd
  exact full_tk hf ha hpc hlt hal hm (noteret hK 31 (by decide) (by decide) (by decide)) hd

/-- **`cbz xt`** (any 19-bit offset): taken iff `x t = 0` -/
theorem full_cbz (hK : w &&& 0xFF000000#32 = 0xB4000000#32) (ht : (Sail.BitVec.slice w 0 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFull s' ∧
      s'.regs.get? ._PC = some (if a.x (Sail.BitVec.slice w 0 5).toNat = 0
        then pc + sign_extend (Sail.BitVec.slice w 5 19 +++ 0#2) 64 else pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_cbzsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  have he := noteret hK 30 (by decide) (by decide) (by decide)
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5)] at hd
  by_cases hz : a.x (Sail.BitVec.slice w 0 5).toNat = 0
  · rw [cbz_taken (s0_pins' hf w _) _ ht _ (s0_pc hpc w _) (s0_xk ha w _ ht) hz] at hd
    rw [if_pos hz]; exact full_tk hf ha hpc hlt hal hm he hd
  · rw [cbz_not (s0_pins' hf w _) _ ht _ (s0_pc hpc w _) (s0_xk ha w _ ht) hz] at hd
    rw [if_neg hz]; exact full_nt hf ha hpc hlt hal hm he hd

/-- **`cbnz xt`** (any 19-bit offset): taken iff `x t ≠ 0` -/
theorem full_cbnz (hK : w &&& 0xFF000000#32 = 0xB5000000#32) (ht : (Sail.BitVec.slice w 0 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFull s' ∧
      s'.regs.get? ._PC = some (if a.x (Sail.BitVec.slice w 0 5).toNat = 0
        then pc + 4 else pc + sign_extend (Sail.BitVec.slice w 5 19 +++ 0#2) 64) ∧ s'.mem = s.mem := by
  have hd := dec_cbnzsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  have he := noteret hK 30 (by decide) (by decide) (by decide)
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), cbnz_eq_cbz] at hd
  by_cases hz : a.x (Sail.BitVec.slice w 0 5).toNat = 0
  · rw [cbnz_not (s0_pins' hf w _) _ ht _ (s0_pc hpc w _) (s0_xk ha w _ ht) hz] at hd
    rw [if_pos hz]; exact full_nt hf ha hpc hlt hal hm he hd
  · rw [cbnz_taken (s0_pins' hf w _) _ ht _ (s0_pc hpc w _) (s0_xk ha w _ ht) hz] at hd
    rw [if_neg hz]; exact full_tk hf ha hpc hlt hal hm he hd

/-- **`b.cond`** (any condition, any 19-bit offset): taken iff the condition holds on NZCV -/
theorem full_bc (hK : w &&& 0xFF000010#32 = 0x54000000#32) {p : ProcState} (hp : s.regs.get? .PSTATE = some p) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFull s' ∧
      s'.regs.get? ._PC = some (if condP (Sail.BitVec.slice w 0 4) p
        then pc + sign_extend (Sail.BitVec.slice w 5 19 +++ 0#2) 64 else pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_bcsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  have he := noteret hK 31 (by decide) (by decide) (by decide)
  have hp0 : ((s0of s w).regs.insert .SEE (69 : Int)).get? .PSTATE = some p := by
    simp only [Std.ExtDHashMap.get?_insert]; simp; exact (s0_get _ _ _ (by decide) (by decide)).trans hp
  by_cases hz : condP (Sail.BitVec.slice w 0 4) p = true
  · rw [bc_taken (s0_pins' hf w _) _ _ (s0_pc hpc w _) hp0 hz] at hd
    rw [if_pos hz]; exact full_tk hf ha hpc hlt hal hm he hd
  · rw [bc_not (s0_pins' hf w _) _ _ (s0_pc hpc w _) hp0 (by simpa using hz)] at hd
    rw [if_neg hz]; exact full_nt hf ha hpc hlt hal hm he hd

/-- **`movz xd, #imm16, lsl #16hw`** -/
theorem full_movz (hK : w &&& 0xFF800000#32 = 0xD2800000#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat
        ((Sail.BitVec.slice w 5 16).setWidth 64 <<< ((Sail.BitVec.slice w 21 2).toNat * 16))) ∧
      ArmFull s' ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_movzsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), movz_exec' hd31] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 26 (by decide) (by decide) (by decide)) hd31 hd

/-- **`movk xd, #imm16, lsl #16hw`** -/
theorem full_movk (hK : w &&& 0xFF800000#32 = 0xF2800000#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat
        (~~~(0xFFFF#64 <<< ((Sail.BitVec.slice w 21 2).toNat * 16)) &&& a.x (Sail.BitVec.slice w 0 5).toNat |||
          (Sail.BitVec.slice w 5 16).setWidth 64 <<< ((Sail.BitVec.slice w 21 2).toNat * 16))) ∧
      ArmFull s' ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_movksym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), movk_exec' hd31 _ _ (s0_xk ha w _ hd31)] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 29 (by decide) (by decide) (by decide)) hd31 hd

/-- **`add xd, xn, #imm12`** (`d n < 31`) -/
theorem full_addi (hK : w &&& 0xFFC00000#32 = 0x91000000#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 10 12).setWidth 64)) ∧
      ArmFull s' ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_addisym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    addi_exec hd31 hn31 (s0_xk ha w _ hn31)] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 30 (by decide) (by decide) (by decide)) hd31 hd

/-- **`sub xd, xn, #imm12`** (`d n < 31`) -/
theorem full_subi (hK : w &&& 0xFFC00000#32 = 0xD1000000#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (a.x (Sail.BitVec.slice w 5 5).toNat - (Sail.BitVec.slice w 10 12).setWidth 64)) ∧
      ArmFull s' ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_subisym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    subi_exec hd31 hn31 (s0_xk ha w _ hn31)] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 26 (by decide) (by decide) (by decide)) hd31 hd

/-- **`bl`** (any 26-bit offset): x30 := PC + 4, PC := PC + offset -/
theorem full_bl (hK : w &&& 0xFC000000#32 = 0x94000000#32) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' (a.setX 30 (pc + 4)) ∧ ArmFull s' ∧
      s'.regs.get? ._PC = some (pc + sign_extend (Sail.BitVec.slice w 0 26 +++ 0#2) 64) ∧ s'.mem = s.mem := by
  have hd := dec_blsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [bl_exec (s0_pins' hf w _) _ (s0_pc hpc w _)] at hd
  let t := pc + sign_extend (Sail.BitVec.slice w 0 26 +++ 0#2) 64
  have hx : ∀ r : Register, r ≠ .R30 → r ≠ .SEE → r ≠ ._PC → r ≠ .__BranchTaken → r ≠ .Branchtypetaken →
      ((((((s0of s w).regs.insert .SEE (68 : Int)).insert .R30 (pc + 4)).insert .Branchtypetaken .BranchType_DIRCALL).insert
        ._PC t).insert .__BranchTaken true).get? r = (s0of s w).regs.get? r := fun r h0 h1 h2 h3 h4 => by
    simp [Std.ExtDHashMap.get?_insert, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]
  have h30 : ∀ r : Register, (∀ i < 31, xreg i ≠ r) → r ≠ .R30 := fun r h e => h 30 (by decide) e.symm
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_gen hf hpc hlt hal hm (noteret hK 30 (by decide) (by decide) (by decide)) hd
    (bt := true) (pc1 := t) (b := .BranchType_DIRCALL)
    (fun r h1 _ h3 h4 h5 h6 _ => hx r (h30 r h1) h3 h4 h5 h6)
    (fun p hp => ⟨p, by rw [hx _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s0_ps hf ha hpc hlt hal hm (noteret hK 30 (by decide) (by decide) (by decide)) p hp, pkeep_refl p⟩)
    (by simp [Std.ExtDHashMap.get?_insert]) (by simp [t, Std.ExtDHashMap.get?_insert])
    (by simp [Std.ExtDHashMap.get?_insert]) (by decide)
    (by rw [hx _ (by decide) (by decide) (by decide) (by decide) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hf.btn)
    (by
      have := Abs.xset (abs_ins (s0_abs ha w) .SEE (by decide) (by decide) (68 : Int)) (d := 30) (by decide) (pc + 4)
      rw [xset30] at this
      have := abs_ins this .Branchtypetaken (by decide) (by decide) .BranchType_DIRCALL
      exact abs_ins (abs_ins this ._PC (by decide) (by decide) t) .__BranchTaken (by decide) (by decide) true)
  exact ⟨s', h1, h2, h3, h4, h5⟩

end

end ArmProof
