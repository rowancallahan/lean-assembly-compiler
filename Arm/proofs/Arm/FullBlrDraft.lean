/- DRAFT, not compiled on its own: `blr xn`, split out of FullBrLdur.lean (whose `br` and `ldur` parts compile).
`blr_exec`'s `ret_simp` leaves goals open on Lean 4.34.1. rv2arm does not emit `blr`. The theorems need
FullBrLdur's `section` variables (`hc : Pins s.regs`; `hf ha hpc hlt hal hm`) around them. -/

theorem dec_blrsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFFFFC1F#32 = 0xD63F0000#32) :
    __DecodeA64 pc w s = decode_blr_aarch64_instrs_branch_unconditional_register 0#5 (Sail.BitVec.slice w 5 5) 0#1 0#1 1#2 0#1
      { s with regs := s.regs.insert .SEE (90 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_BranchExcSys
  sfin hK h hs see
  all_goals rfl


theorem blr_exec {n : Nat} (hn : n < 31) {t : BitVec 64} (ht : xget s.regs n = some t) {pc : BitVec 64}
    (hpc : s.regs.get? ._PC = some pc) :
    decode_blr_aarch64_instrs_branch_unconditional_register 0#5 (BitVec.ofNat 5 n) 0#1 0#1 1#2 0#1 s =
      .ok () { s with regs := indRegs (s.regs.insert .R30 (pc + 4)) 2#2 .BranchType_INDCALL t } := by
  have hr := retcfg_of hc
  obtain ⟨p, hp, hrw, hel⟩ := hr.p
  obtain ⟨fi, hfi, hgcs, hbrbe, hspe, hpac, hvhe, ha64⟩ := hr.fi
  obtain ⟨scr, hscr⟩ := hr.scr
  idx n
  have hx : ∀ s' : St, X_set 30 64 (BitVec.addInt pc 4) s' = .ok () { s' with regs := s'.regs.insert .R30 (pc + 4) } := by
    intro s'; have := write_gpr_ok (s := s') (d := 30) (by decide) (pc + 4)
    simp only [X_set, set_R, addInt4] at *; simp (config := {decide := true}) [bind, pure, EStateM.bind, EStateM.pure, this]; rfl
  simp only [decode_blr_aarch64_instrs_branch_unconditional_register, indRegs]
  rcases hel with ⟨hel3, tcr, htcr, htbi⟩ | ⟨hel1, -⟩
  · ret_simp
  · obtain ⟨q, hq, h3, -⟩ := hc.ps; rw [hp] at hq; cases hq; rw [hel1] at h3; cases h3


/-- **`blr xn`** (`n < 31`): x30 := PC + 4, PC := (old) xn; `BTypeNext` (and PSTATE.BTYPE) become `0b10` -/
theorem full_blrB (hK : w &&& 0xFFFFFC1F#32 = 0xD63F0000#32) (hn : (Sail.BitVec.slice w 5 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' (a.setX 30 (pc + 4)) ∧ ArmFullB s' 2#2 ∧
      s'.regs.get? ._PC = some (a.x (Sail.BitVec.slice w 5 5).toNat) ∧ s'.mem = s.mem := by
  have hd := dec_blrsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  let t := a.x (Sail.BitVec.slice w 5 5).toNat
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    blr_exec (s0B_pins hf w _) hn (s0_xk ha w _ hn) (s0_pc hpc w _)] at hd
  have hx : ∀ r : Register, r ≠ .R30 → r ≠ .SEE → r ≠ ._PC → r ≠ .__BranchTaken → r ≠ .Branchtypetaken → r ≠ .BTypeNext →
      (indRegs (((s0of s w).regs.insert .SEE (90 : Int)).insert .R30 (pc + 4)) 2#2 .BranchType_INDCALL t).get? r =
        (s0of s w).regs.get? r := fun r h0 h1 h2 h3 h4 h5 => by
    simp [indRegs, Std.ExtDHashMap.get?_insert, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
  have h30 : ∀ r : Register, (∀ i < 31, xreg i ≠ r) → r ≠ .R30 := fun r h e => h 30 (by decide) e.symm
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_gen hf hpc hlt hal hm (noteret hK 23 (by decide) (by decide) (by decide)) hd
    (bt := true) (pc1 := t) (b := .BranchType_INDCALL)
    (fun r h1 _ h3 h4 h5 h6 h7 => hx r (h30 r h1) h3 h4 h5 h6 h7)
    (fun p hp => ⟨p, by rw [hx _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact (s0_get _ _ _ (by decide) (by decide)).trans hp, pkeep_refl p⟩)
    (by simp [indRegs, Std.ExtDHashMap.get?_insert]) (by simp [indRegs, Std.ExtDHashMap.get?_insert])
    (by simp [indRegs, Std.ExtDHashMap.get?_insert]) (by decide)
    (by simp [indRegs, Std.ExtDHashMap.get?_insert])
    (by
      have := Abs.xset (abs_ins (s0_abs ha w) .SEE (by decide) (by decide) (90 : Int)) (d := 30) (by decide) (pc + 4)
      rw [xset30] at this
      have := abs_ins this .BTypeNext (by decide) (by decide) 2#2
      have := abs_ins this .Branchtypetaken (by decide) (by decide) .BranchType_INDCALL
      exact abs_ins (abs_ins this ._PC (by decide) (by decide) t) .__BranchTaken (by decide) (by decide) true)
  exact ⟨s', h1, h2, h3, h4, h5⟩


/-- **`blr xn`** from `ArmFull` (ends in `ArmFullB _ 2`, not `ArmFull`) -/
theorem full_blr (hK : w &&& 0xFFFFFC1F#32 = 0xD63F0000#32) (hn : (Sail.BitVec.slice w 5 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' (a.setX 30 (pc + 4)) ∧ ArmFullB s' 2#2 ∧
      s'.regs.get? ._PC = some (a.x (Sail.BitVec.slice w 5 5).toNat) ∧ s'.mem = s.mem :=
  full_blrB hf ha hpc hlt hal hm hK hn


#print axioms ArmProof.dec_blrsym

#print axioms ArmProof.blr_exec

#print axioms ArmProof.full_blrB

#print axioms ArmProof.full_blr
