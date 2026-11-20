/- DRAFT, not compiled on its own: `cset xd, c`, split out of FullCmp.lean (whose `cmp` part compiles).
`cset_exec`'s `exec_simp` leaves the `undefined_bitvector` match open on Lean 4.34.1. rv2arm does not emit `cset`.
The theorems need FullCmp's `section` variables around them. -/

theorem dec_csetsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFFF0FE0#32 = 0x9A9F07E0#32) :
    __DecodeA64 pc w s = decode_csinc_aarch64_instrs_integer_conditional_select (Sail.BitVec.slice w 0 5) 31#5 1#1
      (Sail.BitVec.slice w 12 4) 31#5 0#1 1#1
      { s with regs := s.regs.insert .SEE (188 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcReg
  sfin hK h hs see
  all_goals rfl


/-- `cset xd, !c`: `csinc xd, xzr, xzr, c` writes `0` if `c` holds on NZCV, else `1` -/
theorem cset_exec (c : BitVec 4) (hd : d < 31) (hp : s.regs.get? .PSTATE = some p)
    (hspe : s.regs.get? .SPESampleInFlight = some false) :
    decode_csinc_aarch64_instrs_integer_conditional_select (BitVec.ofNat 5 d) 31#5 1#1 c 31#5 0#1 1#1 s
      = .ok () { s with regs := xset s.regs d (if condP c p then 0 else 1) } := by
  idx d
  have hc := cond_ok (s := s) c hp
  dsimp only [decode_csinc_aarch64_instrs_integer_conditional_select]; dsimp
  simp only [execute_aarch64_instrs_integer_conditional_select, hc, bind, pure, EStateM.bind, EStateM.pure]
  split <;> exec_simp

/-- **`cset xd, !c`** (`csinc xd, xzr, xzr, c`, `d < 31`, any 4-bit condition field `c`) -/
theorem full_cset (hK : w &&& 0xFFFF0FE0#32 = 0x9A9F07E0#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (if a.cond (Sail.BitVec.slice w 12 4) then 0 else 1)) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  obtain ⟨p, hp, hN, hZ, hC, hV⟩ := ha.p
  have hd := dec_csetsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  have hp0 : ((s0of s w).regs.insert .SEE (188 : Int)).get? .PSTATE = some p := by
    simp only [Std.ExtDHashMap.get?_insert]; simp; exact (s0_get _ _ _ (by decide) (by decide)).trans hp
  have hspe : ((s0of s w).regs.insert .SEE (188 : Int)).get? .SPESampleInFlight = some false := by
    simp only [Std.ExtDHashMap.get?_insert]; simp; exact (s0_get _ _ _ (by decide) (by decide)).trans hf.pins.spe
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), cset_exec _ hd31 hp0 hspe, condP_abs _ hN hZ hC hV] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 30 (by decide) (by decide) (by decide)) hd31 hd
