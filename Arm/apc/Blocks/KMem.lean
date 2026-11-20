/- J `ld`/`sd`/`lbu`/`sb` on DeepMind's machine. Premises beyond `validJ`: ArmBlock's `AccOK` (the cell is in `D`) and
`SafeX`'s `0 ≤ x[rs] + off`. Address forms: `[xn, #off]` (ld/sd: 8 | off < 32768; lbu/sb: off < 4096) or
`add/sub x16, xn, #|off|; … [x16]`. -/
import Blocks.KBr
import Blocks.MemLem
import Blocks.Mem
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Proven.Apc.Blocks
open CallProbe Proven.Arm ArmBlock

/-- one word that falls through and may store (the code is kept) -/
theorem seqM {C : List J} {b i : Nat} {j : J} {k : Nat} {t : Arm64.State} {A : Proven.Arm.AState} {m' : Arm64.Memory}
    (h : Mid C b i j k t) (hc : CodeOK C b m')
    (hS : ∃ t', Arm64.Step Pg t t' ∧ abs t' = A ∧ Post t t' (t.pc + 4) m') :
    ∃ t', Arm64.Step Pg t t' ∧ Mid C b i j (k + 1) t' ∧ abs t' = A ∧ t'.sp = t.sp ∧ t'.mem = m' := by
  obtain ⟨t', hs, ha, hp⟩ := hS
  refine ⟨t', hs, ⟨hp.run, ?_, by rw [hp.mem]; exact hc, h.hj⟩, ha, hp.sp, hp.mem⟩
  rw [hp.pc, h.pc]; apply BitVec.eq_of_toNat_eq; simp; omega

/-- the J effective address, as the A64 sum -/
theorem ea_pos (x : UInt64) (f : Int) (h0 : 0 ≤ f) (h1 : (x.toNat : Int) + f < 2 ^ 64) :
    x.toBitVec + BitVec.ofNat 64 f.toNat = ad (CallProbe.ea x f) := by
  apply BitVec.eq_of_toNat_eq; have := x.toNat_lt; simp [CallProbe.ea]; omega
theorem ea_neg (x : UInt64) (f : Int) (h0 : f < 0) (h1 : 0 ≤ (x.toNat : Int) + f) :
    x.toBitVec - BitVec.ofNat 64 f.natAbs = ad (CallProbe.ea x f) := by
  apply BitVec.eq_of_toNat_eq; have := x.toNat_lt; simp [CallProbe.ea, BitVec.toNat_sub]; omega

/-- `addr16 rs f`: x16 := J's address -/
theorem addr16_ok {t : Arm64.State} {s : St} {K} {rs : Nat} {f : Int} (hr : RegsOK (abs t) s K) (hl : live rs)
    (hf1 : -2048 ≤ f) (hf2 : f < 2048) (h0 : 0 ≤ ((s.x rs).toNat : Int) + f) (h1 : ((s.x rs).toNat : Int) + f < 2 ^ 64)
    (hA : At t (wd (addr16 rs f))) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX 16 (ad (CallProbe.ea (s.x rs) f)) ∧ Post t t' (t.pc + 4) t.mem := by
  have hs31 := hl.1
  have hx := hr.1 rs hl
  unfold addr16 at hA; split at hA
  · rename_i hneg; simp only [subi] at hA
    have := dm_subi (by mask32) (by fldt) (by fldt) hA
    rw [show ((wd (0xD1000000 + f.natAbs * 2 ^ 10 + pi rs * 2 ^ 5 + 16)).extractLsb' 0 5).toNat = 16 by fldt,
      show ((wd (0xD1000000 + f.natAbs * 2 ^ 10 + pi rs * 2 ^ 5 + 16)).extractLsb' 5 5).toNat = pi rs by fldt,
      show ((wd (0xD1000000 + f.natAbs * 2 ^ 10 + pi rs * 2 ^ 5 + 16)).extractLsb' 10 12).setWidth 64 =
        BitVec.ofNat 64 f.natAbs by immt, hx, ea_neg _ _ hneg h0] at this
    exact this
  · rename_i hpos; simp only [ArmBlock.addi] at hA
    have := dm_addi (by mask32) (by fldt) (by fldt) hA
    rw [show ((wd (0x91000000 + f.toNat * 2 ^ 10 + pi rs * 2 ^ 5 + 16)).extractLsb' 0 5).toNat = 16 by fldt,
      show ((wd (0x91000000 + f.toNat * 2 ^ 10 + pi rs * 2 ^ 5 + 16)).extractLsb' 5 5).toNat = pi rs by fldt,
      show ((wd (0x91000000 + f.toNat * 2 ^ 10 + pi rs * 2 ^ 5 + 16)).extractLsb' 10 12).setWidth 64 =
        BitVec.ofNat 64 f.toNat by immt, hx, ea_pos _ _ (by omega) h1] at this
    exact this

/-- `ldr xd, [xn, #f']` with `x[n] + f' = e`, a cell of `D` -/
theorem ldr_ok {t : Arm64.State} {D} {m : Nat → UInt64} {d n f' e : Nat} (hm : MemOK D m t.mem) (he : D e)
    (hd : d < 31) (hn : n < 31) (hf : f' % 8 = 0) (hf2 : f' < 32768) (hx : (abs t).x n + BitVec.ofNat 64 f' = ad e)
    (hA : At t (wd (ldr d n f'))) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX d (m e).toBitVec ∧ Post t t' (t.pc + 4) t.mem := by
  simp only [ldr] at hA
  have ea' : Blocks.ea t (wd (0xF9400000 + f' / 8 * 2 ^ 10 + n * 2 ^ 5 + d)) 3 = ad e := by
    unfold Blocks.ea
    rw [show ((wd (0xF9400000 + f' / 8 * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 5 5).toNat = n by fldt,
      show ((wd (0xF9400000 + f' / 8 * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 10 12).setWidth 64 <<< 3 =
        BitVec.ofNat 64 f' by apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]; omega, hx]
  obtain ⟨hr, hv⟩ := read64_cell hm he
  have := dm_ldr (by mask32) (by fldt) (by fldt) (by rw [ea']; exact hr) hA
  rwa [ea', hv, show ((wd (0xF9400000 + f' / 8 * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 0 5).toNat = d by fldt] at this

theorem wr_m (s : St) (r : Nat) (v : UInt64) : (wr s r v).m = s.m := by unfold wr; split <;> rfl
theorem wr_wk (s : St) (r : Nat) (v : UInt64) : (wr s r v).wk = s.wk := by unfold wr; split <;> rfl
theorem wr_x0 (s : St) (r : Nat) (v : UInt64) (h : s.x 0 = 0) : (wr s r v).x 0 = 0 := by
  unfold wr; split
  · exact h
  · rename_i h0; simp [CallProbe.upd, Ne.symm h0, h]

/-- finish a block that wrote J register `rd` (and maybe scratch), memory unchanged -/
theorem fin_wr {C : List J} {D K} {pc : Nat} {s : St} {t t' : Arm64.State} {j : J} {rd : Nat} {V : UInt64}
    {A : Proven.Arm.AState} (hR : RelD C D K (pc, s) t) (hl : live rd) (m' : Mid C s.b pc j 4 t') (hA : RegsOK A s K)
    (a' : abs t' = A.setX (pi rd) V.toBitVec) (p' : t'.sp = t.sp) (q' : t'.mem = t.mem) :
    RelD C D K (pc + 1, wr s rd V) t' :=
  relD_next hR m' (a' ▸ regs_wr hA hl _) p' (by rw [q', wr_m]; exact hR.mem) (wr_b _ _ _) (wr_x0 _ _ _ hR.zero)
    (wr_w _ _ _)

theorem blk_ld {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {rd rs : Nat} {f : Int}
    (hj : C[pc]? = some (.ld rd rs f)) (hv : validJ C.length pc (.ld rd rs f)) (hacc : D (CallProbe.ea (s.x rs) f))
    (hnw : 0 ≤ ((s.x rs).toNat : Int) + f) (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (pc + 1, wr s rd (s.m (CallProbe.ea (s.x rs) f)))) := by
  obtain ⟨hs0, hrs, hrd, hf1, hf2⟩ := hv
  have hm := hR.mid hj
  have hsl := live_of_rd hrs hs0
  have hmem : MemOK D s.m t.mem := hR.mem
  obtain ⟨he8, hel, -⟩ := hmem _ hacc
  have hup : ((s.x rs).toNat : Int) + f < 2 ^ 64 := by unfold CallProbe.ea at hel; omega
  by_cases h0 : rd = 0
  · subst h0
    have hb : blockJ (.ld 0 rs f) = [PAD, PAD, PAD, PAD] := by simp [blockJ, body, pad4]
    refine (pads 4 0 rfl hm (pads4 hb)).mono fun t' ⟨m', a', p', q'⟩ => ?_
    simp only [wr, ite_true]
    exact relD_next hR m' (a' ▸ hR.regs) p' (q' ▸ hR.mem) rfl hR.zero rfl
  have hl := live_of_wr hrd h0
  by_cases hdir : f % 8 = 0 ∧ 0 ≤ f ∧ f < 32768
  · have hb : blockJ (.ld rd rs f) = [ldr (pi rd) (pi rs) f.toNat, PAD, PAD, PAD] := by
      simp [blockJ, body, pad4, h0, hdir]
    refine (word_pads (A := (abs t).setX (pi rd) (s.m (CallProbe.ea (s.x rs) f)).toBitVec) hm (by omega) (fun hA => ?_)
      (pads3 hb)).mono fun t' ⟨m', a', p', q'⟩ => fin_wr hR hl m' hR.regs a' p' q'
    rw [bw_of hb] at hA; simp only [List.getD_cons_zero] at hA
    exact ldr_ok hmem hacc hl.1 hsl.1 (by omega) (by omega)
      (by rw [hR.regs.1 rs hsl]; exact ea_pos _ _ hdir.2.1 hup) hA
  · have hb : blockJ (.ld rd rs f) = [addr16 rs f, ldr (pi rd) 16 0, PAD, PAD] := by
      simp [blockJ, body, pad4, h0, hdir]
    have hA0 := hm.at (by omega); rw [bw_of hb] at hA0; simp only [List.getD_cons_zero] at hA0
    obtain ⟨t1, s1, m1, a1, p1, q1⟩ := seq1 hm (by omega) (addr16_ok hR.regs hsl hf1 hf2 hnw hup hA0)
    refine Reach.cons s1 ((word_pads (A := ((abs t).setX 16 (ad (CallProbe.ea (s.x rs) f))).setX (pi rd)
      (s.m (CallProbe.ea (s.x rs) f)).toBitVec) m1 (by omega) (fun hA => ?_) (pads2 hb)).mono
      fun t' ⟨m', a', p', q'⟩ => fin_wr hR hl m' (regs_scr hR.regs (.inl rfl) _) a' (p'.trans p1) (q'.trans q1))
    rw [bw_of hb] at hA; simp only [List.getD_cons_succ, List.getD_cons_zero] at hA
    have := ldr_ok (q1 ▸ hmem) hacc hl.1 (by decide) (by decide) (by decide)
      (by rw [a1, setX_eq _ (by decide), BitVec.add_zero]) hA
    rwa [a1] at this

/-- `str xd, [xn, #f']` with `x[n] + f' = e ∈ D` -/
theorem str_ok {t : Arm64.State} {D} {m : Nat → UInt64} {d n f' e : Nat} {V : UInt64} (hm : MemOK D m t.mem) (he : D e)
    (hd : d < 31) (hn : n < 31) (hf : f' % 8 = 0) (hf2 : f' < 32768) (hx : (abs t).x n + BitVec.ofNat 64 f' = ad e)
    (hv : (abs t).x d = V.toBitVec) (hA : At t (wd (str d n f'))) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = abs t ∧ Post t t' (t.pc + 4) (t.mem.write64 (ad e) V.toBitVec) := by
  simp only [str] at hA
  have ea' : Blocks.ea t (wd (0xF9000000 + f' / 8 * 2 ^ 10 + n * 2 ^ 5 + d)) 3 = ad e := by
    unfold Blocks.ea
    rw [show ((wd (0xF9000000 + f' / 8 * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 5 5).toNat = n by fldt,
      show ((wd (0xF9000000 + f' / 8 * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 10 12).setWidth 64 <<< 3 =
        BitVec.ofNat 64 f' by apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]; omega, hx]
  have hw := canWrite_of t.mem 8 _ (canWrite_cell hm he)
  have := dm_str (by mask32) (by fldt) (by fldt) (by rw [ea']; exact hw) hA
  rwa [ea', show ((wd (0xF9000000 + f' / 8 * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 0 5).toNat = d by fldt, hv] at this

/-- the store word at `k`, then PADs -/
theorem sd_tail {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {j : J} {k d n f' e : Nat} {V : UInt64}
    {t1 : Arm64.State} {A1 : Proven.Arm.AState} (hR : RelD C D K (pc, s) t) (hk : k < 4) (m1 : Mid C s.b pc j k t1)
    (a1 : abs t1 = A1) (r1 : RegsOK A1 s K) (he : D e) (hd : d < 31) (hn : n < 31) (hf : f' % 8 = 0) (hf2 : f' < 32768)
    (hx : A1.x n + BitVec.ofNat 64 f' = ad e) (hv : A1.x d = V.toBitVec) (w0 : bw j k = wd (str d n f'))
    (hp : PadsFrom j (k + 1)) (p1 : t1.sp = t.sp) (q1 : t1.mem = t.mem) :
    Reach t1 (RelD C D K (pc + 1, { s with m := CallProbe.upd s.m e V })) := by
  have hmem : MemOK D s.m t1.mem := q1 ▸ hR.mem
  have hA := m1.at hk; rw [w0] at hA
  have hc : CodeOK C s.b (t1.mem.write64 (ad e) V.toBitVec) :=
    w64_keep (CodeOK C s.b) (fun m a v hw h => h.w8 hw v) _ _ _ (canWrite_cell hmem he) m1.code
  obtain ⟨t2, s2, m2, a2, p2, q2⟩ := seqM m1 hc (str_ok hmem he hd hn hf hf2 (a1 ▸ hx) (a1 ▸ hv) hA)
  refine Reach.cons s2 ((pads (3 - k) (k + 1) (by omega) m2 hp).mono fun t' ⟨m', a', p', q'⟩ => ?_)
  refine relD_next hR m' (by rw [a', a2, a1]; exact r1) (p'.trans (p2.trans p1)) ?_ rfl hR.zero rfl
  rw [q', q2]; exact memOK_w64 hmem he V

theorem dat_lt {r : Nat} (hr : wrOK r) : dat r < 31 := by
  unfold dat; split
  · decide
  · rename_i h0; exact (live_of_wr hr h0).1

theorem blk_sd {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {r2 r1 : Nat} {f : Int}
    (hj : C[pc]? = some (.sd r2 r1 f)) (hv : validJ C.length pc (.sd r2 r1 f)) (hacc : D (CallProbe.ea (s.x r1) f))
    (hnw : 0 ≤ ((s.x r1).toNat : Int) + f) (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (pc + 1, { s with m := CallProbe.upd s.m (CallProbe.ea (s.x r1) f) (s.x r2) })) := by
  obtain ⟨hs0, hrs, hrd, hf1, hf2⟩ := hv
  have hm := hR.mid hj
  have hz : s.x 0 = 0 := hR.zero
  have hsl := live_of_rd hrs hs0
  have hmem : MemOK D s.m t.mem := hR.mem
  obtain ⟨he8, hel, -⟩ := hmem _ hacc
  have hup : ((s.x r1).toNat : Int) + f < 2 ^ 64 := by unfold CallProbe.ea at hel; omega
  have hdl := dat_lt hrd
  have ea_d : ∀ (hdir : f % 8 = 0 ∧ 0 ≤ f ∧ f < 32768), (s.x r1).toBitVec + BitVec.ofNat 64 f.toNat =
      ad (CallProbe.ea (s.x r1) f) := fun hdir => ea_pos _ _ hdir.2.1 hup
  have x1 := hR.regs.1 r1 hsl
  have p16 := (pi_rng hsl).1; have p17 := (pi_rng hsl).2.1
  by_cases h0 : r2 = 0
  · subst h0
    have hA0 := hm.at (by omega)
    by_cases hdir : f % 8 = 0 ∧ 0 ≤ f ∧ f < 32768
    · have hb : blockJ (.sd 0 r1 f) = [movz 17 0, str 17 (pi r1) f.toNat, PAD, PAD] := by
        simp [blockJ, body, pad4, zpre, dat, hdir]
      rw [bw_of hb] at hA0
      obtain ⟨t1, s1, m1, a1, p1, q1⟩ := seq1 hm (by omega) (movz_ok (by decide) (by decide) hA0)
      exact Reach.cons s1 (sd_tail hR (k := 1) (d := 17) (n := pi r1) (f' := f.toNat) (e := CallProbe.ea (s.x r1) f) (V := s.x 0) (by omega) m1 a1
        (regs_scr hR.regs (.inr rfl) _) hacc (by decide) hsl.1
        (by omega) (by omega) (by rw [setX_ne _ p17, x1]; exact ea_d hdir)
        (by rw [setX_eq _ (by decide), hz]; rfl) (by rw [bw_of hb]; rfl) (pads2 hb) p1 q1)
    · have hb : blockJ (.sd 0 r1 f) = [movz 17 0, addr16 r1 f, str 17 16 0, PAD] := by
        simp [blockJ, body, pad4, zpre, dat, hdir]
      rw [bw_of hb] at hA0
      obtain ⟨t1, s1, m1, a1, p1, q1⟩ := seq1 hm (by omega) (movz_ok (by decide) (by decide) hA0)
      have r1' := regs_scr hR.regs (.inr rfl) (BitVec.ofNat 64 0)
      have hA1 := m1.at (by omega); rw [bw_of hb] at hA1
      obtain ⟨t2, s2, m2, a2, p2, q2⟩ := seq1 m1 (by omega) (addr16_ok (a1 ▸ r1') hsl hf1 hf2 hnw hup hA1)
      exact Reach.cons s1 (Reach.cons s2 (sd_tail hR (k := 2) (d := 17) (n := 16) (f' := 0) (e := CallProbe.ea (s.x r1) f) (V := s.x 0) (by omega) m2 a2 (regs_scr (a1 ▸ r1') (.inl rfl) _) hacc
        (by decide) (by decide) (by omega) (by omega) (by rw [setX_eq _ (by decide), BitVec.add_zero])
        (by rw [setX_ne _ (by decide), a1, setX_eq _ (by decide), hz]; rfl) (by rw [bw_of hb]; rfl) (pads1 hb)
        (p2.trans p1) (q2.trans q1)))
  · have hl2 := live_of_wr hrd h0
    have x2 := hR.regs.1 r2 hl2
    by_cases hdir : f % 8 = 0 ∧ 0 ≤ f ∧ f < 32768
    · have hb : blockJ (.sd r2 r1 f) = [str (pi r2) (pi r1) f.toNat, PAD, PAD, PAD] := by
        simp [blockJ, body, pad4, zpre, dat, hdir, h0]
      exact sd_tail hR (k := 0) (d := pi r2) (n := pi r1) (f' := f.toNat) (e := CallProbe.ea (s.x r1) f) (V := s.x r2) (by omega) hm rfl hR.regs hacc hl2.1 hsl.1 (by omega) (by omega)
        (by rw [x1]; exact ea_d hdir) x2 (by rw [bw_of hb]; rfl) (pads3 hb) rfl rfl
    · have hb : blockJ (.sd r2 r1 f) = [addr16 r1 f, str (pi r2) 16 0, PAD, PAD] := by
        simp [blockJ, body, pad4, zpre, dat, hdir, h0]
      have hA0 := hm.at (by omega); rw [bw_of hb] at hA0
      obtain ⟨t1, s1, m1, a1, p1, q1⟩ := seq1 hm (by omega) (addr16_ok hR.regs hsl hf1 hf2 hnw hup hA0)
      exact Reach.cons s1 (sd_tail hR (k := 1) (d := pi r2) (n := 16) (f' := 0) (e := CallProbe.ea (s.x r1) f) (V := s.x r2) (by omega) m1 a1
        (regs_scr hR.regs (.inl rfl) _) hacc hl2.1 (by decide)
        (by omega) (by omega) (by rw [setX_eq _ (by decide), BitVec.add_zero]) (by rw [setX_ne _ (pi_rng hl2).1, x2])
        (by rw [bw_of hb]; rfl) (pads2 hb) p1 q1)

end Proven.Apc.Blocks
