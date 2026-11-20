/- J branches on DeepMind's machine: `beq`/`bne`/`bltu`/`bgeu` (cbz, b, or `subs x16; b.cond`), `jal` (b / PADs + bl),
`jalr x0, rs` (br). Branch arithmetic: `ofs19`, `ofs26`. -/
import Blocks.KShift
import Blocks.Branch
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Proven.Apc.Blocks
open CallProbe Proven.Arm ArmBlock

theorem ad_add (A n : Nat) (h : A + n < 2 ^ 64) : ad A + BitVec.ofNat 64 n = ad (A + n) := by
  apply BitVec.eq_of_toNat_eq; simp
theorem ad_sub (A n : Nat) (h : n ≤ A) (h' : A < 2 ^ 64) (hn : 0 < n) :
    ad A + BitVec.ofNat 64 (2 ^ 64 - n) = ad (A - n) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem ofsW (w : Nat) (hw1 : 1 ≤ w) (hw2 : w ≤ 26) (f : Int) (hm : mo f w = if 0 ≤ f then f.toNat else 2 ^ w - f.natAbs)
    (h1 : -2 ^ (w - 1) ≤ f) (h2 : f < 2 ^ (w - 1)) (A : Nat) (hA : 0 ≤ (A : Int) + 4 * f)
    (hA2 : (A : Int) + 4 * f < 2 ^ 64) (hAl : A < 2 ^ 64) :
    ad A + ((BitVec.ofNat w (mo f w)).signExtend 64 <<< 2) = ad ((A : Int) + 4 * f).toNat := by
  have p1 : (2 : Int) ^ (w - 1) = ((2 ^ (w - 1) : Nat) : Int) := by push_cast; rfl
  rw [hm]; split
  · rename_i h0
    rw [off_fwd (w := w) (by omega) (by omega) (show f.toNat < 2 ^ (w - 1) by omega), ad_add _ _ (by omega)]
    congr 1; omega
  · rename_i h0
    have hp : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    rw [off_back (w := w) (by omega) (by omega) (show 0 < f.natAbs by omega) (show f.natAbs ≤ 2 ^ (w - 1) by omega),
      ad_sub _ _ (by omega) hAl (by omega)]
    congr 1; omega

theorem ofs19 (f : Int) (h1 : -2 ^ 18 ≤ f) (h2 : f < 2 ^ 18) (A : Nat) (hA : 0 ≤ (A : Int) + 4 * f)
    (hA2 : (A : Int) + 4 * f < 2 ^ 64) (hAl : A < 2 ^ 64) :
    ad A + ((BitVec.ofNat 19 (mo f 19)).signExtend 64 <<< 2) = ad ((A : Int) + 4 * f).toNat :=
  ofsW 19 (by decide) (by decide) f (by unfold mo; split <;> simp only [Nat.reducePow] <;> omega) h1 h2 A hA hA2 hAl
theorem ofs26 (f : Int) (h1 : -2 ^ 25 ≤ f) (h2 : f < 2 ^ 25) (A : Nat) (hA : 0 ≤ (A : Int) + 4 * f)
    (hA2 : (A : Int) + 4 * f < 2 ^ 64) (hAl : A < 2 ^ 64) :
    ad A + ((BitVec.ofNat 26 (mo f 26)).signExtend 64 <<< 2) = ad ((A : Int) + 4 * f).toNat :=
  ofsW 26 (by decide) (by decide) f (by unfold mo; split <;> simp only [Nat.reducePow] <;> omega) h1 h2 A hA hA2 hAl

/-- `RelD` after a jump to block `npc` (J state unchanged) -/
theorem relD_jump {C : List J} {D K} {pc npc : Nat} {s : St} {t t' : Arm64.State} (h : RelD C D K (pc, s) t)
    (hrun : t'.status = .Running) (hpc : t'.pc = ad (s.b + 16 * npc)) (hm : t'.mem = t.mem) (hr : RegsOK (abs t') s K)
    (hsp : t'.sp = t.sp) : RelD C D K (npc, s) t' :=
  ⟨hrun, hpc, hm ▸ h.code, hr, h.zero, hsp.trans h.sp, h.wk, hm ▸ h.mem⟩

/-- J's compare for the condition codes rv2arm uses: 0 eq, 1 ne, 2 hs (bgeu), 3 lo (bltu) -/
def jc (c : Nat) (x y : UInt64) : Bool :=
  match c with
  | 0 => x == y | 1 => x != y | 2 => decide (y.toNat ≤ x.toNat) | _ => decide (x.toNat < y.toNat)

theorem cond_sub (A : AState) (c : Nat) (hc : c < 4) (x y : UInt64) (v : BitVec 64) :
    ((A.setSub x.toBitVec y.toBitVec).setX 16 v).cond (BitVec.ofNat 4 c) = jc c x y := by
  have hxy : (x.toBitVec - y.toBitVec = 0#64) ↔ x = y := by
    constructor
    · intro h; apply UInt64.toBitVec_inj.mp
      rw [← BitVec.sub_add_cancel x.toBitVec y.toBitVec, h, BitVec.zero_add]
    · intro h; rw [h, BitVec.sub_self]
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp [AState.cond, AState.setX, AState.setSub, jc, hxy, UInt64.lt_iff_toNat_lt]
  · by_cases e : x = y <;> simp [e]
  · by_cases e : x = y <;> simp [e]
  · by_cases e : y.toNat ≤ x.toNat <;> simp [e] <;> omega

theorem regs_sub {A : AState} {s : St} {K} (h : RegsOK A s K) (x y : BitVec 64) : RegsOK (A.setSub x y) s K := h

theorem mo_lt (f : Int) (k : Nat) : mo f k < 2 ^ k := by
  unfold mo
  have hp := Nat.pow_pos (n := k) (by decide : 0 < 2)
  have h1 := Int.emod_lt_of_pos f (show (0 : Int) < ((2 ^ k : Nat) : Int) by omega)
  have h2 := Int.emod_nonneg f (show ((2 ^ k : Nat) : Int) ≠ 0 by omega)
  omega

/-- `subs x16, xn, xm; b.cond` at words `k`, `k + 1` of the block (then PADs) -/
theorem cmp_tail {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {j : J} {k c n m a b : Nat} {o : Int}
    {t1 : Arm64.State} {A1 : AState} (hR : RelD C D K (pc, s) t) (hk : k ≤ 1) (m1 : Mid C s.b pc j k t1)
    (a1 : abs t1 = A1) (r1 : RegsOK A1 s K) (xn : A1.x n = (s.x a).toBitVec) (xm : A1.x m = (s.x b).toBitVec)
    (hn : n < 31) (hm : m < 31) (hc : c < 4) (w0 : bw j k = wd (subsR n m)) (w1 : bw j (k + 1) = wd (bc c (4 * o - (k + 1))))
    (hp : PadsFrom j (k + 2)) (ho1 : -65535 ≤ o) (ho2 : o ≤ 65535) (hpo : 0 ≤ (pc : Int) + o) (hpo2 : (pc : Int) + o < C.length)
    (p1 : t1.sp = t.sp) (q1 : t1.mem = t.mem) :
    Reach t1 (RelD C D K (if jc c (s.x a) (s.x b) then ((pc : Int) + o).toNat else pc + 1, s)) := by
  have hA0 := m1.at (by omega); rw [w0] at hA0
  obtain ⟨ed, en, em⟩ := rr_f (c := 0xEB000000) (d := 16) (n := n) (m := m) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have h0 := dm_subsR (w := wd (subsR n m)) (by simp only [subsR]; mask32) (by simp only [subsR]; omega)
    (by simp only [subsR]; omega) (by simp only [subsR]; omega) hA0
  simp only [subsR] at h0 ed en em; rw [ed, en, em, a1, xn, xm] at h0
  obtain ⟨t2, s2, m2, a2, p2, q2⟩ := seq1 m1 (by omega) h0
  have hA1 := m2.at (by omega); rw [w1] at hA1; simp only [bc] at hA1
  have hmo := mo_lt (4 * o - (k + 1)) 19
  have h1 := dm_bc (by mask32) hA1
  rw [show (wd (0x54000000 + mo (4 * o - (k + 1)) 19 * 2 ^ 5 + c)).extractLsb' 0 4 = BitVec.ofNat 4 c by
      apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega,
    show (wd (0x54000000 + mo (4 * o - (k + 1)) 19 * 2 ^ 5 + c)).extractLsb' 5 19 = BitVec.ofNat 19 (mo (4 * o - (k + 1)) 19) by
      apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega,
    a2, cond_sub _ c hc] at h1
  obtain ⟨t3, s3, a3, P3⟩ := h1
  have hlt := m2.lt (by omega)
  have hcl : s.b + 16 * C.length < 2 ^ 64 := hR.code.lt
  refine Reach.cons s2 (Reach.cons s3 ?_)
  have r3 : RegsOK (abs t3) s K := by rw [a3]; exact regs_scr (regs_sub r1 _ _) (.inl rfl) _
  by_cases hj : jc c (s.x a) (s.x b) = true
  · simp only [hj, ite_true] at P3 ⊢
    refine Reach.done (relD_jump hR P3.run ?_ (P3.mem.trans (q2.trans q1)) r3 (P3.sp.trans (p2.trans p1)))
    rw [P3.pc, m2.pc, ofs19 _ (by omega) (by omega) _ (by omega) (by omega) hlt]
    congr 1; omega
  · simp only [hj, ite_false, Bool.false_eq_true] at P3 ⊢
    have m3 : Mid C s.b pc j (k + 2) t3 := ⟨P3.run, by rw [P3.pc, m2.pc]; apply BitVec.eq_of_toNat_eq; simp; omega,
      P3.mem ▸ m2.code, m2.hj⟩
    refine (pads (2 - k) (k + 2) (by omega) m3 hp).mono fun t' ⟨m', a', p', q'⟩ => ?_
    exact relD_next hR m' (by rw [a', a3]; exact regs_scr (regs_sub r1 _ _) (.inl rfl) _) (p'.trans (P3.sp.trans (p2.trans p1)))
      (by rw [q', P3.mem, q2, q1]; exact hR.mem) rfl hR.zero rfl

/-- `compBr c a b o` (with the x17 prefix when an operand is x0) -/
theorem blk_cmp {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {j : J} {c a b : Nat} {o : Int}
    (hj : C[pc]? = some j) (hb : blockJ j = pad4 (compBr c a b o)) (hc : c < 4) (hra : rdOK a) (hrb : rdOK b)
    (ho1 : -65535 ≤ o) (ho2 : o ≤ 65535) (hpo : 0 ≤ (pc : Int) + o) (hpo2 : (pc : Int) + o < C.length)
    (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (if jc c (s.x a) (s.x b) then ((pc : Int) + o).toNat else pc + 1, s)) := by
  have hm := hR.mid hj
  have hz : s.x 0 = 0 := hR.zero
  by_cases hZ : a = 0 ∨ b = 0
  · have hb2 : blockJ j = [movz 17 0, subsR (opR a) (opR b), bc c (4 * o - 2), PAD] := by
      rw [hb]; simp [pad4, compBr, hZ]
    have hA0 := hm.at (by omega); rw [bw_of hb2] at hA0
    obtain ⟨t1, s1, m1, a1, p1, q1⟩ := seq1 hm (by omega) (movz_ok (by decide) (by decide) hA0)
    exact Reach.cons s1 (cmp_tail hR (k := 1) (by omega) m1 a1 (regs_scr hR.regs (.inr rfl) _) (opv hR.regs hz hra)
      (opv hR.regs hz hrb) (opR_lt hra) (opR_lt hrb) hc (by rw [bw_of hb2]; rfl)
      (by rw [bw_of hb2]; simp) (pads1 hb2) ho1 ho2 hpo hpo2 p1 q1)
  · simp at hZ
    have hb2 : blockJ j = [subsR (pi a) (pi b), bc c (4 * o - 1), PAD, PAD] := by
      rw [hb]; simp [pad4, compBr, hZ]
    have hla := live_of_rd hra hZ.1; have hlb := live_of_rd hrb hZ.2
    exact cmp_tail hR (k := 0) (by omega) hm rfl hR.regs (hR.regs.1 a hla) (hR.regs.1 b hlb) hla.1 hlb.1 hc
      (by rw [bw_of hb2]; rfl) (by rw [bw_of hb2]; simp) (pads2 hb2) ho1 ho2 hpo hpo2 rfl rfl

/-- `b (4 o)` then PADs: always to block `pc + o` -/
theorem b_blk {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {j : J} {o : Int}
    (hj : C[pc]? = some j) (hb : blockJ j = [bB (4 * o), PAD, PAD, PAD]) (ho1 : -2 ^ 23 ≤ o) (ho2 : o < 2 ^ 23)
    (hpo : 0 ≤ (pc : Int) + o) (hpo2 : (pc : Int) + o < C.length) (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (((pc : Int) + o).toNat, s)) := by
  have hm := hR.mid hj
  have hA := hm.at (by omega); rw [bw_of hb] at hA; simp only [List.getD_cons_zero, bB] at hA
  have hmo := mo_lt (4 * o) 26
  obtain ⟨t1, s1, a1, P1⟩ := dm_b (by mask32) hA
  rw [show (wd (0x14000000 + mo (4 * o) 26)).extractLsb' 0 26 = BitVec.ofNat 26 (mo (4 * o) 26) by
    apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega] at P1
  have hlt := hm.lt (by omega)
  have hcl : s.b + 16 * C.length < 2 ^ 64 := hR.code.lt
  refine Reach.cons s1 (Reach.done (relD_jump hR P1.run ?_ P1.mem (a1 ▸ hR.regs) P1.sp))
  rw [P1.pc, hm.pc, ofs26 _ (by omega) (by omega) _ (by omega) (by omega) hlt]
  congr 1; omega

/-- `cbz x[π q], (4 o)` then PADs -/
theorem cbz_blk {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {j : J} {q : Nat} {o : Int}
    (hj : C[pc]? = some j) (hb : blockJ j = [cbz (pi q) (4 * o), PAD, PAD, PAD]) (hq : live q) (ho1 : -65535 ≤ o)
    (ho2 : o ≤ 65535) (hpo : 0 ≤ (pc : Int) + o) (hpo2 : (pc : Int) + o < C.length) (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (if s.x q = 0 then ((pc : Int) + o).toNat else pc + 1, s)) := by
  have hm := hR.mid hj
  have hA := hm.at (by omega); rw [bw_of hb] at hA; simp only [List.getD_cons_zero, cbz] at hA
  have hmo := mo_lt (4 * o) 19
  have hq31 := hq.1
  obtain ⟨t1, s1, a1, P1⟩ := dm_cbz (by mask32) (by fldt) hA
  rw [show (wd (0xB4000000 + mo (4 * o) 19 * 2 ^ 5 + pi q)).extractLsb' 5 19 = BitVec.ofNat 19 (mo (4 * o) 19) by
      apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega,
    show ((wd (0xB4000000 + mo (4 * o) 19 * 2 ^ 5 + pi q)).extractLsb' 0 5).toNat = pi q by fldt,
    hR.regs.1 q hq] at P1
  have hlt := hm.lt (by omega)
  have hcl : s.b + 16 * C.length < 2 ^ 64 := hR.code.lt
  have e0 : ((s.x q).toBitVec = 0) ↔ s.x q = 0 := by
    constructor
    · intro h; exact UInt64.toBitVec_inj.mp h
    · intro h; rw [h]; rfl
  refine Reach.cons s1 ?_
  by_cases hz : s.x q = 0
  · simp only [hz, ite_true, show (UInt64.toBitVec 0 = 0) from rfl] at P1 ⊢
    refine Reach.done (relD_jump hR P1.run ?_ P1.mem (a1 ▸ hR.regs) P1.sp)
    rw [P1.pc, hm.pc, ofs19 _ (by omega) (by omega) _ (by omega) (by omega) hlt]
    congr 1; omega
  · simp only [hz, ite_false, show ¬ (s.x q).toBitVec = 0 from fun h => hz (e0.mp h)] at P1 ⊢
    have m1 : Mid C s.b pc j 1 t1 := ⟨P1.run, by rw [P1.pc, hm.pc]; apply BitVec.eq_of_toNat_eq; simp,
      P1.mem ▸ hm.code, hm.hj⟩
    refine (pads 3 1 rfl m1 (pads3 hb)).mono fun t' ⟨m', a', p', q'⟩ => ?_
    exact relD_next hR m' (by rw [a', a1]; exact hR.regs) (p'.trans P1.sp) (by rw [q', P1.mem]; exact hR.mem) rfl
      hR.zero rfl

theorem blk_bne {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {a b : Nat} {o : Int}
    (hj : C[pc]? = some (.bne a b o)) (hv : validJ C.length pc (.bne a b o)) (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (if s.x a ≠ s.x b then ((pc : Int) + o).toNat else pc + 1, s)) := by
  obtain ⟨hra, hrb, h1, h2, h3, h4⟩ := hv
  have := blk_cmp (c := 1) hj (by simp [blockJ, body]) (by decide) hra hrb h3 h4 h1 h2 hR
  simpa [jc] using this

theorem blk_bltu {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {a b : Nat} {o : Int}
    (hj : C[pc]? = some (.bltu a b o)) (hv : validJ C.length pc (.bltu a b o)) (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (if (s.x a).toNat < (s.x b).toNat then ((pc : Int) + o).toNat else pc + 1, s)) := by
  obtain ⟨hra, hrb, h1, h2, h3, h4⟩ := hv
  have := blk_cmp (c := 3) hj (by simp [blockJ, body]) (by decide) hra hrb h3 h4 h1 h2 hR
  simpa [jc] using this

theorem blk_bgeu {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {a b : Nat} {o : Int}
    (hj : C[pc]? = some (.bgeu a b o)) (hv : validJ C.length pc (.bgeu a b o)) (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (if (s.x b).toNat ≤ (s.x a).toNat then ((pc : Int) + o).toNat else pc + 1, s)) := by
  obtain ⟨hra, hrb, h1, h2, h3, h4⟩ := hv
  have := blk_cmp (c := 2) hj (by simp [blockJ, body]) (by decide) hra hrb h3 h4 h1 h2 hR
  simpa [jc] using this

theorem blk_beq {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {a b : Nat} {o : Int}
    (hj : C[pc]? = some (.beq a b o)) (hv : validJ C.length pc (.beq a b o)) (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (if s.x a = s.x b then ((pc : Int) + o).toNat else pc + 1, s)) := by
  obtain ⟨hra, hrb, h1, h2, h3, h4⟩ := hv
  have hz : s.x 0 = 0 := hR.zero
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · subst ha hb
    simp only [ite_true]
    exact b_blk hj (by simp [blockJ, body, pad4]) (by omega) (by omega) h1 h2 hR
  · subst ha
    have := cbz_blk (q := b) hj (by simp [blockJ, body, pad4, hb]) (live_of_rd hrb hb) h3 h4 h1 h2 hR
    simpa [hz, eq_comm] using this
  · subst hb
    have := cbz_blk (q := a) hj (by simp [blockJ, body, pad4, ha]) (live_of_rd hra ha) h3 h4 h1 h2 hR
    simpa [hz] using this
  · have := blk_cmp (c := 0) hj (by simp [blockJ, body, ha, hb]) (by decide) hra hrb h3 h4 h1 h2 hR
    simpa [jc] using this

/-- `jal rd o` (rd ∈ {x0, x1}). Premise beyond `validJ`: the offset fits `b`/`bl` (±2^23 J instructions) -/
theorem blk_jal {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {rd : Nat} {o : Int}
    (hj : C[pc]? = some (.jal rd o)) (hv : validJ C.length pc (.jal rd o)) (ho1 : -2 ^ 23 < o) (ho2 : o < 2 ^ 23)
    (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (((pc : Int) + o).toNat, wr s rd (UInt64.ofNat (s.b + s.w * (pc + 1))))) := by
  obtain ⟨hrd, h1, h2⟩ := hv
  rcases hrd with rfl | rfl
  · simp only [wr, ite_true]
    exact b_blk hj (by simp [blockJ, body, pad4]) (by omega) ho2 h1 h2 hR
  have hb : blockJ (.jal 1 o) = [PAD, PAD, PAD, blB (4 * o - 3)] := by simp [blockJ, body, pad4]
  have hm := hR.mid hj
  have pw : ∀ k, k < 3 → bw (.jal 1 o) k = wd PAD := by
    intro k hk; rw [bw_of hb]; rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> rfl
  obtain ⟨t1, s1, m1, a1, p1, q1⟩ := pad_ok hm (by omega) (pw 0 (by omega))
  obtain ⟨t2, s2, m2, a2, p2, q2⟩ := pad_ok m1 (by omega) (pw 1 (by omega))
  obtain ⟨t3, s3, m3, a3, p3, q3⟩ := pad_ok m2 (by omega) (pw 2 (by omega))
  have hA := m3.at (by omega); rw [bw_of hb] at hA; simp only [List.getD_cons_succ, List.getD_cons_zero, blB] at hA
  have hmo := mo_lt (4 * o - 3) 26
  obtain ⟨t4, s4, a4, P4⟩ := dm_bl (by mask32) hA
  rw [show (wd (0x94000000 + mo (4 * o - 3) 26)).extractLsb' 0 26 = BitVec.ofNat 26 (mo (4 * o - 3) 26) by
    apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega] at P4
  have hlt := m3.lt (by omega)
  have hcl : s.b + 16 * C.length < 2 ^ 64 := hR.code.lt
  have hw : s.w = 16 := by have : s.wk = 3 := hR.wk; unfold St.w; omega
  have hpc : pc < C.length := by
    rcases Nat.lt_or_ge pc C.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hj; cases hj
  refine Reach.cons s1 (Reach.cons s2 (Reach.cons s3 (Reach.cons s4 (Reach.done ⟨P4.run, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))))
  · rw [P4.pc, m3.pc, ofs26 _ (by omega) (by omega) _ (by omega) (by omega) hlt]
    simp only [wr, show (1 : Nat) ≠ 0 by decide, ite_false]; congr 1; omega
  · simp only [wr, show (1 : Nat) ≠ 0 by decide, ite_false]; rw [P4.mem, q3, q2, q1]; exact hR.code
  · rw [a4, a3, a2, a1, m3.pc]
    have := regs_wr hR.regs (rd := 1) ⟨by decide, by decide⟩ (UInt64.ofNat (s.b + s.w * (pc + 1)))
    have e : ad (s.b + 16 * pc + 4 * (0 + 1 + 1 + 1)) + 4 = (UInt64.ofNat (s.b + s.w * (pc + 1))).toBitVec := by
      rw [hw]; apply BitVec.eq_of_toNat_eq; simp; omega
    rw [e]; exact this
  · simp [wr, upd]; exact hR.zero
  · rw [P4.sp, p3, p2, p1]; exact hR.sp
  · simp only [wr, show (1 : Nat) ≠ 0 by decide, ite_false]; exact hR.wk
  · simp only [wr, show (1 : Nat) ≠ 0 by decide, ite_false]; rw [P4.mem, q3, q2, q1]; exact hR.mem

/-- `jalr x0, rs`. Premise (ArmBlock's `AccOK`): the target is a block address -/
theorem blk_jalr {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {rd rs : Nat}
    (hj : C[pc]? = some (.jalr rd rs)) (hv : validJ C.length pc (.jalr rd rs))
    (hacc : s.b ≤ (s.x rs).toNat ∧ ((s.x rs).toNat - s.b) % 16 = 0) (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (((s.x rs).toNat - s.b) / s.w, wr s rd (UInt64.ofNat (s.b + s.w * (pc + 1))))) := by
  obtain ⟨rfl, hs0, hs31⟩ := hv
  simp only [wr, ite_true]
  have hl : live rs := ⟨hs31, hs0⟩
  have hb : blockJ (.jalr 0 rs) = [brR (pi rs), PAD, PAD, PAD] := by simp [blockJ, body, pad4]
  have hm := hR.mid hj
  have hA := hm.at (by omega); rw [bw_of hb] at hA; simp only [List.getD_cons_zero, brR] at hA
  obtain ⟨t1, s1, a1, P1⟩ := dm_br (by mask32) (by fldt) hA
  rw [show ((wd (0xD61F0000 + pi rs * 2 ^ 5)).extractLsb' 5 5).toNat = pi rs by fldt, hR.regs.1 rs hl] at P1
  have hw : s.w = 16 := by have : s.wk = 3 := hR.wk; unfold St.w; omega
  refine Reach.cons s1 (Reach.done (relD_jump hR P1.run ?_ P1.mem (a1 ▸ hR.regs) P1.sp))
  rw [P1.pc, hw]; apply BitVec.eq_of_toNat_eq
  have := (s.x rs).toNat_lt
  simp; omega

end Proven.Apc.Blocks
