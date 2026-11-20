/- J `slli`/`srli rd rs sh` (sh < 64) on DeepMind's machine. Block: `[movz x17, #0]` (rs = x0), `movz x16, #sh`,
`lslv`/`lsrv d, s', x16`, PADs. -/
import Blocks.KAlu
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Proven.Apc.Blocks
open CallProbe Proven.Arm ArmBlock

theorem pads1 {j : J} {w0 w1 w2 : Nat} (h : blockJ j = [w0, w1, w2, PAD]) : PadsFrom j 3 := by
  intro k h1 h2; rw [bw_of h]; rcases (show k = 3 by omega) with rfl; rfl

/-- `movz xd, #i` (i < 2^16) sets `x[d] := i` -/
theorem movz_ok {t : Arm64.State} {d i : Nat} (hd : d < 31) (hi : i < 65536) (hA : At t (wd (movz d i))) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX d (BitVec.ofNat 64 i) ∧ Post t t' (t.pc + 4) t.mem := by
  simp only [movz] at hA
  have := dm_movz (by mask32) (by fldt) hA
  rw [show ((wd (0xD2800000 + i * 2 ^ 5 + d)).extractLsb' 0 5).toNat = d by fldt,
    show ((wd (0xD2800000 + i * 2 ^ 5 + d)).extractLsb' 21 2).toNat = 0 by fldt,
    show ((wd (0xD2800000 + i * 2 ^ 5 + d)).extractLsb' 5 16).setWidth 64 = BitVec.ofNat 64 i by immt] at this
  simpa using this

/-- the shift block, for op 6 (lslv) / 7 (lsrv) -/
theorem blk_shift {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {j : J} {op rd rs sh : Nat}
    (hop : op = 6 ∨ op = 7) (hj : C[pc]? = some j) (hsh : sh < 64) (hrs : rdOK rs) (hrd : wrOK rd)
    (hb : rd ≠ 0 → blockJ j = pad4 (zpre rs ++ [movz 16 sh, rr (aluC op) (pi rd) (opR rs) 16]))
    (hb0 : rd = 0 → blockJ j = [PAD, PAD, PAD, PAD]) (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (pc + 1, wr s rd (aluf op (s.x rs) sh.toUInt64))) := by
  have hm := hR.mid hj
  have hz : s.x 0 = 0 := hR.zero
  by_cases h0 : rd = 0
  · subst h0
    refine (pads 4 0 rfl hm (pads4 (hb0 rfl))).mono fun t' ⟨m', a', p', q'⟩ => ?_
    simp only [wr, ite_true]
    exact relD_next hR m' (a' ▸ hR.regs) p' (q' ▸ hR.mem) rfl hR.zero rfl
  have hl := live_of_wr hrd h0
  have hsl := opR_lt hrs
  have hshv : (sh.toUInt64).toBitVec = BitVec.ofNat 64 sh := by
    apply BitVec.eq_of_toNat_eq; simp
  have fin : ∀ {t' : Arm64.State} {A : AState}, Mid C s.b pc j 4 t' → RegsOK A s K →
      abs t' = A.setX (pi rd) (aluf op (s.x rs) sh.toUInt64).toBitVec → t'.sp = t.sp → t'.mem = t.mem →
      RelD C D K (pc + 1, wr s rd (aluf op (s.x rs) sh.toUInt64)) t' := by
    intro t' A m' hA a' p' q'
    refine relD_next hR m' (a' ▸ regs_wr hA hl _) p' (q' ▸ ?_) ?_ ?_ ?_
    all_goals simp [wr, h0, upd, hz, hR.mem, Ne.symm h0]
  -- the last two real words, from a state whose `x[opR rs]` holds `s.x rs`
  have tail : ∀ {k : Nat} {t1 : Arm64.State} {A : AState}, k + 2 ≤ 4 → Mid C s.b pc j k t1 → abs t1 = A →
      RegsOK A s K → A.x (opR rs) = (s.x rs).toBitVec → bw j k = wd (movz 16 sh) →
      bw j (k + 1) = wd (rr (aluC op) (pi rd) (opR rs) 16) → PadsFrom j (k + 2) → t1.sp = t.sp → t1.mem = t.mem →
      Reach t1 (RelD C D K (pc + 1, wr s rd (aluf op (s.x rs) sh.toUInt64))) := by
    intro k t1 A hk m1 a1 rA xA w0 w1 hp p1 q1
    have hA0 := m1.at (by omega); rw [w0] at hA0
    obtain ⟨t2, s2, m2, a2, p2, q2⟩ := seq1 m1 (by omega) (movz_ok (by decide) (by omega) hA0)
    refine Reach.cons s2 ((word_pads (A := (A.setX 16 (BitVec.ofNat 64 sh)).setX (pi rd)
      (aluf op (s.x rs) sh.toUInt64).toBitVec) m2 (by omega) (fun hA => ?_) hp).mono
      fun t' ⟨m', a', p', q'⟩ => fin m' (regs_scr rA (.inl rfl) _) a' (p'.trans (p2.trans p1)) (q'.trans (q2.trans q1)))
    rw [w1] at hA
    have e16 : (abs t2).x 16 = (sh.toUInt64).toBitVec := by rw [a2, a1, setX_eq _ (by decide), hshv]
    have eop : (abs t2).x (opR rs) = (s.x rs).toBitVec := by
      rw [a2, a1, setX_ne]; exact xA
      unfold opR; split
      · decide
      · rename_i hn; exact (pi_rng (live_of_rd hrs hn)).1
    have := alu_word (by omega) hl.1 hsl (by decide) eop e16 (fun h => by omega) hA
    rwa [a2, a1] at this
  have hb' := hb h0
  by_cases hs0 : rs = 0
  · subst hs0
    have hb2 : blockJ j = [movz 17 0, movz 16 sh, rr (aluC op) (pi rd) 17 16, PAD] := by
      rw [hb']; simp [pad4, zpre, opR]
    have hA0 := hm.at (by omega); rw [bw_of hb2] at hA0
    obtain ⟨t1, s1, m1, a1, p1, q1⟩ := seq1 hm (by omega) (movz_ok (by decide) (by decide) hA0)
    exact Reach.cons s1 (tail (by omega) m1 a1 (regs_scr hR.regs (.inr rfl) _)
      (by simp only [opR, ite_true]; rw [setX_eq _ (by decide), hz]; rfl)
      (by rw [bw_of hb2]; rfl) (by rw [bw_of hb2]; simp [opR]) (pads1 hb2) p1 q1)
  · have hb2 : blockJ j = [movz 16 sh, rr (aluC op) (pi rd) (pi rs) 16, PAD, PAD] := by
      rw [hb']; simp [pad4, zpre, opR, hs0]
    have hsl' := live_of_rd hrs hs0
    exact tail (by omega) hm rfl hR.regs (by simp only [opR, hs0, ite_false]; exact hR.regs.1 rs hsl')
      (by rw [bw_of hb2]; rfl) (by rw [bw_of hb2]; simp [opR, hs0]) (pads2 hb2) rfl rfl

theorem blk_slli {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {rd rs sh : Nat}
    (hj : C[pc]? = some (.slli rd rs sh)) (hv : validJ C.length pc (.slli rd rs sh)) (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (pc + 1, wr s rd (s.x rs <<< sh.toUInt64))) := by
  obtain ⟨hsh, hrs, hrd⟩ := hv
  have := blk_shift (op := 6) (.inl rfl) hj hsh hrs hrd (fun h0 => by simp [blockJ, body, h0, aluC])
    (fun h0 => by subst h0; simp [blockJ, body, pad4]) hR
  simpa [aluf] using this

theorem blk_srli {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {rd rs sh : Nat}
    (hj : C[pc]? = some (.srli rd rs sh)) (hv : validJ C.length pc (.srli rd rs sh)) (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (pc + 1, wr s rd (s.x rs >>> sh.toUInt64))) := by
  obtain ⟨hsh, hrs, hrd⟩ := hv
  have := blk_shift (op := 7) (.inr rfl) hj hsh hrs hrd (fun h0 => by simp [blockJ, body, h0, aluC])
    (fun h0 => by subst h0; simp [blockJ, body, pad4]) hR
  simpa [aluf] using this

end Proven.Apc.Blocks
