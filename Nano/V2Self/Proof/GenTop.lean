/- Gen soundness on success, the def and program levels: `def_run` (one def: header g38, root visit, ENDDEF) and,
by iteration, the whole main loop g39; then g42/g41. -/
import Nano.V2Self.Proof.GenRef
namespace GenRef
open C CallProbe

/-- the header's register file (g38) -/
theorem hdr_regs (r : Buf) (hr : r.length = 10) (a b c d : UInt64) :
    (g15 (g15 (g15 (g15 (g15 r 0 a) 1 b) 7 c) 2 d) 6 2).length = 10 ∧
    ∀ j : UInt64, bget (g15 (g15 (g15 (g15 (g15 r 0 a) 1 b) 7 c) 2 d) 6 2) j =
      if 6 = j then 2 else if 2 = j then d else if 7 = j then c else if 1 = j then b else if 0 = j then a else bget r j := by
  simp only [g15]
  have l1 : (bset r 0 a).length = 10 := by rw [BufL.length_bset]; exact hr
  have l2 : (bset (bset r 0 a) 1 b).length = 10 := by rw [BufL.length_bset]; exact l1
  have l3 : (bset (bset (bset r 0 a) 1 b) 7 c).length = 10 := by rw [BufL.length_bset]; exact l2
  have l4 : (bset (bset (bset (bset r 0 a) 1 b) 7 c) 2 d).length = 10 := by rw [BufL.length_bset]; exact l3
  refine ⟨by rw [BufL.length_bset]; exact l4, fun j => ?_⟩
  rw [rget _ l4 6 j _ (by decide), rget _ l3 2 j _ (by decide), rget _ l2 7 j _ (by decide), rget _ l1 1 j _ (by decide),
    rget _ hr 0 j _ (by decide)]

/-- ENDDEF's register file: cursor past the ENDDEF, no items -/
theorem end_regs (r : Buf) (hr : r.length = 10) (a : UInt64) :
    (g15 (g15 r 6 0) 0 a).length = 10 ∧
    ∀ j : UInt64, bget (g15 (g15 r 6 0) 0 a) j = if 0 = j then a else if 6 = j then 0 else bget r j := by
  simp only [g15]
  have l1 : (bset r 6 0).length = 10 := by rw [BufL.length_bset]; exact hr
  refine ⟨by rw [BufL.length_bset]; exact l1, fun j => ?_⟩
  rw [rget _ l1 0 j _ (by decide), rget _ hr 6 j _ (by decide)]

theorem g29_len : ∀ (n : Nat) (p q j : UInt64) (o : Buf), (g29 n p q j o).length ≤ o.length + 2 * n + 3
  | 0, p, q, j, o => by simp [g29]
  | n + 1, p, q, j, o => by
    unfold g29; split
    · have := g29_len n p q (j + 1) (bpush (bpush o (g11 5 31 ((q - 1 - j) <<< 3))) (g12 5 8 ((p <<< 3) + g_16 - ((j + 1) <<< 3))))
      simp only [bpush, List.length_append, List.length_singleton] at this ⊢; omega
    · simp [bpush]

theorem bset_keep4 (r : Buf) (j v : UInt64) (hj : j ≠ 4) (h : bget r 4 = 1) : bget (bset r j v) 4 = 1 := by
  rw [BufL.bget_bset, if_neg]; · exact h
  intro ⟨e, _⟩; exact hj (UInt64.toNat.inj e)

/-- the state after ENDDEF -/
def EPost (K : Cx) (F : List UInt64) (i1 : Nat) (s0 s : GS) : Prop :=
  tg K.X i1 = 21 ∧ s.x = s0.x ∧ s.k = s0.k ∧ s.t = s0.t ∧ s.f = s0.f ∧
  s.o = g29 512 K.p K.q 0 (bpush (bpush (patchR (bsize s0.o) s0.o F.reverse) (g11 14 8 8)) (g11 15 8 0)) ∧
  s.o.length < 2 ^ 24 ∧ s.r.length = 10 ∧ bget s.r 0 = (i1 + 1).toUInt64 ∧ bget s.r 6 = 0 ∧ bget s.r 8 = 0 ∧
  ∀ j : UInt64, j ≠ 0 → j ≠ 6 → j ≠ 8 → bget s.r j = bget s0.r j

/-- the ENDDEF item: tag 21 at the cursor, exits patched, epilogue; else error -/
theorem end_step {K s F i1} (hI : Inv K s [(12, 0, 0)] F) (hr0 : bget s.r 0 = i1.toUInt64) (hi1 : i1 < 2 ^ 32) :
    Run s (EPost K F i1 s) := by
  have hL := live_of hI (by simp)
  have hs : Stk s.k ([] ++ [((12 : UInt64), (0 : UInt64), (0 : UInt64))]) := hI.stk
  obtain ⟨t0, -, -⟩ := stk_top hs
  have hn : bget s.r 6 - 1 = 0 := by rw [hI.r6]; rfl
  have hc : bget s.k ((bget s.r 6 - 1) * 3) = 12 := by rw [hn]; simpa [bget] using t0
  have l1 : (g15 s.r 6 0).length = 10 := by simp only [g15]; rw [BufL.length_bset]; exact hI.rl
  have h10 : bget (g15 s.r 6 0) 0 = i1.toUInt64 := by
    simp only [g15]; rw [rget _ hI.rl 6 0 _ (by decide), if_neg (by decide), hr0]
  have hx : bget s.x (bget (g15 s.r 6 0) 0) = tg K.X i1 := by rw [h10, hI.x, tg_u _ _ (by omega)]
  have hF : F.length ≤ 65536 := by have := hI.fx.1; have := hI.fl; omega
  have h8' : bget (g15 s.r 6 0) 8 = F.length.toUInt64 := by
    simp only [g15]; rw [rget _ hI.rl 6 8 _ (by decide), if_neg (by decide), hI.r8]
  by_cases h21 : tg K.X i1 = 21
  · have hif : (if bget s.x (bget (g15 s.r 6 0) 0) == 21 then g15 (g15 s.r 6 0) 0 (bget (g15 s.r 6 0) 0 + 1)
        else g16 (g15 s.r 6 0)) = g15 (g15 s.r 6 0) 0 (i1 + 1).toUInt64 := by
      rw [if_pos (by rw [hx, h21]; rfl), h10, ← u_add]; rfl
    obtain ⟨l2, hg2⟩ := end_regs s.r hI.rl (i1 + 1).toUInt64
    generalize hR2 : g15 (g15 s.r 6 0) 0 (i1 + 1).toUInt64 = R2 at hif l2 hg2
    have h8 : bget R2 8 = F.length.toUInt64 := by rw [hg2, if_neg (by decide), if_neg (by decide), hI.r8]
    obtain ⟨a1, a2, a3⟩ := g28_ok 65536 F s.f R2 s.o hF (by omega) hI.fx.2
    generalize hg : g28 65536 F.length.toUInt64 (s.f, (R2, s.o)) = res at a1 a2 a3
    obtain ⟨f1, r3, o3⟩ := res
    simp only at a1 a2 a3
    have hst := st_t12 s 0 hn hc f1 r3 o3 (by rw [hif, h8]; exact hg)
    rw [hif] at hst
    refine Run.ofReach (Reach.step hL ?_)
    rw [hst]
    rcases a3 with a3 | a3
    · rw [a3]; subst a2 a1
      have hp : bget R2 1 = K.p := by rw [hg2, if_neg (by decide), if_neg (by decide), hI.r1]
      have hq : bget R2 2 = K.q := by rw [hg2, if_neg (by decide), if_neg (by decide), hI.r2]
      rw [hp, hq]
      have hol := g29_len 512 K.p K.q 0 (bpush (bpush (patchR (bsize s.o) s.o F.reverse) (g11 14 8 8)) (g11 15 8 0))
      have hpl := patchR_len (bsize s.o) F.reverse s.o
      have hsl := hI.ol
      have hb2 : (bpush (bpush (patchR (bsize s.o) s.o F.reverse) (g11 14 8 8)) (g11 15 8 0)).length = s.o.length + 2 := by
        simp [bpush, hpl]
      rw [hb2] at hol
      by_cases hb : 2 ^ 24 ≤ (g29 512 K.p K.q 0 (bpush (bpush (patchR (bsize s.o) s.o F.reverse) (g11 14 8 8)) (g11 15 8 0))).length
      · exact Reach.toobig ⟨hb, by dsimp only; omega⟩
      obtain ⟨l3, hg3⟩ : (g15 R2 8 0).length = 10 ∧ ∀ j : UInt64, bget (g15 R2 8 0) j = if 8 = j then 0 else bget R2 j :=
        ⟨by simp only [g15]; rw [BufL.length_bset]; exact l2, fun j => by simp only [g15]; rw [rget _ l2 8 j _ (by decide)]⟩
      refine Reach.done ⟨h21, rfl, rfl, rfl, rfl, rfl, by dsimp only; omega, l3, ?_, ?_, ?_, fun j j0 j6 j8 => ?_⟩
      · rw [hg3, if_neg (by decide), hg2, if_pos rfl]
      · rw [hg3, if_neg (by decide), hg2, if_neg (by decide), if_pos rfl]
      · rw [hg3, if_pos rfl]
      · rw [hg3, if_neg (Ne.symm j8), hg2, if_neg (Ne.symm j0), if_neg (Ne.symm j6)]
    · exact Reach.error (bset_keep4 _ _ _ (by decide) (a3 (by rw [l2]; omega)))
  · have hif : (if bget s.x (bget (g15 s.r 6 0) 0) == 21 then g15 (g15 s.r 6 0) 0 (bget (g15 s.r 6 0) 0 + 1)
        else g16 (g15 s.r 6 0)) = g16 (g15 s.r 6 0) := by
      rw [if_neg (by rw [hx]; simpa using h21)]
    have h8 : bget (g16 (g15 s.r 6 0)) 8 = F.length.toUInt64 := by
      unfold g16; rw [rget _ l1 4 8 _ (by decide), if_neg (by decide), h8']
    have l2 : (g16 (g15 s.r 6 0)).length = 10 := by unfold g16; rw [BufL.length_bset]; exact l1
    obtain ⟨a1, a2, a3⟩ := g28_ok 65536 F s.f (g16 (g15 s.r 6 0)) s.o hF (by omega) hI.fx.2
    generalize hg : g28 65536 F.length.toUInt64 (s.f, (g16 (g15 s.r 6 0), s.o)) = res at a1 a2 a3
    obtain ⟨f1, r3, o3⟩ := res
    simp only at a1 a2 a3
    have hst := st_t12 s 0 hn hc f1 r3 o3 (by rw [hif, h8]; exact hg)
    refine Run.ofReach (Reach.step hL ?_)
    rw [hst]
    have h4 : bget r3 4 = 1 := by
      rcases a3 with a3 | a3
      · rw [a3]; exact g16_err _ l1
      · exact a3 (by rw [l2]; omega)
    exact Reach.error (bset_keep4 _ _ _ (by decide) h4)

/-- the result of one def: DefC, a new boundary, the def-start table pushed, the cursor past the ENDDEF -/
def DPost (X : Buf) (u : UInt64) (s0 : GS) (i : Nat) (s : GS) : Prop :=
  ∃ i', DefC X u s0.t i s0.o s.o i' ∧ Bnd X u s ∧ s.t = bpush s0.t (bsize s0.o) ∧ bget s.r 0 = i'.toUInt64 ∧
    i + 8 ≤ i' ∧ i' ≤ X.length

theorem bsize_ok (o : Buf) (h : o.length < 2 ^ 24) : ¬ 16777215 < bsize o := by
  rw [bsize_u, UInt64.lt_iff_toNat_lt, u_toNat _ (by omega)]; simp; omega

/-- **one def**: from a def boundary with the cursor at i < |X|, the main loop compiles the def (DefC) or fails -/
theorem def_run {X u s i} (hB : Bnd X u s) (hr0 : bget s.r 0 = i.toUInt64) (hi : i < X.length) (hX : X.length < 2 ^ 31)
    (ht : 8 * s.t.length ≤ i) : Run s (DPost X u s i) := by
  have h0 : g55 s.x s.r s.o = 0 := by
    unfold g55
    rw [if_neg (by simpa using hB.r5), if_neg (by simpa using hB.r4), if_neg (bsize_ok _ hB.ol), if_pos (by simp [hB.r6]),
      if_pos (by rw [hr0, hB.x, bsize_u, UInt64.lt_iff_toNat_lt, u_toNat _ (by omega), u_toNat _ (by omega)]; exact hi)]
    rfl
  refine Run.stepDef h0 hB.r6 (by rw [hB.rl]; omega) ?_
  by_cases hd : ¬ HdOk s.x s.t (bget s.r 0)
  · rw [g38_bad _ _ _ _ _ hd]; exact Run.error (g16_err _ hB.rl)
  rw [Classical.not_not] at hd
  rw [g38_ok _ _ _ _ _ hd]
  dsimp only
  have e1 : bget s.x (i.toUInt64 + 1) = tg X (i + 1) := by rw [hB.x]; exact tg_u1 _ i 1 (by omega)
  have e2 : bget s.x (i.toUInt64 + 2) = tg X (i + 2) := by rw [hB.x]; exact tg_u1 _ i 2 (by omega)
  have e3 : bget s.x (i.toUInt64 + 3) = tg X (i + 3) := by rw [hB.x]; exact tg_u1 _ i 3 (by omega)
  have e5 : bget s.x (i.toUInt64 + 5) = tg X (i + 5) := by rw [hB.x]; exact tg_u1 _ i 5 (by omega)
  obtain ⟨d1, d2, d3, d4, d5⟩ := hd
  rw [hr0, hB.x, tg_u _ _ (by omega)] at d1
  rw [hr0, e3] at d2; rw [hr0, e2, e3] at d3; rw [hr0, e5] at d4; rw [hr0, e1] at d5
  rw [hr0, e2, e3, e5]
  obtain ⟨hl1, hg1⟩ := hdr_regs s.r hB.rl (i.toUInt64 + 6) (tg X (i + 2)) (tg X (i + 3)) (tg X (i + 5))
  generalize hR1 : g15 (g15 (g15 (g15 (g15 s.r 0 (i.toUInt64 + 6)) 1 (tg X (i + 2))) 7 (tg X (i + 3))) 2 (tg X (i + 5))) 6 2
    = r1 at hl1 hg1 ⊢
  have sk0 : Stk s.k ([] : List Item) := ⟨by simp, fun j e h => by simp at h⟩
  obtain ⟨sk1, kl1⟩ := stk_push s.k [] 12 0 0 sk0 hB.kl (by simp)
  obtain ⟨sk2, kl2⟩ := stk_push _ _ 1 0 0 sk1 (by rw [kl1]; have := hB.kl; simp; omega) (by simp)
  simp only [List.length_nil, List.nil_append, List.length_singleton] at sk1 kl1 sk2 kl2
  rw [kl1] at kl2
  generalize hK1 : g18 (g18 s.k (Nat.toUInt64 0) 12 0 0) (Nat.toUInt64 1) 1 0 0 = k1 at sk2 kl2
  have hk1 : g18 (g18 s.k 0 12 0 0) 1 1 0 0 = k1 := hK1
  have hpl : (proW (tg X (i + 2)) (tg X (i + 3)) s.o).length = s.o.length + 12 := by simp [proW, g22, bpush]
  by_cases hbig : 2 ^ 24 ≤ s.o.length + 12
  · exact Run.toobig ⟨by dsimp only; omega, by dsimp only; have := hB.ol; omega⟩
  have hI : Inv (dK X u (bpush s.t (bsize s.o)) i) ⟨s.x, r1, proW (tg X (i + 2)) (tg X (i + 3)) s.o, k1,
      bpush s.t (bsize s.o), s.f⟩ ([(12, 0, 0)] ++ [(1, 0, 0)]) [] := {
    x := hB.x
    t := rfl
    rl := hl1
    r1 := by rw [hg1]; rfl
    r2 := by rw [hg1]; rfl
    r7 := by rw [hg1]; rfl
    r9 := by rw [hg1]; exact hB.r9
    r4 := by rw [hg1]; exact hB.r4
    r5 := by rw [hg1]; exact hB.r5
    r6 := by rw [hg1]; rfl
    stk := sk2
    kl := by dsimp only; have := hB.kl; omega
    Ll := by simp
    fx := ⟨Nat.zero_le _, fun j h => by simp at h⟩
    r8 := by rw [hg1]; exact hB.r8
    fl := hB.fl
    ol := by dsimp only; omega }
  have hr06 : bget r1 0 = (i + 6).toUInt64 := by rw [hg1]; exact u_add i 6
  have hV := root_visit _ hX (i + 6) (by omega) _ [(12, 0, 0)] [] hI hr06 (by simp [dK]; omega)
  refine (Run.ofReach hV).bind ?_
  rintro s' ⟨c, i1, E, hcg, hI', ho', hr0', ⟨hi1, hi1X⟩, -⟩
  simp only [List.nil_append, List.length_singleton] at hI' hcg
  refine (end_step hI' hr0' (by simp [dK] at hi1X; omega)).bind ?_
  rintro s'' ⟨h21, ex, ek, et, ef, eo, hol, hrl, hr0'', hr6, hr8, hrj⟩
  have hi1l : i1 < X.length := tg_lt X i1 (by simp [dK] at h21; rw [h21]; decide)
  refine Run.done ⟨i1 + 1, ⟨d1, d2, d3, d4, d5, c, i1, E, hcg, h21, rfl, ?_⟩, ?_, ?_, hr0'', by omega, by omega⟩
  · rw [eo, ho']; rfl
  · exact { x := by rw [ex, hI'.x]; rfl
            rl := hrl
            r4 := by rw [hrj 4 (by decide) (by decide) (by decide)]; exact hI'.r4
            r5 := by rw [hrj 5 (by decide) (by decide) (by decide)]; exact hI'.r5
            r6 := hr6
            r8 := hr8
            r9 := by rw [hrj 9 (by decide) (by decide) (by decide)]; exact hI'.r9
            kl := by rw [ek]; exact hI'.kl
            fl := by rw [ef]; exact hI'.fl
            ol := hol
            tl := by rw [et, hI'.t]; simp [dK, bpush]; omega }
  · rw [et, hI'.t]; rfl

end GenRef
