/- Gen soundness on success, the def and program levels: `def_run` (one def: header g38, root visit, ENDDEF) and,
by iteration, the whole main loop g39; then g42/g41. -/
import Nano.V2Self.Proof.Gen.GenRef
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
  (∀ j : UInt64, j ≠ 0 → j ≠ 6 → j ≠ 8 → bget s.r j = bget s0.r j) ∧ ∀ e ∈ F, g14 e (bsize s0.o) = 1

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
    rcases a3 with ⟨a3, a5⟩ | a3
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
      refine Reach.done ⟨h21, rfl, rfl, rfl, rfl, rfl, by dsimp only; omega, l3, ?_, ?_, ?_, fun j j0 j6 j8 => ?_, a5⟩
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
      rcases a3 with ⟨a3, -⟩ | a3
      · rw [a3]; exact g16_err _ l1
      · exact a3 (by rw [l2]; omega)
    exact Reach.error (bset_keep4 _ _ _ (by decide) h4)

/-- the result of one def: DefC, a new boundary, the def-start table pushed, the cursor past the ENDDEF -/
def DPost (X : Buf) (u : UInt64) (s0 : GS) (i : Nat) (s : GS) : Prop :=
  ∃ i', DefC X u s0.t i s0.o s.o i' ∧ Bnd X u s ∧ s.t = bpush s0.t (bsize s0.o) ∧ bget s.r 0 = i'.toUInt64 ∧
    i + 8 ≤ i' ∧ i' ≤ X.length ∧ bget s.r 1 = tg X (i + 2) ∧ bget s.r 2 = tg X (i + 5)

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
  rintro s'' ⟨h21, ex, ek, et, ef, eo, hol, hrl, hr0'', hr6, hr8, hrj, hjx⟩
  have hi1l : i1 < X.length := tg_lt X i1 (by simp [dK] at h21; rw [h21]; decide)
  refine Run.done ⟨i1 + 1, ⟨d1, d2, d3, d4, d5, c, i1, E, hcg, h21, rfl, ?_, fun e he => ?_⟩, ?_, ?_, hr0'', by omega, by omega, ?_, ?_⟩
  · rw [eo, ho']; rfl
  · have := hjx e.toUInt64 (by simp; exact ⟨e, he, rfl⟩)
    rw [ho', bsize_u] at this; exact this
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
  · rw [hrj 1 (by decide) (by decide) (by decide)]; exact hI'.r1
  · rw [hrj 2 (by decide) (by decide) (by decide)]; exact hI'.r2

/-- consecutive defs: header positions hs, def-start table T → T', cursor i → i', code o → o' -/
inductive DefsC (X : Buf) (u : UInt64) : Buf → Nat → Buf → List Nat → Buf → Nat → Buf → Prop
  | nil {T i o} : DefsC X u T i o [] T i o
  | cons {T i o o1 i1 hs T' i' o'} : DefC X u T i o o1 i1 → DefsC X u (bpush T (bsize o)) i1 o1 hs T' i' o' →
      DefsC X u T i o (i :: hs) T' i' o'

theorem DefsC.nil_eq {X u T i o T' i' o'} (h : DefsC X u T i o [] T' i' o') : T = T' ∧ i = i' ∧ o = o' := by
  cases h; exact ⟨rfl, rfl, rfl⟩

/-- the main loop's def phase: all defs up to the end of the AST -/
def PPost (X : Buf) (u : UInt64) (s0 : GS) (i : Nat) (s : GS) : Prop :=
  ∃ hs i', DefsC X u s0.t i s0.o hs s.t i' s.o ∧ Bnd X u s ∧ bget s.r 0 = i'.toUInt64 ∧ i' = X.length ∧
    (hs = [] → bget s.r 1 = bget s0.r 1 ∧ bget s.r 2 = bget s0.r 2) ∧
    (hs ≠ [] → bget s.r 1 = tg X (hs.getLastD 0 + 2) ∧ bget s.r 2 = tg X (hs.getLastD 0 + 5))

theorem prog_run (X : Buf) (u : UInt64) (hX : X.length < 2 ^ 31) : ∀ n s i, X.length - i ≤ n → Bnd X u s →
    bget s.r 0 = i.toUInt64 → i ≤ X.length → 8 * s.t.length ≤ i → Run s (PPost X u s i) := by
  intro n
  induction n with
  | zero =>
    intro s i hn hB hr0 hi _
    exact Run.done ⟨[], i, .nil, hB, hr0, by omega, fun _ => ⟨rfl, rfl⟩, fun h => absurd rfl h⟩
  | succ n ih =>
    intro s i hn hB hr0 hi ht
    by_cases hiX : i = X.length
    · exact Run.done ⟨[], i, .nil, hB, hr0, hiX, fun _ => ⟨rfl, rfl⟩, fun h => absurd rfl h⟩
    refine (def_run hB hr0 (by omega) hX ht).bind ?_
    rintro s1 ⟨i1, hD, hB1, ht1, hr1, hii, hiX1, hp1, hq1⟩
    refine (ih s1 i1 (by omega) hB1 hr1 hiX1 (by rw [ht1]; simp [bpush]; omega)).bind ?_
    rintro s2 ⟨hs, i2, hDs, hB2, hr2, hi2, hn2, hc2⟩
    refine Run.done ⟨i :: hs, i2, .cons hD (by rw [← ht1]; exact hDs), hB2, hr2, hi2, fun h => by simp at h, fun _ => ?_⟩
    rcases hs with _ | ⟨j, hs⟩
    · obtain ⟨a, b⟩ := hn2 rfl; rw [a, b, hp1, hq1]; simp
    · obtain ⟨a, b⟩ := hc2 (by simp); rw [a, b]; simp [List.getLastD]

/-! ## the end of the main loop (g56), the width pass's AST, g42 -/

/-! g35/g56 bind g19/g20 results with `match`; the kernel unfolds such a matcher (abbrev) before the enclosing def
and then evaluates g14's range test on a 2^21 literal (deep recursion).  So g35 is unfolded at function level
(`g35_fun`: both sides are lambdas, the bodies are the same term) and its matches are only met on pairs. -/
def stT (o3 : Buf) : Buf :=
  let o4 := bpush (bpush (bpush o3 (g11 5 31 0)) (g11 7 5 0)) (g4 1 7 0 16);
  let h4 := bsize o4;
  let o5 := bpush (bpush (bpush o4 (g10 10 0 1)) (g10 11 0 0)) (g13 0 (h4 + 2) (h4 + 14));
  let o6 := bpush (bpush (bpush o5 (g10 11 7 0)) (g10 6 5 16)) (g10 14 13 0);
  let o7 := bpush (bpush (bpush (bpush (bpush (bpush o6 (g4 0 7 0 28)) (g11 15 6 0)) (g3 0 15 14 0)) (g10 6 6 8))
    (g10 14 14 1)) (g10 7 7 g_901);
  let h7 := bsize o7;
  let o8 := bpush (bpush o7 (g13 0 h7 (h7 - 6))) (g10 10 0 0);
  bpush (bpush (bpush o8 (g11 1 12 0)) (g11 8 12 8)) (g2 g_103 0 0 1 0)
def stH (o : Buf) : Buf :=
  let o1 := bpush (bpush (bpush o (g10 30 12 16)) (g2 g_19 5 31 2 3)) (g2 g_19 1 31 31 3);
  let o2 := bpush (bpush (bpush (bpush o1 (g4 7 31 30 16)) (g10 10 0 g_901)) (g10 11 0 0)) (g2 g_103 0 0 1 0);
  bpush (bpush (bpush (bpush o2 (g12 1 12 0)) (g12 8 12 8)) (g10 28 10 0)) (g10 29 11 0)

theorem g35_fun : g35 = fun r o w =>
  let o1 := bpush (bpush (bpush o (g10 30 12 16)) (g2 g_19 5 31 2 3)) (g2 g_19 1 31 31 3);
  let o2 := bpush (bpush (bpush (bpush o1 (g4 7 31 30 16)) (g10 10 0 g_901)) (g10 11 0 0)) (g2 g_103 0 0 1 0);
  let o9 := bpush (bpush (bpush (bpush o2 (g12 1 12 0)) (g12 8 12 8)) (g10 28 10 0)) (g10 29 11 0);
  let (r1, o3) := g19 r o9 1 w;
  let o4 := bpush (bpush (bpush o3 (g11 5 31 0)) (g11 7 5 0)) (g4 1 7 0 16);
  let h4 := bsize o4;
  let o5 := bpush (bpush (bpush o4 (g10 10 0 1)) (g10 11 0 0)) (g13 0 (h4 + 2) (h4 + 14));
  let o6 := bpush (bpush (bpush o5 (g10 11 7 0)) (g10 6 5 16)) (g10 14 13 0);
  let o7 := bpush (bpush (bpush (bpush (bpush (bpush o6 (g4 0 7 0 28)) (g11 15 6 0)) (g3 0 15 14 0)) (g10 6 6 8))
    (g10 14 14 1)) (g10 7 7 g_901);
  let h7 := bsize o7;
  let o8 := bpush (bpush o7 (g13 0 h7 (h7 - 6))) (g10 10 0 0);
  (r1, bpush (bpush (bpush o8 (g11 1 12 0)) (g11 8 12 8)) (g2 g_103 0 0 1 0)) := by
  delta g35
  exact rfl

/-- g35: the call to main (a jal, error flag if out of range) between the start code's two parts -/
theorem g35_eq (r o : Buf) (w : UInt64) :
    g35 r o w = (if g14 (bsize (stH o)) w == 1 then r else g16 r, stT (bpush (stH o) (g13 1 (bsize (stH o)) w))) := by
  have h := congrFun (congrFun (congrFun g35_fun r) o) w
  rw [h]
  extract_lets o1 o2 o9
  rw [g19_eq]
  rfl

/-- the start code's words -/
def startW (o : Buf) (w : UInt64) : Buf := stT (bpush (stH o) (g13 1 (bsize (stH o)) w))

/-- Gen's shared pair matcher, by an equation (never by unfolding it on a g19/g20 result) -/
theorem m28 {α : Type} (p : Buf × Buf) (f : Buf → Buf → α) : g28.match_1 (fun _ => α) p f = f p.1 p.2 := by
  cases p; rfl

/-- the stop branch: after the last def, word 0 patched, the start code; any failure sets the error flag -/
theorem g56_res (r o t : Buf) (hl : r.length = 10) (h5 : bget r 5 ≠ 1) (h4 : bget r 4 ≠ 1) (hb : ¬ 16777215 < bsize o)
    (hok : bget (g56 r o t).1 4 ≠ 1) :
    bsize t ≠ 0 ∧ bget r 1 = 0 ∧ bget r 2 = 1 ∧ (g56 r o t).2 = startW (bset o 0 (g13 0 0 (bsize o))) (bget t (bsize t - 1)) := by
  unfold g56 at hok ⊢
  rw [if_neg (by simpa using h5), if_neg (by simpa using h4), if_neg hb] at hok ⊢
  extract_lets w m at hok ⊢
  have hw' : w = bsize t := rfl
  have hm : m = (if (bget r 1 == 0) = true then if (bget r 2 == 1) = true then g_1 else g_0 else g_0) := rfl
  clear_value w m
  subst hw' hm
  by_cases hw : (bsize t == 0) = true
  · rw [if_pos hw] at hok; exact absurd (g16_err _ hl) hok
  rw [if_neg hw] at hok ⊢
  by_cases h12 : bget r 1 = 0 ∧ bget r 2 = 1
  · have hm : (if (bget r 1 == 0) = true then if (bget r 2 == 1) = true then g_1 else g_0 else g_0) = 1 := by
      simp [h12.1, h12.2, g_1]
    rw [hm, if_neg (by decide)] at hok ⊢
    refine ⟨by simpa using hw, h12.1, h12.2, ?_⟩
    rw [m28 (g20 r o 0) (fun r1 o1 => g28.match_1 (fun _ => Buf × Buf) (g35 r1 o1 (bget t (bsize t - 1)))
      (fun r2 o2 => (g15 r2 5 1, o2)))]
    rw [m28 (g35 (g20 r o 0).1 (g20 r o 0).2 (bget t (bsize t - 1))) (fun r2 o2 => (g15 r2 5 1, o2))]
    rw [g20_eq, g35_eq]
    rfl
  · have hm : (if (bget r 1 == 0) = true then if (bget r 2 == 1) = true then g_1 else g_0 else g_0) = 0 := by
      by_cases h1 : bget r 1 = 0
      · have h2 : ¬ bget r 2 = 1 := fun h2 => h12 ⟨h1, h2⟩
        simp only [h1, h2, beq_self_eq_true, if_true, beq_iff_eq, if_false]; rfl
      · simp only [beq_iff_eq, h1, if_false]; rfl
    rw [hm, if_pos (by decide)] at hok
    exact absurd (g16_err _ hl) hok

/-- a stopped boundary state: the next g39 step is g56 -/
theorem G_stop {X u s} (hB : Bnd X u s) (hr0 : bget s.r 0 = X.length.toUInt64) (n : Nat) :
    G (n + 1) s = g56 s.r s.o s.t := by
  have h1 : g55 s.x s.r s.o = 1 := by
    unfold g55
    rw [if_neg (by simpa using hB.r5), if_neg (by simpa using hB.r4), if_neg (bsize_ok _ hB.ol), if_pos (by simp [hB.r6]),
      if_neg (by rw [hr0, hB.x, bsize_u]; exact Nat.lt_irrefl _)]
    rfl
  unfold G; rw [g39, h1, if_pos (by decide)]

theorem g52_x : ∀ (n : Nat) (y : Buf × (Buf × Buf)), (g52 n y).1 = y.1
  | 0, (x, (d, s)) => rfl
  | n + 1, (x, (d, s)) => by
    unfold g52; dsimp only
    split
    · rfl
    split
    · rfl
    rw [g52_x n]

theorem g53_x (x : Buf) : (g53 x).1 = x := by
  unfold g53; dsimp only
  have := g52_x 16777216 (x, (bnew, bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush bnew 1) 0) 0) 0) 0) 0) 0) 0))
  generalize g52 _ _ = p at this ⊢
  obtain ⟨_, _, _⟩ := p
  exact this

/-- **Gen soundness on success**: a nonempty g42 output is the LE bytes of: the g34 stubs, then every def's DefC code
(headers at hs, def starts T), word 0 patched to the start code, main = the last def (npw 0, nres 1) -/
theorem gen_ok (c : List UInt8) (x : Buf) (u : UInt64) (hX : x.length < 2 ^ 31) (h : g42 c x u ≠ []) :
    bget x 0 = 2 ∧ (g53 x).2 ≠ 0 ∧ ∃ hs T o, DefsC x u bnew 1 (g34 bnew) hs T x.length o ∧ hs ≠ [] ∧
      tg x (hs.getLastD 0 + 2) = 0 ∧ tg x (hs.getLastD 0 + 5) = 1 ∧
      g42 c x u = g40 16777216 c (startW (bset o 0 (g13 0 0 (bsize o))) (bget T (bsize T - 1))) 0 [] ∧
      o.length < 2 ^ 24 ∧ o.length + 32 < 2 ^ 18 := by
  unfold g42 at h ⊢
  by_cases hbig : 2147483647 < bsize x
  · rw [if_pos hbig] at h; exact absurd rfl h
  rw [if_neg hbig] at h ⊢
  by_cases h0 : ¬ (bget x 0 == 2) = true
  · rw [if_neg h0] at h; exact absurd rfl h
  rw [Classical.not_not] at h0
  rw [if_pos h0] at h ⊢
  refine ⟨by simpa using h0, ?_⟩
  have hx := g53_x x
  generalize g53 x = p at h hx ⊢
  obtain ⟨x2, w⟩ := p
  simp only at hx; subst x2
  dsimp only at h ⊢
  by_cases hw : (w == 0) = true
  · rw [if_pos hw] at h; exact absurd rfl h
  rw [if_neg hw] at h ⊢
  refine ⟨by simpa using hw, ?_⟩
  let s0 : GS := ⟨x, bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush bnew 1) 0) 0) 0) 0) 0) 0) 0) 0) u,
    g34 bnew, bnew, bnew, bnew⟩
  have hG : g39 16777216 x s0.r (g34 bnew) bnew bnew bnew = G 16777216 s0 := rfl
  rw [hG] at h ⊢
  generalize hN : G 16777216 s0 = R at h ⊢
  obtain ⟨r1, o1⟩ := R
  dsimp only at h ⊢
  by_cases he : (bget r1 4 == 1) = true
  · rw [if_pos he] at h; exact absurd rfl h
  rw [if_neg he] at h ⊢
  by_cases hz : 16777215 < bsize o1
  · rw [if_pos hz] at h; exact absurd rfl h
  rw [if_neg hz] at h ⊢
  by_cases hz2 : 262143 < bsize o1
  · rw [if_pos hz2] at h; exact absurd rfl h
  rw [if_neg hz2]
  have hx1 : 1 ≤ x.length := by
    have : bget x 0 = 2 := by simpa using h0
    rcases x with _ | ⟨a, x⟩
    · simp [bget] at this
    · simp
  have hB0 : Bnd x u s0 := {
    x := rfl
    rl := rfl
    r4 := by simp [s0, bget, bpush, bnew]
    r5 := by simp [s0, bget, bpush, bnew]
    r6 := rfl
    r8 := rfl
    r9 := rfl
    kl := by simp [s0, bnew]
    fl := by simp [s0, bnew]
    ol := by simp [s0, g34, bpush, bnew]
    tl := by simp [s0, bnew] }
  have hrun := prog_run x u hX x.length s0 1 (by omega) hB0 rfl hx1 (by simp [s0, bnew]) 16777216
    (by rw [hN]; simpa using he) (by rw [hN]; exact hz)
  obtain ⟨m, hm, s', ⟨hs, i', hD, hB', hr0', hi', hn, hc⟩, hE⟩ := hrun
  subst hi'
  rw [hN] at hE
  rcases Nat.eq_zero_or_pos (16777216 - m) with hz0 | hpos
  · exfalso; rw [hz0] at hE; unfold G at hE; rw [g39] at hE
    apply he; have := congrArg Prod.fst hE; simp only at this; rw [this, g16_err _ hB'.rl]; rfl
  rw [show 16777216 - m = (16777216 - m - 1) + 1 by omega, G_stop hB' hr0'] at hE
  have hok : bget (g56 s'.r s'.o s'.t).1 4 ≠ 1 := by rw [← hE]; simpa using he
  obtain ⟨a1, a2, a3, a4⟩ := g56_res _ _ _ hB'.rl hB'.r5 hB'.r4 (bsize_ok _ hB'.ol) hok
  have hsn : hs ≠ [] := by
    rintro rfl; obtain ⟨e, -, -⟩ := hD.nil_eq; rw [← e] at a1; exact a1 rfl
  obtain ⟨b1, b2⟩ := hc hsn
  refine ⟨hs, s'.t, s'.o, hD, hsn, by rw [← b1, a2], by rw [← b2, a3], by rw [← a4, ← hE], hB'.ol, ?_⟩
  have e1 : o1 = startW (bset s'.o 0 (g13 0 0 (bsize s'.o))) (bget s'.t (bsize s'.t - 1)) := by
    rw [← a4]; have := congrArg Prod.snd hE; simpa using this
  have hl : o1.length = s'.o.length + 32 := by
    rw [e1]; simp [startW, stT, stH, bpush, BufL.length_bset]
  have := hB'.ol
  rw [bsize_u, UInt64.lt_iff_toNat_lt, u_toNat _ (by omega)] at hz2
  simp at hz2; omega

/-- the same for g41 (κ = g_999) -/
theorem gen41_ok (c : List UInt8) (x : Buf) (hX : x.length < 2 ^ 31) (h : g41 c x ≠ []) :
    bget x 0 = 2 ∧ (g53 x).2 ≠ 0 ∧ ∃ hs T o, DefsC x g_999 bnew 1 (g34 bnew) hs T x.length o ∧ hs ≠ [] ∧
      tg x (hs.getLastD 0 + 2) = 0 ∧ tg x (hs.getLastD 0 + 5) = 1 ∧
      g41 c x = g40 16777216 c (startW (bset o 0 (g13 0 0 (bsize o))) (bget T (bsize T - 1))) 0 [] ∧
      o.length < 2 ^ 24 ∧ o.length + 32 < 2 ^ 18 :=
  gen_ok c x g_999 hX h

end GenRef
