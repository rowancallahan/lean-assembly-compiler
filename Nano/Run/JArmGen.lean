/- L8: `g42` (Gen's top function) is `g40` (the byte output) of `e70` (Gen's word buffer, `bnew` on reject), and
`e70`'s buffer has fewer than 2^18 words (the argument of `gen_ok`, GenTop.lean, redone on `e70`). -/
import Nano.Codegen.JArmTop
import Nano.Codegen.GenTop
namespace NanoMain
open C CallProbe GenRef

theorem g40_nil (n : Nat) (c : List UInt8) : C.g40 n c bnew 0 [] = [] := by
  cases n with
  | zero => rfl
  | succ n => rw [C.g40, if_neg (by decide)]

/-- (L8a) `g42` = the byte output of `e70` -/
theorem g42_e70 (c : List UInt8) (x : Buf) (u : UInt64) : C.g42 c x u = C.g40 16777216 c (C.e70 x u) 0 [] := by
  unfold C.g42 C.e70
  by_cases hbig : 2147483647 < bsize x
  · rw [if_pos hbig, if_pos hbig, g40_nil]
  rw [if_neg hbig, if_neg hbig]
  by_cases h0 : (bget x 0 == 2) = true
  · rw [if_pos h0, if_pos h0]
    generalize g53 x = p
    obtain ⟨x2, w⟩ := p
    dsimp only
    by_cases hw : (w == 0) = true
    · rw [if_pos hw, if_pos hw, g40_nil]
    rw [if_neg hw, if_neg hw]
    generalize g39 16777216 x2 _ (g34 bnew) bnew bnew bnew = R
    obtain ⟨r1, o1⟩ := R
    dsimp only
    by_cases he : (bget r1 4 == 1) = true
    · rw [if_pos he, if_pos he, g40_nil]
    rw [if_neg he, if_neg he]
    by_cases hz : 16777215 < bsize o1
    · rw [if_pos hz, if_pos hz, g40_nil]
    rw [if_neg hz, if_neg hz]
    by_cases hz2 : 262143 < bsize o1
    · rw [if_pos hz2, if_pos hz2, g40_nil]
    rw [if_neg hz2, if_neg hz2]
  · rw [if_neg h0, if_neg h0, g40_nil]

/-- (L8b) `e70`'s word buffer is short (list length, not just `bsize`) -/
theorem e70_len (x : Buf) (u : UInt64) (hX : x.length < 2 ^ 31) : (C.e70 x u).length < 2 ^ 18 := by
  unfold C.e70
  by_cases hbig : 2147483647 < bsize x
  · rw [if_pos hbig]; decide
  rw [if_neg hbig]
  by_cases h0 : ¬ (bget x 0 == 2) = true
  · rw [if_neg h0]; decide
  rw [Classical.not_not] at h0
  rw [if_pos h0]
  have hx := g53_x x
  generalize g53 x = p at hx ⊢
  obtain ⟨x2, w⟩ := p
  simp only at hx; subst x2
  dsimp only
  by_cases hw : (w == 0) = true
  · rw [if_pos hw]; decide
  rw [if_neg hw]
  let s0 : GS := ⟨x, bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush bnew 1) 0) 0) 0) 0) 0) 0) 0) 0) u,
    g34 bnew, bnew, bnew, bnew⟩
  have hG : g39 16777216 x s0.r (g34 bnew) bnew bnew bnew = G 16777216 s0 := rfl
  rw [hG]
  generalize hN : G 16777216 s0 = R
  obtain ⟨r1, o1⟩ := R
  dsimp only
  by_cases he : (bget r1 4 == 1) = true
  · rw [if_pos he]; decide
  rw [if_neg he]
  by_cases hz : 16777215 < bsize o1
  · rw [if_pos hz]; decide
  rw [if_neg hz]
  by_cases hz2 : 262143 < bsize o1
  · rw [if_pos hz2]; decide
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
  have e1 : o1 = startW (bset s'.o 0 (g13 0 0 (bsize s'.o))) (bget s'.t (bsize s'.t - 1)) := by
    rw [← a4]; have := congrArg Prod.snd hE; simpa using this
  have hl : o1.length = s'.o.length + 32 := by
    rw [e1]; simp [startW, stT, stH, bpush, BufL.length_bset]
  have := hB'.ol
  rw [bsize_u, UInt64.lt_iff_toNat_lt, u_toNat _ (by omega)] at hz2
  simp at hz2; omega

end NanoMain

/-! `e70_len` without the length hypothesis: a fuel-based growth bound.  Every `g39` step (`g54`: `g38` or `g37`) adds at
most 1280 words to the code buffer (the worst case is `g25 256`), the stop step `g56` at most 32, so `g39 2^24`'s buffer has
under 2^35 words whatever `x` is (even if `bsize x` wrapped); its `bsize` is then exact and `e70`'s last test bounds it. -/
namespace NanoMain
open C CallProbe GenRef

private theorem l19 (r o : Buf) (d b : UInt64) : (g19 r o d b).2.length = o.length + 1 := by rw [g19_eq]; simp [bpush]
private theorem l20 (r o : Buf) (p : UInt64) : (g20 r o p).2.length = o.length := by rw [g20_eq]; simp [bset]
private theorem l30 (o : Buf) (k : UInt64) : (g30 o k).length = o.length + 3 := by simp [g30, bpush]
private theorem l31 (o : Buf) (p : UInt64) : (g31 o p).length = o.length + 5 := by simp [g31, g30, bpush]
private theorem lpush (o : Buf) (v : UInt64) : (bpush o v).length = o.length + 1 := by simp [bpush]

private theorem l28 : ∀ (n : Nat) (c : UInt64) (f r o : Buf), (g28 n c (f, (r, o))).2.2.length = o.length
  | 0, c, f, r, o => rfl
  | n + 1, c, f, r, o => by
    unfold g28; split
    · rfl
    · dsimp only
      have h20 := l20 r o (bget f (c - 1))
      generalize g20 r o (bget f (c - 1)) = p at h20 ⊢
      obtain ⟨r', o'⟩ := p
      rw [l28 n]; exact h20

local macro "ifc " c:term " => " t:tactic : tactic =>
  `(tactic| (by_cases hh : $c; (case pos => (rw [if_pos hh]; $t)); rw [if_neg hh]; clear hh))
local macro "le0" : tactic => `(tactic| exact Nat.le_add_right _ _)

private theorem l36 (x r o k : Buf) (y : UInt64) : (g36 x r o k y).2.1.length ≤ o.length + 1280 := by
  unfold g36
  extract_lets i n c0 c z b a e v q7 q8 h o1
  clear_value c z a
  ifc (a == 0) = true => le0
  by_cases hy : (y == 1) = true
  · rw [if_pos hy]
    ifc (z == 0) = true => le0
    ifc (c == 10) = true => le0
    ifc (c == 4) = true => le0
    ifc (e == 1) = true => le0
    le0
  rw [if_neg hy]
  ifc (c == 1) = true => (dsimp only; rw [g21_len]; exact Nat.le_trans (Nat.add_le_add_right (g23_len _ _ _) 4) (by omega))
  by_cases h2 : (c == 2) = true
  · rw [if_pos h2]
    ifc (e == 1) = true => le0
    exact Nat.le_trans (g25_len _ _ _ _ _) (by omega)
  rw [if_neg h2]
  ifc (c == 3) = true => le0
  ifc (c == 4) = true => le0
  by_cases h5 : (c == 5) = true
  · rw [if_pos h5]
    ifc (e == 1) = true => le0
    le0
  rw [if_neg h5]
  by_cases h6 : (c == 6) = true
  · rw [if_pos h6]
    ifc b < 251 => le0
    le0
  rw [if_neg h6]
  by_cases h7 : (c == 7) = true
  · rw [if_pos h7]
    ifc q7 < 251 => le0
    le0
  rw [if_neg h7]
  ifc (c == 8) = true => le0
  by_cases h9 : (c == 9) = true
  · rw [if_pos h9]
    ifc (n == 1) = true => (simp +zetaDelta only [lpush]; omega)
    le0
  rw [if_neg h9]
  le0

private theorem l37 (x r o k t f : Buf) : (g37 x r o k t f).2.1.length ≤ o.length + 1280 := by
  unfold g37
  extract_lets n c z y r1
  by_cases h1 : (c == 1) = true
  · rw [if_pos h1]
    generalize hp : g36 x r1 o k z = p
    have hl := l36 x r1 o k z; rw [hp] at hl
    obtain ⟨r2, o2, k2⟩ := p; exact hl
  rw [if_neg h1]
  by_cases h2 : (c == 2) = true
  · rw [if_pos h2]
    simp +zetaDelta only [l31]; omega
  rw [if_neg h2]
  by_cases h3 : (c == 3) = true
  · rw [if_pos h3]
    simp +zetaDelta only [lpush, l30]; omega
  rw [if_neg h3]
  by_cases h4 : (c == 4) = true
  · rw [if_pos h4]
    generalize hp : g20 r1 (bpush o 0) z = p
    have hl := l20 r1 (bpush o 0) z; rw [hp, lpush] at hl
    obtain ⟨r2, o2⟩ := p; dsimp only at hl ⊢; omega
  rw [if_neg h4]
  by_cases h5 : (c == 5) = true
  · rw [if_pos h5]
    generalize hp : g20 r1 o z = p
    have hl := l20 r1 o z; rw [hp] at hl
    obtain ⟨r2, o2⟩ := p; dsimp only at hl ⊢; omega
  rw [if_neg h5]
  by_cases h6 : (c == 6) = true
  · rw [if_pos h6]
    dsimp only; exact Nat.le_trans (g26_len _ _ _ _ _) (by omega)
  rw [if_neg h6]
  by_cases h7 : (c == 7) = true
  · rw [if_pos h7]
    generalize hp : (if z < bsize t then g19 r1 o 1 (bget t z) else (g16 r1, o)) = p
    have hl : p.2.length ≤ o.length + 1 := by
      rw [← hp]; split
      · rw [l19]; exact Nat.le_refl _
      · exact Nat.le_add_right _ _
    obtain ⟨r2, o2⟩ := p; dsimp only at hl ⊢; omega
  rw [if_neg h7]
  by_cases h8 : (c == 8) = true
  · rw [if_pos h8]
    dsimp only; exact Nat.le_trans (g32_len _ _ _) (by omega)
  rw [if_neg h8]
  by_cases h9 : (c == 9) = true
  · rw [if_pos h9]
    split
    · exact Nat.le_add_right _ _
    · simp only [lpush]; omega
  rw [if_neg h9]
  by_cases h10 : (c == 10) = true
  · rw [if_pos h10]
    generalize hp : g19 r1 _ 0 _ = p
    have hl : p.2.length ≤ o.length + 769 := by
      rw [← hp, l19]; exact Nat.le_trans (Nat.add_le_add_right (g26_len _ _ _ _ _) 1) (by omega)
    obtain ⟨r2, o2⟩ := p; dsimp only at hl ⊢; omega
  rw [if_neg h10]
  by_cases h11 : (c == 11) = true
  · rw [if_pos h11]
    generalize hp : g20 r1 o z = p
    have hl := l20 r1 o z; rw [hp] at hl
    obtain ⟨r2, o2⟩ := p; dsimp only at hl ⊢; simp only [lpush]; omega
  rw [if_neg h11]
  generalize hp : g28 65536 _ (f, _, o) = p
  have hl : p.2.2.length = o.length := by rw [← hp]; exact l28 _ _ _ _ _
  obtain ⟨f1, r3, o3⟩ := p
  dsimp only at hl ⊢
  refine Nat.le_trans (g29_len _ _ _ _ _) ?_
  simp only [lpush]; omega

private theorem l38 (x r o k t : Buf) : (g38 x r o k t).2.1.length ≤ o.length + 1280 := by
  unfold g38
  extract_lets i d p s q v z0 z1 z2 z3 z4
  split
  · exact Nat.le_add_right _ _
  · simp +zetaDelta [g22, bpush]

private theorem l54 (x r o k t f : Buf) : (g54 x r o k t f).2.1.length ≤ o.length + 1280 := by
  unfold g54; split
  · generalize hp : g38 x r o k t = p
    have hl := l38 x r o k t; rw [hp] at hl
    obtain ⟨r1, o1, k1, t1⟩ := p; exact hl
  · generalize hp : g37 x r o k t f = p
    have hl := l37 x r o k t f; rw [hp] at hl
    obtain ⟨r1, o1, k1, f1⟩ := p; exact hl

private theorem l56 (r o t : Buf) : (g56 r o t).2.length ≤ o.length + 32 := by
  unfold g56
  by_cases h5 : (bget r 5 == 1) = true
  · rw [if_pos h5]; exact Nat.le_add_right _ _
  rw [if_neg h5]
  by_cases h4 : (bget r 4 == 1) = true
  · rw [if_pos h4]; exact Nat.le_add_right _ _
  rw [if_neg h4]
  by_cases hb : 16777215 < bsize o
  · rw [if_pos hb]; exact Nat.le_add_right _ _
  rw [if_neg hb]
  extract_lets w m
  by_cases hw : (w == 0) = true
  · rw [if_pos hw]; exact Nat.le_add_right _ _
  rw [if_neg hw]
  by_cases hm : (m == 0) = true
  · rw [if_pos hm]; exact Nat.le_add_right _ _
  rw [if_neg hm]
  generalize hp : g20 r o 0 = p
  have hl := l20 r o 0; rw [hp] at hl
  obtain ⟨r1, o1⟩ := p
  dsimp only at hl ⊢
  generalize hq : g35 r1 o1 _ = q
  have hl2 : q.2.length = o1.length + 32 := by rw [← hq, g35_eq]; simp [stT, stH, bpush]
  obtain ⟨r2, o2⟩ := q
  dsimp only at hl2 ⊢; omega

private theorem l39 : ∀ (n : Nat) (x r o k t f : Buf), (g39 n x r o k t f).2.length ≤ o.length + 1280 * n + 32
  | 0, x, r, o, k, t, f => by unfold g39; exact Nat.le_add_right _ _
  | n + 1, x, r, o, k, t, f => by
    unfold g39; split
    · exact Nat.le_trans (l56 _ _ _) (by omega)
    · have hl := l54 x r o k t f
      generalize g54 x r o k t f = p at hl ⊢
      obtain ⟨r1, o1, k1, t1, f1⟩ := p
      dsimp only at hl ⊢
      exact Nat.le_trans (l39 n _ _ _ _ _ _) (by omega)

/-- (L8b′) `e70`'s word buffer is short, with NO length hypothesis on the AST buffer -/
theorem e70_len64 (x : Buf) (u : UInt64) : (C.e70 x u).length < 2 ^ 18 := by
  unfold C.e70
  by_cases hbig : 2147483647 < bsize x
  · rw [if_pos hbig]; decide
  rw [if_neg hbig]
  by_cases h0 : ¬ (bget x 0 == 2) = true
  · rw [if_neg h0]; decide
  rw [Classical.not_not] at h0
  rw [if_pos h0]
  generalize g53 x = p
  obtain ⟨x2, w⟩ := p
  dsimp only
  by_cases hw : (w == 0) = true
  · rw [if_pos hw]; decide
  rw [if_neg hw]
  have hl := l39 16777216 x2 (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush bnew 1) 0) 0) 0) 0) 0) 0) 0) 0) u)
    (g34 bnew) bnew bnew bnew
  generalize g39 16777216 x2 _ (g34 bnew) bnew bnew bnew = R at hl
  obtain ⟨r1, o1⟩ := R
  dsimp only at hl ⊢
  by_cases he : (bget r1 4 == 1) = true
  · rw [if_pos he]; decide
  rw [if_neg he]
  by_cases hz : 16777215 < bsize o1
  · rw [if_pos hz]; decide
  rw [if_neg hz]
  by_cases hz2 : 262143 < bsize o1
  · rw [if_pos hz2]; decide
  rw [if_neg hz2]
  have h34 : (g34 bnew).length = 11 := by simp [g34, bpush, bnew]
  rw [h34] at hl
  rw [bsize_u, UInt64.lt_iff_toNat_lt, u_toNat _ (by omega)] at hz2
  simp at hz2; omega

end NanoMain
