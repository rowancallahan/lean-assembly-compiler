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
