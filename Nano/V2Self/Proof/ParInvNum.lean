/- Nano/V2Self/Proof/ParInvNum: the numeral reader `v87` (box C): the machine's OR of the 8 shifted byte words is ParSpec's
`bytesVal` (byte words < 256 are part of `TokAt`), and the value is below 2^64. -/
import Nano.V2Self.Proof.ParInvLetSemi
namespace ParInv
open C BufL ParSpec ParRun

theorem or_step (acc b : UInt64) (k : Nat) (sh : UInt64) (hsh : sh.toNat = 8 * k) (hk : k ≤ 7) (ha : acc.toNat < 2 ^ (8 * k))
    (hb : b.toNat < 256) : (acc ||| (b <<< sh)).toNat = acc.toNat + 2 ^ (8 * k) * b.toNat := by
  have e1 : (sh.toNat % 64) = 8 * k := by rw [hsh]; omega
  have p8 : 2 ^ (8 * k) * b.toNat < 2 ^ 64 := by
    have : 2 ^ (8 * k) * b.toNat < 2 ^ (8 * k) * 256 := Nat.mul_lt_mul_of_pos_left hb (Nat.two_pow_pos _)
    have h2 : 2 ^ (8 * k) * 256 = 2 ^ (8 * k + 8) := by rw [Nat.pow_add]
    have h3 : 2 ^ (8 * k + 8) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, e1, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by rw [Nat.mul_comm]; exact p8),
    Nat.or_comm, Nat.mul_comm b.toNat, ← Nat.two_pow_add_eq_or_of_lt ha]
  omega

theorem v87_word (b0 b1 b2 b3 b4 b5 b6 b7 : UInt64) (h0 : b0.toNat < 256) (h1 : b1.toNat < 256) (h2 : b2.toNat < 256)
    (h3 : b3.toNat < 256) (h4 : b4.toNat < 256) (h5 : b5.toNat < 256) (h6 : b6.toNat < 256) (h7 : b7.toNat < 256) :
    (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)).toNat =
      bytesVal ([b0, b1, b2, b3, b4, b5, b6, b7].map UInt64.toNat) := by
  have s1 := or_step b0 b1 1 8 rfl (by decide) (by simpa using h0) h1
  have s2 := or_step (b0 ||| (b1 <<< 8)) b2 2 16 rfl (by decide) (by rw [s1]; omega) h2
  have s3 := or_step (b0 ||| (b1 <<< 8) ||| (b2 <<< 16)) b3 3 24 rfl (by decide) (by rw [s2, s1]; omega) h3
  have s4 := or_step (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)) b4 4 32 rfl (by decide) (by rw [s3, s2, s1]; omega) h4
  have s5 := or_step (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32)) b5 5 40 rfl (by decide)
    (by rw [s4, s3, s2, s1]; omega) h5
  have s6 := or_step (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40)) b6 6 48 rfl (by decide)
    (by rw [s5, s4, s3, s2, s1]; omega) h6
  have s7 := or_step (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48)) b7 7 56 rfl
    (by decide) (by rw [s6, s5, s4, s3, s2, s1]; omega) h7
  rw [s7, s6, s5, s4, s3, s2, s1]
  simp [bytesVal]; omega

theorem TokAt.num_inv {h : Buf} {p : UInt64} {v : Nat} {rest : List Tok} (r : TokAt h p (.num v :: rest)) :
    ∃ bs : List UInt64, p < bget h 7 ∧ bget h (d11 + p) = 5 ∧ bs.length = 8 ∧
      (∀ i, i < 8 → bget h (d11 + (p + 1 + i.toUInt64)) = bs.getD i 0) ∧ (∀ b ∈ bs, b.toNat < 256) ∧
      v = bytesVal (bs.map UInt64.toNat) ∧ TokAt h (p + 9) rest := by
  cases r with
  | num bs a b c d f x => exact ⟨bs, a, b, c, d, f, rfl, x⟩

/-- **numerals**: `v87` stores the token's value (< 2^64) in h[31] -/
theorem v87_tok {h : Buf} {p : UInt64} {v : Nat} {rest : List Tok} (r : TokAt h p (.num v :: rest)) (hn : (bget h 7).toNat < 2 ^ 32) :
    v87 h p = bset h 31 v.toUInt64 ∧ v < 2 ^ 64 ∧ TokAt h (p + 9) rest ∧ bget h (d11 + p) = 5 := by
  obtain ⟨bs, hp, h5, hl, hc, hb, hv, tr⟩ := r.num_inv
  have hp' := UInt64.lt_iff_toNat_lt.mp hp
  match bs, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    have cell : ∀ (i : Nat) (k : UInt64), i < 8 → k.toNat = i + 1 → bget h (d11 + (p + k)) = [b0, b1, b2, b3, b4, b5, b6, b7].getD i 0 := by
      intro i k hi hk
      rw [← hc i hi]; congr 2
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, hk]; simp; omega
    have w := v87_word b0 b1 b2 b3 b4 b5 b6 b7 (hb _ (by simp)) (hb _ (by simp)) (hb _ (by simp)) (hb _ (by simp))
      (hb _ (by simp)) (hb _ (by simp)) (hb _ (by simp)) (hb _ (by simp))
    rw [← hv] at w
    have vl : v < 2 ^ 64 := by rw [← w]; exact UInt64.toNat_lt _
    refine ⟨?_, vl, tr, h5⟩
    simp only [v87]
    rw [cell 0 1 (by decide) rfl, cell 1 2 (by decide) rfl, cell 2 3 (by decide) rfl, cell 3 4 (by decide) rfl,
      cell 4 5 (by decide) rfl, cell 5 6 (by decide) rfl, cell 6 7 (by decide) rfl, cell 7 8 (by decide) rfl]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    apply UInt64.toNat_inj.mp
    rw [w]; simp; omega

end ParInv
