/- Nano/V2Self/Proof/Own/OwnP27: buffer loops of the def level: `o37` (append a range), `o40` (pad), `o22` mode 5 (clamp
kinds to ≤ 2). -/
import Nano.V2Self.Proof.Own.OwnP26
namespace OwnP
open C OwnSpec ParSpec

/-- the word `o37` appends for `e` -/
def g37 (c e : UInt64) : UInt64 := if c == 1 then (if e == 3 then 1 else 0) else e

theorem o37_eq : ∀ (m : Nat) (t y : Buf) (j n : Nat) (c : UInt64), n < 2 ^ 64 → n - j ≤ m → j ≤ n →
    o37 m t y (u j) (u n) c = t ++ (List.range' j (n - j)).map fun q => g37 c (y.getD q 0)
  | 0, t, y, j, n, c, hn, hm, _ => by rw [show n - j = 0 by omega]; simp [o37]
  | m + 1, t, y, j, n, c, hn, hm, hjn => by
    rw [o37]
    by_cases hj : j < n
    · rw [if_pos ((u_lt (by omega) hn).mpr hj), show u j + 1 = u (j + 1) from u_add j 1,
        o37_eq m _ y (j + 1) n c hn (by omega) (by omega)]
      rw [show n - j = (n - (j + 1)) + 1 by omega, List.range'_succ]
      simp only [bpush, bget_u y (show j < 2 ^ 64 by omega), g37, List.map_cons, List.append_assoc, List.singleton_append]
    · rw [if_neg (fun h => hj ((u_lt (by omega) hn).mp h)), show n - j = 0 by omega]; simp

theorem o40_ge : ∀ (m : Nat) (b : Buf) (k : Nat), k < 2 ^ 64 → b.length < 2 ^ 64 → k - b.length ≤ m →
    k ≤ (o40 m b (u k)).length ∧ (o40 m b (u k)).length ≤ max b.length k ∧ ∀ q < b.length, (o40 m b (u k)).getD q 0 = b.getD q 0
  | 0, b, k, hk, hb, hm => by rw [o40]; exact ⟨by omega, by omega, fun _ _ => rfl⟩
  | m + 1, b, k, hk, hb, hm => by
    rw [o40]
    by_cases h : b.length < k
    · rw [if_pos (by rw [bsize_u]; exact (u_lt hb hk).mpr h)]
      have ih := o40_ge m (bpush b 0) k hk (by simp [bpush]; omega) (by simp [bpush]; omega)
      simp only [bpush, List.length_append, List.length_singleton] at ih ⊢
      refine ⟨ih.1, by omega, fun q hq => ?_⟩
      rw [ih.2.2 q (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hq]
    · rw [if_neg (by rw [bsize_u]; exact fun e => h ((u_lt hb hk).mp e))]; exact ⟨by omega, by omega, fun _ _ => rfl⟩

/-- the clamp of `o22` mode 5 -/
def cl (x : UInt64) : UInt64 := if x < 2 then x else 2

theorem o22_cl : ∀ (m : Nat) (f : Buf) (j n : Nat), n ≤ f.length → f.length < 2 ^ 62 → n - j ≤ m → j ≤ n → n < 2 ^ 40 →
    (o22 m f (u 0) (u 0) (u j) (u n) (u 5)).length = f.length ∧
    ∀ k, (o22 m f (u 0) (u 0) (u j) (u n) (u 5)).getD k 0 = if j ≤ k ∧ k < n then cl (f.getD k 0) else f.getD k 0 := by
  intro m; induction m with
  | zero => intro f j n _ _ hm _ _; rw [o22]; exact ⟨rfl, fun k => by rw [if_neg (by omega)]⟩
  | succ m ih =>
    intro f j n hl hl2 hm hjn hn
    rw [o22]
    by_cases hj : j < n
    · simp only [u_lt' (show j < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega), hj, if_true, u_add, Nat.zero_add]
      simp only [show (u 5 == 0) = false from rfl, show (u 5 == 1) = false from rfl, show (u 5 == 2) = false from rfl,
        show (u 5 == 3) = false from rfl, show (u 5 == 4) = false from rfl, Bool.false_eq_true, if_false]
      rw [show (1 : UInt64) = u 1 from rfl, u_add, bset_u f (by omega), bget_u f (by omega)]
      have := ih (f.set j (if f.getD j 0 < 2 then f.getD j 0 else 2)) (j + 1) n (by simp; omega) (by simp; omega) (by omega) (by omega) hn
      refine ⟨by rw [this.1]; simp, fun k => ?_⟩
      rw [this.2]; simp only [getD_set]
      by_cases hk : k = j
      · subst hk
        simp only [show ¬ k + 1 ≤ k by omega, false_and, if_false, true_and, show k < f.length by omega, if_true,
          Nat.le_refl, hj, and_self]; rfl
      · by_cases hk2 : j + 1 ≤ k ∧ k < n
        · simp only [hk2, if_true, show ¬ (j = k ∧ j < f.length) by omega, if_false, show j ≤ k ∧ k < n by omega]
        · simp only [hk2, if_false, show ¬ (j = k ∧ j < f.length) by omega, show ¬ (j ≤ k ∧ k < n) by omega]
    · simp only [u_lt' (show j < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega), hj, if_false]
      exact ⟨trivial, fun k => by rw [if_neg (by omega)]⟩

theorem cl_le (x : UInt64) : (cl x).toNat ≤ 2 := by
  unfold cl; split
  · rename_i h; have := UInt64.lt_iff_toNat_lt.mp h; simp at this; omega
  · exact Nat.le_refl _

end OwnP
