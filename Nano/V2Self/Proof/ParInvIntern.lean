/- Nano/V2Self/Proof/ParInvIntern: SHAPE INTERNING `v10` at cell level (box G; used by task 63 `tyPair` and the tuple / pair handlers).
The pair table (rows of 3 words at d7 + 8192 + 3j: left code, right code, width; h[26] = number of rows) is scanned from row `j`:
`v10_scan`: the result is `h[25] := i + 5` for the FIRST row `i ≥ j` equal to `(x, y)` (status 0 if its width is ≥ 2^20), or, when there is none, the allocation
step at row h[26] (`v10 1 g x y h[26]`: reject Nat components, capacity check, new row, h[26] + 1, h[25] := h[26] + 5). -/
import Nano.V2Self.C.Par1
import Nano.V2Self.Proof.BufL
namespace ParInv
open C BufL

/-- row `i` of the pair table is `(x, y)` -/
def PairRow (g : Buf) (x y : UInt64) (i : Nat) : Prop :=
  bget g (d7 + 8192 + 3 * i.toUInt64) = x ∧ bget g (d7 + 8192 + 3 * i.toUInt64 + 1) = y

theorem v10_scan (g : Buf) (x y : UInt64) (n : Nat) (hn : bget g 26 = n.toUInt64) (hn2 : n < 2 ^ 32) :
    ∀ (k N j : Nat), j + k = n → k < N →
      (∃ i, j ≤ i ∧ i < n ∧ PairRow g x y i ∧ (∀ i', j ≤ i' → i' < i → ¬ PairRow g x y i') ∧
        v10 N g x y j.toUInt64 = if (1048575 : UInt64) < bget g (d7 + 8192 + 3 * i.toUInt64 + 2) then bset g 0 0
          else bset g 25 (i.toUInt64 + 5)) ∨
      ((∀ i, j ≤ i → i < n → ¬ PairRow g x y i) ∧ v10 N g x y j.toUInt64 = v10 1 g x y n.toUInt64) := by
  intro k
  induction k with
  | zero =>
    intro N j hj hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have : j = n := by omega
    subst this
    refine Or.inr ⟨fun i a b => absurd a (by omega), ?_⟩
    rw [v10, v10]; simp [hn]
  | succ k ih =>
    intro N j hj hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have hne : (j.toUInt64 == bget g 26) = false := by
      rw [hn, beq_eq_false_iff_ne]; intro q
      have := congrArg UInt64.toNat q
      simp [Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)] at this
      omega
    have e1 : j.toUInt64 + 1 = (j + 1).toUInt64 := by simp
    by_cases hm : PairRow g x y j
    · refine Or.inl ⟨j, Nat.le_refl _, by omega, hm, fun i' a b => absurd a (by omega), ?_⟩
      rw [v10]; simp [hne, hm.1, hm.2]
    · have step : v10 (N' + 1) g x y j.toUInt64 = v10 N' g x y (j + 1).toUInt64 := by
        rw [v10]; simp only [hne]
        by_cases a1 : bget g (d7 + 8192 + 3 * j.toUInt64) = x
        · have a2 : ¬ bget g (d7 + 8192 + 3 * j.toUInt64 + 1) = y := fun q => hm ⟨a1, q⟩
          simp only [a1, a2, beq_self_eq_true, if_true, if_false, beq_iff_eq, Bool.false_eq_true]
          rw [e1]
        · simp only [a1, if_false, beq_iff_eq, Bool.false_eq_true]
          rw [e1]
      rcases ih N' (j + 1) (by omega) (by omega) with ⟨i, h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩
      · refine Or.inl ⟨i, by omega, h2, h3, fun i' a b => ?_, by rw [step, h5]⟩
        by_cases e : i' = j
        · subst e; exact hm
        · exact h4 i' (by omega) b
      · refine Or.inr ⟨fun i a b => ?_, by rw [step, h2]⟩
        by_cases e : i = j
        · subst e; exact hm
        · exact h1 i (by omega) b

end ParInv
