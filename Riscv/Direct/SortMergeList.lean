/- Bottom-up merge sort, pure list level (no machine): one pass `runs w S 0` merges neighbouring runs of
width `w`; if every aligned `w`-chunk of `S` is sorted (`CS w S`), every aligned `2w`-chunk of the result is
sorted, and the result is a permutation of `S`.  Generic in the order `le` (total, transitive). -/

namespace Proven.MS

variable {α : Type} (le : α → α → Bool)

/-- merge the runs `[i, i+w)` and `[i+w, i+2w)`, then the runs from `i + 2w` on -/
def runs (w : Nat) (S : List α) (i : Nat) : List α :=
  if i < S.length ∧ 0 < w then
    ((S.drop i).take w).merge ((S.drop (i + w)).take w) le ++ runs w S (i + 2 * w)
  else []
termination_by S.length - i
decreasing_by omega

/-- every aligned chunk of width `w` is sorted -/
def CS (w : Nat) (S : List α) : Prop := ∀ j, ((S.drop (j * w)).take w).Pairwise (fun a b => le a b)

theorem runs_step {w : Nat} {S : List α} {i : Nat} (hi : i < S.length) (hw : 0 < w) :
    runs le w S i = ((S.drop i).take w).merge ((S.drop (i + w)).take w) le ++ runs le w S (i + 2 * w) := by
  rw [runs, if_pos ⟨hi, hw⟩]

theorem runs_end {w : Nat} {S : List α} {i : Nat} (hi : S.length ≤ i) : runs le w S i = [] := by
  rw [runs, if_neg (by omega)]

theorem runs_perm {w : Nat} (hw : 0 < w) (S : List α) (i : Nat) : (runs le w S i).Perm (S.drop i) := by
  induction h : S.length - i using Nat.strongRecOn generalizing i with
  | ind n ih =>
    by_cases hi : i < S.length
    · rw [runs_step le hi hw]
      refine (List.Perm.append (List.merge_perm_append le) (ih _ (by omega) (i + 2 * w) rfl)).trans ?_
      rw [List.append_assoc, show i + 2 * w = (i + w) + w by omega, ← List.drop_drop (i := w) (j := i + w),
        List.take_append_drop, ← List.drop_drop (i := w) (j := i), List.take_append_drop]
    · rw [runs_end le (by omega), List.drop_of_length_le (by omega)]

theorem runs_length {w : Nat} (hw : 0 < w) (S : List α) (i : Nat) : (runs le w S i).length = S.length - i := by
  rw [(runs_perm le hw S i).length_eq, List.length_drop]

theorem CS_one (S : List α) : CS le 1 S := fun j => by
  cases h : (S.drop (j * 1)) with
  | nil => simp
  | cons a t => simp

theorem CS_sorted {w : Nat} {S : List α} (h : CS le w S) (hw : S.length ≤ w) : S.Pairwise (fun a b => le a b) := by
  have := h 0; rwa [Nat.zero_mul, List.drop_zero, List.take_of_length_le hw] at this

theorem CS_append {m : Nat} {A B : List α} (hA : A.Pairwise (fun a b => le a b))
    (hl : A.length = m ∨ (B = [] ∧ A.length ≤ m)) (hB : CS le m B) : CS le m (A ++ B) := by
  intro j
  cases j with
  | zero =>
    rw [Nat.zero_mul, List.drop_zero]
    rcases hl with hl | ⟨rfl, hl⟩
    · rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]; exact hA
    · rw [List.append_nil, List.take_of_length_le hl]; exact hA
  | succ j =>
    rcases hl with hl | ⟨rfl, hl⟩
    · rw [Nat.succ_mul, Nat.add_comm, ← hl, ← List.drop_drop, List.drop_left]
      rw [hl]; exact hB j
    · rw [List.append_nil, List.drop_of_length_le (by rw [Nat.succ_mul]; omega)]; simp

theorem CS_drop {w : Nat} {S : List α} (h : CS le w S) (m : Nat) : CS le w (S.drop (m * w)) := fun j => by
  rw [List.drop_drop, ← Nat.add_mul]; exact h (m + j)

/-- one pass doubles the sorted chunk width -/
theorem runs_CS (trans : ∀ (a b c : α), le a b → le b c → le a c) (total : ∀ (a b : α), le a b || le b a)
    {w : Nat} (hw : 0 < w) {S : List α} (h : CS le w S) (m : Nat) : CS le (2 * w) (runs le w S (m * (2 * w))) := by
  induction hn : S.length - m * (2 * w) using Nat.strongRecOn generalizing m with
  | ind n ih =>
    by_cases hi : m * (2 * w) < S.length
    · rw [runs_step le hi hw]
      have e1 : m * (2 * w) = (2 * m) * w := by rw [Nat.mul_assoc, Nat.mul_left_comm m 2 w]
      have e2 : m * (2 * w) + w = (2 * m + 1) * w := by rw [e1, Nat.add_mul, Nat.one_mul]
      have e3 : m * (2 * w) + 2 * w = (m + 1) * (2 * w) := (Nat.succ_mul m (2 * w)).symm
      refine CS_append le (List.pairwise_merge trans total _ _ (by rw [e1]; exact h _) (by rw [e2]; exact h _))
        ?_ (by rw [e3]; exact ih _ (by rw [← e3]; omega) (m + 1) rfl)
      by_cases hle : m * (2 * w) + 2 * w ≤ S.length
      · left; simp only [List.length_merge, List.length_take, List.length_drop]; omega
      · right; refine ⟨runs_end le (by omega), ?_⟩
        simp only [List.length_merge, List.length_take, List.length_drop]; omega
    · rw [runs_end le (by omega)]; intro j; simp

end Proven.MS
