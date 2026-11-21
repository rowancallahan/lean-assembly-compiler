/- Nano/Parser/ParInvFin: the ACCEPTANCE TAIL of `v99` (parser lead): the output copy `v98` and the post-checks of `fin`.
`fin ts 1 h ≠ []` gives: status 2, at least one def, the main-def cells (`MainCells`), and the output = the heap from `d11 + |ts| + 1`
(the IRV word 2 and everything the tasks pushed).  `v98` returns `[]` when its fuel runs out, so no size bound is needed. -/
import Nano.Parser.ParInv
namespace ParInv
open C BufL

/-- the output copy: all of `h` from `j` on (or nothing, when the fuel runs out) -/
theorem v98_eq : ∀ (n : Nat) (h : Buf) (j : UInt64) (o : Buf), h.length < 2 ^ 64 → j.toNat ≤ h.length →
    v98 n h j o = [] ∨ v98 n h j o = o ++ h.drop j.toNat
  | 0, _, _, _, _, _ => Or.inl rfl
  | n + 1, h, j, o, hl, hj => by
    by_cases hi : j.toNat < h.length
    · have hlt : j < bsize h := by
        rw [UInt64.lt_iff_toNat_lt]; simp [bsize, UInt64.toNat_ofNat']; omega
      have hs : (j + 1).toNat = j.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      simp only [v98, hlt, if_true]
      rcases v98_eq n h (j + 1) (bpush o (bget h j)) hl (by omega) with e | e
      · exact Or.inl e
      · right
        rw [e, hs]
        simp only [bpush, bget, List.append_assoc]
        congr 1
        rw [List.drop_eq_getElem_cons hi]; simp [List.getD, hi]
    · have hlt : ¬ j < bsize h := by
        rw [UInt64.lt_iff_toNat_lt]; simp [bsize, UInt64.toNat_ofNat']; omega
      simp only [v98, hlt, if_false]
      right; simp [List.drop_eq_nil_of_le (show h.length ≤ j.toNat by omega)]

/-- the cells `fin` checks on the last def row: name spelled `m`, no non-input parameter, exactly one parameter, its code 3 (List), result code 3 -/
def MainCells (h : Buf) : Prop :=
  let j := d7 + 8 * (bget h 12 - 1)
  bget h (d11 + bget h j + 2) = 109 ∧ bget h (d11 + bget h j + 3) = 0 ∧ bget h (j + 2) = 0 ∧
    bget h (j + 6) = 1 ∧ bget h (d7 + 4096 + bget h (j + 5)) = 3 ∧ bget h (j + 3) = 3

/-- **acceptance tail**: a non-empty result of `fin` is the heap from the IRV word on, of an accepted (status 2) state whose last def is main -/
theorem fin_ne (ts h : Buf) (hl : h.length < 2 ^ 64) (hj : (d11 + bsize ts + 1).toNat ≤ h.length) (hne : fin ts 1 h ≠ []) :
    bget h 0 = 2 ∧ 0 < bget h 12 ∧ MainCells h ∧ fin ts 1 h = h.drop (d11 + bsize ts + 1).toNat := by
  unfold fin at hne ⊢
  simp only [] at hne ⊢
  have one : ((1 : UInt64) == 0) = false := by decide
  simp only [one, Bool.false_eq_true, if_false] at hne ⊢
  by_cases h0 : bget h 0 = 2
  · by_cases h12 : 0 < bget h 12
    · simp only [h0, beq_self_eq_true, if_true, h12] at hne ⊢
      by_cases c1 : bget h (d11 + bget h (d7 + 8 * (bget h 12 - 1)) + 2) = 109
      · by_cases c2 : bget h (d11 + bget h (d7 + 8 * (bget h 12 - 1)) + 3) = 0
        · by_cases c3 : bget h (d7 + 8 * (bget h 12 - 1) + 2) = 0
          · by_cases c6 : bget h (d7 + 8 * (bget h 12 - 1) + 6) = 1
            · by_cases c4 : bget h (d7 + 4096 + bget h (d7 + 8 * (bget h 12 - 1) + 5)) = 3
              · by_cases c5 : bget h (d7 + 8 * (bget h 12 - 1) + 3) = 3
                · simp only [c1, c2, c3, c6, c4, c5, beq_self_eq_true, if_true] at hne ⊢
                  refine ⟨trivial, trivial, ⟨c1, c2, c3, c6, c4, c5⟩, ?_⟩
                  rcases v98_eq 16777216 h (d11 + bsize ts + 1) bnew hl hj with e | e
                  · exact absurd e hne
                  · rw [e]; rfl
                · exfalso; apply hne; simp [c1, c2, c3, c6, c4, c5, bnew]
              · exfalso; apply hne; simp [c1, c2, c3, c6, c4, bnew]
            · exfalso; apply hne; simp [c1, c2, c3, c6, bnew]
          · exfalso; apply hne; simp [c1, c2, c3, bnew]
        · exfalso; apply hne; simp [c1, c2, bnew]
      · exfalso; apply hne; simp [c1, bnew]
    · exfalso; apply hne; simp [h0, h12, bnew]
  · exfalso; apply hne; simp [h0, bnew]

end ParInv
