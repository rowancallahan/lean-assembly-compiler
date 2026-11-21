/- Machine bridge (Opus box E): the J-level program, code shape.
`gen_words`: if Gen succeeds on the serialized resolved program `ds`, the code after the def phase is the stub code
followed by the def templates (`defsJ`), def k at its table start word.  `At_defsJ`: each def's template inside it.
That every def runs per its contract is `gen_defs_runO` (CapProg.lean). -/
import Nano.Run.NdProgW
namespace Templates
open CallProbe C GenRef ParSpec

theorem SerAt_serialize (ds : List DefA) : SerAt (serialize ds) 1 (ds.flatMap DefA.ser) := by
  intro j hj
  simp only [serialize, tg, List.getD_eq_getElem?_getD]
  rw [show 1 + j = j + 1 by omega, List.getElem?_cons_succ]

theorem At_defsJ {C : List J} {P : PC} {ds : List DefA} : ∀ (n k h : Nat), At C h (defsJ P ds k n) →
    (∀ j, j < n → P.T (k + j) = h + (defsJ P ds k j).length) →
    ∀ j, j < n → At C (P.T (k + j)) (defT (scAt P ds (k + j)) (dA ds (k + j)).body (P.T (k + j)) (dA ds (k + j)).nres)
  | 0, _, _, _, _, j, hj => absurd hj (by omega)
  | n + 1, k, h, hC, hT, j, hj => by
    simp only [defsJ] at hC
    rcases j with _ | j
    · have := hT 0 (by omega); simp only [Nat.add_zero, defsJ, List.length_nil] at this ⊢
      rw [this] at hC ⊢; exact hC.left
    · have r := At_defsJ n (k + 1) _ hC.right (fun j' hj' => by
        have := hT (j' + 1) (by omega)
        rw [show k + (j' + 1) = k + 1 + j' by omega] at this
        rw [this]; simp [defsJ, Nat.add_assoc]
        try (have e := hT 0 (by omega); simp [defsJ] at e
             rw [e]; simp [defT, proA, pushA, push, tm_len, epi, copy_len]; omega)) j (by omega)
      rw [show k + (j + 1) = k + 1 + j by omega]; exact r

/-- the start-word table Gen built -/
def pcOf (κ hb : Nat) (c29 : UInt64) (inp : Nat → UInt64) (T : Buf) : PC :=
  ⟨κ, hb, c29, inp, fun j => (bget T j.toUInt64).toNat⟩

end Templates
