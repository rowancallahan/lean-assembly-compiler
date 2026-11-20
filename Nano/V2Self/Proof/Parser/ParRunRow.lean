/- Nano/V2Self/Proof/Parser/ParRunRow: def-row facts at row construction (parser lead), pure Layer 2.
`firstLs_snoc`: appending a parameter `w` keeps the FirstLs (input) positions of the prefix and makes the new position the input
iff `w` is a List and the prefix has none — exactly the input flag `n1` of stateTy (74) and assign (68). -/
import Nano.V2Self.Proof.Parser.ParRunAtom
namespace ParRun
open ParSpec

theorem hasLs_false_iff (ps : List Sh) : hasLs (ps.map some) = false ↔ ∀ j, j < ps.length → ps[j]? ≠ some .ls := by
  simp only [hasLs, List.any_eq_false, List.mem_map]
  constructor
  · intro h j hj e
    exact h (some .ls) ⟨.ls, List.mem_of_getElem? e, rfl⟩ (by decide)
  · rintro h _ ⟨s, hs, rfl⟩ e
    simp at e; subst e
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hs
    exact h j hj (by rw [List.getElem?_eq_getElem hj, hje])

theorem firstLs_snoc (ps : List Sh) (w : Sh) (i : Nat) :
    FirstLs (ps ++ [w]) i ↔ (i < ps.length ∧ FirstLs ps i) ∨ (i = ps.length ∧ w = .ls ∧ hasLs (ps.map some) = false) := by
  rw [hasLs_false_iff]
  unfold FirstLs
  have ga : ∀ j, j < ps.length → (ps ++ [w])[j]? = ps[j]? := fun j hj => List.getElem?_append_left hj
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hi : i < ps.length
    · left; refine ⟨hi, by rwa [ga i hi] at h1, fun j hj => by rw [← ga j (by omega)]; exact h2 j hj⟩
    · right
      have hlt : i < ps.length + 1 := by
        have := (List.getElem?_eq_some_iff.mp h1).1; simp at this; omega
      have e : i = ps.length := by omega
      subst e
      refine ⟨rfl, ?_, fun j hj => by rw [← ga j hj]; exact h2 j hj⟩
      rw [List.getElem?_append_right (Nat.le_refl _)] at h1; simpa using h1
  · rintro (⟨hi, h1, h2⟩ | ⟨rfl, rfl, h2⟩)
    · exact ⟨by rw [ga i hi]; exact h1, fun j hj => by rw [ga j (by omega)]; exact h2 j hj⟩
    · exact ⟨by rw [List.getElem?_append_right (Nat.le_refl _)]; simp, fun j hj => by rw [ga j hj]; exact h2 j hj⟩

end ParRun
