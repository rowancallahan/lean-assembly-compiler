/- Nano/V2Self/Proof/Cert/Asm: assembling the per-def certificates along `means` (each def sees the meanings before it). -/
import Nano.V2Self.Proof.Cert.Rules

namespace Cert
open NanoMain ParSpec

/-- def `k`, `k+1`, … of `ds` meet their specifications, given `Good` meanings of the defs before -/
def AllOk (inp : List UInt8) (κ : Nat) (specs : List (Fn → Prop)) : Nat → List DefA → Prop
  | _, [] => True
  | k, d :: ds => (∀ ms, Good specs ms k → ∃ S : Fn → Prop, specs[k]? = some S ∧ S (defMean inp κ ms d)) ∧
      AllOk inp κ specs (k + 1) ds

theorem means_all (inp : List UInt8) (κ : Nat) (specs : List (Fn → Prop)) :
    ∀ (ds : List DefA) (ms : List Fn) (k : Nat), Good specs ms k → AllOk inp κ specs k ds →
      Good specs (means inp κ ms ds) (k + ds.length)
  | [], ms, k, G, _ => by simpa [means] using G
  | d :: ds, ms, k, G, H => by
    obtain ⟨S, hS, hSF⟩ := H.1 ms G
    have G' : Good specs (ms ++ [defMean inp κ ms d]) (k + 1) := by
      refine ⟨by simp [G.1], fun j F hj => ?_⟩
      by_cases c : j < ms.length
      · rw [List.getElem?_append_left c] at hj; exact G.2 j F hj
      · have hj' : j = ms.length := by
          have := (List.getElem?_eq_some_iff.mp hj).1; simp at this; omega
        subst hj'
        simp at hj; subst hj
        exact ⟨S, by rw [G.1]; exact hS, hSF⟩
    have := means_all inp κ specs ds (ms ++ [defMean inp κ ms d]) (k + 1) G' H.2
    simp only [means, List.length_cons]
    rw [show k + (ds.length + 1) = k + 1 + ds.length by omega]; exact this

/-- the program's meaning from the last def's specification -/
theorem sem_of_good {inp : List UInt8} {κ : Nat} {p : List DefA} {specs : List (Fn → Prop)} {n : Nat} {S : Fn → Prop}
    {out : List UInt64} (G : Good specs (means inp κ [] p) (n + 1)) (hS : specs[n]? = some S)
    (h : ∀ F, S F → Ref (F []) [.b out]) : Ref (Sem κ p inp) (out.map UInt64.toUInt8) := by
  obtain ⟨F, hF, hSF⟩ := G.get (Nat.lt_succ_self n) hS
  have hl : (means inp κ [] p).getLast? = some F := by
    rw [List.getLast?_eq_getElem?, G.1]; exact hF
  unfold Sem
  rw [hl]
  rcases h F hSF with h | h <;> simp [Ref, h]

end Cert
