/- Opus box E: the capacity exit as SAFE runs.  `bpush_capS`: BPUSH on a full buffer reaches the cap stub (word 6)
on safe steps, memory untouched. -/
import Nano.V2Self.Proof.SemX
import Nano.V2Self.Proof.EVSFin
namespace Templates
open CallProbe SimW

theorem bpush_capS {K : LayW} {C : List J} {pc : Nat} (s : St) (hC : At C pc (bpushT 6 pc)) (hx0 : s.x 0 = 0)
    (hsp : (s.x 31).toNat + 16 < 2 ^ 62)
    (hlen : (s.m ((s.m ((s.x 31).toNat + 8)).toNat + 8)).toNat ≤ (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat)
    (hb : (s.m ((s.x 31).toNat + 8)).toNat + 16 < 2 ^ 62)
    (w0 : wok K (s.x 31).toNat) (w1 : wok K ((s.x 31).toNat + 8)) (w2 : wok K (s.m ((s.x 31).toNat + 8)).toNat)
    (w3 : wok K ((s.m ((s.x 31).toNat + 8)).toNat + 8)) (h6 : 6 < C.length) (hC18 : C.length < 2 ^ 18) :
    ∃ s', SStarX K C (pc, s) (6, s') ∧ s'.m = s.m ∧ s'.b = s.b ∧ s'.x 0 = 0 ∧
      ∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 31 → s'.x r = s.x r := by
  have hs : ∀ i, i < 12 → C[pc + i]? = (bpushT 6 pc)[i]? := fun i hi => hC i (by simp [bpushT]; omega)
  have h0 := hs 0 (by omega); have h1 := hs 1 (by omega); have h2 := hs 2 (by omega); have h3 := hs 3 (by omega)
  have h4 := hs 4 (by omega); have h5 := hs 5 (by omega); have h6' := hs 6 (by omega)
  simp [bpushT] at h0 h1 h2 h3 h4 h5 h6'
  have lt := (s.x 31).toNat_lt
  have hpl : pc + 6 < C.length := (List.getElem?_eq_some_iff.1 h6').1
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e8 : ea (s.x 31) 8 = (s.x 31).toNat + 8 := by simp [ea]; omega
  have eb0 : ∀ b : UInt64, ea b 0 = b.toNat := fun b => by simp [ea]
  have blt := (s.m ((s.x 31).toNat + 8)).toNat_lt
  have ebuf8 : ea (s.m ((s.x 31).toNat + 8)) 8 = (s.m ((s.x 31).toNat + 8)).toNat + 8 := by simp [ea]; omega
  have hc : ¬ (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat < (s.m ((s.m ((s.x 31).toNat + 8)).toNat + 8)).toNat := by omega
  have ej : ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 1 + (6 - (pc + 6 : Nat))).toNat = 6 := by omega
  have hr : ∃ s', run C 7 (pc, s) = some (6, s') ∧ s'.m = s.m ∧ s'.b = s.b ∧ s'.x 0 = 0 ∧
      ∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 31 → s'.x r = s.x r := by
    simp [CallProbe.run, CallProbe.step, h0, h1, h2, h3, h4, h5, h6', CallProbe.wr, e0, e8, eb0, ebuf8, hc, upd_ne, upd_same, ej]
    refine ⟨_, ⟨by omega, rfl⟩, rfl, rfl, by simp [upd_ne, hx0], fun r r5 r6 r7 r14 r31 => ?_⟩
    simp [upd, r5, r6, r7, r14, r31]
  obtain ⟨s', hr, rest⟩ := hr
  refine ⟨s', SStarX.of (SafeRun.sstar_of_run hr ?_), rest⟩
  intro j hj c hc'
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [CallProbe.run, CallProbe.step, h0, h1, h2, h3, h4, h5, h6', CallProbe.wr, e0, e8, eb0, ebuf8, hc, upd_ne, upd_same] at hc' <;> subst hc' <;>
    simp [Safe, h0, h1, h2, h3, h4, h5, h6', CallProbe.wr, e0, e8, eb0, ebuf8, hc, upd_ne, upd_same, hx0] <;>
    first | omega | assumption | exact ⟨by omega, by assumption⟩

end Templates
