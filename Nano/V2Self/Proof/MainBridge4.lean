/- Nano/V2Self/Proof/MainBridge4: the Sem ⇐ sv bridge, layer 4 — the node cases.  `NodeOK` = the value-mode claim
for one node: E's `sv` succeeding implies `ev` succeeding with related results, invariants kept. -/
import Nano.V2Self.Proof.MainBridge3

namespace NanoMain
open Templates

/-- the value-mode claim for node `e` in a frame (`Kk` = O's slot kinds, `oc` = O's def context) -/
def NodeOK (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (e : ParSpec.Nd) : Prop :=
  (∀ s, oc.K.getD s 0 ≤ 2) → ∀ Γ ks F F' es env ew σ sp H vs H', TyN D Γ none e ks → OwnSpec.chk oc e F = some (F', es) →
    EnvI σ oc.K F Γ env ew → AHeap K.hb K.κ H σ → H.top % 8 = 0 → K.hb ≤ H.top → sv K e ew sp H = some (vs, H') →
    ∃ σ' v, ev cx e env = .ok (.inl v) ∧ AHeap K.hb K.κ H' σ' ∧ ResI σ' oc.K F' Γ env ew es v vs ∧
      EnvI σ' oc.K F' Γ env ew ∧ Ch σ σ' Γ F F' ew ∧ H'.top % 8 = 0 ∧ K.hb ≤ H'.top

theorem node_const (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (c : UInt64) : NodeOK cx K oc D (ParSpec.Nd.const c) := by
  intro _ Γ ks F F' es env ew σ sp H vs H' _ hc hE hA h8 hb hs
  simp only [OwnSpec.chk, Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
  simp only [sv] at hs; obtain ⟨rfl, rfl⟩ := leafS_some hs
  refine ⟨σ, [.w c], rfl, hA, ⟨rfl, rfl, fun i h1 h2 h3 => ?_⟩, hE, Ch.refl _ _ _ _, h8, hb⟩
  simp at h1; subst h1; simp [VR]

theorem node_loc (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (s w : Nat) : NodeOK cx K oc D (ParSpec.Nd.loc s w) := by
  intro hK2 Γ ks F F' es env ew σ sp H vs H' hT hc hE hA h8 hb hs
  simp only [OwnSpec.chk] at hc; split at hc
  · simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
    simp only [sv] at hs; obtain ⟨rfl, rfl⟩ := localS_some w s hs
    cases hT with
    | loc hk =>
      obtain ⟨hk1, -⟩ := hk
      have hl := hE.len
      have he : ev cx (ParSpec.Nd.loc s w) env = .ok (.inl ((env.drop s).take w)) := by simp [ev, hl, hk1]
      refine ⟨σ, _, he, hA, ⟨by simp [OwnSpec.locE]; omega, by simp; omega, fun i h1 h2 h3 => ?_⟩, hE,
        Ch.refl _ _ _ _, h8, hb⟩
      simp only [OwnSpec.locE, List.length_map, List.length_range] at h1
      simp only [OwnSpec.locE, List.getElem_map, List.getElem_range]
      refine ⟨fun h => by omega, fun h => by omega, fun h => by omega, fun _ => ?_⟩
      have := hK2 (s + i)
      have e1 : (oc.K.getD (s + i) 0 + 4 * (s + i + 1)) / 4 - 1 = s + i := by omega
      rw [e1]; simp only [List.getElem_take, List.getElem_drop]
      refine ⟨by simp, ?_⟩
      rw [List.getElem?_eq_getElem (by omega)]
  · cases hc

end NanoMain
