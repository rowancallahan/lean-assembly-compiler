/- Nano/V2Self/Proof/ParRunCallSpec: Layer 2 → ParSpec for CALL arguments (box G).
`tyMatch_of`: Par1's argument check (`argOK`: shape code = parameter code, or a numeral / len' for a Nat parameter) together with the
input rule (argument is the input local ⇔ parameter is the input: the deferred validation v210) is ParSpec's `tyMatch`.
`toNdL_dropInp`: the flattener's "skip input locals" is ParSpec's `dropInp`. -/
import Nano.V2Self.Proof.ParRunArgs
namespace ParRun
open ParSpec

theorem tyMatch_of {p : Ps} {v : RN} {ty : Ty} (hv : ValOK v ty) (hn : p ≠ .sh .nt) (hi : p = .inp ↔ v.isInp = true)
    (hok : v.sh = some (psCode p) ∨ (psCode p = .nt ∧ (v.tag = 1 ∨ (v.tag = 9 ∧ v.a = 1)))) : tyMatch p ty = true := by
  obtain ⟨hty, hpe, h9⟩ := hv
  have hsh : v.sh = some (psCode p) ∨ (psCode p = .nt ∧ v.tag = 1) := by
    rcases hok with h | ⟨h1, h2 | ⟨h2, h3⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl (by rw [h1]; exact h9 h2 h3)
  cases ty with
  | bot => simp [TyRel] at hty; rw [hpe] at hty; cases hty
  | inp =>
    obtain ⟨hin, hls⟩ := hty
    have := hi.mpr hin; subst this; rfl
  | lit =>
    obtain ⟨huw, hni⟩ := hty
    cases p with
    | inp => have := hi.mp rfl; rw [hni] at this; cases this
    | fuel => rfl
    | sh s =>
      rcases hsh with h | ⟨h1, _⟩
      · rw [huw] at h; simp [psCode] at h; subst h; rfl
      · exact absurd (by simpa [psCode] using h1) hn
  | s t =>
    obtain ⟨hs, hni, ht1⟩ := hty
    cases p with
    | inp =>
      have := hi.mp rfl; rw [hni] at this; cases this
    | fuel =>
      rcases hsh with h | ⟨_, h2⟩
      · rw [hs] at h; simp [psCode] at h; subst h; rfl
      · exact absurd h2 ht1
    | sh s =>
      rcases hsh with h | ⟨h1, _⟩
      · rw [hs] at h; simp [psCode] at h; subst h; simp [tyMatch]
      · exact absurd (by simpa [psCode] using h1) hn

/-- the input rule, position by position: the parameter is the input iff the argument is the input local -/
inductive InpPair : List Ps → List RN → Prop
  | nil : InpPair [] []
  | cons {p ps v vs} : (p = .inp ↔ v.isInp = true) → InpPair ps vs → InpPair (p :: ps) (v :: vs)

theorem toNdL_cons (n : RN) (r : List RN) : RN.toNdL (n :: r) = if n.isInp then RN.toNdL r else RN.toNd n :: RN.toNdL r := by
  rw [RN.toNdL]

theorem toNdL_dropInp : ∀ {ps : List Ps} {vs : List RN}, InpPair ps vs → RN.toNdL vs = dropInp ps (vs.map RN.toNd) := by
  intro ps vs h
  induction h with
  | nil => simp [RN.toNdL, dropInp]
  | @cons p ps v vs hp _ ih =>
    rw [toNdL_cons, ih]
    by_cases hv : v.isInp = true
    · have := hp.mpr hv; subst this
      simp [hv, dropInp]
    · have hne : p ≠ .inp := fun e => hv (hp.mp e)
      simp only [hv, Bool.false_eq_true, if_false]
      cases p with
      | inp => exact absurd rfl hne
      | fuel => simp [dropInp]
      | sh s => simp [dropInp]

end ParRun
