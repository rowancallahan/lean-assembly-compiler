/- Bridge.Real.LamRegime: the regime of a data λ, from con-leche's own `Denotes.lam` rule (no annotation internals).

`Denotes.lam` may read a λ in regime 0 only if its body denotes `pt` at every domain point (`hP`).  So a λ whose
body takes two different values on its domain is read in regime 1, at every annotation the checker stored
(`lam_regime_ne`).  The two values are told apart by a stored theorem `a = b → False` (`ne_of_stored_neg`). -/
import ConLeche.MainTheorem

namespace Bridge.Real.LamRegime
open ConLeche ConLeche.SetModel SetTheory

universe w
variable {V : Type w} [SetTheory V]

/-- **A λ whose body is not constant on its domain is in regime 1.** -/
theorem lam_regime_ne {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {ty body : Expr} {m : BinderMeta} {v A x₁ x₂ y₁ y₂ : V}
    (h : Denotes cval env φ ρ (.lam ty body m) v) (hA : Denotes cval env φ ρ ty A)
    (h₁ : x₁ ∈ˢ A) (h₂ : x₂ ∈ˢ A)
    (d₁ : Denotes cval env φ (push x₁ ρ) body y₁) (d₂ : Denotes cval env φ (push x₂ ρ) body y₂)
    (hne : y₁ ≠ y₂) : regime φ m.pw ≠ 0 := by
  cases h with
  | lam hA' hF hP =>
    intro h0
    obtain rfl := Denotes_functional hA hA'
    have e₁ := Denotes_functional d₁ (hF _ h₁)
    have e₂ := Denotes_functional d₂ (hF _ h₂)
    exact hne (by rw [e₁, e₂, hP h0 _ h₁, hP h0 _ h₂])

/-- a product over a domain point whose fibre is empty has no member, in either regime -/
theorem not_mem_piR {r : Nat} {A x f : V} {B : V → V} (hx : x ∈ˢ A) (hB : B x = empty)
    (hf : f ∈ˢ piR r A B) : False := by
  by_cases hr : r = 0
  · subst hr; rw [piR_zero, mem_truthVal] at hf
    obtain ⟨y, hy⟩ := hf.1 x hx; rw [hB] at hy; exact not_mem_empty _ hy
  · rw [piR_pos hr, mem_piSet] at hf
    obtain ⟨y, hy, -⟩ := hf.2 x hx
    obtain ⟨x', -, y', hy', he⟩ := mem_sigmaPairs.mp (hf.1 _ hy)
    obtain ⟨rfl, rfl⟩ := kpair_inj he
    rw [hB] at hy'; exact not_mem_empty _ hy'

/-- **A stored `@Eq.{u} U a b → False` separates `⟦a⟧` and `⟦b⟧`** (the membership premises are `eq_equality`'s). -/
theorem ne_of_stored_neg (M : Model V env) {c : ConstantInfo} (hc : c ∈ env.consts) {u : Level}
    {U a b : Expr} {m : BinderMeta}
    (ht : c.toConstantVal.type =
      .forallE (.app (.app (.app (.const eqName [u]) U) a) b) (.const falseName []) m)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) {T X Y : V}
    (hU : Denotes M.cval env φ ρ U T) (ha : Denotes M.cval env φ ρ a X) (hb : Denotes M.cval env φ ρ b Y)
    (hT : T ∈ˢ univ (Level.eval φ u)) (hX : X ∈ˢ T) (hY : Y ∈ˢ T) : X ≠ Y := by
  intro hXY
  obtain ⟨Ty, hd, hmem⟩ := M.mem c hc φ ρ
  rw [ht] at hd
  cases hd with
  | pi hA hB _ =>
    cases hA with
    | app h3 hb' =>
      cases h3 with
      | app h2 ha' =>
        cases h2 with
        | app hE hU' =>
          obtain rfl := Denotes_functional hU hU'
          obtain rfl := Denotes_functional ha ha'
          obtain rfl := Denotes_functional hb hb'
          rw [M.eq_equality u φ ρ _ _ _ _ hE hT hX hY] at hmem hB
          subst hXY
          have hpt := pt_mem_eqv_self (V := V) X
          exact not_mem_piR hpt (M.false_empty φ _ _ (hB _ hpt)) hmem

end Bridge.Real.LamRegime
