/- Bridge.Real.Spine: typing a constant applied to a spine of arguments, from its STORED type (real con-leche).

`TeleX M φ ρ Ts xs ρ'`: the arguments `xs` are members of the binder types `Ts` (each denoted at the
environment extended by the earlier arguments).  `spine_mem`: a member of what `∀ Ts, B` denotes, applied to
`xs`, is a member of what `B` denotes at `ρ'`.  Binder data is irrelevant (`mem_app` holds in both regimes). -/
import Bridge.Real.Stored
import Bridge.Real.Levels

namespace Bridge.Real
open ConLeche ConLeche.SetModel SetTheory Bridge

universe w
variable {V : Type w} [SetTheory V] {env : Env}

noncomputable def appN (F : V) : List V → V
  | [] => F
  | x :: xs => appN (app F x) xs

inductive TeleX (M : Model V env) (φ : LevelParam → Nat) :
    (BVarIdx → V) → List Expr → List V → (BVarIdx → V) → Prop
  | nil {ρ} : TeleX M φ ρ [] [] ρ
  | cons {ρ ρ' T Ts A x xs} : Denotes M.cval env φ ρ T A → x ∈ˢ A → TeleX M φ (push x ρ) Ts xs ρ' →
      TeleX M φ ρ (T :: Ts) (x :: xs) ρ'

theorem spine_mem {M : Model V env} {φ : LevelParam → Nat} :
    ∀ {Ts : List Expr} {ms : List BinderMeta} {B : Expr} {ρ ρ' : BVarIdx → V} {xs : List V} {P F : V},
      ms.length = Ts.length → Denotes M.cval env φ ρ (piN (Ts.zip ms) B) P → F ∈ˢ P →
      TeleX M φ ρ Ts xs ρ' → ∃ Bv, Denotes M.cval env φ ρ' B Bv ∧ appN F xs ∈ˢ Bv
  | [], [], _, _, _, _, _, _, _, hP, hF, .nil => ⟨_, hP, hF⟩
  | _ :: _, _ :: _, _, _, _, x :: _, _, F, hl, hP, hF, .cons hA hx ht => by
      obtain ⟨Bx, hB, hm⟩ := mem_app hP hF hA hx
      exact spine_mem (F := app F x) (by simpa using hl) hB hm ht

/-- A stored def/thm record of the accepted stream, at level arguments `us`, applied to `xs` lying in its
declared binder types (denoted at the INDUCED assignment `ψ = substFn φ ps us`): a member of `⟦B⟧ψ ρ'`. -/
theorem stored_spine (V : Type w) [SetTheory V] {pins : List NatOpPinSet} {ds : Array Declaration}
    (accepted : Cached.checkDecls .verified pins ds = .ok env)
    {pd : Declaration} (hmem : pd ∈ ds) {cv : ConstantVal} (hcv : Cached.Declaration.Declares pd cv)
    (Ts : List Expr) (ms : List BinderMeta) (B : Expr) (hl : ms.length = Ts.length)
    (hty : cv.type = piN (Ts.zip ms) B) (hT : ∀ T ∈ Ts, BF T) (hB : BF B)
    (M : Model V env) (ψ : LevelParam → Nat) (ρ ρ' : BVarIdx → V) (xs : List V)
    (ht : TeleX M ψ ρ Ts xs ρ') :
    ∃ Bv, Denotes M.cval env ψ ρ' B Bv ∧ appN (M.cval cv.name ψ) xs ∈ˢ Bv := by
  obtain ⟨c, ms', hf, -, hl', hty'⟩ := stored_tele V accepted hmem hcv Ts ms B hl hty hT hB
  obtain ⟨P, hP, hm⟩ := const_mem M hf ψ ρ
  rw [hty'] at hP
  exact spine_mem hl' hP hm ht

/-- The same record denotes, at levels `us` (of the right length), its `cval` at the induced assignment. -/
theorem stored_den (V : Type w) [SetTheory V] {pins : List NatOpPinSet} {ds : Array Declaration}
    (accepted : Cached.checkDecls .verified pins ds = .ok env)
    {pd : Declaration} (hmem : pd ∈ ds) {cv : ConstantVal} (hcv : Cached.Declaration.Declares pd cv)
    (Ts : List Expr) (ms : List BinderMeta) (B : Expr) (hl : ms.length = Ts.length)
    (hty : cv.type = piN (Ts.zip ms) B) (hT : ∀ T ∈ Ts, BF T) (hB : BF B)
    (M : Model V env) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (us : List Level)
    (hus : us.length = cv.levelParams.length) :
    Denotes M.cval env φ ρ (.const cv.name us) (M.cval cv.name (Level.substFn φ cv.levelParams us)) := by
  obtain ⟨c, ms', hf, hlp, -, -⟩ := stored_tele V accepted hmem hcv Ts ms B hl hty hT hB
  have := Denotes.const (cval := M.cval) (φ := φ) (ρ := ρ) (us := us) hf (by rw [hlp]; exact hus)
  rwa [hlp] at this

end Bridge.Real
