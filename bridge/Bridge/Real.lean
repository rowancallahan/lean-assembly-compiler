/- Bridge.Real: the trimmed-model lemmas of `MiniModel.lean` ported to the REAL con-leche `Denotes`/`Model`
(DENOTES_SPIKE.md §13).  Real names: `Denotes cval env φ ρ`, `Model V env`, `env.find?`, `Level.substFn`. -/
import Bridge.Transfer

namespace Bridge.Real
open ConLeche ConLeche.SetModel SetTheory
universe w
variable {V : Type w} [SetTheory V] {env : Env}

/-- `Mini.natEnc`: the canonical numeral at level assignment `φ` (Mini had no `φ`). -/
noncomputable def natEnc (M : Model V env) (φ : LevelParam → Nat) : Nat → V
  | 0 => M.cval natZeroName φ
  | k + 1 => app (M.cval natSuccName φ) (natEnc M φ k)

/-- constants `Nat.zero`, `Nat.succ` are stored with no level parameters (Mini: `LitEnv.zero/succ`, by membership) -/
structure NatConsts (env : Env) : Prop where
  zero : ∃ ci, env.find? natZeroName = some ci ∧ ci.toConstantVal.levelParams = []
  succ : ∃ ci, env.find? natSuccName = some ci ∧ ci.toConstantVal.levelParams = []

/-- **lit / natLit** (`Mini.lit_denotes`).  Statement change: `NatConsts env` instead of nothing (Mini's
constants were free). -/
theorem lit_denotes (M : Model V env) (H : NatConsts env) (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    ∀ k, Denotes M.cval env φ ρ (.lit (.natVal k)) (natEnc M φ k) := by
  obtain ⟨cz, hz, pz⟩ := H.zero
  obtain ⟨cs, hs, ps⟩ := H.succ
  intro k
  induction k with
  | zero => exact .natLit (Denotes_const' hz pz rfl)
  | succ k ih => exact .natLit (.app (Denotes_const' hs ps rfl) ih)


/-- **const** (`Mini.mem_closed`): a stored constant whose type denotes `Tv` is a member of `Tv`.  Real name:
`Bridge.const_mem` + `Denotes_functional`.  Statement change: the stored constant is found by `env.find?` and its type
is `ci.toConstantVal.type` (Mini: a list of `(name, type)` pairs). -/
theorem mem_closed (M : Model V env) {n : Name} {ci : ConstantInfo} (h : env.find? n = some ci)
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {Tv : V} (hT : Denotes M.cval env φ ρ ci.toConstantVal.type Tv) :
    M.cval n φ ∈ˢ Tv := by
  obtain ⟨T, hT', hm⟩ := const_mem M h φ ρ
  rwa [Denotes_functional hT hT']

/-- the stored shapes `Nat`, `Nat.zero : Nat`, `Nat.succ : Nat → Nat` (Mini: `LitEnv.nat/zero/succ`) -/
structure NatTypes (env : Env) : Prop extends NatConsts env where
  nat : ∃ ci, env.find? natName = some ci ∧ ci.toConstantVal.levelParams = []
  zeroTy : ∀ ci, env.find? natZeroName = some ci → ci.toConstantVal.type = .const natName []
  succTy : ∀ ci, env.find? natSuccName = some ci → ∃ m : BinderMeta, (∀ φ, regime φ m.pw ≠ 0) ∧
    ci.toConstantVal.type = .forallE (.const natName []) (.const natName []) m

/-- `natEnc k ∈ ⟦Nat⟧` (`Mini.natEnc_mem`) -/
theorem natEnc_mem (M : Model V env) (H : NatTypes env) (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    ∀ k, natEnc M φ k ∈ˢ M.cval natName φ := by
  obtain ⟨cn, hn, pn⟩ := H.nat
  obtain ⟨cz, hz, pz⟩ := H.zero
  obtain ⟨cs, hs, ps⟩ := H.succ
  have dN : ∀ ρ', Denotes M.cval env φ ρ' (.const natName []) (M.cval natName φ) := fun _ =>
    Denotes_const' hn pn rfl
  intro k
  induction k with
  | zero => exact mem_closed M hz (ρ := ρ) (by rw [H.zeroTy cz hz]; exact dN _)
  | succ k ih =>
    obtain ⟨m, hm, hty⟩ := H.succTy cs hs
    have dP : Denotes M.cval env φ ρ (.forallE (.const natName []) (.const natName []) m)
        (piR (regime φ m.pw) (M.cval natName φ) fun _ => M.cval natName φ) :=
      .pi (dN _) (fun _ _ => dN _) (fun h => absurd h (hm φ))
    have hS : M.cval natSuccName φ ∈ˢ _ := mem_closed M hs (ρ := ρ) (by rw [hty]; exact dP)
    obtain ⟨Bx, hB, hmem⟩ := mem_app dP hS (dN _) ih
    rwa [Denotes_functional hB (dN _)] at hmem

#print axioms lit_denotes
#print axioms natEnc_mem
end Bridge.Real
