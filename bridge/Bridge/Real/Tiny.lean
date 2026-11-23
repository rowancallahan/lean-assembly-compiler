/- Bridge.Real.Tiny: step 2 of the DENOTES-3 plan, against REAL con-leche.

Program: `def f (x : Nat) : Nat := x + 1`.  The exported stream holds `f` (a def of declared type `Nat → Nat`)
and a theorem `f_eq : ∀ x : Nat, f x = Nat.succ x` (Lean: `fun _ => rfl`).  For EVERY stream `ds` holding two
such records that con-leche accepts (`checkDecls .verified pins ds = .ok env`), with literal support
(`natLitSupported env`, the checker's own guard), in EVERY model of `env` (in particular the one `model_exists`
gives) and every level assignment / variable environment:
  `⟦f v⟧ = ⟦v + 1⟧`  (both as `Nat` literals: con-leche's `natLit` rule reads them as `succ^k zero`). -/
import Bridge.Real.Stored
import Bridge.ModelExists2

namespace Bridge.Real.Tiny
open ConLeche ConLeche.SetModel SetTheory Bridge

universe w
variable {V : Type w} [SetTheory V]

def natC : Expr := .const natName []
def succC : Expr := .const natSuccName []

/-- declared type of `f` -/
def fTy : Expr := .forallE natC natC ⟨.never⟩
/-- declared type of `f_eq` (binder data as the parser leaves it, `.never`; any other is fine too) -/
def fEqTy (fN : Name) : Expr :=
  .forallE natC (eqE (.succ .zero) natC (.app (.const fN []) (.bvar 0)) (.app succC (.bvar 0))) ⟨.never⟩

theorem substFn_nil (φ : LevelParam → Nat) : Level.substFn φ [] [] = φ := rfl

/-- a stored level-free constant denotes its `cval` at `φ` -/
theorem den_const0 {env : Env} (M : Model V env) {n : Name} {ci : ConstantInfo} (h : env.find? n = some ci)
    (hl : ci.toConstantVal.levelParams = []) (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    Denotes M.cval env φ ρ (.const n []) (M.cval n φ) := by
  have := Denotes.const (cval := M.cval) (φ := φ) (ρ := ρ) (us := []) h (by rw [hl]; rfl)
  rwa [hl] at this

/-- the canonical numerals: `succ^k zero` -/
noncomputable def natV (M : Model V env) (φ : LevelParam → Nat) : Nat → V
  | 0 => M.cval natZeroName φ
  | k + 1 => app (M.cval natSuccName φ) (natV M φ k)

section
variable {env : Env} (M : Model V env) (hnat : natLitSupported env = true) (φ : LevelParam → Nat)
  (ρ : BVarIdx → V)
include hnat

theorem nat_den : Denotes M.cval env φ ρ natC (M.cval natName φ) := by
  obtain ⟨cv, caps, -, -, -, -, -, -, h, -, -, hl, -⟩ := natLitSupported_inv hnat
  exact den_const0 M h hl φ ρ

theorem nat_univ : M.cval natName φ ∈ˢ univ 1 := by
  obtain ⟨cv, caps, -, -, -, -, -, -, h, -, -, hl, -, -, hty, -⟩ := natLitSupported_inv hnat
  obtain ⟨T, hT, hm⟩ := const_mem M h φ (fun _ => M.cval natName φ)
  rw [show (ConstantInfo.indInfo cv caps).toConstantVal = cv from rfl, hty] at hT
  cases hT; exact hm

theorem succ_den : Denotes M.cval env φ ρ succC (M.cval natSuccName φ) := by
  obtain ⟨-, -, -, -, -, cv1, i1, j1, -, -, h, -, -, hl, -⟩ := natLitSupported_inv hnat
  exact den_const0 M h hl φ ρ

theorem natV_mem (ρ : BVarIdx → V) : ∀ k, natV M φ k ∈ˢ M.cval natName φ
  | 0 => by
    obtain ⟨-, -, cv0, i0, j0, -, -, -, -, h, -, -, -, -, -, hty, -⟩ := natLitSupported_inv hnat
    obtain ⟨T, hT, hm⟩ := const_mem M h φ ρ
    rw [show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal = cv0 from rfl, hty] at hT
    rw [Denotes_functional hT (nat_den M hnat φ ρ)] at hm; exact hm
  | k + 1 => by
    obtain ⟨-, -, -, -, -, cv1, i1, j1, -, -, h, -, -, -, -, -, mb, hty⟩ := natLitSupported_inv hnat
    obtain ⟨T, hT, hm⟩ := const_mem M h φ ρ
    rw [show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal = cv1 from rfl, hty] at hT
    obtain ⟨Bx, hB, hmB⟩ := mem_app hT hm (nat_den M hnat φ ρ) (natV_mem ρ k)
    rw [Denotes_functional hB (nat_den M hnat φ _)] at hmB; exact hmB

theorem lit_den : ∀ k, Denotes M.cval env φ ρ (.lit (.natVal k)) (natV M φ k)
  | 0 => by
    obtain ⟨-, -, cv0, i0, j0, -, -, -, -, h, -, -, hl, -⟩ := natLitSupported_inv hnat
    exact .natLit (den_const0 M h hl φ ρ)
  | k + 1 => .natLit (.app (succ_den M hnat φ ρ) (lit_den k))
end

/-- **Tiny, real con-leche.** -/
theorem tiny {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
    (accepted : Cached.checkDecls .verified pins ds = .ok env) (hnat : natLitSupported env = true)
    {fN eN : Name} {fv ev : Expr} {hint : ReducibilityHint}
    (hf : Declaration.defnDecl ⟨fN, [], fTy⟩ fv hint ∈ ds)
    (he : Declaration.thmDecl ⟨eN, [], fEqTy fN⟩ ev ∈ ds)
    (M : Model V env) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (v : Nat) :
    Denotes M.cval env φ ρ (.app (.const fN []) (.lit (.natVal v))) (natV M φ (v + 1)) := by
  -- f is stored, of type Nat → Nat (some binder data)
  obtain ⟨cf, msf, hff, hlpf, hlf, htyf⟩ := stored_tele V accepted hf rfl [natC] [⟨.never⟩] natC rfl rfl
    (by simp [natC, BF]) (by simp [natC, BF])
  obtain ⟨mf, rfl⟩ : ∃ m, msf = [m] := by
    match msf, hlf with | [m], _ => exact ⟨m, rfl⟩
  have hfden : ∀ ρ', Denotes M.cval env φ ρ' (.const fN []) (M.cval fN φ) := den_const0 M hff hlpf φ
  have hfx : ∀ x, x ∈ˢ M.cval natName φ → app (M.cval fN φ) x ∈ˢ M.cval natName φ := by
    intro x hx
    obtain ⟨T, hT, hm⟩ := const_mem M hff φ ρ
    rw [htyf] at hT
    obtain ⟨Bx, hB, hmB⟩ := mem_app hT hm (nat_den M hnat φ ρ) hx
    rw [Denotes_functional hB (nat_den M hnat φ _)] at hmB; exact hmB
  -- f_eq is stored, as ∀ x : Nat, f x = succ x
  obtain ⟨ce, mse, hfe, -, hle, htye⟩ := stored_tele V accepted he rfl [natC] [⟨.never⟩]
    (eqE (.succ .zero) natC (.app (.const fN []) (.bvar 0)) (.app succC (.bvar 0))) rfl rfl
    (by simp [natC, BF]) (by simp [natC, succC, BF, eqE])
  -- transfer at x := natV v
  have hx := natV_mem M hnat φ ρ v
  have key : app (M.cval fN φ) (natV M φ v) = app (M.cval natSuccName φ) (natV M φ v) := by
    obtain ⟨me, rfl⟩ : ∃ m, mse = [m] := by
      match mse, hle with | [m], _ => exact ⟨m, rfl⟩
    refine transferN M hfe htye φ ρ (tele1 (nat_den M hnat φ ρ) hx) (nat_den M hnat φ _)
      (.app (hfden _) .bvar) (.app (succ_den M hnat φ _) .bvar) ?_ (hfx _ hx) ?_
    · simpa [Level.eval] using nat_univ M hnat φ
    · exact natV_mem M hnat φ ρ (v + 1)
  have := Denotes.app (hfden ρ) (lit_den M hnat φ ρ v)
  rw [key] at this; exact this

/-- **Tiny, with the model of the main theorem.**  The model `model_exists'` builds for the accepted env (con-leche's
own `Model.ofEnvModelM`, plus `CvalParams`) satisfies `⟦f v⟧ = ⟦v+1⟧` for every `v`. -/
theorem tiny_model (V : Type w) [SetTheory V] {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
    (accepted : Cached.checkDecls .verified pins ds = .ok env) (hnat : natLitSupported env = true)
    {fN eN : Name} {fv ev : Expr} {hint : ReducibilityHint}
    (hf : Declaration.defnDecl ⟨fN, [], fTy⟩ fv hint ∈ ds)
    (he : Declaration.thmDecl ⟨eN, [], fEqTy fN⟩ ev ∈ ds) :
    ∃ M : Model V env, ModelExists2.CvalParams M ∧ ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (v : Nat) (X : V),
      Denotes M.cval env φ ρ (.lit (.natVal (v + 1))) X →
      Denotes M.cval env φ ρ (.app (.const fN []) (.lit (.natVal v))) X := by
  obtain ⟨M, hP⟩ := ModelExists2.model_exists' V pins ds env accepted
  refine ⟨M, hP, fun φ ρ v X hX => ?_⟩
  rw [Denotes_functional hX (lit_den M hnat φ ρ (v + 1))]
  exact tiny accepted hnat hf he M φ ρ v

end Bridge.Real.Tiny
