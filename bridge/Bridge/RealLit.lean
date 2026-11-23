/- Bridge.RealLit: `Mini.litU_fact` ported to the REAL con-leche `Denotes`/`Model` (DENOTES_SPIKE.md §13).
The level problem (finding (a)) is isolated in ONE explicit hypothesis `CvalParams M` (a model's `cval c` reads only
`c`'s own level parameters; `ModelExists2.CvalParams`, dischargeable by `model_exists'`). -/
import Bridge.Real

namespace Bridge.Real
open ConLeche ConLeche.SetModel SetTheory
open Name (anonymous)
universe w
variable {V : Type w} [SetTheory V] {env : Env}

/-- a model's constant valuation reads only the constant's own level parameters (= `ModelExists2.CvalParams`) -/
def CvalParams (M : Model V env) : Prop :=
  ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) → M.cval n ψ₁ = M.cval n ψ₂

/-- the binder annotation of data binders (never a proposition) -/
def dm : BinderMeta := ⟨.never⟩
theorem regime_dm (φ : LevelParam → Nat) : regime φ dm.pw = 1 := by simp [regime, dm]

/-- `n` is stored with level parameters `ps` and type `ty` -/
def Stored (env : Env) (n : Name) (ps : List Name) (ty : Expr) : Prop :=
  ∃ ci, env.find? n = some ci ∧ ci.toConstantVal.levelParams = ps ∧ ci.toConstantVal.type = ty

theorem Stored.const (M : Model V env) {n : Name} {ps : List Name} {ty : Expr} (h : Stored env n ps ty)
    {us : List Level} (hl : us.length = ps.length) (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    Denotes M.cval env φ ρ (.const n us) (M.cval n (Level.substFn φ ps us)) := by
  obtain ⟨ci, hf, hp, -⟩ := h
  exact Denotes_const' hf hp hl

theorem Stored.mem_of (M : Model V env) {n : Name} {ps : List Name} {ty : Expr} (h : Stored env n ps ty)
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {Tv : V} (hT : Denotes M.cval env φ ρ ty Tv) :
    M.cval n φ ∈ˢ Tv := by
  obtain ⟨ci, hf, -, rfl⟩ := h
  exact mem_closed M hf hT

theorem pi_dm {M : Model V env} {φ : LevelParam → Nat} {ρ : BVarIdx → V} {T b : Expr} {A : V} {B : V → V}
    (hA : Denotes M.cval env φ ρ T A) (hB : ∀ x, x ∈ˢ A → Denotes M.cval env φ (push x ρ) b (B x)) :
    Denotes M.cval env φ ρ (.forallE T b dm) (piR 1 A B) := by
  have := Denotes.pi (m := dm) hA hB (by rw [regime_dm]; intro h; omega)
  rwa [regime_dm] at this

def nU : Name := anonymous |>.str "UInt64"
def nUOf : Name := nU |>.str "ofNat"
def nUInst : Name := nU |>.str "instOfNat"
def nOfNat : Name := anonymous |>.str "OfNat"
def nOfNatH : Name := nOfNat |>.str "ofNat"
def nBrLit : Name := anonymous |>.str "br_lit"
def uP : Name := anonymous |>.str "u"

def tN : Expr := .const natName []
def tU : Expr := .const nU []
/-- `OfNat.ofNat.{0} UInt64 (#0) (UInt64.instOfNat #0)` -/
def lhsE : Expr := .app (.app (.app (.const nOfNatH [.zero]) tU) (.bvar 0)) (.app (.const nUInst []) (.bvar 0))
def rhsE : Expr := .app (.const nUOf []) (.bvar 0)

/-- the stored shapes the `litU` fact reads (Mini: `LitEnv`; there, free list membership) -/
structure LitEnv (env : Env) : Prop where
  nt : NatTypes env
  u64 : Stored env nU [] (.sort (.succ .zero))
  ofNat : Stored env nUOf [] (.forallE tN tU dm)
  /-- `OfNat.{u} : Type u → Nat → Type u` (only its level parameters are read) -/
  cls : ∃ ci, env.find? nOfNat = some ci ∧ ci.toConstantVal.levelParams = [uP]
  ofNatH : Stored env nOfNatH [uP] (.forallE (.sort (.succ (.param uP))) (.forallE tN
      (.forallE (.app (.app (.const nOfNat [.param uP]) (.bvar 1)) (.bvar 0)) (.bvar 2) dm) dm) dm)
  inst : Stored env nUInst [] (.forallE tN (.app (.app (.const nOfNat [.zero]) tU) (.bvar 0)) dm)
  brLit : Stored env nBrLit [] (.forallE tN (eqE (.succ .zero) tU lhsE rhsE) dm)

/-- the level assignment `OfNat.ofNat.{0}` is read at -/
def φ0 (φ : LevelParam → Nat) : LevelParam → Nat := Level.substFn φ [uP] [.zero]

theorem φ0_u (φ : LevelParam → Nat) : φ0 φ uP = 0 := by simp [φ0, Level.substFn, Level.eval]

theorem φ0_self (φ : LevelParam → Nat) : Level.substFn (φ0 φ) [uP] [.param uP] = φ0 φ := by
  funext n; simp only [Level.substFn]; split
  · subst_vars; simp [Level.eval, φ0_u]
  · rfl

/-- **`FactsW.litU`, ported.**  The emitted UInt64 literal denotes `⟦UInt64.ofNat⟧ (natEnc k)`.  Statement changes
vs `Mini.litU_fact`: `φ`, `LitEnv` over `find?`, and `CvalParams M` (finding (a): used once, to read `Nat` in
`OfNat.ofNat.{u}`'s type at `φ[u↦0]` as `Nat` at `φ`). -/
theorem litU_fact (M : Model V env) (H : LitEnv env) (hφ : CvalParams M) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (k : Nat) {R : V}
    (hR : Denotes M.cval env φ ρ (.app (.app (.app (.const nOfNatH [.zero]) tU) (.lit (.natVal k)))
      (.app (.const nUInst []) (.lit (.natVal k)))) R) :
    R = app (M.cval nUOf φ) (natEnc M φ k) := by
  obtain ⟨cn, hn, pn⟩ := H.nt.nat
  have dN : ∀ ψ ρ', Denotes M.cval env ψ ρ' tN (M.cval natName ψ) := fun ψ _ => Denotes_const' hn pn rfl
  have dU : ∀ ρ', Denotes M.cval env φ ρ' tU (M.cval nU φ) := fun _ => H.u64.const M rfl φ _
  have hNφ : M.cval natName (φ0 φ) = M.cval natName φ := hφ _ cn hn _ _ (by simp [pn])
  have hx := natEnc_mem M H.nt φ ρ k
  obtain ⟨x, hxe⟩ : ∃ x, x = natEnc M φ k := ⟨_, rfl⟩
  rw [← hxe] at hx ⊢
  have hU1 : M.cval nU φ ∈ˢ univ 1 := by
    have := H.u64.mem_of M (φ := φ) (ρ := ρ) (Tv := univ (Level.eval φ (.succ .zero))) .sort
    simpa [Level.eval] using this
  -- `UInt64.ofNat x ∈ ⟦UInt64⟧`
  have dPiOf : Denotes M.cval env φ (push x ρ) (.forallE tN tU dm)
      (piR 1 (M.cval natName φ) fun _ => M.cval nU φ) := pi_dm (dN φ _) (fun _ _ => dU _)
  have hOf := H.ofNat.mem_of M dPiOf
  have hb : app (M.cval nUOf φ) x ∈ˢ M.cval nU φ := by
    obtain ⟨Bx, hB, hm⟩ := mem_app dPiOf hOf (dN φ _) hx
    rwa [Denotes_functional hB (dU _)] at hm
  -- the instance
  have dCls : ∀ ρ', Denotes M.cval env φ ρ' (.const nOfNat [.zero]) (M.cval nOfNat (φ0 φ)) := fun _ => by
    obtain ⟨ci, hf, hp⟩ := H.cls
    exact Denotes_const' hf hp rfl
  have dInstTy : Denotes M.cval env φ ρ (.forallE tN (.app (.app (.const nOfNat [.zero]) tU) (.bvar 0)) dm)
      (piR 1 (M.cval natName φ) fun y => app (app (M.cval nOfNat (φ0 φ)) (M.cval nU φ)) y) :=
    pi_dm (dN φ _) (fun y _ => .app (.app (dCls _) (dU _)) .bvar)
  have hInst := H.inst.mem_of M dInstTy
  have hIx : app (M.cval nUInst φ) x ∈ˢ app (app (M.cval nOfNat (φ0 φ)) (M.cval nU φ)) x := by
    obtain ⟨Bx, hB, hm⟩ := mem_app dInstTy hInst (dN φ _) hx
    rwa [Denotes_functional hB (.app (.app (dCls _) (dU _)) .bvar)] at hm
  -- `OfNat.ofNat.{0}`'s type, denoted at `φ0 φ`
  have dOC : ∀ ρ', Denotes M.cval env (φ0 φ) ρ' (.const nOfNat [.param uP]) (M.cval nOfNat (φ0 φ)) := fun ρ' => by
    obtain ⟨ci, hf, hp⟩ := H.cls
    have := Denotes_const' (cval := M.cval) (φ := φ0 φ) (ρ := ρ') hf hp (us := [.param uP]) rfl
    rwa [φ0_self] at this
  have hsort : Level.eval (φ0 φ) (.succ (.param uP)) = 1 := by simp [Level.eval, φ0_u]
  have dSort : Denotes M.cval env (φ0 φ) (push x ρ) (.sort (.succ (.param uP))) (univ 1) := by
    have h := Denotes.sort (cval := M.cval) (env := env) (φ := φ0 φ) (ρ := push x ρ) (u := .succ (.param uP))
    rwa [hsort] at h
  have dTy : Denotes M.cval env (φ0 φ) (push x ρ) (.forallE (.sort (.succ (.param uP))) (.forallE tN
      (.forallE (.app (.app (.const nOfNat [.param uP]) (.bvar 1)) (.bvar 0)) (.bvar 2) dm) dm) dm)
      (piR 1 (univ 1) fun α => piR 1 (M.cval natName (φ0 φ)) fun n =>
        piR 1 (app (app (M.cval nOfNat (φ0 φ)) α) n) fun _ => α) :=
    pi_dm dSort fun α _ => pi_dm (dN _ _) fun n _ => pi_dm (.app (.app (dOC _) .bvar) .bvar) fun _ _ => .bvar
  have hH := H.ofNatH.mem_of M dTy
  have h1 := app_mem_piR hH hU1 (by intro h; omega)
  have h2 := app_mem_piR h1 (hNφ ▸ hx) (by intro h; omega)
  have h3 := app_mem_piR h2 hIx (by intro h; omega)
  -- the transfer, one binder, at `push x ρ`
  obtain ⟨ciB, hfB, -, hty⟩ := H.brLit
  have hI := inhab_const M hfB φ ρ
  rw [hty] at hI
  obtain ⟨Sv, av, bv, hS, ha, hb', hEq⟩ := Inhab.eq (Inhab.pi hI (dN φ ρ) hx)
  have dLhs : Denotes M.cval env φ (push x ρ) lhsE
      (app (app (app (M.cval nOfNatH (φ0 φ)) (M.cval nU φ)) x) (app (M.cval nUInst φ) x)) :=
    .app (.app (.app (H.ofNatH.const M (us := [.zero]) rfl φ _) (dU _)) .bvar)
      (.app (H.inst.const M rfl φ _) .bvar)
  have dRhs : Denotes M.cval env φ (push x ρ) rhsE (app (M.cval nUOf φ) x) :=
    .app (H.ofNat.const M rfl φ _) .bvar
  obtain rfl := Denotes_functional hS (dU _)
  obtain rfl := Denotes_functional ha dLhs
  obtain rfl := Denotes_functional hb' dRhs
  have key := hEq (by simpa [Level.eval] using hU1) h3 hb
  -- the emitted term at `ρ` (literal `k` for the binder)
  have dk := lit_denotes M H.nt.toNatConsts φ ρ k
  obtain ⟨F, I, hF, hI', rfl⟩ := app_inv hR
  obtain ⟨G, n1, hG, hn1, rfl⟩ := app_inv hF
  obtain ⟨Hd, Uv, hHd, hUv, rfl⟩ := app_inv hG
  obtain ⟨J, n2, hJ, hn2, rfl⟩ := app_inv hI'
  rw [Denotes_functional hHd (H.ofNatH.const M (us := [.zero]) rfl φ ρ), Denotes_functional hUv (dU _),
    Denotes_functional hn1 dk, Denotes_functional hJ (H.inst.const M rfl φ ρ), Denotes_functional hn2 dk, ← hxe]
  exact key

#print axioms litU_fact
end Bridge.Real
