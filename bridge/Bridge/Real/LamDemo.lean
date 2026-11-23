/- Bridge.Real.LamDemo: option (4) on a real export.  `Testing/denotes_real/TinyLam.lean` stores
`g_eq : ∀ x : Nat, g x = (fun y : Nat => Nat.succ y) x` and `ne12 : succ zero = succ (succ zero) → False`;
con-leche accepts it.  `lam_regime_g`: whatever binder data the checker stored on that λ, it is read in
regime 1 at every level assignment (so it denotes the graph of `succ`).  From `Model.mem` of `g_eq` alone, via
`LamRegime.lam_regime_ne`; `ne12` tells the two body values apart. -/
import Bridge.Real.LamRegime
import Bridge.Real.Tiny
import Bridge.Real.AddOne
import Bridge.Transfer

namespace Bridge.Real.LamDemo
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real Bridge.Real.Tiny Bridge.Real.LamRegime
open Bridge.Real.AddOne (nm L1)

universe w
variable {V : Type w} [SetTheory V]

def nv : BinderMeta := ⟨.never⟩
def zC : Expr := .const natZeroName []
def lamB : Expr := .app succC (.bvar 0)
def gEqB (m₁ : BinderMeta) : Expr :=
  eqE L1 natC (.app (.const (nm "g") []) (.bvar 0)) (.app (.lam natC lamB m₁) (.bvar 0))
def gEqTy : Expr := .forallE natC (gEqB nv) nv
def neA : Expr := eqE L1 natC (.app succC zC) (.app succC (.app succC zC))
def neTy : Expr := .forallE neA (.const falseName []) nv

theorem rm_forallE {e A B : Expr} (h : e.resetMeta = .forallE A B nv) :
    ∃ A' B' m, e = .forallE A' B' m ∧ A'.resetMeta = A ∧ B'.resetMeta = B := by
  cases e <;> simp [Expr.resetMeta] at h
  exact ⟨_, _, _, rfl, h.1, h.2.1⟩

theorem rm_app {e f a : Expr} (h : e.resetMeta = .app f a) :
    ∃ f' a', e = .app f' a' ∧ f'.resetMeta = f ∧ a'.resetMeta = a := by
  cases e <;> simp [Expr.resetMeta] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem rm_lam {e A B : Expr} (h : e.resetMeta = .lam A B nv) :
    ∃ A' B' m, e = .lam A' B' m ∧ A'.resetMeta = A ∧ B'.resetMeta = B := by
  cases e <;> simp [Expr.resetMeta] at h
  exact ⟨_, _, _, rfl, h.1, h.2.1⟩

theorem bf_eqHead : BF (.app (.app (.const eqName [L1]) natC) (.app (.const (nm "g") []) (.bvar 0))) := by
  simp [BF, natC]

/-- the stored `g_eq`: the declared statement with unknown binder data on the ∀ and on the λ -/
theorem stored_g (V : Type w) [SetTheory V] {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
    (accepted : Cached.checkDecls .verified pins ds = .ok env) {v : Expr}
    (hg : Declaration.thmDecl ⟨nm "g_eq", [], gEqTy⟩ v ∈ ds) :
    ∃ c m₀ m₁, env.find? (nm "g_eq") = some c ∧ c.toConstantVal.type = .forallE natC (gEqB m₁) m₀ := by
  obtain ⟨c, hf, -, han⟩ := Cached.checkDecls_consts V accepted hg rfl
  unfold AnnotOf at han
  simp only [gEqTy, gEqB, nv, eqE, natC, lamB, succC, Expr.zeta, Expr.resetMeta] at han
  obtain ⟨A, B, m₀, he, hA, hB⟩ := rm_forallE han
  obtain ⟨f, a, rfl, hf', ha⟩ := rm_app hB
  obtain ⟨l, x, rfl, hl, hx⟩ := rm_app ha
  obtain ⟨T, Bd, m₁, rfl, hT, hBd⟩ := rm_lam hl
  have := (BF.inv (by simp [BF, natC]) hA); subst this
  have := (BF.inv bf_eqHead hf'); subst this
  have := (BF.inv (by simp [BF, natC]) hT); subst this
  have := (BF.inv (by simp [BF, lamB, succC]) hBd); subst this
  have := (BF.inv (by simp [BF]) hx); subst this
  exact ⟨c, m₀, m₁, hf, he⟩

theorem stored_ne (V : Type w) [SetTheory V] {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
    (accepted : Cached.checkDecls .verified pins ds = .ok env) {v : Expr}
    (hn : Declaration.thmDecl ⟨nm "ne12", [], neTy⟩ v ∈ ds) :
    ∃ c m, env.find? (nm "ne12") = some c ∧ c.toConstantVal.type = .forallE neA (.const falseName []) m := by
  obtain ⟨c, hf, -, han⟩ := Cached.checkDecls_consts V accepted hn rfl
  unfold AnnotOf at han
  simp only [neTy, neA, nv, eqE, natC, succC, zC, Expr.zeta, Expr.resetMeta] at han
  obtain ⟨A, B, m, he, hA, hB⟩ := rm_forallE han
  have := (BF.inv (by simp [BF]) hA); subst this
  have := (BF.inv (by simp [BF]) hB); subst this
  exact ⟨c, m, hf, he⟩

/-- **The data λ stored in `g_eq` is read in regime 1, at every level assignment**, whatever binder data the
checker stored on it.  Hypotheses: acceptance, the two declarations, and the Nat basis (`natLitSupported`). -/
theorem lam_regime_g {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
    (accepted : Cached.checkDecls .verified pins ds = .ok env) (hnat : natLitSupported env = true) {v w : Expr}
    (hg : Declaration.thmDecl ⟨nm "g_eq", [], gEqTy⟩ v ∈ ds)
    (hn : Declaration.thmDecl ⟨nm "ne12", [], neTy⟩ w ∈ ds) (M : Model V env) :
    ∃ c m₀ m₁, env.find? (nm "g_eq") = some c ∧ c.toConstantVal.type = .forallE natC (gEqB m₁) m₀ ∧
      ∀ φ : LevelParam → Nat, regime φ m₁.pw ≠ 0 := by
  obtain ⟨c, m₀, m₁, hc, hty⟩ := stored_g V accepted hg
  obtain ⟨cn, mn, hcn, htyn⟩ := stored_ne V accepted hn
  refine ⟨c, m₀, m₁, hc, hty, fun φ => ?_⟩
  let ρ : BVarIdx → V := fun _ => empty
  have hz : ∀ ρ', Denotes M.cval env φ ρ' zC (natV M φ 0) := by
    intro ρ'
    obtain ⟨-, -, cv0, i0, j0, -, -, -, -, h, -, -, hl, -⟩ := natLitSupported_inv hnat
    exact den_const0 M h hl φ ρ'
  have h1 : ∀ ρ', Denotes M.cval env φ ρ' (.app succC zC) (natV M φ 1) := fun ρ' => .app (succ_den M hnat φ ρ') (hz ρ')
  have h2 : ∀ ρ', Denotes M.cval env φ ρ' (.app succC (.app succC zC)) (natV M φ 2) :=
    fun ρ' => .app (succ_den M hnat φ ρ') (h1 ρ')
  -- ⟦1⟧ ≠ ⟦2⟧, from the stored `ne12`
  have hne : natV M φ 1 ≠ natV M φ 2 :=
    ne_of_stored_neg (u := L1) (U := natC) (a := .app succC zC) (b := .app succC (.app succC zC)) M (find?_mem hcn) htyn φ ρ (nat_den M hnat φ ρ) (h1 ρ) (h2 ρ)
      (by simpa [L1, Level.eval] using nat_univ M hnat φ) (natV_mem M hnat φ ρ 1) (natV_mem M hnat φ ρ 2)
  -- the λ's derivation inside `Model.mem` of `g_eq`, at x = ⟦0⟧
  obtain ⟨T, hT, -⟩ := const_mem M hc φ ρ
  rw [hty] at hT
  cases hT with
  | pi hA hB _ =>
    obtain rfl := Denotes_functional hA (nat_den M hnat φ ρ)
    have hx0 := natV_mem M hnat φ ρ 0
    obtain ⟨Bx, hBx⟩ : ∃ Bx, Denotes M.cval env φ (push (natV M φ 0) ρ) (gEqB m₁) Bx := ⟨_, hB _ hx0⟩
    cases hBx with
    | app _ hr =>
      cases hr with
      | app hl _ =>
        exact lam_regime_ne hl (nat_den M hnat φ _) hx0 (natV_mem M hnat φ ρ 1)
          (.app (succ_den M hnat φ _) .bvar) (.app (succ_den M hnat φ _) .bvar) hne

end Bridge.Real.LamDemo
