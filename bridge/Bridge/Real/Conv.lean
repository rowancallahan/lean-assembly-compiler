/- Bridge.Real.Conv: equational evaluation, sound in the real model.

`Conv tab eqs thms Γ a b T`: `a` and `b` (binder-free, context `Γ` of closed types) are equal at type `T`,
derived from reflexivity (with engine typing), symmetry, transitivity, argument congruence under a head, and
INSTANCES of stored equations `thms` (each a theorem record `∀ (xᵢ : Tᵢ), @Eq.{u} S lhs rhs` of the accepted
stream, closed `Tᵢ` and `S`).  `conv_sound`: both sides denote the same set, a member of what `T` denotes.
A program run `f (enc v) ⇝ enc out` written as a `Conv` derivation is therefore `⟦f v⟧ = ⟦out⟧` in the model of
`model_exists'`. -/
import Bridge.Real.Engine2

namespace Bridge.Real.Engine
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real Bridge.ModelExists2

universe w
variable {V : Type w} [SetTheory V] {env : Env}

/-- a stored equation, by its declared statement -/
structure Thm where
  n : Name
  Ts : List Expr
  u : Level
  S : Expr
  lhs : Expr
  rhs : Expr
  deriving DecidableEq

def Thm.stmt (t : Thm) : Expr := piV t.Ts (eqE t.u t.S t.lhs t.rhs)

/-- syntactic side conditions, decidable -/
def Thm.ok (tab : Tab) (eqs : List (Expr × Expr)) (t : Thm) (k : Nat) : Bool :=
  t.Ts.all (sc 0) && sc 0 t.S && sc t.Ts.length t.lhs && sc t.Ts.length t.rhs &&
    infer tab eqs t.Ts.reverse k t.S == some (.sort t.u) &&
    infer tab eqs t.Ts.reverse k t.lhs == some t.S && infer tab eqs t.Ts.reverse k t.rhs == some t.S

/-- arguments typed against CLOSED binder types -/
inductive ArgsC (tab : Tab) (eqs : List (Expr × Expr)) (Γ : List Expr) : List Expr → List Expr → Prop
  | nil : ArgsC tab eqs Γ [] []
  | cons {T Ts a as} : HasTy tab eqs Γ a T → ArgsC tab eqs Γ Ts as → ArgsC tab eqs Γ (T :: Ts) (a :: as)

mutual
inductive Conv (tab : Tab) (eqs : List (Expr × Expr)) (thms : List Thm) (Γ : List Expr) :
    Expr → Expr → Expr → Prop
  | refl {a T} : HasTy tab eqs Γ a T → Conv tab eqs thms Γ a a T
  | symm {a b T} : Conv tab eqs thms Γ a b T → Conv tab eqs thms Γ b a T
  | trans {a b c T} : Conv tab eqs thms Γ a b T → Conv tab eqs thms Γ b c T → Conv tab eqs thms Γ a c T
  /-- congruence in the arguments of a typed head spine -/
  | cong {h : Expr} {as bs : List Expr} {Ts : List Expr} {T : Expr} :
      HasTy tab eqs Γ (apps h as) T → ConvL tab eqs thms Γ as bs Ts → Conv tab eqs thms Γ (apps h as) (apps h bs) T
  /-- con-leche reads a literal `k+1` as `Nat.succ k` (`Denotes.natLit`) -/
  | litS {k : Nat} : Conv tab eqs thms Γ (.lit (.natVal (k + 1))) (.app Tiny.succC (.lit (.natVal k))) Tiny.natC
  /-- con-leche reads the literal `0` as `Nat.zero` (`Denotes.natLit`) -/
  | lit0 : Conv tab eqs thms Γ (.lit (.natVal 0)) (.const natZeroName []) Tiny.natC
  /-- an instance of a stored equation at typed arguments (outermost binder first) -/
  | inst {t : Thm} {as : List Expr} : t ∈ thms → ArgsC tab eqs Γ t.Ts as →
      Conv tab eqs thms Γ (substB as.reverse t.lhs) (substB as.reverse t.rhs) t.S
/-- pointwise conversion of argument lists -/
inductive ConvL (tab : Tab) (eqs : List (Expr × Expr)) (thms : List Thm) (Γ : List Expr) :
    List Expr → List Expr → List Expr → Prop
  | nil : ConvL tab eqs thms Γ [] [] []
  | cons {a b T as bs Ts} : Conv tab eqs thms Γ a b T → ConvL tab eqs thms Γ as bs Ts →
      ConvL tab eqs thms Γ (a :: as) (b :: bs) (T :: Ts)
end

/-! ## soundness -/

theorem subst_nil : ∀ l : Level, Level.subst [] [] l = l
  | .zero => rfl
  | .succ l => by simp [Level.subst, subst_nil l]
  | .max a b => by simp [Level.subst, subst_nil a, subst_nil b]
  | .imax a b => by simp [Level.subst, subst_nil a, subst_nil b]
  | .param n => rfl

theorem inst_nil : ∀ {k : Nat} {e : Expr}, sc k e = true → inst [] [] e = e
  | _, .bvar _, _ | _, .lit (.natVal _), _ => rfl
  | _, .sort u, _ => by simp [inst, Expr.instantiateLevelParams, subst_nil]
  | _, .const c us, _ => by
    simp only [inst, Expr.instantiateLevelParams]
    congr 1; conv => rhs; rw [← List.map_id us]
    exact List.map_congr_left (fun l _ => subst_nil l)
  | _, .app f a, h => by
    simp only [sc, Bool.and_eq_true] at h
    have h1 := inst_nil h.1; have h2 := inst_nil h.2
    simp only [inst] at h1 h2 ⊢
    simp only [Expr.instantiateLevelParams, h1, h2]
  | _, .lit (.strVal _), h | _, .fvar _ _, h | _, .lam _ _ _, h | _, .forallE _ _ _, h
  | _, .letE _ _ _, h | _, .proj _ _ _, h => by simp [sc] at h

theorem apps_inv {M : Model V env} {φ ρ} : ∀ {f : Expr} {as : List Expr} {X : V},
    Denotes M.cval env φ ρ (apps f as) X → ∃ F xs, Denotes M.cval env φ ρ f F ∧ DenL M φ ρ as xs ∧ X = appN F xs
  | _, [], _, h => ⟨_, [], h, .nil, rfl⟩
  | f, a :: as, X, h => by
    obtain ⟨G, xs, dG, dxs, rfl⟩ := apps_inv (f := .app f a) (as := as) h
    obtain ⟨F, Y, dF, dY, rfl⟩ := app_inv dG
    exact ⟨F, Y :: xs, dF, .cons dY dxs, rfl⟩

theorem DenL.functional {M : Model V env} {φ ρ} : ∀ {as : List Expr} {xs ys : List V},
    DenL M φ ρ as xs → DenL M φ ρ as ys → xs = ys
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons d1 r1, .cons d2 r2 => by rw [Denotes_functional d1 d2, DenL.functional r1 r2]

def ThmsOk (ds : Array Declaration) (tab : Tab) (eqs : List (Expr × Expr))
    (thms : List Thm) : Prop :=
  ∀ t ∈ thms, (∃ v, Declaration.thmDecl ⟨t.n, [], t.stmt⟩ v ∈ ds) ∧ ∃ k, t.ok tab eqs k = true

section
variable {pins : List NatOpPinSet} {ds : Array Declaration}
  (acc : Cached.checkDecls .verified pins ds = .ok env) {M : Model V env} (hP : CvalParams M)
  (hnat : natLitSupported env = true) {tab : Tab} (htab : TabOk M tab) {eqs : List (Expr × Expr)}
  (heqs : EqsOk M eqs) {thms : List Thm} (hthms : ThmsOk ds tab eqs thms)
  {Γ : List Expr} {φ : LevelParam → Nat} {ρ : BVarIdx → V} (hΓ : GammaOk M φ ρ Γ)
include acc hP hnat htab heqs hthms hΓ

theorem argsC_sound : ∀ {Ts as : List Expr}, ArgsC tab eqs Γ Ts as → (∀ T ∈ Ts, sc 0 T = true) →
    ∃ xs, DenL M φ ρ as xs ∧ MemL M φ Ts xs
  | _, _, .nil, _ => ⟨[], .nil, .nil⟩
  | T :: Ts, _, .cons ha hr, hsc => by
    obtain ⟨X, A, dX, dA, hm⟩ := sound hP hnat htab heqs hΓ ha
    obtain ⟨xs, hd, hmL⟩ := argsC_sound hr (fun T h => hsc T (List.mem_cons_of_mem _ h))
    exact ⟨X :: xs, .cons dX hd, .cons (fun ρ' => closed_move (hsc T List.mem_cons_self) dA) hm hmL⟩

mutual
theorem conv_sound : ∀ {a b T : Expr}, Conv tab eqs thms Γ a b T →
    ∃ X A, Denotes M.cval env φ ρ a X ∧ Denotes M.cval env φ ρ b X ∧ Denotes M.cval env φ ρ T A ∧ X ∈ˢ A
  | _, _, _, .refl h => by
    obtain ⟨X, A, dX, dA, hm⟩ := sound hP hnat htab heqs hΓ h
    exact ⟨X, A, dX, dX, dA, hm⟩
  | _, _, _, .symm h => by
    obtain ⟨X, A, d1, d2, dA, hm⟩ := conv_sound h
    exact ⟨X, A, d2, d1, dA, hm⟩
  | _, _, _, .trans h1 h2 => by
    obtain ⟨X, A, d1, d2, dA, hm⟩ := conv_sound h1
    obtain ⟨Y, B, e1, e2, -, -⟩ := conv_sound h2
    exact ⟨X, A, d1, (Denotes_functional e1 d2) ▸ e2, dA, hm⟩
  | _, _, _, .cong (h := hd) (as := as) (bs := bs) hty hl => by
    obtain ⟨X, A, dX, dA, hm⟩ := sound hP hnat htab heqs hΓ hty
    obtain ⟨xs, ha, hb⟩ := convL_sound hl
    refine ⟨X, A, dX, ?_, dA, hm⟩
    obtain ⟨F, ys, dF, dys, rfl⟩ := apps_inv dX
    obtain rfl := DenL.functional dys ha
    exact den_apps dF hb
  | _, _, _, .litS (k := k) => by
    have hd := Tiny.lit_den M hnat φ ρ (k + 1)
    refine ⟨_, _, hd, ?_, Tiny.nat_den M hnat φ ρ, Tiny.natV_mem M hnat φ ρ (k + 1)⟩
    cases hd with | natLit h => exact h
  | _, _, _, .lit0 => by
    have hd := Tiny.lit_den M hnat φ ρ 0
    refine ⟨_, _, hd, ?_, Tiny.nat_den M hnat φ ρ, Tiny.natV_mem M hnat φ ρ 0⟩
    cases hd with | natLit h => exact h
  | _, _, _, .inst (t := t) (as := as) hmem hargs => by
    obtain ⟨hrec, k, hok⟩ := hthms t hmem
    simp only [Thm.ok, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨hTs, hS⟩, hl⟩, hr⟩, tS⟩, tl⟩, tr⟩ := hok
    have hTs' : ∀ T ∈ t.Ts, sc 0 T = true := List.all_eq_true.mp hTs
    obtain ⟨xs, hd, hmL⟩ := argsC_sound acc hP hnat htab heqs hthms hΓ hargs hTs'
    have hΓ' := hmL.gamma (ρ := ρ)
    have tyS := infer_sound k _ _ tS
    have tyl := infer_sound k _ _ tl
    have tyr := infer_sound k _ _ tr
    obtain ⟨X, A, dX, dA, hm⟩ := sound hP hnat htab heqs hΓ' tyl
    obtain ⟨Y, B, dY, dB, -⟩ := sound hP hnat htab heqs hΓ' tyr
    have hXY := etransfer acc hP hnat htab heqs hrec (by simpa using hTs) (by simp [sc_mono (Nat.zero_le _) hS, hl, hr])
      tyS tyl tyr φ ρ hmL dX dY
    subst hXY
    have hlen : as.reverse.length = t.Ts.length := by
      rw [List.length_reverse, hd.length, ← hmL.length]
    have e1 := (inst_den hP (ps := []) (us := []) (ρ0 := ρ) hd.reverse t.lhs (by rw [hlen]; exact hl)).mp dX
    have e2 := (inst_den hP (ps := []) (us := []) (ρ0 := ρ) hd.reverse t.rhs (by rw [hlen]; exact hr)).mp dY
    rw [inst_nil hl] at e1; rw [inst_nil hr] at e2
    exact ⟨X, A, e1, e2, closed_move hS dA, hm⟩
theorem convL_sound : ∀ {as bs Ts : List Expr}, ConvL tab eqs thms Γ as bs Ts →
    ∃ xs, DenL M φ ρ as xs ∧ DenL M φ ρ bs xs
  | _, _, _, .nil => ⟨[], .nil, .nil⟩
  | _, _, _, .cons h hr => by
    obtain ⟨X, -, d1, d2, -, -⟩ := conv_sound h
    obtain ⟨xs, h1, h2⟩ := convL_sound hr
    exact ⟨X :: xs, .cons d1 h1, .cons d2 h2⟩
end
end

end Bridge.Real.Engine
