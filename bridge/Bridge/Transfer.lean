/- Bridge.Transfer: the n-binder transfer kit (DENOTES_SPIKE.md §2, §7 row 1).

Everything is about an ARBITRARY `Model V env` (what `model_exists` gives).  The one source of facts is
`Model.mem`: every stored constant is a member of what its type denotes.  So the TYPE of a stored theorem
denotes an inhabited set; peeling binders keeps it inhabited (`Inhab.pi`), and an inhabited
`@Eq.{u} S a b` forces `⟦a⟧ = ⟦b⟧` (`Inhab.eq`).  The denotations of `S`, `a`, `b` come out of the type's
own denotation (inversion), so the caller never has to build them; only the three membership facts that
`eq_equality` asks for remain (`Typing.lean` produces those).

No regime (`PropWhen`) hypothesis anywhere: `beta` below holds in both regimes, given that the redex
denotes at all (and every redex inside a stored type does, by `mem`).

STATUS: COMPILES unchanged (0 errors, 0 warnings, no sorry) with `lake env lean` in con-leche @3b37939, Lean 4.35.0-rc3; `#print axioms Bridge.transferN` = propext, Classical.choice, Quot.sound. -/
import ConLeche.Denotes
import ConLeche.SetModel.Ops

namespace Bridge
open ConLeche ConLeche.SetModel SetTheory

universe w
variable {V : Type w} [SetTheory V] {env : Env}

/-! ## env lookups -/

theorem find?_name {n : Name} {ci : ConstantInfo} (h : env.find? n = some ci) : ci.name = n := by
  unfold Env.find? at h
  simpa using List.find?_some h

theorem find?_mem {n : Name} {ci : ConstantInfo} (h : env.find? n = some ci) : ci ∈ env.consts := by
  unfold Env.find? at h
  exact List.mem_of_find?_eq_some h

/-- A stored constant at level arguments `us` denotes `cval n` at the induced assignment. -/
theorem Denotes_const' {cval : Name → (LevelParam → Nat) → V} {φ : LevelParam → Nat} {ρ : BVarIdx → V}
    {n : Name} {ci : ConstantInfo} {us : List Level} {ps : List LevelParam}
    (h : env.find? n = some ci) (hps : ci.toConstantVal.levelParams = ps) (hlen : us.length = ps.length) :
    Denotes cval env φ ρ (.const n us) (cval n (Level.substFn φ ps us)) := by
  subst hps; exact .const h hlen

/-! ## inversions -/

theorem app_inv {cval : Name → (LevelParam → Nat) → V} {φ : LevelParam → Nat} {ρ : BVarIdx → V}
    {f a : Expr} {R : V} (h : Denotes cval env φ ρ (.app f a) R) :
    ∃ F X, Denotes cval env φ ρ f F ∧ Denotes cval env φ ρ a X ∧ R = app F X := by
  cases h with
  | app hf ha => exact ⟨_, _, hf, ha, rfl⟩

theorem lam_inv {cval : Name → (LevelParam → Nat) → V} {φ : LevelParam → Nat} {ρ : BVarIdx → V}
    {T b : Expr} {m : BinderMeta} {L : V} (h : Denotes cval env φ ρ (.lam T b m) L) :
    ∃ A F, Denotes cval env φ ρ T A ∧ (∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) b (F x)) ∧
      (regime φ m.pw = 0 → ∀ x, x ∈ˢ A → F x = pt) ∧ L = lamR (regime φ m.pw) A F := by
  cases h with
  | lam hA hF hP => exact ⟨_, _, hA, hF, hP, rfl⟩

theorem pi_inv {cval : Name → (LevelParam → Nat) → V} {φ : LevelParam → Nat} {ρ : BVarIdx → V}
    {T b : Expr} {m : BinderMeta} {P : V} (h : Denotes cval env φ ρ (.forallE T b m) P) :
    ∃ A B, Denotes cval env φ ρ T A ∧ (∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) b (B x)) ∧
      (regime φ m.pw = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) ∧ P = piR (regime φ m.pw) A B := by
  cases h with
  | pi hA hB hP => exact ⟨_, _, hA, hB, hP, rfl⟩

/-! ## beta in both regimes -/

/-- Application of a denoted `λ` to a member of its domain, in EITHER regime: in regime `0` both sides
are `pt` (the `lam` rule's own side condition). -/
theorem app_lam_any {r : Nat} {A x : V} {F : V → V} (hP : r = 0 → ∀ x, x ∈ˢ A → F x = pt)
    (hx : x ∈ˢ A) : app (lamR r A F) x = F x := by
  by_cases hr : r = 0
  · subst hr; rw [lamR_zero, app_pt, hP rfl x hx]
  · exact app_lamR_pos hr hx

/-- **Beta, regime-free.**  If the redex `(λ T. b) v` denotes `R`, and `⟦v⟧ ∈ ⟦T⟧`, then `b` denotes
`R` at `push ⟦v⟧ ρ`.  (A nano `let` emitted as a redex; DENOTES_SPIKE.md §2.) -/
theorem beta {cval : Name → (LevelParam → Nat) → V} {φ : LevelParam → Nat} {ρ : BVarIdx → V}
    {T b v : Expr} {m : BinderMeta} {A X R : V}
    (hR : Denotes cval env φ ρ (.app (.lam T b m) v) R) (hA : Denotes cval env φ ρ T A)
    (hv : Denotes cval env φ ρ v X) (hX : X ∈ˢ A) : Denotes cval env φ (push X ρ) b R := by
  obtain ⟨L, X', hL, hv', rfl⟩ := app_inv hR
  obtain rfl := Denotes_functional hv hv'
  obtain ⟨A', F, hA', hF, hP, rfl⟩ := lam_inv hL
  obtain rfl := Denotes_functional hA hA'
  rw [app_lam_any hP hX]; exact hF X hX

/-! ## typing steps (set level) -/

/-- **Application typing.**  `F` in what a `∀ T. B` denotes, `X ∈ ⟦T⟧`: `app F X` is in what `B` denotes
at `push X ρ`.  Both regimes (the `pi` rule carries the regime-0 side condition). -/
theorem mem_app {cval : Name → (LevelParam → Nat) → V} {φ : LevelParam → Nat} {ρ : BVarIdx → V}
    {T B : Expr} {m : BinderMeta} {P F A X : V}
    (hP : Denotes cval env φ ρ (.forallE T B m) P) (hF : F ∈ˢ P) (hA : Denotes cval env φ ρ T A)
    (hX : X ∈ˢ A) : ∃ Bx, Denotes cval env φ (push X ρ) B Bx ∧ app F X ∈ˢ Bx := by
  obtain ⟨A', Bf, hA', hB, h0, rfl⟩ := pi_inv hP
  obtain rfl := Denotes_functional hA hA'
  refine ⟨Bf X, hB X hX, app_mem_piR hF hX ?_⟩
  intro hr x hx; rw [← univ_zero]; exact h0 hr x hx

/-- A stored constant used at levels `us` is a member of what its stored type denotes at the induced
level assignment. -/
theorem const_mem (M : Model V env) {n : Name} {ci : ConstantInfo} (h : env.find? n = some ci)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    ∃ T, Denotes M.cval env φ ρ ci.toConstantVal.type T ∧ M.cval n φ ∈ˢ T := by
  obtain ⟨T, hT, hm⟩ := M.mem ci (find?_mem h) φ ρ
  have hn : ci.name = n := find?_name h
  exact ⟨T, hT, by rw [← hn]; exact hm⟩

/-! ## transfer, n binders -/

/-- The type `e` denotes an inhabited set at `φ, ρ`. -/
def Inhab (M : Model V env) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (e : Expr) : Prop :=
  ∃ P, Denotes M.cval env φ ρ e P ∧ ∃ y, y ∈ˢ P

/-- The type of every stored constant is inhabited (at every `φ`, `ρ`). -/
theorem inhab_const (M : Model V env) {n : Name} {ci : ConstantInfo} (h : env.find? n = some ci)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) : Inhab M φ ρ ci.toConstantVal.type := by
  obtain ⟨T, hT, hm⟩ := const_mem M h φ ρ
  exact ⟨T, hT, _, hm⟩

/-- Peel one binder: inhabited `∀ T. B` ⇒ `B` inhabited at `push x ρ` for every `x ∈ ⟦T⟧`. -/
theorem Inhab.pi {M : Model V env} {φ : LevelParam → Nat} {ρ : BVarIdx → V} {T B : Expr} {m : BinderMeta}
    {A x : V} (h : Inhab M φ ρ (.forallE T B m)) (hA : Denotes M.cval env φ ρ T A) (hx : x ∈ˢ A) :
    Inhab M φ (push x ρ) B := by
  obtain ⟨P, hP, y, hy⟩ := h
  obtain ⟨Bx, hB, hm⟩ := mem_app hP hy hA hx
  exact ⟨Bx, hB, _, hm⟩

/-- The stored spelling of `@Eq.{u} S a b`. -/
def eqE (u : Level) (S a b : Expr) : Expr := .app (.app (.app (.const eqName [u]) S) a) b

/-- **Inhabited equation.**  `S`, `a`, `b` denote (read off the type's own denotation), and given the three
membership facts `eq_equality` asks for, the two sides denote the same set. -/
theorem Inhab.eq {M : Model V env} {φ : LevelParam → Nat} {ρ : BVarIdx → V} {u : Level} {S a b : Expr}
    (h : Inhab M φ ρ (eqE u S a b)) :
    ∃ Sv av bv, Denotes M.cval env φ ρ S Sv ∧ Denotes M.cval env φ ρ a av ∧ Denotes M.cval env φ ρ b bv ∧
      (Sv ∈ˢ univ (Level.eval φ u) → av ∈ˢ Sv → bv ∈ˢ Sv → av = bv) := by
  obtain ⟨P, hP, y, hy⟩ := h
  obtain ⟨F2, bv, h3, hb, rfl⟩ := app_inv hP
  obtain ⟨F1, av, h2, ha, rfl⟩ := app_inv h3
  obtain ⟨E, Sv, hE, hS, rfl⟩ := app_inv h2
  refine ⟨Sv, av, bv, hS, ha, hb, fun hSu hav hbv => ?_⟩
  rw [M.eq_equality u φ ρ _ _ _ _ hE hSu hav hbv] at hy
  exact eq_of_mem_eqv hy

/-- Same, with given denotations for the two sides (the usual call shape). -/
theorem Inhab.eq' {M : Model V env} {φ : LevelParam → Nat} {ρ : BVarIdx → V} {u : Level} {S a b : Expr}
    {Sv av bv : V} (h : Inhab M φ ρ (eqE u S a b)) (hS : Denotes M.cval env φ ρ S Sv)
    (ha : Denotes M.cval env φ ρ a av) (hb : Denotes M.cval env φ ρ b bv)
    (hSu : Sv ∈ˢ univ (Level.eval φ u)) (hav : av ∈ˢ Sv) (hbv : bv ∈ˢ Sv) : av = bv := by
  obtain ⟨Sv', av', bv', hS', ha', hb', k⟩ := h.eq
  obtain rfl := Denotes_functional hS hS'
  obtain rfl := Denotes_functional ha ha'
  obtain rfl := Denotes_functional hb hb'
  exact k hSu hav hbv

/-- A telescope of binders `∀ (x₁ : T₁) … (xₙ : Tₙ), b` (types may mention earlier binders). -/
def piN : List (Expr × BinderMeta) → Expr → Expr
  | [], b => b
  | (T, m) :: Ts, b => .forallE T (piN Ts b) m

/-- `Tele M φ ρ Ts ρ'`: `ρ'` extends `ρ` by one member of each binder type, in order (dependent). -/
inductive Tele (M : Model V env) (φ : LevelParam → Nat) :
    (BVarIdx → V) → List (Expr × BinderMeta) → (BVarIdx → V) → Prop
  | nil {ρ} : Tele M φ ρ [] ρ
  | cons {ρ ρ' T m Ts A x} : Denotes M.cval env φ ρ T A → x ∈ˢ A → Tele M φ (push x ρ) Ts ρ' →
      Tele M φ ρ ((T, m) :: Ts) ρ'

theorem Inhab.piN {M : Model V env} {φ : LevelParam → Nat} :
    ∀ {ρ ρ' : BVarIdx → V} {Ts : List (Expr × BinderMeta)} {b : Expr},
      Inhab M φ ρ (Bridge.piN Ts b) → Tele M φ ρ Ts ρ' → Inhab M φ ρ' b
  | _, _, [], _, h, .nil => h
  | _, _, (_, _) :: _, _, h, .cons hA hx ht => Inhab.piN (Inhab.pi h hA hx) ht

/-- **Transfer, n binders.**  A stored theorem `thm : ∀ (x₁ : T₁) … (xₙ : Tₙ), @Eq.{u} S a b` (closed, so
any `ρ` will do as the start): at every telescope instance `ρ'`, `⟦a⟧ρ' = ⟦b⟧ρ'`, given the membership
facts.  Usage: `transferN M hfind hty φ ρ ht hS ha hb hSu hav hbv`. -/
theorem transferN (M : Model V env) {n : Name} {ci : ConstantInfo} (h : env.find? n = some ci)
    {Ts : List (Expr × BinderMeta)} {u : Level} {S a b : Expr}
    (hty : ci.toConstantVal.type = piN Ts (eqE u S a b))
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) {ρ' : BVarIdx → V} (ht : Tele M φ ρ Ts ρ')
    {Sv av bv : V} (hS : Denotes M.cval env φ ρ' S Sv)
    (ha : Denotes M.cval env φ ρ' a av) (hb : Denotes M.cval env φ ρ' b bv)
    (hSu : Sv ∈ˢ univ (Level.eval φ u)) (hav : av ∈ˢ Sv) (hbv : bv ∈ˢ Sv) : av = bv := by
  have h0 := inhab_const M h φ ρ
  rw [hty] at h0
  exact (h0.piN ht).eq' hS ha hb hSu hav hbv

/-- Telescope of one binder (most common shapes, to avoid writing `Tele.cons … .nil`). -/
theorem tele1 {M : Model V env} {φ : LevelParam → Nat} {ρ : BVarIdx → V} {T : Expr} {m : BinderMeta}
    {A x : V} (hA : Denotes M.cval env φ ρ T A) (hx : x ∈ˢ A) : Tele M φ ρ [(T, m)] (push x ρ) :=
  .cons hA hx .nil

theorem tele2 {M : Model V env} {φ : LevelParam → Nat} {ρ : BVarIdx → V} {T1 T2 : Expr} {m1 m2 : BinderMeta}
    {A1 A2 x y : V} (h1 : Denotes M.cval env φ ρ T1 A1) (hx : x ∈ˢ A1)
    (h2 : Denotes M.cval env φ (push x ρ) T2 A2) (hy : y ∈ˢ A2) :
    Tele M φ ρ [(T1, m1), (T2, m2)] (push y (push x ρ)) :=
  .cons h1 hx (.cons h2 hy .nil)

end Bridge
