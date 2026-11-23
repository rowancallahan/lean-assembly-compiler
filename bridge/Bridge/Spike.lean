-- DRAFT, NOT BUILT (needs con-leche built; owner: do not build it tonight). Moved from Testing/denotes_spike.
/- DENOTES spike (nano ↔ con-leche).  Checked against con-leche @ main on Lean 4.35.0-rc3 with
`lake env lean DenotesSpike.lean` from the con-leche checkout.  Everything here is about an ARBITRARY
`Model V env` (what `model_exists` gives): the only facts about constants are `mem`, `false_empty`,
`eq_equality`. -/
import ConLeche.Denotes
import ConLeche.SetModel.Ops

namespace DenotesSpike
open ConLeche ConLeche.SetModel SetTheory

universe w
variable {V : Type w} [SetTheory V]

/-- A member of a dependent product (either regime) has an inhabitant in every fibre on the domain. -/
theorem fibre_inhabited {r : Nat} {A f : V} {B : V → V} (hf : f ∈ˢ piR r A B) :
    ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x := by
  intro x hx
  by_cases hr : r = 0
  · subst hr; rw [piR_zero] at hf; exact of_mem_truthVal hf x hx
  · exact ⟨_, app_mem_piR_pos hr hf hx⟩

/-- Inversion of the `app` rule. -/
theorem app_inv {env : Env} {cval : Name → (LevelParam → Nat) → V} {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {f a : Expr} {R : V} (h : Denotes cval env φ ρ (.app f a) R) :
    ∃ F X, Denotes cval env φ ρ f F ∧ Denotes cval env φ ρ a X ∧ R = app F X := by
  cases h with
  | app hf ha => exact ⟨_, _, hf, ha, rfl⟩

/-- **Transfer, one binder.**  If the env stores a constant (a theorem) of type
`∀ x : T, @Eq.{u} S a b`, then in every model, on the domain of `T`, `a` and `b` denote the same set
(given the membership facts that `eq_equality` asks for). -/
theorem transfer1 {env : Env} (M : Model V env) {c : ConstantInfo} (hc : c ∈ env.consts)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    {T S a b : Expr} {m : BinderMeta} {u : Level}
    (hty : c.toConstantVal.type = .forallE T (.app (.app (.app (.const eqName [u]) S) a) b) m)
    {A : V} (hA : Denotes M.cval env φ ρ T A) {Sx ax bx : V → V}
    (hS : ∀ x, x ∈ˢ A → Denotes M.cval env φ (push x ρ) S (Sx x))
    (ha : ∀ x, x ∈ˢ A → Denotes M.cval env φ (push x ρ) a (ax x))
    (hb : ∀ x, x ∈ˢ A → Denotes M.cval env φ (push x ρ) b (bx x))
    (hSu : ∀ x, x ∈ˢ A → Sx x ∈ˢ univ (Level.eval φ u))
    (hax : ∀ x, x ∈ˢ A → ax x ∈ˢ Sx x) (hbx : ∀ x, x ∈ˢ A → bx x ∈ˢ Sx x) :
    ∀ x, x ∈ˢ A → ax x = bx x := by
  obtain ⟨Tt, hD, hmem⟩ := M.mem c hc φ ρ
  rw [hty] at hD
  cases hD with
  | pi hA' hB _ =>
    obtain rfl := Denotes_functional hA hA'
    intro x hx
    obtain ⟨y, hy⟩ := fibre_inhabited hmem x hx
    obtain ⟨F2, Bv, h3, hbD, e3⟩ := app_inv (hB x hx)
    obtain ⟨F1, Av, h2, haD, e2⟩ := app_inv h3
    obtain ⟨E, Sv, hE, hSD, e1⟩ := app_inv h2
    rw [e3] at hy; subst e2 e1
    obtain rfl := Denotes_functional (hS x hx) hSD
    obtain rfl := Denotes_functional (ha x hx) haD
    obtain rfl := Denotes_functional (hb x hx) hbD
    rw [M.eq_equality u φ (push x ρ) _ _ _ _ hE (hSu x hx) (hax x hx) (hbx x hx)] at hy
    exact eq_of_mem_eqv hy


/-- **Transfer, no binder**: a stored theorem `@Eq.{u} S a b` makes `a` and `b` denote the same set. -/
theorem transfer0 {env : Env} (M : Model V env) {c : ConstantInfo} (hc : c ∈ env.consts)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) {S a b : Expr} {u : Level}
    (hty : c.toConstantVal.type = .app (.app (.app (.const eqName [u]) S) a) b)
    {Sv av bv : V} (hS : Denotes M.cval env φ ρ S Sv) (ha : Denotes M.cval env φ ρ a av)
    (hb : Denotes M.cval env φ ρ b bv) (hSu : Sv ∈ˢ univ (Level.eval φ u))
    (hav : av ∈ˢ Sv) (hbv : bv ∈ˢ Sv) : av = bv := by
  obtain ⟨Tt, hD, hmem⟩ := M.mem c hc φ ρ
  rw [hty] at hD
  obtain ⟨F2, Bv, h3, hbD, e3⟩ := app_inv hD
  obtain ⟨F1, Av, h2, haD, e2⟩ := app_inv h3
  obtain ⟨E, Sv', hE, hSD, e1⟩ := app_inv h2
  rw [e3] at hmem; subst e2 e1
  obtain rfl := Denotes_functional hS hSD
  obtain rfl := Denotes_functional ha haD
  obtain rfl := Denotes_functional hb hbD
  rw [M.eq_equality u φ ρ _ _ _ _ hE hSu hav hbv] at hmem
  exact eq_of_mem_eqv hmem

/-- **A call of a program def `f`** (one argument shown): with the stored theorem `f = λ (x : T). body`
(nano emits it, Lean proves it by `rfl`), `f a` denotes the body at `push ⟦a⟧ ρ`. -/
theorem Denotes_call {env : Env} (M : Model V env) {c : ConstantInfo} (hc : c ∈ env.consts)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) {S T body a : Expr} {m : BinderMeta} {u : Level} {f : Name}
    (hty : c.toConstantVal.type =
      .app (.app (.app (.const eqName [u]) S) (.const f [])) (.lam T body m))
    {Sv Fv A X R : V} {G : V → V} (hreg : regime φ m.pw ≠ 0)
    (hS : Denotes M.cval env φ ρ S Sv) (hf : Denotes M.cval env φ ρ (.const f []) Fv)
    (hA : Denotes M.cval env φ ρ T A)
    (hG : ∀ x, x ∈ˢ A → Denotes M.cval env φ (push x ρ) body (G x))
    (hSu : Sv ∈ˢ univ (Level.eval φ u)) (hFv : Fv ∈ˢ Sv) (hL : lamR (regime φ m.pw) A G ∈ˢ Sv)
    (ha : Denotes M.cval env φ ρ a X) (hX : X ∈ˢ A)
    (hR : Denotes M.cval env φ ρ (.app (.const f []) a) R) : R = G X := by
  have hlam : Denotes M.cval env φ ρ (.lam T body m) (lamR (regime φ m.pw) A G) :=
    .lam hA hG (fun h => absurd h hreg)
  have heq := transfer0 M hc φ ρ hty hS hf hlam hSu hFv hL
  rw [Denotes_functional hR (.app hf ha), heq, app_lamR_pos hreg hX]

/-! ## Nat: the canonical encoding and literals -/

/-- `natEnc k` = what the constructor numeral `succ^k zero` denotes (constants with no level params). -/
noncomputable def natEnc {env : Env} (M : Model V env) (φ : LevelParam → Nat) : Nat → V
  | 0 => M.cval natZeroName (Level.substFn φ [] [])
  | k + 1 => app (M.cval natSuccName (Level.substFn φ [] [])) (natEnc M φ k)

/-- A literal `lit k` denotes `natEnc k` (given `Nat.zero`/`Nat.succ` are stored without level params). -/
theorem Denotes_lit {env : Env} (M : Model V env) (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    {cz cs : ConstantInfo} (hz : env.find? natZeroName = some cz)
    (hz0 : cz.toConstantVal.levelParams = [])
    (hs : env.find? natSuccName = some cs) (hs0 : cs.toConstantVal.levelParams = []) :
    ∀ k, Denotes M.cval env φ ρ (.lit (.natVal k)) (natEnc M φ k) := by
  have dz : Denotes M.cval env φ ρ (.const natZeroName []) (natEnc M φ 0) := by
    have h := Denotes.const (cval := M.cval) (env := env) (φ := φ) (ρ := ρ) (us := []) hz
      (by rw [hz0]; rfl)
    rwa [hz0] at h
  have ds : Denotes M.cval env φ ρ (.const natSuccName [])
      (M.cval natSuccName (Level.substFn φ [] [])) := by
    have h := Denotes.const (cval := M.cval) (env := env) (φ := φ) (ρ := ρ) (us := []) hs
      (by rw [hs0]; rfl)
    rwa [hs0] at h
  intro k
  induction k with
  | zero => exact .natLit dz
  | succ k ih => exact .natLit (.app ds ih)

/-! ## A nano `let` as a beta-redex: `Denotes` has no `letE` rule, the redex form computes. -/

/-- `(λ (x : T). b) v` denotes `b` at `push ⟦v⟧ ρ`, in the graph regime, for `⟦v⟧` in `⟦T⟧`. -/
theorem Denotes_beta {env : Env} {cval : Name → (LevelParam → Nat) → V} {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {T b v : Expr} {m : BinderMeta} {A X R : V} {F : V → V}
    (hreg : regime φ m.pw ≠ 0)
    (hA : Denotes cval env φ ρ T A) (hF : ∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) b (F x))
    (hv : Denotes cval env φ ρ v X) (hX : X ∈ˢ A)
    (hR : Denotes cval env φ ρ (.app (.lam T b m) v) R) : R = F X := by
  have hlam : Denotes cval env φ ρ (.lam T b m) (lamR (regime φ m.pw) A F) :=
    .lam hA hF (fun h => absurd h hreg)
  have h := Denotes_functional hR (.app hlam hv)
  rw [h, app_lamR_pos hreg hX]


/-! ## Per-constant facts at the set level.  `ADD`, `OF`, ... are the sets the model gives the applied
constant heads (e.g. `ADD = ⟦@HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat)⟧`); the hypotheses are exactly what
`transfer` yields from the named Lean theorems stored in the env. -/

section SetLevel
variable (Z S : V)

/-- the constructor numeral as sets -/
noncomputable def nat : Nat → V
  | 0 => Z
  | k + 1 => app S (nat k)

/-- `Nat.add` from its two recursion theorems (`n + 0 = n`, `n + succ m = succ (n + m)`). -/
theorem add_nat (ADD : V) (hz : ∀ x, app (app ADD x) Z = x)
    (hs : ∀ x y, app (app ADD x) (app S y) = app S (app (app ADD x) y)) :
    ∀ a b, app (app ADD (nat Z S a)) (nat Z S b) = nat Z S (a + b) := by
  intro a b
  induction b with
  | zero => exact hz _
  | succ b ih => rw [nat, hs, ih]; rfl

/-- **UInt64.add.**  Encoding: `u64 x = ⟦UInt64.ofNat⟧ (nat x.toNat)`.  Theorems used:
`br_add : ∀ a b : Nat, UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b)` and
`br_wrap : ∀ n, UInt64.ofNat (n + 2^64) = UInt64.ofNat n`, plus the `Nat.add` recursion. -/
theorem add_u64 (ADD ADD64 OF : V) (hz : ∀ x, app (app ADD x) Z = x)
    (hs : ∀ x y, app (app ADD x) (app S y) = app S (app (app ADD x) y))
    (hadd : ∀ x y, app (app ADD64 (app OF x)) (app OF y) = app OF (app (app ADD x) y))
    (hwrap : ∀ x, app OF (app (app ADD x) (nat Z S UInt64.size)) = app OF x) :
    ∀ x y : UInt64, app (app ADD64 (app OF (nat Z S x.toNat))) (app OF (nat Z S y.toNat)) =
      app OF (nat Z S (x + y).toNat) := by
  intro x y
  rw [hadd, add_nat Z S ADD hz hs, UInt64.toNat_add, show (2:Nat) ^ 64 = UInt64.size from rfl]
  have hx := x.toNat_lt_size; have hy := y.toNat_lt_size
  generalize UInt64.size = N at hx hy hwrap ⊢
  by_cases h : x.toNat + y.toNat < N
  · rw [Nat.mod_eq_of_lt h]
  · have hk : x.toNat + y.toNat = (x.toNat + y.toNat - N) + N := by omega
    have hm : (x.toNat + y.toNat) % N = x.toNat + y.toNat - N := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hm, hk, ← add_nat Z S ADD hz hs, hwrap, Nat.add_sub_cancel]

/-- **ite on an `Eq Bool c true` condition.**  Theorems used: `@ite R (true = true) (instDecidableEqBool true true)
t e = t` and its `false` twin (both `rfl`), as `ITE_T`/`ITE_F` (the heads applied to the instance at `c`). -/
theorem ite_bool (ITE_T ITE_F : V) (R t e : V)
    (ht : app (app (app ITE_T R) t) e = t) (hf : app (app (app ITE_F R) t) e = e) (c : Bool) :
    app (app (app (if c then ITE_T else ITE_F) R) t) e = if c then t else e := by
  cases c <;> simpa

/-- **List.cons needs no theorem**: a constructor application IS the encoding. -/
noncomputable def list (NIL CONS T : V) (enc : UInt8 → V) : List UInt8 → V
  | [] => app NIL T
  | a :: l => app (app (app CONS T) (enc a)) (list NIL CONS T enc l)

end SetLevel

end DenotesSpike


