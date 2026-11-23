/- Bridge.Real.Engine: typing soundness for binder-free terms, against REAL con-leche.

A table of heads (constant name ↦ declared level params, binder domains `Ts`, body `B`, all binder-free and
scoped) and a syntactic judgment `HasTy`: a head at levels `us` applied to arguments whose types are the
instantiated binder domains.  `sound`: in a model with `CvalParams`, a `HasTy` term denotes, and its value is
a member of what its type denotes.  The link between a type denoted at the induced level assignment under the
pushed argument values and the INSTANTIATED type at the program's assignment is `inst_den` (levels by
`eval_subst` + `CvalParams`, bound variables by the arguments' denotations). -/
import Bridge.Real.Spine
import Bridge.Real.Tiny
import Bridge.Real.Scope

namespace Bridge.Real.Engine
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real Bridge.ModelExists2

universe w
variable {V : Type w} [SetTheory V] {env : Env}

/-! ## syntax -/

/-- binder-free and scoped below `k` bound variables -/
def sc (k : Nat) : Expr → Bool
  | .bvar j => j < k
  | .sort _ | .const _ _ | .lit (.natVal _) => true
  | .app f a => sc k f && sc k a
  | _ => false

/-- substitute bound variables by arguments (innermost first) -/
def substB (as : List Expr) : Expr → Expr
  | .bvar j => as.getD j (.bvar 0)
  | .app f a => .app (substB as f) (substB as a)
  | e => e

def inst (ps : List Name) (us : List Level) (e : Expr) : Expr := e.instantiateLevelParams ps us

def apps (f : Expr) : List Expr → Expr
  | [] => f
  | a :: as => apps (.app f a) as

structure Head where
  ps : List Name
  Ts : List Expr
  B : Expr
  deriving DecidableEq

abbrev Tab := Name → Option Head

mutual
/-- `HasTy tab eqs Γ t T`: `t` has type `T` in context `Γ` (types of bound variables, closed). -/
inductive HasTy (tab : Tab) (eqs : List (Expr × Expr)) : List Expr → Expr → Expr → Prop
  | sort {Γ : List Expr} {u : Level} : HasTy tab eqs Γ (.sort u) (.sort (.succ u))
  | conv {Γ : List Expr} {t T T' : Expr} : HasTy tab eqs Γ t T → (T, T') ∈ eqs → HasTy tab eqs Γ t T'
  | bvar {Γ : List Expr} {i : Nat} {T : Expr} : Γ[i]? = some T → HasTy tab eqs Γ (.bvar i) T
  | lit {Γ : List Expr} {n : Nat} : HasTy tab eqs Γ (.lit (.natVal n)) Tiny.natC
  | head {Γ : List Expr} {n : Name} {us : List Level} {h : Head} {as : List Expr} :
      tab n = some h → us.length = h.ps.length → ArgsTy tab eqs Γ h.ps us h.Ts as [] →
      HasTy tab eqs Γ (apps (.const n us) as) (substB as.reverse (inst h.ps us h.B))
  /-- a non-dependent λ, read in regime 1 (binder data `.never`); closed domain, codomain and context -/
  | lam {Γ : List Expr} {T b S : Expr} {u : Level} : HasTy tab eqs Γ T (.sort u) → EngineLam.wfk 0 T = true → EngineLam.wfk 0 S = true → (∀ U ∈ Γ, EngineLam.wfk 0 U = true) →
      HasTy tab eqs (T :: Γ) b S → HasTy tab eqs Γ (.lam T b ⟨.never⟩) (.forallE T S ⟨.never⟩)
  /-- application at a non-dependent arrow -/
  | app {Γ : List Expr} {f a T S : Expr} : HasTy tab eqs Γ f (.forallE T S ⟨.never⟩) → HasTy tab eqs Γ a T →
      EngineLam.wfk 0 S = true → HasTy tab eqs Γ (.app f a) S
/-- arguments against a telescope; `done` = earlier arguments, innermost first -/
inductive ArgsTy (tab : Tab) (eqs : List (Expr × Expr)) :
    List Expr → List Name → List Level → List Expr → List Expr → List Expr → Prop
  | nil {Γ : List Expr} {ps : List Name} {us : List Level} {done : List Expr} : ArgsTy tab eqs Γ ps us [] [] done
  | cons {Γ : List Expr} {ps : List Name} {us : List Level} {T : Expr} {Ts : List Expr} {a : Expr} {as done : List Expr} :
      HasTy tab eqs Γ a (substB done (inst ps us T)) → ArgsTy tab eqs Γ ps us Ts as (a :: done) →
      ArgsTy tab eqs Γ ps us (T :: Ts) (a :: as) done
end

/-! ## semantics of heads -/

/-- What a head must satisfy in the model: it denotes its `cval` at the induced assignment, and its `cval` is a
member of what its stored telescope (with SOME binder data) denotes. -/
structure HeadSem (M : Model V env) (n : Name) (h : Head) : Prop where
  den : ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (us : List Level), us.length = h.ps.length →
    Denotes M.cval env φ ρ (.const n us) (M.cval n (Level.substFn φ h.ps us))
  mem : ∀ (ψ : LevelParam → Nat) (ρ : BVarIdx → V), ∃ (ms : List BinderMeta) (P : V), ms.length = h.Ts.length ∧
    Denotes M.cval env ψ ρ (piN (h.Ts.zip ms) h.B) P ∧ M.cval n ψ ∈ˢ P
  scT : ∀ i (T : Expr), h.Ts[i]? = some T → sc i T = true
  scB : sc h.Ts.length h.B = true

def TabOk (M : Model V env) (tab : Tab) : Prop := ∀ n h, tab n = some h → HeadSem M n h

/-- type equations the checker may convert along: closed, and the left side's denotation is the right's -/
def EqsOk (M : Model V env) (eqs : List (Expr × Expr)) : Prop :=
  ∀ p ∈ eqs, sc 0 p.1 = true ∧ sc 0 p.2 = true ∧
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V), Denotes M.cval env φ ρ p.1 X → Denotes M.cval env φ ρ p.2 X

/-! ## environments of values -/

def pushAll (xs : List V) (ρ : BVarIdx → V) : BVarIdx → V :=
  xs.foldr push ρ

inductive DenL (M : Model V env) (φ : LevelParam → Nat) (ρ : BVarIdx → V) : List Expr → List V → Prop
  | nil : DenL M φ ρ [] []
  | cons {a as v vs} : Denotes M.cval env φ ρ a v → DenL M φ ρ as vs → DenL M φ ρ (a :: as) (v :: vs)

theorem DenL.length {M : Model V env} {φ ρ} : ∀ {as : List Expr} {vs : List V}, DenL M φ ρ as vs →
    as.length = vs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [h.length]

theorem DenL.get {M : Model V env} {φ ρ} : ∀ {as : List Expr} {vs : List V}, DenL M φ ρ as vs →
    ∀ j, j < as.length → Denotes M.cval env φ ρ (as.getD j (.bvar 0)) (pushAll vs ρ j) := by
  intro as vs h
  induction h with
  | nil => intro j hj; simp at hj
  | @cons a as v vs ha hr ih =>
    intro j hj
    cases j with
    | zero => simpa [pushAll, push] using ha
    | succ j =>
      have := ih j (by simpa using hj)
      simpa [pushAll, push] using this

/-! ## moving a constant between assignments -/

theorem const_move {M : Model V env} (hP : CvalParams M) {φ φ' : LevelParam → Nat} {ρ ρ' : BVarIdx → V}
    {c : Name} {us us' : List Level} {X : V} (h : Denotes M.cval env φ ρ (.const c us) X)
    (hev : us'.map (Level.eval φ') = us.map (Level.eval φ)) : Denotes M.cval env φ' ρ' (.const c us') X := by
  cases h with
  | @const _ _ _ ci hf hl =>
    have hl' : us'.length = ci.toConstantVal.levelParams.length := by
      rw [← List.length_map (f := Level.eval φ'), hev, List.length_map]; exact hl
    have h2 := Denotes.const (cval := M.cval) (φ := φ') (ρ := ρ') hf hl'
    have e := const_agree hP h2 (Denotes.const (ρ := ρ) hf hl) hev
    exact e ▸ h2

/-! ## literals are φ- and ρ-independent -/

theorem lit_agree {M : Model V env} (hP : CvalParams M) {φ φ' : LevelParam → Nat} {ρ ρ' : BVarIdx → V} :
    ∀ (n : Nat) {X : V}, Denotes M.cval env φ ρ (.lit (.natVal n)) X → Denotes M.cval env φ' ρ' (.lit (.natVal n)) X
  | 0, X, h => by
    cases h with
    | natLit h => exact .natLit (const_move hP (us := []) (us' := []) h rfl)
  | n + 1, X, h => by
    cases h with
    | natLit h =>
      cases h with
      | app hf ha => exact .natLit (.app (const_move hP (us' := []) hf rfl) (lit_agree hP n ha))

/-! ## the instantiation lemma -/

theorem inst_den {M : Model V env} (hP : CvalParams M) {φ : LevelParam → Nat} {ρ ρ0 : BVarIdx → V}
    {ps : List Name} {us : List Level} {done : List Expr} {xsd : List V} (hd : DenL M φ ρ done xsd) :
    ∀ (T : Expr), sc done.length T = true → ∀ {Y : V},
      (Denotes M.cval env (Level.substFn φ ps us) (pushAll xsd ρ0) T Y ↔
        Denotes M.cval env φ ρ (substB done (inst ps us T)) Y)
  | .bvar j, hs, Y => by
    simp only [sc, decide_eq_true_eq] at hs
    have hj := hd.get j hs
    have hl := hd.length
    simp only [inst, Expr.instantiateLevelParams, substB]
    constructor
    · intro h; cases h
      have : pushAll xsd ρ0 j = pushAll xsd ρ j := by
        have hj' : j < xsd.length := hl ▸ hs
        clear hd hj hl hs
        induction xsd generalizing j with
        | nil => simp at hj'
        | cons x xs ih => cases j <;> simp_all [pushAll, push]
      rw [this]; exact hj
    · intro h
      have := Denotes_functional h hj
      subst this
      have : pushAll xsd ρ0 j = pushAll xsd ρ j := by
        have hj' : j < xsd.length := hl ▸ hs
        clear hd hj hl hs h
        induction xsd generalizing j with
        | nil => simp at hj'
        | cons x xs ih => cases j <;> simp_all [pushAll, push]
      rw [← this]; exact .bvar
  | .sort u, _, Y => by
    simp only [inst, Expr.instantiateLevelParams, substB]
    constructor
    · intro h; cases h; rw [← Level.eval_subst]; exact .sort
    · intro h; cases h; rw [Level.eval_subst]; exact .sort
  | .const c vs, _, Y => by
    simp only [inst, Expr.instantiateLevelParams, substB]
    have hev : vs.map (Level.eval (Level.substFn φ ps us)) = (vs.map (Level.subst ps us)).map (Level.eval φ) := by
      simp [List.map_map, Function.comp_def, Level.eval_subst]
    exact ⟨fun h => const_move hP h hev.symm, fun h => const_move hP h hev⟩
  | .lit (.natVal n), _, Y => by
    simp only [inst, Expr.instantiateLevelParams, substB]
    exact ⟨lit_agree hP n, lit_agree hP n⟩
  | .app f a, hs, Y => by
    simp only [sc, Bool.and_eq_true] at hs
    simp only [inst, Expr.instantiateLevelParams, substB]
    have ihf := fun {Y} => inst_den hP (ρ0 := ρ0) (ps := ps) (us := us) hd f hs.1 (Y := Y)
    have iha := fun {Y} => inst_den hP (ρ0 := ρ0) (ps := ps) (us := us) hd a hs.2 (Y := Y)
    simp only [inst] at ihf iha
    constructor
    · intro h; cases h with
      | app h1 h2 => exact .app (ihf.mp h1) (iha.mp h2)
    · intro h; cases h with
      | app h1 h2 => exact .app (ihf.mpr h1) (iha.mpr h2)
  | .lit (.strVal _), hs, _ => by simp [sc] at hs
  | .fvar _ _, hs, _ | .lam _ _ _, hs, _ | .forallE _ _ _, hs, _ | .letE _ _ _, hs, _ | .proj _ _ _, hs, _ => by
    simp [sc] at hs

/-! ## soundness -/

theorem DenL.append {M : Model V env} {φ ρ} : ∀ {as bs : List Expr} {xs ys : List V}, DenL M φ ρ as xs →
    DenL M φ ρ bs ys → DenL M φ ρ (as ++ bs) (xs ++ ys)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons ha hr, h => .cons ha (hr.append h)

theorem DenL.reverse {M : Model V env} {φ ρ} : ∀ {as : List Expr} {xs : List V}, DenL M φ ρ as xs →
    DenL M φ ρ as.reverse xs.reverse
  | _, _, .nil => .nil
  | _, _, .cons ha hr => by simpa using hr.reverse.append (.cons ha .nil)

theorem den_apps {M : Model V env} {φ : LevelParam → Nat} {ρ : BVarIdx → V} :
    ∀ {f : Expr} {F : V} {as : List Expr} {vs : List V}, Denotes M.cval env φ ρ f F →
      DenL M φ ρ as vs → Denotes M.cval env φ ρ (apps f as) (appN F vs)
  | f, F, a :: _, v :: _, hf, .cons ha hr => den_apps (f := .app f a) (F := app F v) (.app hf ha) hr
  | _, _, [], [], hf, .nil => hf

theorem ArgsTy.length {tab eqs Γ} : ∀ {ps us Ts as done}, ArgsTy tab eqs Γ ps us Ts as done → as.length = Ts.length
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons _ h => by simp [h.length]

/-- the bound variables' values are members of their declared types -/
def GammaOk (M : Model V env) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (Γ : List Expr) : Prop :=
  ∀ i T, Γ[i]? = some T → ∃ A, Denotes M.cval env φ ρ T A ∧ ρ i ∈ˢ A

section
variable {M : Model V env} (hP : CvalParams M) (hnat : natLitSupported env = true) {tab : Tab}
  (htab : TabOk M tab) {eqs : List (Expr × Expr)} (heqs : EqsOk M eqs) {φ : LevelParam → Nat}
include hP hnat htab heqs

mutual
theorem sound {Γ : List Expr} {ρ : BVarIdx → V} (hΓ : GammaOk M φ ρ Γ) : ∀ {t T : Expr}, HasTy tab eqs Γ t T →
    ∃ X A, Denotes M.cval env φ ρ t X ∧ Denotes M.cval env φ ρ T A ∧ X ∈ˢ A
  | _, _, .sort (u := u) => ⟨_, _, .sort, .sort, by simpa [Level.eval] using univ_mem_univ (Level.eval φ u)⟩
  | _, _, .conv ht hp => by
    obtain ⟨X, A, hX, hA, hm⟩ := sound hΓ ht
    exact ⟨X, A, hX, (heqs _ hp).2.2 φ ρ A hA, hm⟩
  | _, _, .bvar h => by
    obtain ⟨A, hA, hm⟩ := hΓ _ _ h
    exact ⟨_, A, .bvar, hA, hm⟩
  | _, _, .lit (n := n) =>
    ⟨_, _, Tiny.lit_den M hnat φ ρ n, Tiny.nat_den M hnat φ ρ, Tiny.natV_mem M hnat φ ρ n⟩
  | _, _, @HasTy.head _ _ _ n us h as htn hus hargs => by
    have hs := htab n h htn
    obtain ⟨xs, hdl, ht⟩ := soundArgs hΓ hargs [] ρ .nil (fun i T hi => by simpa using hs.scT i T hi)
    obtain ⟨ms, P, hml, hPd, hPm⟩ := hs.mem (Level.substFn φ h.ps us) ρ
    obtain ⟨Bv, hB, hBm⟩ := spine_mem hml hPd hPm ht
    have hd := hdl.reverse
    have hsc : sc as.reverse.length h.B = true := by
      rw [List.length_reverse, hargs.length]; exact hs.scB
    have hB' := (inst_den hP (ρ0 := ρ) hd h.B hsc).mp (by simpa using hB)
    exact ⟨_, Bv, den_apps (hs.den φ ρ us hus) hdl, hB', hBm⟩
  | _, _, .lam (T := T) (b := b) (S := S) hTy hT hS hG hb => by
    -- the body at each point of the domain, in the pushed context of closed types
    have hΓx : ∀ A x, Denotes M.cval env φ ρ T A → x ∈ˢ A → GammaOk M φ (push x ρ) (T :: Γ) := by
      intro A x hA hx i U hi
      cases i with
      | zero =>
        simp at hi; subst hi
        exact ⟨A, EngineLam.den_move hT (fun _ h => absurd h (Nat.not_lt_zero _)) hA, hx⟩
      | succ i =>
        simp at hi
        obtain ⟨A', hA', hm'⟩ := hΓ i U hi
        exact ⟨A', EngineLam.den_move (hG U (List.mem_of_getElem? hi)) (fun _ h => absurd h (Nat.not_lt_zero _)) hA', hm'⟩
    haveI := Classical.propDecidable
    obtain ⟨A, -, dT, -, -⟩ := sound hΓ hTy
    have hx : ∀ x, x ∈ˢ A → ∃ X B, Denotes M.cval env φ (push x ρ) b X ∧ Denotes M.cval env φ (push x ρ) S B ∧ X ∈ˢ B :=
      fun x hx => sound (hΓx A x dT hx) hb
    let F : V → V := fun x => if h : x ∈ˢ A then Classical.choose (hx x h) else empty
    let B : V → V := fun x => if h : x ∈ˢ A then Classical.choose (Classical.choose_spec (hx x h)) else empty
    have hFB : ∀ x (h : x ∈ˢ A), Denotes M.cval env φ (push x ρ) b (F x) ∧ Denotes M.cval env φ (push x ρ) S (B x) ∧
        F x ∈ˢ B x := by
      intro x h
      simp only [F, B, h, dif_pos]
      exact Classical.choose_spec (Classical.choose_spec (hx x h))
    have hr : regime φ (⟨.never⟩ : BinderMeta).pw ≠ 0 := by rw [EngineLam.regime_never]; exact Nat.one_ne_zero
    refine ⟨_, _, .lam dT (fun x h => (hFB x h).1) (fun h0 => absurd h0 hr),
      .pi dT (fun x h => (hFB x h).2.1) (fun h0 => absurd h0 hr), ?_⟩
    rw [lamR_pos hr, piR_pos hr]
    exact graph_mem_piSet (fun x h => (hFB x h).2.2)
  | _, _, .app hf ha hS => by
    obtain ⟨Ff, P, dF, dP, hFm⟩ := sound hΓ hf
    obtain ⟨Xa, A, da, dA, hXa⟩ := sound hΓ ha
    obtain ⟨Bx, dB, hm⟩ := mem_app dP hFm dA hXa
    exact ⟨_, Bx, .app dF da, EngineLam.den_move hS (fun _ h => absurd h (Nat.not_lt_zero _)) dB, hm⟩
theorem soundArgs {Γ : List Expr} {ρ : BVarIdx → V} (hΓ : GammaOk M φ ρ Γ) : ∀ {ps : List Name} {us : List Level} {Ts as done : List Expr},
    ArgsTy tab eqs Γ ps us Ts as done → ∀ (xsd : List V) (ρ0 : BVarIdx → V), DenL M φ ρ done xsd →
    (∀ i T, Ts[i]? = some T → sc (done.length + i) T = true) →
    ∃ xs, DenL M φ ρ as xs ∧
      TeleX M (Level.substFn φ ps us) (pushAll xsd ρ0) Ts xs (pushAll (xs.reverse ++ xsd) ρ0)
  | _, _, _, _, _, .nil, xsd, ρ0, _, _ => ⟨[], .nil, by simpa using TeleX.nil⟩
  | _, _, T :: Ts, a :: as, done, .cons ha hr, xsd, ρ0, hd, hsc => by
    obtain ⟨X, A, hX, hA, hm⟩ := sound hΓ ha
    have hA' := (inst_den hP (ρ0 := ρ0) hd T (by simpa using hsc 0 T rfl)).mpr hA
    obtain ⟨xs, hdl, ht⟩ := soundArgs hΓ hr (X :: xsd) ρ0 (.cons hX hd)
      (fun i T' hi => by have := hsc (i + 1) T' (by simpa using hi); simpa [Nat.add_assoc, Nat.add_comm 1] using this)
    refine ⟨X :: xs, .cons hX hdl, ?_⟩
    have e : (X :: xs).reverse ++ xsd = xs.reverse ++ X :: xsd := by simp
    rw [e]; exact .cons hA' hm ht
end
end

end Bridge.Real.Engine
