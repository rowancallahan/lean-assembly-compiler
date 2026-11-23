/- Bridge.Real.Engine2: heads from the accepted stream, transfer through the engine, and a Bool checker.

* `headSem_def`: a def/thm record of the accepted stream with a scoped binder-free declared telescope is a
  `HeadSem` head.  `headSem_nat*`: `Nat`, `Nat.zero`, `Nat.succ` from `natLitSupported`.
* `etransfer`: a theorem record `∀ (x₁:T₁)…(xₙ:Tₙ), @Eq.{u} S a b` with closed `Tᵢ`, whose `S`, `a`, `b` the
  engine types (`HasTy`), gives `⟦a⟧ = ⟦b⟧` at every instance of the binders.
* `check`: a Bool checker for `HasTy` (fuel-bounded), sound (`check_sound`), so instances go by `decide`. -/
import Bridge.Real.Engine

namespace Bridge.Real.Engine
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real Bridge.ModelExists2

universe w
variable {V : Type w} [SetTheory V] {env : Env}

/-! ## heads -/

def nev (Ts : List Expr) : List BinderMeta := Ts.map fun _ => ⟨.never⟩
def piV (Ts : List Expr) (B : Expr) : Expr := piN (Ts.zip (nev Ts)) B

/-- scoped-ness of a head's declared telescope (decidable) -/
def headSc (h : Head) : Bool :=
  (List.range h.Ts.length).all (fun i => sc i (h.Ts.getD i (.bvar 0))) && sc h.Ts.length h.B

theorem sc_BF : ∀ {k : Nat} {e : Expr}, sc k e = true → BF e
  | _, .bvar _, _ | _, .sort _, _ | _, .const _ _, _ | _, .lit (.natVal _), _ => trivial
  | _, .app f a, h => by
    simp only [sc, Bool.and_eq_true] at h; exact ⟨sc_BF h.1, sc_BF h.2⟩
  | _, .lit (.strVal _), h | _, .fvar _ _, h | _, .lam _ _ _, h | _, .forallE _ _ _, h
  | _, .letE _ _ _, h | _, .proj _ _ _, h => by simp [sc] at h

theorem headSc_T {h : Head} (hh : headSc h = true) : ∀ i T, h.Ts[i]? = some T → sc i T = true := by
  intro i T hi
  simp only [headSc, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hh
  have hl : i < h.Ts.length := (List.getElem?_eq_some_iff.mp hi).1
  have := hh.1 i hl
  rwa [List.getD_eq_getElem?_getD, hi, Option.getD_some] at this

theorem headSc_B {h : Head} (hh : headSc h = true) : sc h.Ts.length h.B = true := by
  simp only [headSc, Bool.and_eq_true] at hh; exact hh.2

/-- **A def/thm record of the accepted stream is a head.** -/
theorem headSem_rec {pins : List NatOpPinSet} {ds : Array Declaration}
    (acc : Cached.checkDecls .verified pins ds = .ok env) (M : Model V env) {n : Name} {h : Head}
    {pd : Declaration} (hmem : pd ∈ ds) (hcv : Cached.Declaration.Declares pd ⟨n, h.ps, piV h.Ts h.B⟩)
    (hh : headSc h = true) : HeadSem M n h := by
  have hT : ∀ T ∈ h.Ts, BF T := by
    intro T hT
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT
    exact sc_BF (headSc_T hh i _ (List.getElem?_eq_getElem hi))
  have hB : BF h.B := sc_BF (headSc_B hh)
  obtain ⟨c, ms', hf, hlp, hl', hty⟩ := stored_tele V acc hmem hcv h.Ts (nev h.Ts) h.B (by simp [nev]) rfl hT hB
  refine ⟨fun φ ρ us hus => ?_, fun ψ ρ => ?_, headSc_T hh, headSc_B hh⟩
  · have := Denotes.const (cval := M.cval) (φ := φ) (ρ := ρ) (us := us) hf (by rw [hlp]; exact hus)
    rwa [hlp] at this
  · obtain ⟨P, hP, hm⟩ := const_mem M hf ψ ρ
    rw [hty] at hP
    exact ⟨ms', P, hl', hP, hm⟩

theorem headSem_defn {pins : List NatOpPinSet} {ds : Array Declaration}
    (acc : Cached.checkDecls .verified pins ds = .ok env) (M : Model V env) {n : Name} {h : Head}
    (hmem : ∃ v hint, Declaration.defnDecl ⟨n, h.ps, piV h.Ts h.B⟩ v hint ∈ ds) (hh : headSc h = true) :
    HeadSem M n h := by
  obtain ⟨v, hint, hm⟩ := hmem; exact headSem_rec acc M hm rfl hh

theorem headSem_thm {pins : List NatOpPinSet} {ds : Array Declaration}
    (acc : Cached.checkDecls .verified pins ds = .ok env) (M : Model V env) {n : Name} {h : Head}
    (hmem : ∃ v, Declaration.thmDecl ⟨n, h.ps, piV h.Ts h.B⟩ v ∈ ds) (hh : headSc h = true) :
    HeadSem M n h := by
  obtain ⟨v, hm⟩ := hmem; exact headSem_rec acc M hm rfl hh

def natHead : Head := ⟨[], [], .sort (.succ .zero)⟩
def zeroHead : Head := ⟨[], [], Tiny.natC⟩
def succHead : Head := ⟨[], [Tiny.natC], Tiny.natC⟩

theorem headSem_lp0 {M : Model V env} {n : Name} {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hl : ci.toConstantVal.levelParams = []) {Ts : List Expr} {B : Expr}
    (hty : ∃ ms : List BinderMeta, ms.length = Ts.length ∧ ci.toConstantVal.type = piN (Ts.zip ms) B)
    (hT : ∀ i T, Ts[i]? = some T → sc i T = true) (hB : sc Ts.length B = true) :
    HeadSem M n ⟨[], Ts, B⟩ := by
  obtain ⟨ms, hml, hty⟩ := hty
  refine ⟨fun φ ρ us hus => ?_, fun ψ ρ => ?_, hT, hB⟩
  · have := Denotes.const (cval := M.cval) (φ := φ) (ρ := ρ) (us := us) hf (by rw [hl]; exact hus)
    rwa [hl] at this
  · obtain ⟨P, hP, hm⟩ := const_mem M hf ψ ρ
    rw [hty] at hP
    exact ⟨ms, P, hml, hP, hm⟩

theorem headSem_nat (M : Model V env) (hnat : natLitSupported env = true) :
    HeadSem M natName natHead ∧ HeadSem M natZeroName zeroHead ∧ HeadSem M natSuccName succHead := by
  obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, h1, h2, h3, l1, l2, l3, t1, t2, mb, t3⟩ := natLitSupported_inv hnat
  refine ⟨headSem_lp0 h1 l1 ⟨[], rfl, t1⟩ (by simp) (by simp [sc]),
    headSem_lp0 h2 l2 ⟨[], rfl, t2⟩ (by simp) (by simp [sc, Tiny.natC]),
    headSem_lp0 h3 l3 ⟨[mb], rfl, t3⟩ (fun i T hi => ?_) (by simp [sc, Tiny.natC])⟩
  match i, hi with
  | 0, hi => simp at hi; subst hi; rfl

/-! ## closed terms move between variable environments -/

theorem closed_move {M : Model V env} {φ : LevelParam → Nat} {ρ ρ' : BVarIdx → V} :
    ∀ {T : Expr} {Y : V}, sc 0 T = true → Denotes M.cval env φ ρ T Y → Denotes M.cval env φ ρ' T Y
  | .bvar _, _, hs, _ => by simp [sc] at hs
  | .sort _, _, _, h => by cases h; exact .sort
  | .const _ _, _, _, h => by cases h with | const hf hl => exact .const hf hl
  | .lit (.natVal n), _, _, h => by
    cases h with
    | natLit h =>
      refine .natLit ?_
      cases n with
      | zero => cases h with | const hf hl => exact .const hf hl
      | succ k =>
        cases h with
        | app hf ha =>
          cases hf with
          | const hf hl => exact .app (.const hf hl) (closed_move (T := .lit (.natVal k)) rfl ha)
  | .app f a, _, hs, h => by
    simp only [sc, Bool.and_eq_true] at hs
    cases h with | app h1 h2 => exact .app (closed_move hs.1 h1) (closed_move hs.2 h2)
  | .lit (.strVal _), _, hs, _ | .fvar _ _, _, hs, _ | .lam _ _ _, _, hs, _ | .forallE _ _ _, _, hs, _
  | .letE _ _ _, _, hs, _ | .proj _ _ _, _, hs, _ => by simp [sc] at hs

/-! ## transfer through the engine -/

/-- `xs` (outermost binder first) are members of the closed binder types `Ts`. -/
inductive MemL (M : Model V env) (φ : LevelParam → Nat) : List Expr → List V → Prop
  | nil : MemL M φ [] []
  | cons {T Ts A x xs} : (∀ ρ, Denotes M.cval env φ ρ T A) → x ∈ˢ A → MemL M φ Ts xs → MemL M φ (T :: Ts) (x :: xs)

theorem MemL.length {M : Model V env} {φ : LevelParam → Nat} : ∀ {Ts : List Expr} {xs : List V},
    MemL M φ Ts xs → Ts.length = xs.length
  | _, _, .nil => rfl
  | _, _, .cons _ _ h => by simp [MemL.length h]

theorem MemL.teleX {M : Model V env} {φ : LevelParam → Nat} : ∀ {Ts : List Expr} {xs : List V} {ρ : BVarIdx → V},
    MemL M φ Ts xs → TeleX M φ ρ Ts xs (pushAll xs.reverse ρ)
  | _, _, _, .nil => .nil
  | _, x :: xs, ρ, .cons hA hx hr => by
    have := hr.teleX (ρ := push x ρ)
    have e : pushAll (x :: xs).reverse ρ = pushAll xs.reverse (push x ρ) := by
      simp [pushAll, List.foldr_append]
    rw [e]; exact .cons (hA ρ) hx this

theorem pushAll_len (x : V) (ρ : BVarIdx → V) : ∀ ys : List V, pushAll ys (push x ρ) ys.length = x
  | [] => rfl
  | y :: ys => by simpa [pushAll, push] using pushAll_len x ρ ys

theorem MemL.gamma {M : Model V env} {φ : LevelParam → Nat} {ρ : BVarIdx → V} :
    ∀ {Ts : List Expr} {xs : List V}, MemL M φ Ts xs → GammaOk M φ (pushAll xs.reverse ρ) Ts.reverse := by
  intro Ts xs h
  induction h generalizing ρ with
  | nil => intro i T hi; simp at hi
  | @cons T Ts A x xs hA hx hr ih =>
    intro i T' hi
    simp only [List.reverse_cons] at hi
    have e : pushAll (x :: xs).reverse ρ = pushAll xs.reverse (push x ρ) := by
      simp [pushAll, List.foldr_append]
    rw [e]
    rcases Nat.lt_or_ge i Ts.length with hlt | hge
    · rw [List.getElem?_append_left (by simpa using hlt)] at hi
      exact ih (ρ := push x ρ) i T' hi
    · rw [List.getElem?_append_right (by simpa using hge)] at hi
      simp only [List.length_reverse] at hi
      have hi0 : i - Ts.length = 0 := by
        cases h : i - Ts.length with
        | zero => rfl
        | succ k => rw [h] at hi; simp at hi
      rw [hi0] at hi; simp at hi; subst hi
      have hil : i = xs.reverse.length := by
        have h1 := hr.length; have h2 := hi0; have h3 := hge; rw [List.length_reverse, ← h1]; exact Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp h2) h3
      refine ⟨A, hA _, ?_⟩
      subst hil
      rw [pushAll_len]; exact hx

theorem teleX_tele' {M : Model V env} {φ : LevelParam → Nat} :
    ∀ {ρ ρ' : BVarIdx → V} {Ts : List Expr} {xs : List V} (ms : List BinderMeta), ms.length = Ts.length →
      TeleX M φ ρ Ts xs ρ' → Tele M φ ρ (Ts.zip ms) ρ'
  | _, _, [], [], [], _, .nil => .nil
  | _, _, _ :: _, _ :: _, _ :: _, hl, .cons hA hx ht => .cons hA hx (teleX_tele' _ (by simpa using hl) ht)

theorem sc_mono : ∀ {k k' : Nat} {e : Expr}, k ≤ k' → sc k e = true → sc k' e = true
  | _, _, .bvar _, hk, h => by simp [sc] at h ⊢; omega
  | _, _, .sort _, _, _ | _, _, .const _ _, _, _ | _, _, .lit (.natVal _), _, _ => rfl
  | _, _, .app f a, hk, h => by
    simp only [sc, Bool.and_eq_true] at h ⊢; exact ⟨sc_mono hk h.1, sc_mono hk h.2⟩
  | _, _, .lit (.strVal _), _, h | _, _, .fvar _ _, _, h | _, _, .lam _ _ _, _, h | _, _, .forallE _ _ _, _, h
  | _, _, .letE _ _ _, _, h | _, _, .proj _ _ _, _, h => by simp [sc] at h

/-- **Transfer through the engine.**  A theorem record `∀ (xᵢ : Tᵢ), @Eq.{u} S a b` (closed `Tᵢ`) of the
accepted stream, whose `S : Sort u`, `a : S`, `b : S` the engine types in context `Ts.reverse`: at every
instance `xs` of the binders, the two sides denote the same set. -/
theorem etransfer {pins : List NatOpPinSet} {ds : Array Declaration}
    (acc : Cached.checkDecls .verified pins ds = .ok env) {M : Model V env} (hP : CvalParams M)
    (hnat : natLitSupported env = true) {tab : Tab} (htab : TabOk M tab) {eqs : List (Expr × Expr)} (heqs : EqsOk M eqs)
    {n : Name} {Ts : List Expr} {u : Level} {S a b : Expr}
    (h : ∃ v, Declaration.thmDecl ⟨n, [], piV Ts (eqE u S a b)⟩ v ∈ ds)
    (hTs : Ts.all (sc 0) = true) (hsc : sc Ts.length S && sc Ts.length a && sc Ts.length b = true)
    (hS : HasTy tab eqs Ts.reverse S (.sort u)) (ha : HasTy tab eqs Ts.reverse a S) (hb : HasTy tab eqs Ts.reverse b S)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) {xs : List V} (hm : MemL M φ Ts xs) {X Y : V}
    (hX : Denotes M.cval env φ (pushAll xs.reverse ρ) a X) (hY : Denotes M.cval env φ (pushAll xs.reverse ρ) b Y) :
    X = Y := by
  simp only [Bool.and_eq_true] at hsc
  obtain ⟨⟨hsS, hsa⟩, hsb⟩ := hsc
  have hΓ := hm.gamma (ρ := ρ)
  obtain ⟨Sv, U, dS, dU, hSU⟩ := sound hP hnat htab heqs hΓ hS
  cases dU
  obtain ⟨X', A, dX, dA, hXA⟩ := sound hP hnat htab heqs hΓ ha
  obtain ⟨Y', B, dY, dB, hYB⟩ := sound hP hnat htab heqs hΓ hb
  obtain rfl := Denotes_functional dA dS
  obtain rfl := Denotes_functional dB dS
  obtain rfl := Denotes_functional hX dX
  obtain rfl := Denotes_functional hY dY
  obtain ⟨v, hmem⟩ := h
  have hT : ∀ T ∈ Ts, BF T := fun T hT => sc_BF (List.all_eq_true.mp hTs T hT)
  obtain ⟨c, ms', hf, -, hl', hty⟩ := stored_tele V acc hmem rfl Ts (nev Ts) (eqE u S a b) (by simp [nev]) rfl hT
    (by simp only [eqE, BF]; exact ⟨⟨⟨trivial, sc_BF hsS⟩, sc_BF hsa⟩, sc_BF hsb⟩)
  exact transferN M hf hty φ ρ (teleX_tele' ms' hl' hm.teleX) dS dX dY hSU hXA hYB

/-! ## a Bool checker -/

def spine : Expr → Expr × List Expr
  | .app f a => let p := spine f; (p.1, p.2 ++ [a])
  | e => (e, [])

theorem spine_apps : ∀ e : Expr, e = apps (spine e).1 (spine e).2
  | .app f a => by
    have := spine_apps f
    simp only [spine]
    conv => lhs; rw [this]
    generalize (spine f).1 = g; generalize (spine f).2 = l
    induction l generalizing g with
    | nil => rfl
    | cons x xs ih => exact ih _
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _ | .forallE _ _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ => rfl

mutual
def infer (tab : Tab) (eqs : List (Expr × Expr)) (Γ : List Expr) : Nat → Expr → Option Expr
  | 0, _ => none
  | k + 1, e =>
    match e with
    | .bvar i => Γ[i]?
    | .sort u => some (.sort (.succ u))
    | .lit (.natVal _) => some Tiny.natC
    | e =>
      match spine e with
      | (.const n us, as) =>
        match tab n with
        | some h =>
          if us.length = h.ps.length ∧ chkArgs tab eqs Γ k h.ps us h.Ts as [] = true then
            some (substB as.reverse (inst h.ps us h.B))
          else none
        | none => none
      | _ => none
termination_by structural k => k
def chkArgs (tab : Tab) (eqs : List (Expr × Expr)) (Γ : List Expr) :
    Nat → List Name → List Level → List Expr → List Expr → List Expr → Bool
  | 0, _, _, _, _, _ => false
  | _ + 1, _, _, [], [], _ => true
  | k + 1, ps, us, T :: Ts, a :: as, done =>
    (match infer tab eqs Γ k a with
     | some Ta => Ta == substB done (inst ps us T) || eqs.contains (Ta, substB done (inst ps us T))
     | none => false) && chkArgs tab eqs Γ k ps us Ts as (a :: done)
  | _ + 1, _, _, _, _, _ => false
termination_by structural k => k
end

mutual
theorem infer_sound {tab : Tab} {eqs : List (Expr × Expr)} {Γ : List Expr} :
    ∀ (k : Nat) (e T : Expr), infer tab eqs Γ k e = some T → HasTy tab eqs Γ e T
  | 0, _, _, h => by simp [infer] at h
  | k + 1, e, T, h => by
    unfold infer at h
    split at h
    · exact .bvar h
    · cases h; exact .sort
    · cases h; exact .lit
    · rename_i hb hl
      split at h
      · rename_i n us as hsp
        split at h
        · rename_i hd htn
          split at h
          · rename_i hc
            cases h
            have he := spine_apps e
            rw [hsp] at he
            rw [he]
            exact .head htn hc.1 (chkArgs_sound k _ _ _ _ _ hc.2)
          · cases h
        · cases h
      · cases h
theorem chkArgs_sound {tab : Tab} {eqs : List (Expr × Expr)} {Γ : List Expr} : ∀ (k : Nat) (ps : List Name)
    (us : List Level) (Ts as done : List Expr), chkArgs tab eqs Γ k ps us Ts as done = true →
    ArgsTy tab eqs Γ ps us Ts as done
  | 0, _, _, _, _, _, h => by simp [chkArgs] at h
  | _ + 1, _, _, [], [], _, _ => .nil
  | k + 1, ps, us, T :: Ts, a :: as, done, h => by
    simp only [chkArgs, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    refine .cons ?_ (chkArgs_sound k ps us Ts as (a :: done) h2)
    split at h1
    · rename_i Ta hTa
      simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h1
      rcases h1 with h1 | h1
      · rw [← h1]; exact infer_sound k a _ hTa
      · exact .conv (infer_sound k a _ hTa) h1
    · cases h1
  | _ + 1, _, _, [], _ :: _, _, h | _ + 1, _, _, _ :: _, [], _, h => by simp [chkArgs] at h
end

end Bridge.Real.Engine
