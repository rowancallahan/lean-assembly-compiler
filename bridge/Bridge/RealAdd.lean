/- Bridge.RealAdd: the `+` fact (`Bridge.Add.add_field`, `hAdd_mem`) ported to the REAL con-leche `Denotes`/`Model`.
Levels: `HAdd.hAdd.{0,0,0}` is read at `φA := substFn φ [u,v,w] [0,0,0]`, `instHAdd.{0}`/`Add.{0}` at `φ0 φ`;
`CvalParams` is used once, for `outParam` (its type inside `HAdd.hAdd`'s is read at `u↦2`, `v,w↦0`, but
`outParam_eq` is stored at `u↦2` with the ambient `v,w`). -/
import Bridge.RealLit

namespace Bridge.Real
open ConLeche ConLeche.SetModel SetTheory
open Name (anonymous)
universe w
variable {V : Type w} [SetTheory V] {env : Env}

def nHAdd : Name := anonymous |>.str "HAdd"
def nHAddH : Name := nHAdd |>.str "hAdd"
def nInstHAdd : Name := anonymous |>.str "instHAdd"
def nAdd : Name := anonymous |>.str "Add"
def nInstAddU : Name := anonymous |>.str "instAddUInt64"
def nInstAddN : Name := anonymous |>.str "instAddNat"
def nOutParam : Name := anonymous |>.str "outParam"
def nOutEq : Name := anonymous |>.str "outParam_eq"
def vP : Name := anonymous |>.str "v"
def wP : Name := anonymous |>.str "w"

/-- `HAdd.hAdd.{0,0,0}` is read here -/
def φA (φ : LevelParam → Nat) : LevelParam → Nat := Level.substFn φ [uP, vP, wP] [.zero, .zero, .zero]

theorem φA_u (φ) : φA φ uP = 0 := by simp [φA, Level.substFn, Level.eval]
theorem φA_v (φ) : φA φ vP = 0 := by
  have : uP ≠ vP := by decide
  simp [φA, Level.substFn, Level.eval, *]
theorem φA_w (φ) : φA φ wP = 0 := by
  have : uP ≠ wP := by decide
  have : vP ≠ wP := by decide
  simp [φA, Level.substFn, Level.eval, *]

theorem φA_self (φ) : Level.substFn (φA φ) [uP, vP, wP] [.param uP, .param vP, .param wP] = φA φ :=
  Level.substFn_param_self (φA φ) [uP, vP, wP]

/-- `instHAdd.{0}`'s type reads `HAdd.{u,u,u}` at `φ0 φ` ⇒ `φA φ` -/
theorem φ0_hadd (φ) : Level.substFn (φ0 φ) [uP, vP, wP] [.param uP, .param uP, .param uP] = φA φ := by
  funext n
  have h1 : uP ≠ vP := by decide
  have h2 : uP ≠ wP := by decide
  have h3 : vP ≠ wP := by decide
  by_cases a : n = uP
  · subst a; simp [φA, φ0, Level.substFn, Level.eval]
  by_cases b : n = vP
  · subst b; simp [φA, φ0, Level.substFn, Level.eval, h1, h1.symm]
  by_cases c : n = wP
  · subst c; simp [φA, φ0, Level.substFn, Level.eval, h2, h3, h2.symm, h3.symm]
  simp [φA, φ0, Level.substFn, Level.eval, a, b, c, Ne.symm a, Ne.symm b, Ne.symm c]

/-- `n` is stored with level parameters `ps` (type not read) -/
def HasLv (env : Env) (n : Name) (ps : List Name) : Prop :=
  ∃ ci, env.find? n = some ci ∧ ci.toConstantVal.levelParams = ps

theorem HasLv.const (M : Model V env) {n : Name} {ps : List Name} (h : HasLv env n ps) {us : List Level}
    (hl : us.length = ps.length) (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    Denotes M.cval env φ ρ (.const n us) (M.cval n (Level.substFn φ ps us)) := by
  obtain ⟨ci, hf, hp⟩ := h
  exact Denotes_const' hf hp hl

def lv1 : Level := .succ .zero
def lv2 : Level := .succ lv1
def lv3 : Level := .succ lv2

/-- stored shapes read by `+` -/
structure AddEnv (env : Env) : Prop where
  outParam : Stored env nOutParam [uP] (.forallE (.sort (.param uP)) (.sort (.param uP)) dm)
  outEq : Stored env nOutEq [] (eqE lv3 (.sort lv2) (.app (.const nOutParam [lv2]) (.sort lv1)) (.sort lv1))
  hadd : HasLv env nHAdd [uP, vP, wP]
  add : HasLv env nAdd [uP]
  hAddH : Stored env nHAddH [uP, vP, wP] (.forallE (.sort (.succ (.param uP))) (.forallE (.sort (.succ (.param vP)))
    (.forallE (.app (.const nOutParam [.succ (.succ (.param wP))]) (.sort (.succ (.param wP))))
      (.forallE (.app (.app (.app (.const nHAdd [.param uP, .param vP, .param wP]) (.bvar 2)) (.bvar 1)) (.bvar 0))
        (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 3) dm) dm) dm) dm) dm) dm)
  instHAdd : Stored env nInstHAdd [uP] (.forallE (.sort (.succ (.param uP)))
    (.forallE (.app (.const nAdd [.param uP]) (.bvar 0))
      (.app (.app (.app (.const nHAdd [.param uP, .param uP, .param uP]) (.bvar 1)) (.bvar 1)) (.bvar 1)) dm) dm)
  addNat : Stored env nInstAddN [] (.app (.const nAdd [.zero]) tN)
  addU64 : Stored env nInstAddU [] (.app (.const nAdd [.zero]) tU)

/-- `⟦outParam Type⟧ = ⟦Type⟧` at the assignment `HAdd.hAdd`'s type reads it at -/
theorem outParam_type (M : Model V env) (HA : AddEnv env) (hφ : CvalParams M) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) :
    app (M.cval nOutParam (Level.substFn (φA φ) [uP] [.succ (.succ (.param wP))])) (univ 1) = univ 1 := by
  have hc : M.cval nOutParam (Level.substFn (φA φ) [uP] [.succ (.succ (.param wP))]) =
      M.cval nOutParam (Level.substFn φ [uP] [lv2]) := by
    obtain ⟨ci, hf, hp, -⟩ := HA.outParam
    refine hφ _ ci hf _ _ fun p hp' => ?_
    rw [hp] at hp'; simp at hp'; subst hp'
    simp [Level.substFn, Level.eval, lv2, lv1, φA_w]
  rw [hc]
  obtain ⟨φc, hφc⟩ : ∃ φc, φc = Level.substFn φ [uP] [lv2] := ⟨_, rfl⟩
  rw [← hφc]
  have hu : φc uP = 2 := by simp [hφc, Level.substFn, Level.eval, lv2, lv1]
  have dS : ∀ ρ' : BVarIdx → V, Denotes M.cval env φc ρ' (.sort (.param uP)) (univ 2) := fun ρ' => by
    have h := Denotes.sort (cval := M.cval) (env := env) (φ := φc) (ρ := ρ') (u := .param uP)
    simpa [Level.eval, hu] using h
  have dO : Denotes M.cval env φc ρ (.forallE (.sort (.param uP)) (.sort (.param uP)) dm)
      (piR 1 (univ 2) fun _ => univ 2) := pi_dm (dS _) fun _ _ => dS _
  have hO := HA.outParam.mem_of M dO
  have dS1 : Denotes M.cval env φ ρ (.sort lv1) (univ 1) := Denotes.sort
  have dS2 : ∀ ρ', Denotes M.cval env φ ρ' (.sort lv2) (univ 2) := fun _ => Denotes.sort
  have dOC : Denotes M.cval env φ ρ (.const nOutParam [lv2]) (M.cval nOutParam φc) :=
    hφc ▸ HA.outParam.const M (us := [lv2]) rfl φ ρ
  have h1 : app (M.cval nOutParam φc) (univ 1) ∈ˢ univ 2 := by
    obtain ⟨Bx, hB, hm⟩ := mem_app dO hO (dS _) (univ_mem_univ 1)
    rwa [Denotes_functional hB (dS _)] at hm
  obtain ⟨ciE, hfE, -, hty⟩ := HA.outEq
  have hI := inhab_const M hfE φ ρ
  rw [hty] at hI
  obtain ⟨Sv, av, bv, hS, ha, hb, hEq⟩ := Inhab.eq hI
  obtain rfl := Denotes_functional hS (dS2 _)
  obtain rfl := Denotes_functional ha (.app dOC dS1)
  obtain rfl := Denotes_functional hb dS1
  exact hEq (by simpa [Level.eval, lv3, lv2, lv1] using univ_mem_univ 2) h1 (univ_mem_univ 1)

theorem dsort (M : Model V env) (ψ : LevelParam → Nat) (ρ : BVarIdx → V) (l : Level) (n : Nat)
    (h : Level.eval ψ l = n) : Denotes M.cval env ψ ρ (.sort l) (univ n) := h ▸ Denotes.sort

/-- typing of `@HAdd.hAdd.{0,0,0} T T T (instHAdd.{0} T I)` -/
theorem hAdd_mem (M : Model V env) (HA : AddEnv env) (hφ : CvalParams M) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) {T I : V} (hT : T ∈ˢ univ 1) (hI : I ∈ˢ app (M.cval nAdd (φ0 φ)) T) :
    app (app (app (app (M.cval nHAddH (φA φ)) T) T) T) (app (app (M.cval nInstHAdd (φ0 φ)) T) I) ∈ˢ
      piR 1 T fun _ => piR 1 T fun _ => T := by
  have oP := outParam_type M HA hφ φ ρ
  have sU : ∀ ρ', Denotes M.cval env (φA φ) ρ' (.sort (.succ (.param uP))) (univ 1) := fun _ =>
    dsort M _ _ _ _ (by simp [Level.eval, φA_u])
  have sV : ∀ ρ', Denotes M.cval env (φA φ) ρ' (.sort (.succ (.param vP))) (univ 1) := fun _ =>
    dsort M _ _ _ _ (by simp [Level.eval, φA_v])
  have sW : ∀ ρ', Denotes M.cval env (φA φ) ρ' (.sort (.succ (.param wP))) (univ 1) := fun _ =>
    dsort M _ _ _ _ (by simp [Level.eval, φA_w])
  have dHA : ∀ ρ', Denotes M.cval env (φA φ) ρ' (.const nHAdd [.param uP, .param vP, .param wP])
      (M.cval nHAdd (φA φ)) := fun ρ' => by
    have := HA.hadd.const M (us := [.param uP, .param vP, .param wP]) rfl (φA φ) ρ'
    rwa [φA_self] at this
  have dOut : ∀ ρ', Denotes M.cval env (φA φ) ρ' (.const nOutParam [.succ (.succ (.param wP))])
      (M.cval nOutParam (Level.substFn (φA φ) [uP] [.succ (.succ (.param wP))])) := fun ρ' =>
    HA.outParam.const M (us := [.succ (.succ (.param wP))]) rfl (φA φ) ρ'
  have dTy : Denotes M.cval env (φA φ) ρ (.forallE (.sort (.succ (.param uP))) (.forallE (.sort (.succ (.param vP)))
      (.forallE (.app (.const nOutParam [.succ (.succ (.param wP))]) (.sort (.succ (.param wP))))
        (.forallE (.app (.app (.app (.const nHAdd [.param uP, .param vP, .param wP]) (.bvar 2)) (.bvar 1)) (.bvar 0))
          (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 3) dm) dm) dm) dm) dm) dm)
      (piR 1 (univ 1) fun a => piR 1 (univ 1) fun b =>
        piR 1 (app (M.cval nOutParam (Level.substFn (φA φ) [uP] [.succ (.succ (.param wP))])) (univ 1)) fun c =>
          piR 1 (app (app (app (M.cval nHAdd (φA φ)) a) b) c) fun _ => piR 1 a fun _ => piR 1 b fun _ => c) :=
    pi_dm (sU _) fun _ _ => pi_dm (sV _) fun _ _ => pi_dm (.app (dOut _) (sW _)) fun _ _ =>
      pi_dm (.app (.app (.app (dHA _) .bvar) .bvar) .bvar) fun _ _ => pi_dm .bvar fun _ _ => pi_dm .bvar fun _ _ => .bvar
  have hH := HA.hAddH.mem_of M dTy
  -- the instance
  have sU0 : ∀ ρ', Denotes M.cval env (φ0 φ) ρ' (.sort (.succ (.param uP))) (univ 1) := fun _ =>
    dsort M _ _ _ _ (by simp [Level.eval, φ0_u])
  have dAdd : ∀ ρ', Denotes M.cval env (φ0 φ) ρ' (.const nAdd [.param uP]) (M.cval nAdd (φ0 φ)) := fun ρ' => by
    have := HA.add.const M (us := [.param uP]) rfl (φ0 φ) ρ'
    rwa [φ0_self] at this
  have dHA0 : ∀ ρ', Denotes M.cval env (φ0 φ) ρ' (.const nHAdd [.param uP, .param uP, .param uP])
      (M.cval nHAdd (φA φ)) := fun ρ' => by
    have := HA.hadd.const M (us := [.param uP, .param uP, .param uP]) rfl (φ0 φ) ρ'
    rwa [φ0_hadd] at this
  have dInst : Denotes M.cval env (φ0 φ) ρ (.forallE (.sort (.succ (.param uP)))
      (.forallE (.app (.const nAdd [.param uP]) (.bvar 0))
        (.app (.app (.app (.const nHAdd [.param uP, .param uP, .param uP]) (.bvar 1)) (.bvar 1)) (.bvar 1)) dm) dm)
      (piR 1 (univ 1) fun a => piR 1 (app (M.cval nAdd (φ0 φ)) a) fun _ =>
        app (app (app (M.cval nHAdd (φA φ)) a) a) a) :=
    pi_dm (sU0 _) fun _ _ => pi_dm (.app (dAdd _) .bvar) fun _ _ => .app (.app (.app (dHA0 _) .bvar) .bvar) .bvar
  have hInst := HA.instHAdd.mem_of M dInst
  have hI1 := app_mem_piR hInst hT (by intro h; omega)
  have hI2 := app_mem_piR hI1 hI (by intro h; omega)
  have hT' : T ∈ˢ app (M.cval nOutParam (Level.substFn (φA φ) [uP] [.succ (.succ (.param wP))])) (univ 1) := by
    rw [oP]; exact hT
  have e1 := app_mem_piR hH hT (by intro h; omega)
  have e2 := app_mem_piR e1 hT (by intro h; omega)
  have e3 := app_mem_piR e2 hT' (by intro h; omega)
  have e4 := app_mem_piR e3 hI2 (by intro h; omega)
  exact e4

/-- the canonical `UInt64` encoding -/
noncomputable def encU (M : Model V env) (φ : LevelParam → Nat) (x : UInt64) : V :=
  app (M.cval nUOf φ) (natEnc M φ x.toNat)

def hAddE (T : Expr) (i : Name) : Expr :=
  .app (.app (.app (.app (.const nHAddH [.zero, .zero, .zero]) T) T) T) (.app (.app (.const nInstHAdd [.zero]) T) (.const i []))
def addNE (a b : Expr) : Expr := .app (.app (hAddE tN nInstAddN) a) b
def addUE (a b : Expr) : Expr := .app (.app (hAddE tU nInstAddU) a) b
def ofNE (a : Expr) : Expr := .app (.const nUOf []) a
/-- `OfNat.ofNat.{0} Nat (lit 2^64) (instOfNatNat (lit 2^64))` -/
def litNatE : Expr := .app (.app (.app (.const nOfNatH [.zero]) tN) (.lit (.natVal UInt64.size)))
  (.app (.const (anonymous |>.str "instOfNatNat") []) (.lit (.natVal UInt64.size)))

def nAdd0 : Name := anonymous |>.str "add0"
def nAddS : Name := anonymous |>.str "addS"
def nBrAdd : Name := anonymous |>.str "br_add"
def nBrWrap : Name := anonymous |>.str "br_wrap"

/-- the stored theorems `+` reads (Mini: `AddEnv.add0/addS/brAdd/brWrap`, with `Nat.zero`/`Nat.succ` spelled out) -/
structure AddThms (env : Env) : Prop where
  natSort : Stored env natName [] (.sort lv1)
  add0 : Stored env nAdd0 [] (.forallE tN (eqE lv1 tN (addNE (.bvar 0) (.const natZeroName [])) (.bvar 0)) dm)
  addS : Stored env nAddS [] (.forallE tN (.forallE tN (eqE lv1 tN
    (addNE (.bvar 1) (.app (.const natSuccName []) (.bvar 0))) (.app (.const natSuccName []) (addNE (.bvar 1) (.bvar 0)))) dm) dm)
  brAdd : Stored env nBrAdd [] (.forallE tN (.forallE tN (eqE lv1 tU
    (addUE (ofNE (.bvar 1)) (ofNE (.bvar 0))) (ofNE (addNE (.bvar 1) (.bvar 0)))) dm) dm)
  brWrap : Stored env nBrWrap [] (.forallE tN (eqE lv1 tU (ofNE (addNE (.bvar 0) litNatE)) (ofNE (.bvar 0))) dm)

/-- one stored `∀ x : T, a = b` at an instance (Mini: `transferN`, 1 binder) -/
theorem Stored.eq1 (M : Model V env) {n : Name} {T : Expr} {u : Level} {S a b : Expr}
    (h : Stored env n [] (.forallE T (eqE u S a b) dm)) {φ : LevelParam → Nat} {ρ : BVarIdx → V} {A x Sv av bv : V}
    (hA : Denotes M.cval env φ ρ T A) (hx : x ∈ˢ A) (hS : Denotes M.cval env φ (push x ρ) S Sv)
    (ha : Denotes M.cval env φ (push x ρ) a av) (hb : Denotes M.cval env φ (push x ρ) b bv)
    (hSu : Sv ∈ˢ univ (Level.eval φ u)) (hav : av ∈ˢ Sv) (hbv : bv ∈ˢ Sv) : av = bv := by
  obtain ⟨ci, hf, -, hty⟩ := h
  have hI := inhab_const M hf φ ρ
  rw [hty] at hI
  obtain ⟨Sv', av', bv', hS', ha', hb', hE⟩ := Inhab.eq (Inhab.pi hI hA hx)
  obtain rfl := Denotes_functional hS hS'
  obtain rfl := Denotes_functional ha ha'
  obtain rfl := Denotes_functional hb hb'
  exact hE hSu hav hbv

/-- two binders over the same closed type `T` -/
theorem Stored.eq2 (M : Model V env) {n : Name} {T : Expr} {u : Level} {S a b : Expr}
    (h : Stored env n [] (.forallE T (.forallE T (eqE u S a b) dm) dm)) {φ : LevelParam → Nat} {ρ : BVarIdx → V}
    {A x y Sv av bv : V} (hA : Denotes M.cval env φ ρ T A) (hA' : Denotes M.cval env φ (push x ρ) T A)
    (hx : x ∈ˢ A) (hy : y ∈ˢ A) (hS : Denotes M.cval env φ (push y (push x ρ)) S Sv)
    (ha : Denotes M.cval env φ (push y (push x ρ)) a av) (hb : Denotes M.cval env φ (push y (push x ρ)) b bv)
    (hSu : Sv ∈ˢ univ (Level.eval φ u)) (hav : av ∈ˢ Sv) (hbv : bv ∈ˢ Sv) : av = bv := by
  obtain ⟨ci, hf, -, hty⟩ := h
  have hI := inhab_const M hf φ ρ
  rw [hty] at hI
  obtain ⟨Sv', av', bv', hS', ha', hb', hE⟩ := Inhab.eq (Inhab.pi (Inhab.pi hI hA hx) hA' hy)
  obtain rfl := Denotes_functional hS hS'
  obtain rfl := Denotes_functional ha ha'
  obtain rfl := Denotes_functional hb hb'
  exact hE hSu hav hbv

/-- `Nat.add` from its two recursion theorems, on canonical numerals -/
theorem add_nat (Z Sc ADD N : V) (nat : Nat → V) (hnz : nat 0 = Z) (hns : ∀ k, nat (k + 1) = app Sc (nat k))
    (hmem : ∀ k, nat k ∈ˢ N)
    (hz : ∀ x, x ∈ˢ N → app (app ADD x) Z = x)
    (hs : ∀ x y, x ∈ˢ N → y ∈ˢ N → app (app ADD x) (app Sc y) = app Sc (app (app ADD x) y)) :
    ∀ a b, app (app ADD (nat a)) (nat b) = nat (a + b) := by
  intro a b
  induction b with
  | zero => rw [hnz, hz _ (hmem a)]; rfl
  | succ b ih => rw [hns, hs _ _ (hmem a) (hmem b), ih, ← hns]; rfl

/-- `Nat.succ` maps `Nat` into `Nat` (the step of `natEnc_mem`) -/
theorem succ_mem (M : Model V env) (H : NatTypes env) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (a : V)
    (ha : a ∈ˢ M.cval natName φ) : app (M.cval natSuccName φ) a ∈ˢ M.cval natName φ := by
  obtain ⟨cn, hn, pn⟩ := H.nat
  obtain ⟨cs, hs, ps⟩ := H.succ
  have dN : ∀ ρ', Denotes M.cval env φ ρ' (.const natName []) (M.cval natName φ) := fun _ => Denotes_const' hn pn rfl
  obtain ⟨m, hm, hty⟩ := H.succTy cs hs
  have dP : Denotes M.cval env φ ρ (.forallE (.const natName []) (.const natName []) m)
      (piR (regime φ m.pw) (M.cval natName φ) fun _ => M.cval natName φ) :=
    .pi (dN _) (fun _ _ => dN _) (fun h => absurd h (hm φ))
  have hS : M.cval natSuccName φ ∈ˢ _ := mem_closed M hs (ρ := ρ) (by rw [hty]; exact dP)
  obtain ⟨Bx, hB, hmem⟩ := mem_app dP hS (dN _) ha
  rwa [Denotes_functional hB (dN _)] at hmem

/-- **`Open.bin` for `+` (`Add.add_field`), ported.**  `hlit` is the `br_litN` fact for `2^64` (`Mini.litN_field`), as a
hypothesis until `litN` is ported (same pattern as `litU_fact`). -/
theorem add_core (M : Model V env) (H : LitEnv env) (HA : AddEnv env) (HT : AddThms env) (hφ : CvalParams M)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    (hlit : ∀ ρ', Denotes M.cval env φ ρ' litNatE (natEnc M φ UInt64.size)) :
    ∃ ADD ADD64 : V, (∀ ρ', Denotes M.cval env φ ρ' (hAddE tN nInstAddN) ADD) ∧
      (∀ ρ', Denotes M.cval env φ ρ' (hAddE tU nInstAddU) ADD64) ∧
      (∀ a b, a ∈ˢ M.cval natName φ → b ∈ˢ M.cval natName φ → app (app ADD a) b ∈ˢ M.cval natName φ) ∧
      (∀ a b, app (app ADD (natEnc M φ a)) (natEnc M φ b) = natEnc M φ (a + b)) ∧
      (∀ a b, a ∈ˢ M.cval natName φ → b ∈ˢ M.cval natName φ →
        app (app ADD64 (app (M.cval nUOf φ) a)) (app (M.cval nUOf φ) b) = app (M.cval nUOf φ) (app (app ADD a) b)) ∧
      (∀ a, a ∈ˢ M.cval natName φ →
        app (M.cval nUOf φ) (app (app ADD a) (natEnc M φ UInt64.size)) = app (M.cval nUOf φ) a) := by
  obtain ⟨cn, hn, pn⟩ := H.nt.nat
  have dN : ∀ ρ', Denotes M.cval env φ ρ' tN (M.cval natName φ) := fun _ => Denotes_const' hn pn rfl
  have dU : ∀ ρ', Denotes M.cval env φ ρ' tU (M.cval nU φ) := fun _ => H.u64.const M rfl φ _
  have hNe : M.cval natName φ ∈ˢ univ (Level.eval φ lv1) := HT.natSort.mem_of M (φ := φ) (ρ := ρ) Denotes.sort
  have hUe : M.cval nU φ ∈ˢ univ (Level.eval φ lv1) := H.u64.mem_of M (φ := φ) (ρ := ρ) Denotes.sort
  have hNu : M.cval natName φ ∈ˢ univ 1 := hNe
  have hUu : M.cval nU φ ∈ˢ univ 1 := hUe
  have hnat := natEnc_mem M H.nt φ ρ
  obtain ⟨cz, hz', pz⟩ := H.nt.zero
  obtain ⟨cs, hs', ps⟩ := H.nt.succ
  have dZ : ∀ ρ', Denotes M.cval env φ ρ' (.const natZeroName []) (M.cval natZeroName φ) := fun _ => Denotes_const' hz' pz rfl
  have dS : ∀ ρ', Denotes M.cval env φ ρ' (.const natSuccName []) (M.cval natSuccName φ) := fun _ => Denotes_const' hs' ps rfl
  -- heads
  obtain ⟨ADD, hADD⟩ : ∃ A, A = app (app (app (app (M.cval nHAddH (φA φ)) (M.cval natName φ)) (M.cval natName φ)) (M.cval natName φ))
        (app (app (M.cval nInstHAdd (φ0 φ)) (M.cval natName φ)) (M.cval nInstAddN φ)) := ⟨_, rfl⟩
  obtain ⟨ADD64, hADD64⟩ : ∃ A, A = app (app (app (app (M.cval nHAddH (φA φ)) (M.cval nU φ)) (M.cval nU φ)) (M.cval nU φ))
        (app (app (M.cval nInstHAdd (φ0 φ)) (M.cval nU φ)) (M.cval nInstAddU φ)) := ⟨_, rfl⟩
  have dAddNE : ∀ ρ', Denotes M.cval env φ ρ' (hAddE tN nInstAddN) ADD := fun ρ' => hADD ▸
    .app (.app (.app (.app (HA.hAddH.const M (us := [.zero, .zero, .zero]) rfl φ ρ') (dN _)) (dN _)) (dN _))
      (.app (.app (HA.instHAdd.const M (us := [.zero]) rfl φ ρ') (dN _)) (HA.addNat.const M (us := []) rfl φ ρ'))
  have dAddUE : ∀ ρ', Denotes M.cval env φ ρ' (hAddE tU nInstAddU) ADD64 := fun ρ' => hADD64 ▸
    .app (.app (.app (.app (HA.hAddH.const M (us := [.zero, .zero, .zero]) rfl φ ρ') (dU _)) (dU _)) (dU _))
      (.app (.app (HA.instHAdd.const M (us := [.zero]) rfl φ ρ') (dU _)) (HA.addU64.const M (us := []) rfl φ ρ'))
  -- typing
  have hIN : M.cval nInstAddN φ ∈ˢ app (M.cval nAdd (φ0 φ)) (M.cval natName φ) :=
    HA.addNat.mem_of M (.app (HA.add.const M (us := [.zero]) rfl φ ρ) (dN _))
  have hIU : M.cval nInstAddU φ ∈ˢ app (M.cval nAdd (φ0 φ)) (M.cval nU φ) :=
    HA.addU64.mem_of M (.app (HA.add.const M (us := [.zero]) rfl φ ρ) (dU _))
  have hAN := hAdd_mem M HA hφ φ ρ hNu hIN
  have hAU := hAdd_mem M HA hφ φ ρ hUu hIU
  rw [← hADD] at hAN
  rw [← hADD64] at hAU
  have addMem : ∀ a b, a ∈ˢ M.cval natName φ → b ∈ˢ M.cval natName φ → app (app ADD a) b ∈ˢ M.cval natName φ := by
    intro a b ha hb
    have e1 := app_mem_piR hAN ha (by intro h; omega)
    exact app_mem_piR e1 hb (by intro h; omega)
  have dOF : Denotes M.cval env φ ρ (.forallE tN tU dm) (piR 1 (M.cval natName φ) fun _ => M.cval nU φ) :=
    pi_dm (dN _) fun _ _ => dU _
  have ofMem : ∀ a, a ∈ˢ M.cval natName φ → app (M.cval nUOf φ) a ∈ˢ M.cval nU φ := by
    intro a ha
    obtain ⟨Bx, hB, hm⟩ := mem_app dOF (H.ofNat.mem_of M dOF) (dN _) ha
    rwa [Denotes_functional hB (dU _)] at hm
  have sMem : ∀ a, a ∈ˢ M.cval natName φ → app (M.cval natSuccName φ) a ∈ˢ M.cval natName φ := by
    intro a ha
    exact succ_mem M H.nt φ ρ a ha
  have hz0 : M.cval natZeroName φ ∈ˢ M.cval natName φ := hnat 0
  have dOFc : ∀ ρ', Denotes M.cval env φ ρ' (.const nUOf []) (M.cval nUOf φ) := fun ρ' => H.ofNat.const M rfl φ ρ'
  -- the four transfers
  have hz : ∀ a, a ∈ˢ M.cval natName φ → app (app ADD a) (M.cval natZeroName φ) = a := by
    intro a ha
    exact HT.add0.eq1 M (dN ρ) ha (dN _) (.app (.app (dAddNE _) .bvar) (dZ _)) .bvar hNe (addMem _ _ ha hz0) ha
  have hs : ∀ a b, a ∈ˢ M.cval natName φ → b ∈ˢ M.cval natName φ →
      app (app ADD a) (app (M.cval natSuccName φ) b) = app (M.cval natSuccName φ) (app (app ADD a) b) := by
    intro a b ha hb
    exact HT.addS.eq2 M (dN ρ) (dN _) ha hb (dN _) (.app (.app (dAddNE _) .bvar) (.app (dS _) .bvar))
      (.app (dS _) (.app (.app (dAddNE _) .bvar) .bvar)) hNe (addMem _ _ ha (sMem _ hb)) (sMem _ (addMem _ _ ha hb))
  have hadd : ∀ a b, a ∈ˢ M.cval natName φ → b ∈ˢ M.cval natName φ →
      app (app ADD64 (app (M.cval nUOf φ) a)) (app (M.cval nUOf φ) b) = app (M.cval nUOf φ) (app (app ADD a) b) := by
    intro a b ha hb
    have e1 := app_mem_piR hAU (ofMem _ ha) (by intro h; omega)
    exact HT.brAdd.eq2 M (dN ρ) (dN _) ha hb (dU _)
      (.app (.app (dAddUE _) (.app (dOFc _) .bvar)) (.app (dOFc _) .bvar))
      (.app (dOFc _) (.app (.app (dAddNE _) .bvar) .bvar)) hUe (app_mem_piR e1 (ofMem _ hb) (by intro h; omega))
      (ofMem _ (addMem _ _ ha hb))
  have hwrap : ∀ a, a ∈ˢ M.cval natName φ →
      app (M.cval nUOf φ) (app (app ADD a) (natEnc M φ UInt64.size)) = app (M.cval nUOf φ) a := by
    intro a ha
    exact HT.brWrap.eq1 M (dN ρ) ha (dU _) (.app (dOFc _) (.app (.app (dAddNE _) .bvar) (hlit _)))
      (.app (dOFc _) .bvar) hUe (ofMem _ (addMem _ _ ha (hnat _))) (ofMem _ ha)
  -- algebra
  have hAdd := add_nat (M.cval natZeroName φ) (M.cval natSuccName φ) ADD (M.cval natName φ) (natEnc M φ) rfl
    (fun _ => rfl) hnat hz hs
  exact ⟨ADD, ADD64, dAddNE, dAddUE, addMem, hAdd, hadd, hwrap⟩

/-- the 2^64 wrap on canonical numerals: `ofNat k = ofNat (k % 2^64)` (`Len.wrap_mod`) -/
theorem wrap_mod (M : Model V env) (H : LitEnv env) (HA : AddEnv env) (HT : AddThms env) (hφ : CvalParams M)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    (hlit : ∀ ρ', Denotes M.cval env φ ρ' litNatE (natEnc M φ UInt64.size)) :
    ∀ k, app (M.cval nUOf φ) (natEnc M φ k) = app (M.cval nUOf φ) (natEnc M φ (k % UInt64.size)) := by
  obtain ⟨ADD, ADD64, -, -, -, hAdd, -, hwrap⟩ := add_core M H HA HT hφ φ ρ hlit
  have hnat := natEnc_mem M H.nt φ ρ
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases h : k < UInt64.size
    · rw [Nat.mod_eq_of_lt h]
    · have hk : k = (k - UInt64.size) + UInt64.size := by omega
      have := ih (k - UInt64.size) (by have : 0 < UInt64.size := by decide
                                       omega)
      rw [hk, ← hAdd, hwrap _ (hnat _), this, Nat.add_mod_right]

/-- **`Open.bin` for `+` (`Add.add_field`), ported.**  `hlit` is the `br_litN` fact for `2^64` (`Mini.litN_field`), as a
hypothesis until `litN` is ported (same pattern as `litU_fact`). -/
theorem add_fact (M : Model V env) (H : LitEnv env) (HA : AddEnv env) (HT : AddThms env) (hφ : CvalParams M)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    (hlit : ∀ ρ', Denotes M.cval env φ ρ' litNatE (natEnc M φ UInt64.size)) {Hv : V}
    (hH : Denotes M.cval env φ ρ (hAddE tU nInstAddU) Hv) (x y : UInt64) :
    app (app Hv (encU M φ x)) (encU M φ y) = encU M φ (x + y) := by
  obtain ⟨ADD, ADD64, dN', dU', -, hAdd, hadd, hwrap⟩ := add_core M H HA HT hφ φ ρ hlit
  have hnat := natEnc_mem M H.nt φ ρ
  rw [Denotes_functional hH (dU' ρ)]
  show app (app ADD64 (app (M.cval nUOf φ) (natEnc M φ x.toNat))) (app (M.cval nUOf φ) (natEnc M φ y.toNat)) =
    app (M.cval nUOf φ) (natEnc M φ (x + y).toNat)
  rw [hadd _ _ (hnat _) (hnat _), hAdd, UInt64.toNat_add, show (2:Nat) ^ 64 = UInt64.size from rfl]
  have hx := x.toNat_lt_size
  have hy := y.toNat_lt_size
  generalize UInt64.size = N at hx hy hwrap hAdd ⊢
  by_cases h : x.toNat + y.toNat < N
  · rw [Nat.mod_eq_of_lt h]
  · have hk : x.toNat + y.toNat = (x.toNat + y.toNat - N) + N := by omega
    have hm : (x.toNat + y.toNat) % N = x.toNat + y.toNat - N := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hm, hk, ← hAdd, hwrap _ (hnat _), Nat.add_sub_cancel]

#print axioms add_fact
end Bridge.Real
