/- Bridge.RealArith: `*` (op 3) of `Bridge.Arith` ported to the REAL con-leche `Denotes`/`Model`
(generic heterogeneous-operator typing `op_mem`, `mul_set`, `mul_field`).  `-` needs `guard_mem` (Cmp) and is not ported. -/
import Bridge.RealAdd

namespace Bridge.Real
open ConLeche ConLeche.SetModel SetTheory
open Name (anonymous)
universe w
variable {V : Type w} [SetTheory V] {env : Env}

/-- `@f.{0,0,0} T T T (hi.{0} T I)` -/
def opHead (f hi : Name) (T : Expr) (I : Name) : Expr :=
  .app (.app (.app (.app (.const f [.zero, .zero, .zero]) T) T) T) (.app (.app (.const hi [.zero]) T) (.const I []))

theorem hAddE_eq (T : Expr) (i : Name) : hAddE T i = opHead nHAddH nInstHAdd T i := rfl

/-- the set of `@f T T T (hi T I)` -/
noncomputable def opS (M : Model V env) (φ : LevelParam → Nat) (f hi : Name) (T : V) (I : Name) : V :=
  app (app (app (app (M.cval f (φA φ)) T) T) T) (app (app (M.cval hi (φ0 φ)) T) (M.cval I φ))

/-- a heterogeneous operator `f : {α β γ} [H α β γ] → α → β → γ` with homogeneous instance `hi : {α} [K α] → H α α α` -/
structure OpEnv (env : Env) (f H hi K kN kU : Name) : Prop where
  cls : HasLv env H [uP, vP, wP]
  fH : Stored env f [uP, vP, wP] (.forallE (.sort (.succ (.param uP))) (.forallE (.sort (.succ (.param vP)))
    (.forallE (.app (.const nOutParam [.succ (.succ (.param wP))]) (.sort (.succ (.param wP))))
      (.forallE (.app (.app (.app (.const H [.param uP, .param vP, .param wP]) (.bvar 2)) (.bvar 1)) (.bvar 0))
        (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 3) dm) dm) dm) dm) dm) dm)
  k : HasLv env K [uP]
  hiT : Stored env hi [uP] (.forallE (.sort (.succ (.param uP))) (.forallE (.app (.const K [.param uP]) (.bvar 0))
    (.app (.app (.app (.const H [.param uP, .param uP, .param uP]) (.bvar 1)) (.bvar 1)) (.bvar 1)) dm) dm)
  kNat : Stored env kN [] (.app (.const K [.zero]) tN)
  kU64 : Stored env kU [] (.app (.const K [.zero]) tU)

/-- typing of `@f T T T (hi T I) X Y` (`Arith.op_mem`) -/
theorem op_mem (M : Model V env) {f H hi K kN kU : Name} (HA : AddEnv env) (HO : OpEnv env f H hi K kN kU)
    (hφ : CvalParams M) (φ : LevelParam → Nat) (ρ : BVarIdx → V) {T X Y : V} {I : Name} (hT : T ∈ˢ univ 1)
    (hI : M.cval I φ ∈ˢ app (M.cval K (φ0 φ)) T) (hX : X ∈ˢ T) (hY : Y ∈ˢ T) :
    app (app (opS M φ f hi T I) X) Y ∈ˢ T := by
  have oP := outParam_type M HA hφ φ ρ
  have sU : ∀ ρ', Denotes M.cval env (φA φ) ρ' (.sort (.succ (.param uP))) (univ 1) := fun _ =>
    dsort M _ _ _ _ (by simp [Level.eval, φA_u])
  have sV : ∀ ρ', Denotes M.cval env (φA φ) ρ' (.sort (.succ (.param vP))) (univ 1) := fun _ =>
    dsort M _ _ _ _ (by simp [Level.eval, φA_v])
  have sW : ∀ ρ', Denotes M.cval env (φA φ) ρ' (.sort (.succ (.param wP))) (univ 1) := fun _ =>
    dsort M _ _ _ _ (by simp [Level.eval, φA_w])
  have dHA : ∀ ρ', Denotes M.cval env (φA φ) ρ' (.const H [.param uP, .param vP, .param wP]) (M.cval H (φA φ)) :=
    fun ρ' => by
      have := HO.cls.const M (us := [.param uP, .param vP, .param wP]) rfl (φA φ) ρ'
      rwa [φA_self] at this
  have dOut : ∀ ρ', Denotes M.cval env (φA φ) ρ' (.const nOutParam [.succ (.succ (.param wP))])
      (M.cval nOutParam (Level.substFn (φA φ) [uP] [.succ (.succ (.param wP))])) := fun ρ' =>
    HA.outParam.const M (us := [.succ (.succ (.param wP))]) rfl (φA φ) ρ'
  have dTy : Denotes M.cval env (φA φ) ρ (.forallE (.sort (.succ (.param uP))) (.forallE (.sort (.succ (.param vP)))
      (.forallE (.app (.const nOutParam [.succ (.succ (.param wP))]) (.sort (.succ (.param wP))))
        (.forallE (.app (.app (.app (.const H [.param uP, .param vP, .param wP]) (.bvar 2)) (.bvar 1)) (.bvar 0))
          (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 3) dm) dm) dm) dm) dm) dm)
      (piR 1 (univ 1) fun a => piR 1 (univ 1) fun b =>
        piR 1 (app (M.cval nOutParam (Level.substFn (φA φ) [uP] [.succ (.succ (.param wP))])) (univ 1)) fun c =>
          piR 1 (app (app (app (M.cval H (φA φ)) a) b) c) fun _ => piR 1 a fun _ => piR 1 b fun _ => c) :=
    pi_dm (sU _) fun _ _ => pi_dm (sV _) fun _ _ => pi_dm (.app (dOut _) (sW _)) fun _ _ =>
      pi_dm (.app (.app (.app (dHA _) .bvar) .bvar) .bvar) fun _ _ => pi_dm .bvar fun _ _ => pi_dm .bvar fun _ _ => .bvar
  have hH := HO.fH.mem_of M dTy
  have sU0 : ∀ ρ', Denotes M.cval env (φ0 φ) ρ' (.sort (.succ (.param uP))) (univ 1) := fun _ =>
    dsort M _ _ _ _ (by simp [Level.eval, φ0_u])
  have dK : ∀ ρ', Denotes M.cval env (φ0 φ) ρ' (.const K [.param uP]) (M.cval K (φ0 φ)) := fun ρ' => by
    have := HO.k.const M (us := [.param uP]) rfl (φ0 φ) ρ'
    rwa [φ0_self] at this
  have dHA0 : ∀ ρ', Denotes M.cval env (φ0 φ) ρ' (.const H [.param uP, .param uP, .param uP]) (M.cval H (φA φ)) :=
    fun ρ' => by
      have := HO.cls.const M (us := [.param uP, .param uP, .param uP]) rfl (φ0 φ) ρ'
      rwa [φ0_hadd] at this
  have dInst : Denotes M.cval env (φ0 φ) ρ (.forallE (.sort (.succ (.param uP)))
      (.forallE (.app (.const K [.param uP]) (.bvar 0))
        (.app (.app (.app (.const H [.param uP, .param uP, .param uP]) (.bvar 1)) (.bvar 1)) (.bvar 1)) dm) dm)
      (piR 1 (univ 1) fun a => piR 1 (app (M.cval K (φ0 φ)) a) fun _ =>
        app (app (app (M.cval H (φA φ)) a) a) a) :=
    pi_dm (sU0 _) fun _ _ => pi_dm (.app (dK _) .bvar) fun _ _ => .app (.app (.app (dHA0 _) .bvar) .bvar) .bvar
  have hInst := HO.hiT.mem_of M dInst
  have hI1 := app_mem_piR hInst hT (by intro h; omega)
  have hI2 := app_mem_piR hI1 hI (by intro h; omega)
  have hT' : T ∈ˢ app (M.cval nOutParam (Level.substFn (φA φ) [uP] [.succ (.succ (.param wP))])) (univ 1) := by
    rw [oP]; exact hT
  have e1 := app_mem_piR hH hT (by intro h; omega)
  have e2 := app_mem_piR e1 hT (by intro h; omega)
  have e3 := app_mem_piR e2 hT' (by intro h; omega)
  have e4 := app_mem_piR e3 hI2 (by intro h; omega)
  have e5 := app_mem_piR e4 hX (by intro h; omega)
  exact app_mem_piR e5 hY (by intro h; omega)

theorem opS_D (M : Model V env) {f H hi K kN kU : Name} (HO : OpEnv env f H hi K kN kU) {I : Name} {ty : Expr}
    (hI : Stored env I [] ty) (φ : LevelParam → Nat) {ρ : BVarIdx → V} {T : Expr} {Tv : V}
    (hT : Denotes M.cval env φ ρ T Tv) : Denotes M.cval env φ ρ (opHead f hi T I) (opS M φ f hi Tv I) :=
  .app (.app (.app (.app (HO.fH.const M (us := [.zero, .zero, .zero]) rfl φ ρ) hT) hT) hT)
    (.app (.app (HO.hiT.const M (us := [.zero]) rfl φ ρ) hT) (hI.const M (us := []) rfl φ ρ))

def nHMulH : Name := anonymous |>.str "HMul" |>.str "hMul"
def nHMul : Name := anonymous |>.str "HMul"
def nInstHMul : Name := anonymous |>.str "instHMul"
def nMul : Name := anonymous |>.str "Mul"
def nInstMulN : Name := anonymous |>.str "instMulNat"
def nInstMulU : Name := anonymous |>.str "instMulUInt64"
def nMulN0 : Name := anonymous |>.str "mul_n0"
def nMulNs : Name := anonymous |>.str "mul_ns"
def nBrMul : Name := anonymous |>.str "br_mul"

def mulNE (a b : Expr) : Expr := .app (.app (opHead nHMulH nInstHMul tN nInstMulN) a) b
def mulUE (a b : Expr) : Expr := .app (.app (opHead nHMulH nInstHMul tU nInstMulU) a) b

structure MulThms (env : Env) : Prop where
  op : OpEnv env nHMulH nHMul nInstHMul nMul nInstMulN nInstMulU
  n0 : Stored env nMulN0 [] (.forallE tN (eqE lv1 tN (mulNE (.bvar 0) (.const natZeroName [])) (.const natZeroName [])) dm)
  ns : Stored env nMulNs [] (.forallE tN (.forallE tN (eqE lv1 tN (mulNE (.bvar 1) (.app (.const natSuccName []) (.bvar 0)))
    (addNE (mulNE (.bvar 1) (.bvar 0)) (.bvar 1))) dm) dm)
  br : Stored env nBrMul [] (.forallE tN (.forallE tN (eqE lv1 tU
    (mulUE (ofNE (.bvar 1)) (ofNE (.bvar 0))) (ofNE (mulNE (.bvar 1) (.bvar 0)))) dm) dm)

set_option maxHeartbeats 800000 in
/-- **`*` (op 3)** (`Arith.mul_field`, with `mul_set` inside) -/
theorem mul_field (M : Model V env) (H : LitEnv env) (HA : AddEnv env) (HT : AddThms env) (HM : MulThms env)
    (hφ : CvalParams M) (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    (hlit : ∀ ρ', Denotes M.cval env φ ρ' litNatE (natEnc M φ UInt64.size)) {Hv : V}
    (hH : Denotes M.cval env φ ρ (opHead nHMulH nInstHMul tU nInstMulU) Hv) (x y : UInt64) :
    app (app Hv (encU M φ x)) (encU M φ y) = encU M φ (x * y) := by
  obtain ⟨ADD, ADD64, dADD, -, addMem, hAdd, -, -⟩ := add_core M H HA HT hφ φ ρ hlit
  have wrap := wrap_mod M H HA HT hφ φ ρ hlit
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
  have dOFc : ∀ ρ', Denotes M.cval env φ ρ' (.const nUOf []) (M.cval nUOf φ) := fun ρ' => H.ofNat.const M rfl φ ρ'
  have dOF : Denotes M.cval env φ ρ (.forallE tN tU dm) (piR 1 (M.cval natName φ) fun _ => M.cval nU φ) :=
    pi_dm (dN _) fun _ _ => dU _
  have ofMem : ∀ a, a ∈ˢ M.cval natName φ → app (M.cval nUOf φ) a ∈ˢ M.cval nU φ := by
    intro a ha
    obtain ⟨Bx, hB, hm⟩ := mem_app dOF (H.ofNat.mem_of M dOF) (dN _) ha
    rwa [Denotes_functional hB (dU _)] at hm
  have hIN : M.cval nInstMulN φ ∈ˢ app (M.cval nMul (φ0 φ)) (M.cval natName φ) :=
    HM.op.kNat.mem_of M (.app (HM.op.k.const M (us := [.zero]) rfl φ ρ) (dN _))
  have hIU : M.cval nInstMulU φ ∈ˢ app (M.cval nMul (φ0 φ)) (M.cval nU φ) :=
    HM.op.kU64.mem_of M (.app (HM.op.k.const M (us := [.zero]) rfl φ ρ) (dU _))
  have mm : ∀ a b, a ∈ˢ M.cval natName φ → b ∈ˢ M.cval natName φ →
      app (app (opS M φ nHMulH nInstHMul (M.cval natName φ) nInstMulN) a) b ∈ˢ M.cval natName φ :=
    fun a b ha hb => op_mem M HA HM.op hφ φ ρ hNu hIN ha hb
  have dMulN : ∀ ρ', Denotes M.cval env φ ρ' (opHead nHMulH nInstHMul tN nInstMulN)
      (opS M φ nHMulH nInstHMul (M.cval natName φ) nInstMulN) := fun ρ' => opS_D M HM.op HM.op.kNat φ (dN _)
  have dMulU : ∀ ρ', Denotes M.cval env φ ρ' (opHead nHMulH nInstHMul tU nInstMulU)
      (opS M φ nHMulH nInstHMul (M.cval nU φ) nInstMulU) := fun ρ' => opS_D M HM.op HM.op.kU64 φ (dU _)
  have dAddN : ∀ ρ', Denotes M.cval env φ ρ' (hAddE tN nInstAddN) ADD := dADD
  -- `mul_set`
  have mul_set : ∀ a b, app (app (opS M φ nHMulH nInstHMul (M.cval natName φ) nInstMulN) (natEnc M φ a)) (natEnc M φ b) =
      natEnc M φ (a * b) := by
    intro a b
    induction b with
    | zero =>
      exact HM.n0.eq1 M (dN ρ) (hnat a) (dN _) (.app (.app (dMulN _) .bvar) (dZ _)) (dZ _) hNe (mm _ _ (hnat a) (hnat 0)) (hnat 0)
    | succ b ih =>
      have key := HM.ns.eq2 M (dN ρ) (dN _) (hnat a) (hnat b) (dN _) (.app (.app (dMulN _) .bvar) (.app (dS _) .bvar))
        (.app (.app (dAddN _) (.app (.app (dMulN _) .bvar) .bvar)) .bvar) hNe (mm _ _ (hnat a) (hnat (b + 1)))
        (addMem _ _ (mm _ _ (hnat a) (hnat b)) (hnat a))
      simp only [push] at key
      have e : natEnc M φ (b + 1) = app (M.cval natSuccName φ) (natEnc M φ b) := rfl
      rw [e, key, ih, hAdd]
      rfl
  -- the `br_mul` transfer
  have key := HM.br.eq2 M (dN ρ) (dN _) (hnat x.toNat) (hnat y.toNat) (dU _)
    (.app (.app (dMulU _) (.app (dOFc _) .bvar)) (.app (dOFc _) .bvar))
    (.app (dOFc _) (.app (.app (dMulN _) .bvar) .bvar)) hUe
    (op_mem M HA HM.op hφ φ ρ hUu hIU (ofMem _ (hnat _)) (ofMem _ (hnat _)))
    (ofMem _ (mm _ _ (hnat _) (hnat _)))
  simp only [push] at key
  rw [Denotes_functional hH (dMulU ρ)]
  show app (app (opS M φ nHMulH nInstHMul (M.cval nU φ) nInstMulU) (app (M.cval nUOf φ) (natEnc M φ x.toNat)))
    (app (M.cval nUOf φ) (natEnc M φ y.toNat)) = app (M.cval nUOf φ) (natEnc M φ (x * y).toNat)
  rw [key, mul_set, wrap, UInt64.toNat_mul]

#print axioms mul_field
end Bridge.Real
