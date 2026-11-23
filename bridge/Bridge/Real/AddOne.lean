/- Bridge.Real.AddOne: growth step 3a, against REAL con-leche.

Program: `def f (x : Nat) : Nat := x + 1`, now through its REAL emitted body: the stream holds
  `e1 : ∀ x : Nat, f x = x + 1`   (pp.all: `@HAdd.hAdd.{0,0,0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) x
                                      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))`)
  `e2 : ∀ x : Nat, x + 1 = Nat.succ x`,   `e3 : outParam.{2} Type = Type`   (all `rfl` in Lean)
and the defs the body mentions (HAdd.hAdd, instHAdd, instAddNat, OfNat.ofNat, instOfNatNat, outParam) by their
declared types.  This is the first step that needs level bookkeeping (finding (a)): `HAdd`, `Add`, `OfNat`, `Nat`
are read inside level-polymorphic heads at induced assignments; `CvalParams` (model_exists') relates them
(`const_agree`).  The inductives `HAdd`/`Add`/`OfNat` need NO typing of their own: their `find?` comes out of
the denotation of the defs' stored types. -/
import Bridge.Real.Tiny
import Bridge.Real.Spine

namespace Bridge.Real.AddOne
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real Bridge.Real.Tiny Bridge.ModelExists2

universe w
variable {V : Type w} [SetTheory V]

def nm (s : String) : Name := .str .anonymous s
def nm2 (a b : String) : Name := .str (.str .anonymous a) b
def lu : Name := nm "u"
def lv : Name := nm "v"
def lw : Name := nm "w"
def pu : Level := .param lu
def pv : Level := .param lv
def pw : Level := .param lw
def L1 : Level := .succ .zero
def L2 : Level := .succ L1
def L3 : Level := .succ L2

def nev (Ts : List Expr) : List BinderMeta := Ts.map fun _ => ⟨.never⟩
/-- a declared telescope as the parser leaves it (binder data `.never`) -/
def piV (Ts : List Expr) (B : Expr) : Expr := piN (Ts.zip (nev Ts)) B
def apps (f : Expr) : List Expr → Expr
  | [] => f
  | a :: as => apps (.app f a) as

def hAddN : Name := nm2 "HAdd" "hAdd"
def hAddC : Name := nm "HAdd"
def instHAddN : Name := nm "instHAdd"
def addC : Name := nm "Add"
def instAddNatN : Name := nm "instAddNat"
def ofNatN : Name := nm2 "OfNat" "ofNat"
def ofNatC : Name := nm "OfNat"
def instOfNatNatN : Name := nm "instOfNatNat"
def outParamN : Name := nm "outParam"

/-! declared types, as (binder domains, body) -/
def hAddTs : List Expr := [.sort (.succ pu), .sort (.succ pv),
  .app (.const outParamN [.succ (.succ pw)]) (.sort (.succ pw)),
  apps (.const hAddC [pu, pv, pw]) [.bvar 2, .bvar 1, .bvar 0], .bvar 3, .bvar 3]
def instHAddTs : List Expr := [.sort (.succ pu), .app (.const addC [pu]) (.bvar 0)]
def instHAddB : Expr := apps (.const hAddC [pu, pu, pu]) [.bvar 1, .bvar 1, .bvar 1]
def instAddNatB : Expr := .app (.const addC [.zero]) natC
def ofNatTs : List Expr := [.sort (.succ pu), natC, apps (.const ofNatC [pu]) [.bvar 1, .bvar 0]]
def instOfNatNatB : Expr := apps (.const ofNatC [.zero]) [natC, .bvar 0]

/-! the emitted terms -/
def instE : Expr := apps (.const instHAddN [.zero]) [natC, .const instAddNatN []]
def oneE : Expr := apps (.const ofNatN [.zero]) [natC, .lit (.natVal 1), .app (.const instOfNatNatN []) (.lit (.natVal 1))]
def plus (e : Expr) : Expr := apps (.const hAddN [.zero, .zero, .zero]) [natC, natC, natC, instE, e, oneE]

def e1B (fN : Name) : Expr := eqE L1 natC (.app (.const fN []) (.bvar 0)) (plus (.bvar 0))
def e2B : Expr := eqE L1 natC (plus (.bvar 0)) (.app succC (.bvar 0))
def e3B : Expr := eqE L3 (.sort L2) (.app (.const outParamN [L2]) (.sort L1)) (.sort L1)

/-- The records the accepted stream must hold (declared exactly so). -/
structure Recs (ds : Array Declaration) (fN e1 e2 e3 : Name) : Prop where
  f : ∃ v h, Declaration.defnDecl ⟨fN, [], piV [natC] natC⟩ v h ∈ ds
  hAdd : ∃ v h, Declaration.defnDecl ⟨hAddN, [lu, lv, lw], piV hAddTs (.bvar 3)⟩ v h ∈ ds
  instHAdd : ∃ v h, Declaration.defnDecl ⟨instHAddN, [lu], piV instHAddTs instHAddB⟩ v h ∈ ds
  instAddNat : ∃ v h, Declaration.defnDecl ⟨instAddNatN, [], piV [] instAddNatB⟩ v h ∈ ds
  ofNat : ∃ v h, Declaration.defnDecl ⟨ofNatN, [lu], piV ofNatTs (.bvar 2)⟩ v h ∈ ds
  instOfNatNat : ∃ v h, Declaration.defnDecl ⟨instOfNatNatN, [], piV [natC] instOfNatNatB⟩ v h ∈ ds
  outParam : ∃ v h, Declaration.defnDecl ⟨outParamN, [lu], piV [.sort pu] (.sort pu)⟩ v h ∈ ds
  e1 : ∃ v, Declaration.thmDecl ⟨e1, [], piV [natC] (e1B fN)⟩ v ∈ ds
  e2 : ∃ v, Declaration.thmDecl ⟨e2, [], piV [natC] e2B⟩ v ∈ ds
  e3 : ∃ v, Declaration.thmDecl ⟨e3, [], piV [] e3B⟩ v ∈ ds

/-! ## generic wrappers -/
theorem teleX_tele {env : Env} {M : Model V env} {φ : LevelParam → Nat} :
    ∀ {ρ ρ' : BVarIdx → V} {Ts : List Expr} {xs : List V} (ms : List BinderMeta), ms.length = Ts.length →
      TeleX M φ ρ Ts xs ρ' → Tele M φ ρ (Ts.zip ms) ρ'
  | _, _, [], [], [], _, .nil => .nil
  | _, _, _ :: _, _ :: _, _ :: _, hl, .cons hA hx ht => .cons hA hx (teleX_tele _ (by simpa using hl) ht)

section
variable {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
  (acc : Cached.checkDecls .verified pins ds = .ok env)
include acc

theorem dspine {n : Name} {ps : List LevelParam} {Ts : List Expr} {B : Expr}
    (h : ∃ v hh, Declaration.defnDecl ⟨n, ps, piV Ts B⟩ v hh ∈ ds) (hT : ∀ T ∈ Ts, BF T) (hB : BF B)
    (M : Model V env) (ψ : LevelParam → Nat) (ρ ρ' : BVarIdx → V) (xs : List V)
    (ht : TeleX M ψ ρ Ts xs ρ') : ∃ Bv, Denotes M.cval env ψ ρ' B Bv ∧ appN (M.cval n ψ) xs ∈ˢ Bv := by
  obtain ⟨v, hh, hm⟩ := h
  exact stored_spine V acc hm rfl Ts (nev Ts) B (by simp [nev]) rfl hT hB M ψ ρ ρ' xs ht

theorem dden {n : Name} {ps : List LevelParam} {Ts : List Expr} {B : Expr}
    (h : ∃ v hh, Declaration.defnDecl ⟨n, ps, piV Ts B⟩ v hh ∈ ds) (hT : ∀ T ∈ Ts, BF T) (hB : BF B)
    (M : Model V env) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (us : List Level) (hus : us.length = ps.length) :
    Denotes M.cval env φ ρ (.const n us) (M.cval n (Level.substFn φ ps us)) := by
  obtain ⟨v, hh, hm⟩ := h
  exact stored_den V acc hm rfl Ts (nev Ts) B (by simp [nev]) rfl hT hB M φ ρ us hus

/-- transfer from a theorem record, by its declared type -/
theorem ttransfer {n : Name} {Ts : List Expr} {u : Level} {S a b : Expr}
    (h : ∃ v, Declaration.thmDecl ⟨n, [], piV Ts (eqE u S a b)⟩ v ∈ ds) (hT : ∀ T ∈ Ts, BF T)
    (hS : BF S) (ha : BF a) (hb : BF b)
    (M : Model V env) (φ : LevelParam → Nat) (ρ ρ' : BVarIdx → V) (xs : List V) (ht : TeleX M φ ρ Ts xs ρ')
    {Sv av bv : V} (dS : Denotes M.cval env φ ρ' S Sv) (da : Denotes M.cval env φ ρ' a av)
    (db : Denotes M.cval env φ ρ' b bv) (hSu : Sv ∈ˢ univ (Level.eval φ u)) (hav : av ∈ˢ Sv) (hbv : bv ∈ˢ Sv) :
    av = bv := by
  obtain ⟨v, hm⟩ := h
  obtain ⟨c, ms', hf, -, hl', hty⟩ := stored_tele V acc hm rfl Ts (nev Ts) (eqE u S a b) (by simp [nev]) rfl hT
    (by simp [eqE, BF, hS, ha, hb])
  exact transferN M hf hty φ ρ (teleX_tele ms' hl' ht) dS da db hSu hav hbv
end

/-- pointwise denotation of an argument list -/
inductive DenL {env : Env} (M : Model V env) (φ : LevelParam → Nat) (ρ : BVarIdx → V) : List Expr → List V → Prop
  | nil : DenL M φ ρ [] []
  | cons {a as v vs} : Denotes M.cval env φ ρ a v → DenL M φ ρ as vs → DenL M φ ρ (a :: as) (v :: vs)

theorem den_apps {env : Env} {M : Model V env} {φ : LevelParam → Nat} {ρ : BVarIdx → V} :
    ∀ {f : Expr} {F : V} {as : List Expr} {vs : List V}, Denotes M.cval env φ ρ f F →
      DenL M φ ρ as vs → Denotes M.cval env φ ρ (apps f as) (appN F vs)
  | _, _, [], [], hf, .nil => hf
  | f, F, a :: _, v :: _, hf, .cons ha hr => den_apps (f := .app f a) (F := app F v) (.app hf ha) hr

/-! ## the step -/

section
variable {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
  (acc : Cached.checkDecls .verified pins ds = .ok env) (hnat : natLitSupported env = true)
  {fN e1 e2 e3 : Name} (R : Recs ds fN e1 e2 e3) (M : Model V env) (hP : CvalParams M)
include acc hnat R hP

/-- `outParam.{2} Type` denotes `Type`, at every assignment. -/
theorem outParam_univ (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    app (M.cval outParamN (Level.substFn φ [lu] [L2])) (univ 1) = univ 1 := by
  have hBF : ∀ T ∈ [Expr.sort pu], BF T := by simp [BF]
  have dop := dden acc R.outParam hBF trivial M φ ρ [L2] rfl
  have hψo : Level.eval (Level.substFn φ [lu] [L2]) pu = 2 := by simp [pu, Level.substFn, Level.eval, L2, L1]
  have hm : (univ 1 : V) ∈ˢ univ (Level.eval (Level.substFn φ [lu] [L2]) pu) := by rw [hψo]; exact univ_mem_univ 1
  obtain ⟨Bv, hB, hmB⟩ := dspine acc R.outParam hBF trivial M (Level.substFn φ [lu] [L2]) ρ _ [univ 1] (.cons .sort hm .nil)
  cases hB
  rw [hψo] at hmB
  refine ttransfer acc R.e3 (by simp) trivial ⟨trivial, trivial⟩ trivial M φ ρ ρ [] .nil .sort (.app dop .sort)
    .sort ?_ ?_ ?_
  · simpa [L3, L2, L1, Level.eval] using univ_mem_univ (V := V) 2
  · simpa [L2, L1, Level.eval, appN] using hmB
  · simpa [L2, L1, Level.eval] using univ_mem_univ (V := V) 1

/-- `x + 1` (the emitted spelling) is a `Nat`, with its denotation. -/
theorem plus_mem (φ : LevelParam → Nat) (ρ : BVarIdx → V) {e : Expr} {x : V}
    (he : Denotes M.cval env φ ρ e x) (hx : x ∈ˢ M.cval natName φ) :
    ∃ P, Denotes M.cval env φ ρ (plus e) P ∧ P ∈ˢ M.cval natName φ := by
  have N1 := nat_univ M hnat φ
  have dN : ∀ ρ', Denotes M.cval env φ ρ' natC (M.cval natName φ) := nat_den M hnat φ
  -- instAddNat : Add.{0} Nat  (gives Add's find?)
  obtain ⟨BA, hBA, hA⟩ := dspine acc R.instAddNat (by simp) (by simp [BF, instAddNatB, natC]) M φ ρ ρ [] .nil
  change Denotes _ _ _ _ (.app (.const addC [.zero]) natC) _ at hBA
  obtain ⟨FA, XA, hFA, hXA, rfl⟩ := app_inv hBA
  cases hFA with
  | @const _ _ _ ciA hfA hlA =>
  rw [Denotes_functional hXA (dN ρ)] at hA
  -- instHAdd.{0} Nat instAddNat : HAdd Nat Nat Nat  (gives HAdd's find?)
  have u2 : M.cval natName φ ∈ˢ univ (Level.eval (Level.substFn φ [lu] [.zero]) (.succ pu)) := by
    simpa [pu, Level.substFn, Level.eval] using N1
  have hlA' : [pu].length = ciA.toConstantVal.levelParams.length := by simpa using hlA
  have dAdd : Denotes M.cval env (Level.substFn φ [lu] [.zero]) (push (M.cval natName φ) ρ)
      (.app (.const addC [pu]) (.bvar 0))
      (app (M.cval addC (Level.substFn (Level.substFn φ [lu] [.zero]) ciA.toConstantVal.levelParams [pu]))
        (M.cval natName φ)) := .app (.const hfA hlA') .bvar
  have eA : M.cval addC (Level.substFn (Level.substFn φ [lu] [.zero]) ciA.toConstantVal.levelParams [pu]) =
      M.cval addC (Level.substFn φ ciA.toConstantVal.levelParams [.zero]) :=
    hP addC ciA hfA _ _ (substFn_agree _ _ _ [pu] [.zero] (by simp [pu, Level.substFn, Level.eval]) hlA')
  have hA' := hA
  rw [← eA] at hA'
  obtain ⟨BH, hBH, hI⟩ := dspine acc R.instHAdd (by simp [instHAddTs, BF, pu, addC])
    (by simp [instHAddB, apps, BF]) M (Level.substFn φ [lu] [.zero]) ρ _ _ (.cons .sort u2 (.cons dAdd hA' .nil))
  change Denotes _ _ _ _ (.app (.app (.app (.const hAddC [pu, pu, pu]) (.bvar 1)) (.bvar 1)) (.bvar 1)) _ at hBH
  obtain ⟨F2, X3, hF2, hX3, rfl⟩ := app_inv hBH
  obtain ⟨F1, X2, hF1, hX2, rfl⟩ := app_inv hF2
  obtain ⟨H, X1, hH, hX1, rfl⟩ := app_inv hF1
  cases hX1; cases hX2; cases hX3
  cases hH with
  | @const _ _ _ ciH hfH hlH =>
  have hlH' : [pu, pv, pw].length = ciH.toConstantVal.levelParams.length := by simpa using hlH
  have eH : M.cval hAddC (Level.substFn (Level.substFn φ [lu, lv, lw] [.zero, .zero, .zero])
        ciH.toConstantVal.levelParams [pu, pv, pw]) =
      M.cval hAddC (Level.substFn (Level.substFn φ [lu] [.zero]) ciH.toConstantVal.levelParams [pu, pu, pu]) :=
    hP hAddC ciH hfH _ _ (substFn_agree _ _ _ _ _
      (by simp [pu, pv, pw, lu, lv, lw, nm, Level.substFn, Level.eval]) hlH')
  -- One : Nat
  have nv1 := natV_mem M hnat φ ρ 1
  obtain ⟨BO, hBO, hJ⟩ := dspine acc R.instOfNatNat (by simp [BF, natC])
    (by simp [instOfNatNatB, apps, BF, natC]) M φ ρ _ _ (.cons (dN ρ) nv1 .nil)
  change Denotes _ _ _ _ (.app (.app (.const ofNatC [.zero]) natC) (.bvar 0)) _ at hBO
  obtain ⟨FO, XO2, hFO, hXO2, rfl⟩ := app_inv hBO
  obtain ⟨O, XO1, hO, hXO1, rfl⟩ := app_inv hFO
  cases hXO2
  rw [Denotes_functional hXO1 (dN _)] at hJ
  cases hO with
  | @const _ _ _ ciO hfO hlO =>
  have hlO' : [pu].length = ciO.toConstantVal.levelParams.length := by simpa using hlO
  have eNat : M.cval natName (Level.substFn φ [lu] [.zero]) = M.cval natName φ :=
    const_agree0 hP (nat_den M hnat _ ρ) (nat_den M hnat φ ρ)
  have nv1' : natV M φ 1 ∈ˢ M.cval natName (Level.substFn φ [lu] [.zero]) := by rw [eNat]; exact nv1
  have eO : M.cval ofNatC (Level.substFn (Level.substFn φ [lu] [.zero]) ciO.toConstantVal.levelParams [pu]) =
      M.cval ofNatC (Level.substFn φ ciO.toConstantVal.levelParams [.zero]) :=
    hP ofNatC ciO hfO _ _ (substFn_agree _ _ _ [pu] [.zero] (by simp [pu, Level.substFn, Level.eval]) hlO')
  have hJ' := hJ
  rw [← eO] at hJ'
  have dOf : Denotes M.cval env (Level.substFn φ [lu] [.zero])
      (push (natV M φ 1) (push (M.cval natName φ) ρ)) (apps (.const ofNatC [pu]) [.bvar 1, .bvar 0])
      (app (app (M.cval ofNatC (Level.substFn (Level.substFn φ [lu] [.zero]) ciO.toConstantVal.levelParams [pu]))
        (M.cval natName φ)) (natV M φ 1)) := .app (.app (.const hfO hlO') .bvar) .bvar
  obtain ⟨BOne, hBOne, hOne⟩ := dspine acc R.ofNat (by simp [ofNatTs, BF, apps, natC]) trivial M
    (Level.substFn φ [lu] [.zero]) ρ _ _ (.cons .sort u2 (.cons (nat_den M hnat _ _) nv1' (.cons dOf hJ' .nil)))
  cases hBOne
  -- x + 1 : Nat, through HAdd.hAdd's stored type at ψ1
  have u1 : ∀ l, l = lu ∨ l = lv → M.cval natName φ ∈ˢ
      univ (Level.eval (Level.substFn φ [lu, lv, lw] [.zero, .zero, .zero]) (.succ (.param l))) := by
    rintro l (rfl | rfl) <;> simpa [lu, lv, lw, nm, Level.substFn, Level.eval] using N1
  have eop : Level.substFn (Level.substFn φ [lu, lv, lw] [.zero, .zero, .zero]) [lu] [.succ (.succ pw)] =
      Level.substFn (Level.substFn φ [lu, lv, lw] [.zero, .zero, .zero]) [lu] [L2] := by
    funext n; simp [Level.substFn, Level.eval, pw, lu, lw, lv, nm, L2, L1]
  have u3 : M.cval natName φ ∈ˢ app (M.cval outParamN
      (Level.substFn (Level.substFn φ [lu, lv, lw] [.zero, .zero, .zero]) [lu] [.succ (.succ pw)]))
      (univ (Level.eval (Level.substFn φ [lu, lv, lw] [.zero, .zero, .zero]) (.succ pw))) := by
    have e1 : Level.eval (Level.substFn φ [lu, lv, lw] [.zero, .zero, .zero]) (.succ pw) = 1 := by
      simp [pw, lw, lu, lv, nm, Level.substFn, Level.eval]
    rw [eop, e1, outParam_univ acc hnat R M hP _ ρ]
    exact N1
  have hT1 : ∀ T ∈ hAddTs, BF T := by simp [hAddTs, BF, apps]
  have hI' : appN (M.cval instHAddN (Level.substFn φ [lu] [.zero])) [M.cval natName φ, M.cval instAddNatN φ] ∈ˢ
      app (app (app (M.cval hAddC (Level.substFn (Level.substFn φ [lu, lv, lw] [.zero, .zero, .zero])
        ciH.toConstantVal.levelParams [pu, pv, pw])) (M.cval natName φ)) (M.cval natName φ)) (M.cval natName φ) := by
    rw [eH]; exact hI
  obtain ⟨BP, hBP, hPm⟩ := dspine acc R.hAdd hT1 trivial M (Level.substFn φ [lu, lv, lw] [.zero, .zero, .zero]) ρ _
    [M.cval natName φ, M.cval natName φ, M.cval natName φ,
      appN (M.cval instHAddN (Level.substFn φ [lu] [.zero])) [M.cval natName φ, M.cval instAddNatN φ], x,
      appN (M.cval ofNatN (Level.substFn φ [lu] [.zero]))
        [M.cval natName φ, natV M φ 1, appN (M.cval instOfNatNatN φ) [natV M φ 1]]]
    (.cons .sort (u1 lu (Or.inl rfl)) (.cons .sort (u1 lv (Or.inr rfl))
      (.cons (.app (dden acc R.outParam (by simp [BF]) trivial M _ _ [.succ (.succ pw)] rfl) .sort) u3
      (.cons (.app (.app (.app (.const hfH hlH') .bvar) .bvar) .bvar) hI'
      (.cons .bvar hx (.cons .bvar hOne .nil))))))
  cases hBP
  have dI := den_apps (dden acc R.instHAdd (by simp [instHAddTs, BF, pu, addC]) (by simp [instHAddB, apps, BF])
    M φ ρ [.zero] rfl) (.cons (dN ρ) (.cons (dden acc R.instAddNat (by simp) (by simp [BF, instAddNatB, natC])
      M φ ρ [] rfl) .nil))
  have dOne := den_apps (dden acc R.ofNat (by simp [ofNatTs, BF, apps, natC]) trivial M φ ρ [.zero] rfl)
    (.cons (dN ρ) (.cons (lit_den M hnat φ ρ 1) (.cons (.app (dden acc R.instOfNatNat (by simp [BF, natC])
      (by simp [instOfNatNatB, apps, BF, natC]) M φ ρ [] rfl) (lit_den M hnat φ ρ 1)) .nil)))
  exact ⟨_, den_apps (dden acc R.hAdd hT1 trivial M φ ρ [.zero, .zero, .zero] rfl)
    (.cons (dN ρ) (.cons (dN ρ) (.cons (dN ρ) (.cons dI (.cons he (.cons dOne .nil)))))), hPm⟩

/-- **Step 3a, real con-leche.**  `⟦f v⟧ = ⟦v+1⟧`, through `f`'s emitted body `x + 1`. -/
theorem addOne (φ : LevelParam → Nat) (ρ : BVarIdx → V) (v : Nat) :
    Denotes M.cval env φ ρ (.app (.const fN []) (.lit (.natVal v))) (natV M φ (v + 1)) := by
  have hx := natV_mem M hnat φ ρ v
  have dN : ∀ ρ', Denotes M.cval env φ ρ' natC (M.cval natName φ) := nat_den M hnat φ
  have hfden : ∀ ρ', Denotes M.cval env φ ρ' (.const fN []) (M.cval fN φ) := fun ρ' =>
    dden acc R.f (by simp [BF, natC]) (by simp [BF, natC]) M φ ρ' [] rfl
  obtain ⟨Bf, hBf, hfx⟩ := dspine acc R.f (by simp [BF, natC]) (by simp [BF, natC]) M φ ρ _ [natV M φ v]
    (.cons (dN ρ) hx .nil)
  rw [Denotes_functional hBf (dN _)] at hfx
  obtain ⟨P, hPd, hPm⟩ := plus_mem acc hnat R M hP φ (push (natV M φ v) ρ) (e := .bvar 0) .bvar hx
  have hu : M.cval natName φ ∈ˢ univ (Level.eval φ L1) := by simpa [L1, Level.eval] using nat_univ M hnat φ
  have k1 : app (M.cval fN φ) (natV M φ v) = P :=
    ttransfer acc R.e1 (by simp [BF, natC]) trivial ⟨trivial, trivial⟩ (by simp [plus, apps, instE, oneE, BF, natC])
      M φ ρ _ [natV M φ v] (.cons (dN ρ) hx .nil) (dN _) (.app (hfden _) .bvar) hPd hu hfx hPm
  have k2 : P = natV M φ (v + 1) :=
    ttransfer acc R.e2 (by simp [BF, natC]) trivial (by simp [plus, apps, instE, oneE, BF, natC])
      ⟨trivial, trivial⟩ M φ ρ _ [natV M φ v] (.cons (dN ρ) hx .nil) (dN _) hPd
      (.app (succ_den M hnat φ _) .bvar) hu hPm (natV_mem M hnat φ ρ (v + 1))
  have := Denotes.app (hfden ρ) (lit_den M hnat φ ρ v)
  rwa [k1, k2] at this

end

/-- **Step 3a with the model of the main theorem.** -/
theorem addOne_model (V : Type w) [SetTheory V] {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
    (acc : Cached.checkDecls .verified pins ds = .ok env) (hnat : natLitSupported env = true)
    {fN e1 e2 e3 : Name} (R : Recs ds fN e1 e2 e3) :
    ∃ M : Model V env, CvalParams M ∧ ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (v : Nat) (X : V),
      Denotes M.cval env φ ρ (.lit (.natVal (v + 1))) X →
      Denotes M.cval env φ ρ (.app (.const fN []) (.lit (.natVal v))) X := by
  obtain ⟨M, hP⟩ := model_exists' V pins ds env acc
  refine ⟨M, hP, fun φ ρ v X hX => ?_⟩
  rw [Denotes_functional hX (lit_den M hnat φ ρ (v + 1))]
  exact addOne acc hnat R M hP φ ρ v

end Bridge.Real.AddOne
