/- Bridge.Real.EngineAdd: step 3a again, now through the generic engine (validation of Engine/Engine2).
Same records as `Real.AddOne.Recs` (checked present in the accepted export by Testing/denotes_real/CheckTiny.lean).
All typing is by the Bool checker (`decide`); the only hand-work is listing heads and equations. -/
import Bridge.Real.Engine2
import Bridge.Real.AddOne

namespace Bridge.Real.EngineAdd
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real Bridge.ModelExists2 Bridge.Real.Engine
open Bridge.Real.AddOne (nm hAddN instHAddN instAddNatN ofNatN instOfNatNatN outParamN lu lv lw li pu L1 L2 L3
  hAddTs instHAddTs instHAddB instAddNatB ofNatTs instOfNatNatB plus e1B e2B e3B Recs)
open Bridge.Real.Tiny (natC succC natV)

universe w
variable {V : Type w} [SetTheory V]

def fN : Name := nm "f"

def tabL : List (Name × Head) :=
  [(natName, natHead), (natZeroName, zeroHead), (natSuccName, succHead), (fN, ⟨[], [natC], natC⟩),
   (hAddN, ⟨[lu, lv, lw], hAddTs, .bvar 3⟩), (instHAddN, ⟨[li], instHAddTs, instHAddB⟩),
   (instAddNatN, ⟨[], [], instAddNatB⟩), (ofNatN, ⟨[lu], ofNatTs, .bvar 2⟩),
   (instOfNatNatN, ⟨[], [natC], instOfNatNatB⟩), (outParamN, ⟨[lu], [.sort pu], .sort pu⟩)]

def tab : Tab := fun n => tabL.lookup n

def opEq : Expr × Expr := (.sort L1, .app (.const outParamN [L2]) (.sort L1))

theorem tabOk_of {env : Env} {M : Model V env} {L : List (Name × Head)} (h : ∀ p ∈ L, HeadSem M p.1 p.2) :
    TabOk M (fun n => L.lookup n) := by
  intro n hd hn
  induction L with
  | nil => simp at hn
  | cons p ps ih =>
    simp only [List.lookup] at hn
    split at hn
    · rename_i hb; cases hn
      have := h p List.mem_cons_self
      rw [beq_iff_eq] at hb; rw [hb]; exact this
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) hn

section
variable {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
  (acc : Cached.checkDecls .verified pins ds = .ok env) (hnat : natLitSupported env = true)
  {e1 e2 e3 : Name} (R : Recs ds fN e1 e2 e3) (M : Model V env) (hP : CvalParams M)
include acc hnat R hP

theorem tabOk : TabOk M tab := by
  obtain ⟨h1, h2, h3⟩ := headSem_nat M hnat
  apply tabOk_of
  simp only [tabL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨h1, h2, h3, headSem_defn acc M R.f (by decide), headSem_defn acc M R.hAdd (by decide),
    headSem_defn acc M R.instHAdd (by decide), headSem_defn acc M R.instAddNat (by decide),
    headSem_defn acc M R.ofNat (by decide), headSem_defn acc M R.instOfNatNat (by decide),
    headSem_defn acc M R.outParam (by decide)⟩

theorem eqsOk : EqsOk M [opEq] := by
  intro p hp
  simp only [List.mem_singleton] at hp; subst hp
  refine ⟨rfl, rfl, fun φ ρ X hX => ?_⟩
  have ht := tabOk acc hnat R M hP
  have h0 : EqsOk M ([] : List (Expr × Expr)) := fun _ h => by cases h
  have tyA : HasTy tab [] [] (.app (.const outParamN [L2]) (.sort L1)) (.sort L2) :=
    infer_sound 40 _ _ (by decide +kernel)
  obtain ⟨Y, -, dY, -, -⟩ := sound hP hnat ht h0 (Γ := []) (φ := φ) (ρ := ρ) (fun _ _ h => by simp at h) tyA
  have := etransfer acc hP hnat ht h0 (Ts := []) R.e3 (by decide) (by decide)
    (infer_sound 40 _ _ (by decide +kernel)) tyA (infer_sound 40 _ _ (by decide +kernel))
    φ ρ .nil dY hX
  rw [← this]; exact dY

/-- **Step 3a through the engine.** -/
theorem addOne' (φ : LevelParam → Nat) (ρ : BVarIdx → V) (v : Nat) :
    Denotes M.cval env φ ρ (.app (.const fN []) (.lit (.natVal v))) (natV M φ (v + 1)) := by
  have ht := tabOk acc hnat R M hP
  have he := eqsOk acc hnat R M hP
  have hx := Tiny.natV_mem M hnat φ ρ v
  have hm : MemL M φ [natC] [natV M φ v] := .cons (Tiny.nat_den M hnat φ) hx .nil
  -- the two sides of e1, e2 denote (engine), then transfer
  have hΓ := hm.gamma (ρ := ρ)
  have tyP : HasTy tab [opEq] [natC] (plus (.bvar 0)) natC := infer_sound 40 _ _ (by decide +kernel)
  obtain ⟨P, _, dP, -, -⟩ := sound hP hnat ht he hΓ tyP
  have dF : Denotes M.cval env φ (pushAll [natV M φ v].reverse ρ) (.app (.const fN []) (.bvar 0))
      (app (M.cval fN φ) (natV M φ v)) :=
    .app ((ht fN ⟨[], [natC], natC⟩ (by decide +kernel)).den φ _ [] rfl) .bvar
  have k1 := etransfer acc hP hnat ht he (Ts := [natC]) R.e1 (by decide) (by decide)
    (infer_sound 40 _ _ (by decide +kernel)) (infer_sound 40 _ _ (by decide +kernel)) tyP φ ρ hm dF dP
  have k2 := etransfer acc hP hnat ht he (Ts := [natC]) R.e2 (by decide) (by decide)
    (infer_sound 40 _ _ (by decide +kernel)) tyP (infer_sound 40 _ _ (by decide +kernel)) φ ρ hm dP
    (.app (Tiny.succ_den M hnat φ _) .bvar)
  have := Denotes.app ((ht fN ⟨[], [natC], natC⟩ (by decide +kernel)).den φ ρ [] rfl) (Tiny.lit_den M hnat φ ρ v)
  change Denotes _ _ _ _ _ (app (M.cval fN φ) (natV M φ v)) at this
  rw [k1, k2] at this; exact this
end

end Bridge.Real.EngineAdd
