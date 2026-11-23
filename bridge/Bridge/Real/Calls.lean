/- Bridge.Real.Calls: growth step 3b (calls), through `Conv` (equational evaluation), real con-leche.

Program: `f x = x + 1`, `g x = f (f x)`.  Stored: `f_body : f x = x + 1`, `add_one : x + 1 = succ x`,
`g_eq : g x = f (f x)` (+ the heads of `x + 1`).  Export `Testing/denotes_real/tiny.ndjson`: accepted (29 decls).
`calls`: `⟦g v⟧ = ⟦v + 2⟧` in every `CvalParams` model of an accepting env, hence in `model_exists'`'s. -/
import Bridge.Real.Conv
import Bridge.Real.EngineAdd

namespace Bridge.Real.Calls
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real Bridge.ModelExists2 Bridge.Real.Engine
open Bridge.Real.AddOne (nm L1 plus e1B e2B Recs)
open Bridge.Real.EngineAdd (fN tabL opEq)
open Bridge.Real.Tiny (natC succC natV)

universe w
variable {V : Type w} [SetTheory V]

def gN : Name := nm "g"
def tab : Tab := fun n => ((gN, (⟨[], [natC], natC⟩ : Head)) :: tabL).lookup n

def fBody : Thm := ⟨nm "f_body", [natC], L1, natC, .app (.const fN []) (.bvar 0), plus (.bvar 0)⟩
def addOne : Thm := ⟨nm "add_one", [natC], L1, natC, plus (.bvar 0), .app succC (.bvar 0)⟩
def gEq : Thm := ⟨nm "g_eq", [natC], L1, natC, .app (.const gN []) (.bvar 0),
  .app (.const fN []) (.app (.const fN []) (.bvar 0))⟩
def thms : List Thm := [fBody, addOne, gEq]

def x0 : Expr := .bvar 0
def sx : Expr := .app succC x0

section
variable {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
  (acc : Cached.checkDecls .verified pins ds = .ok env) (hnat : natLitSupported env = true)
  (R : Recs ds fN (nm "f_body") (nm "add_one") (nm "outParam_eq"))
  (hg : ∃ v h, Declaration.defnDecl ⟨gN, [], piV [natC] natC⟩ v h ∈ ds)
  (hgEq : ∃ v, Declaration.thmDecl ⟨nm "g_eq", [], gEq.stmt⟩ v ∈ ds)
  (M : Model V env) (hP : CvalParams M)
include acc hnat R hg hgEq hP

theorem tabOk : TabOk M tab := by
  intro n h hn
  simp only [tab, List.lookup] at hn
  split at hn
  · rename_i hb; cases hn; rw [beq_iff_eq] at hb; rw [hb]; exact headSem_defn acc M hg (by decide)
  · exact EngineAdd.tabOk acc hnat R M hP n h hn

theorem thmsOk : ThmsOk ds tab [opEq] thms := by
  intro t ht
  simp only [thms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact ⟨R.e1, 40, by decide +kernel⟩
  · exact ⟨R.e2, 40, by decide +kernel⟩
  · exact ⟨hgEq, 40, by decide +kernel⟩

/-- the run of `g` on a symbolic `x`, as an equational derivation -/
theorem run : Conv tab [opEq] thms [natC] (.app (.const gN []) x0) (.app succC sx) natC := by
  have ty : ∀ e T, infer tab [opEq] [natC] 40 e = some T → HasTy tab [opEq] [natC] e T := infer_sound 40
  have fx : HasTy tab [opEq] [natC] x0 natC := ty _ _ (by decide +kernel)
  have fsx : HasTy tab [opEq] [natC] sx natC := ty _ _ (by decide +kernel)
  have s1 : Conv tab [opEq] thms [natC] (.app (.const fN []) x0) (.app succC x0) natC :=
    .trans (.inst (t := fBody) (as := [x0]) (by simp [thms]) (.cons fx .nil))
      (.inst (t := addOne) (as := [x0]) (by simp [thms]) (.cons fx .nil))
  have s2 : Conv tab [opEq] thms [natC] (.app (.const fN []) sx) (.app succC sx) natC :=
    .trans (.inst (t := fBody) (as := [sx]) (by simp [thms]) (.cons fsx .nil))
      (.inst (t := addOne) (as := [sx]) (by simp [thms]) (.cons fsx .nil))
  have s3 : Conv tab [opEq] thms [natC] (.app (.const fN []) (.app (.const fN []) x0)) (.app (.const fN []) sx) natC :=
    .cong (h := .const fN []) (as := [.app (.const fN []) x0]) (bs := [sx]) (ty _ _ (by decide +kernel))
      (.cons s1 .nil)
  exact .trans (.inst (t := gEq) (as := [x0]) (by simp [thms]) (.cons fx .nil)) (.trans s3 s2)

/-- **Step 3b (calls), real con-leche.** -/
theorem calls (φ : LevelParam → Nat) (ρ : BVarIdx → V) (v : Nat) :
    Denotes M.cval env φ ρ (.app (.const gN []) (.lit (.natVal v))) (natV M φ (v + 2)) := by
  have hx := Tiny.natV_mem M hnat φ ρ v
  have hm : MemL M φ [natC] [natV M φ v] := .cons (Tiny.nat_den M hnat φ) hx .nil
  obtain ⟨X, -, d1, d2, -, -⟩ := conv_sound acc hP hnat (tabOk acc hnat R hg hgEq M hP) (EngineAdd.eqsOk acc hnat R M hP)
    (thmsOk acc hnat R hg hgEq M hP) (hm.gamma (ρ := ρ)) (run acc hnat R hg hgEq M hP)
  have dg := (tabOk acc hnat R hg hgEq M hP gN ⟨[], [natC], natC⟩ (by decide +kernel)).den φ ρ [] rfl
  -- X is ⟦g⟧ applied to the input, and also succ (succ input)
  obtain ⟨G, Y, dG, dY, rfl⟩ := app_inv d1
  cases dY
  obtain rfl := Denotes_functional dG ((tabOk acc hnat R hg hgEq M hP gN ⟨[], [natC], natC⟩
    (by decide +kernel)).den φ _ [] rfl)
  obtain ⟨S1, Z, dS1, dZ, hZ⟩ := app_inv d2
  obtain ⟨S2, W, dS2, dW, rfl⟩ := app_inv dZ
  cases dW
  obtain rfl := Denotes_functional dS1 (Tiny.succ_den M hnat φ _)
  obtain rfl := Denotes_functional dS2 (Tiny.succ_den M hnat φ _)
  have := Denotes.app dg (Tiny.lit_den M hnat φ ρ v)
  change Denotes _ _ _ _ _ (app _ (natV M φ v)) at this
  rw [show app (M.cval gN (Level.substFn φ [] [])) (natV M φ v) = natV M φ (v + 2) from hZ] at this
  exact this
end

end Bridge.Real.Calls
