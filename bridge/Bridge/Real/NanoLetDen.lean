/- Bridge.Real.NanoLetDen: growth step `let`, con-leche side.  con-leche stores a `let` zeta-inlined (`AnnotOf`), so the
stored `m_eq` is `m x = put [] (rd x 0 * 3 + rd x 0)`: no binder.  Same prelude as `u64 ops`. -/
import Bridge.Real.NanoADen
import Bridge.Real.NanoLet

namespace Bridge.Real.NanoLetDen
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real Bridge.ModelExists2 Bridge.Real.Engine
open Bridge.Real.NanoDen
open Bridge.Real.NanoRDen (litUC rdC u8ofC)
open Bridge.Real.NanoLDen
open Bridge.Real.NanoADen (conv_out cong_cons1 cong_u8of)
open Bridge.Real.Tiny (natC succC natV)

universe w
variable {V : Type w} [SetTheory V]

def bodyTC (x : Expr) : Expr := putC nilC (add64C (mul64C (rdC x) (litUC 3)) (rdC x))
def mEqT : Thm := ⟨nm "m_eq", [LU8c], L1, LU8c, .app (.const (nm "m") []) (.bvar 0), bodyTC (.bvar 0)⟩
def thmsT : List Thm := mEqT :: thmsP

def recsOkT (ds : Array Declaration) : Bool :=
  ((defHeads ++ defHeadsL).all fun p => ds.any fun | .defnDecl cv _ _ => cv == ⟨p.1, p.2.ps, piV p.2.Ts p.2.B⟩ | _ => false) &&
  ((NanoRDen.opEqT :: thmsT).all fun t => ds.any fun | .thmDecl cv _ => cv == ⟨t.n, [], t.stmt⟩ | _ => false)

theorem thmsT_ok_all : thmsT.all (fun t => t.ok NanoLDen.tab NanoLDen.eqs 40) = true := by decide +kernel

/-- **the run of `m` on any input, in the model** -/
theorem run (inp : List UInt8) :
    Conv NanoLDen.tab NanoLDen.eqs thmsT [] (.app (.const (nm "m") []) (encL inp)) (encL [NanoLet.outT inp]) LU8c := by
  have hx := hty_encL inp
  have hR := hty_rd hx
  have c0 : Conv NanoLDen.tab NanoLDen.eqs thmsT [] (.app (.const (nm "m") []) (encL inp)) (bodyTC (encL inp)) LU8c :=
    .inst (t := mEqT) (as := [encL inp]) (by simp [thmsT]) (.cons hx .nil)
  have cR := conv_rd inp
  have c3 : C (litUC 3) (u64ofC (litC 3)) u64C := .inst (t := lit64) (as := [litC 3]) (by simp [thmsP]) (.cons .lit .nil)
  have hM := hty_mul64 hR (hty_litU 3)
  have cM : C (mul64C (rdC (encL inp)) (litUC 3)) (u64ofC (litC ((inp.getD 0 0).toNat * 3))) u64C :=
    .trans (cong_mul64 hR (hty_litU 3) cR c3)
      (.trans (.inst (t := brMul64) (as := [litC _, litC 3]) (by simp [thmsP]) (.cons .lit (.cons .lit .nil)))
        (cong_u64of (hty_natMul .lit .lit) (conv_mul _ _)))
  have cA : C (add64C (mul64C (rdC (encL inp)) (litUC 3)) (rdC (encL inp)))
      (u64ofC (litC ((inp.getD 0 0).toNat * 3 + (inp.getD 0 0).toNat))) u64C :=
    .trans (cong_add64 hM hR cM cR)
      (.trans (.inst (t := brAdd64) (as := [litC _, litC _]) (by simp [thmsP]) (.cons .lit (.cons .lit .nil)))
        (cong_u64of (hty_natAdd .lit .lit) (conv_add _ _)))
  have cP : C (bodyTC (encL inp)) (putC nilC (u64ofC (litC ((inp.getD 0 0).toNat * 3 + (inp.getD 0 0).toNat)))) LU8c :=
    cong_put hty_nil (hty_add64 hM hR) cA
  have e : encL [NanoLet.outT inp] =
      consC (u8ofC (litC (((inp.getD 0 0).toNat * 3 + (inp.getD 0 0).toNat) % 256))) nilC := by
    simp only [encL, byteC, u8ofC, litC, NanoLet.outT_toNat]
  rw [e]
  exact .trans c0 (Conv.mono (fun t ht => List.mem_cons_of_mem _ ht) (.trans cP (conv_out _)))

/-! ## the semantic side (structure as `NanoLDen`) -/

section
variable {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
  (acc : Cached.checkDecls .verified pins ds = .ok env) (hnat : natLitSupported env = true)
  (hind : IndStored env (IndHeads.blockHeads blocksL)) (hrec : recsOkT ds = true) (M : Model V env)
include acc hnat hind hrec

theorem tabOk : TabOk M NanoLDen.tab := by
  simp only [recsOkT, Bool.and_eq_true, List.all_eq_true] at hrec
  have hs : ∀ p ∈ NanoLDen.tabL, HeadSem M p.1 p.2 := by
    obtain ⟨h1, h2, h3⟩ := headSem_nat M hnat
    intro p hp
    simp only [NanoLDen.tabL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (((rfl | rfl | rfl) | hd) | hr) | hi
    · exact h1
    · exact h2
    · exact h3
    · exact headSem_defn acc M (any_def (hrec.1 p (List.mem_append_left _ hd))) (by
        simp only [defHeads, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    · exact headSem_defn acc M (any_def (hrec.1 p (List.mem_append_right _ hr)))
        (List.all_eq_true.mp (show defHeadsL.all (fun p => headSc p.2) = true by decide +kernel) p hr)
    · exact headSem_ind M (hind p hi) (by
        have : (IndHeads.blockHeads blocksL).all (fun p => headSc p.2) = true := by decide +kernel
        exact List.all_eq_true.mp this p hi)
  intro n hd hn
  have : ∀ L : List (Name × Head), (∀ p ∈ L, HeadSem M p.1 p.2) → L.lookup n = some hd → HeadSem M n hd := by
    intro L hL hl
    induction L with
    | nil => simp at hl
    | cons p ps ih =>
      simp only [List.lookup] at hl
      split at hl
      · rename_i hb; cases hl; rw [beq_iff_eq] at hb; rw [hb]; exact hL p List.mem_cons_self
      · exact ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) hl
  exact this _ hs hn

theorem thmsOk : ThmsOk ds NanoLDen.tab NanoLDen.eqs thmsT := by
  simp only [recsOkT, Bool.and_eq_true, List.all_eq_true] at hrec
  intro t ht
  exact ⟨any_thm (hrec.2 t (List.mem_cons_of_mem _ ht)), 40, List.all_eq_true.mp thmsT_ok_all t ht⟩

theorem eqsOk (hP : CvalParams M) : EqsOk M NanoLDen.eqs := by
  intro p hp
  simp only [NanoLDen.eqs, List.mem_singleton] at hp; subst hp
  refine ⟨rfl, rfl, fun φ ρ X hX => ?_⟩
  have ht := tabOk acc hnat hind hrec M
  have h0 : EqsOk M ([] : List (Expr × Expr)) := fun _ h => by cases h
  have tyA : HasTy NanoLDen.tab [] [] (.app (.const AddOne.outParamN [AddOne.L2]) (.sort AddOne.L1)) (.sort AddOne.L2) :=
    infer_sound 40 _ _ (by decide +kernel)
  obtain ⟨Y, -, dY, -, -⟩ := sound hP hnat ht h0 (Γ := []) (φ := φ) (ρ := ρ) (fun _ _ h => by simp at h) tyA
  simp only [recsOkT, Bool.and_eq_true, List.all_eq_true] at hrec
  have hrec3 := any_thm (hrec.2 NanoRDen.opEqT List.mem_cons_self)
  have := etransfer acc hP hnat ht h0 (Ts := []) hrec3 (by decide) (by decide)
    (infer_sound 40 _ _ (by decide +kernel)) tyA (infer_sound 40 _ _ (by decide +kernel))
    φ ρ .nil dY hX
  rw [← this]; exact dY

/-- **the emitted `m` on any input denotes the encoding of `[outA inp]`** -/
theorem den_mT (hP : CvalParams M) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (inp : List UInt8) :
    ∃ x, Denotes M.cval env φ ρ (encL inp) x ∧
      ∀ Y, Denotes M.cval env φ ρ (encL [NanoLet.outT inp]) Y →
        Denotes M.cval env φ (push x ρ) (tr NanoTiny.mainX) Y := by
  have ht := tabOk acc hnat hind hrec M
  have he := eqsOk acc hnat hind hrec M hP
  have h0 : GammaOk M φ ρ ([] : List Expr) := fun _ _ h => by simp at h
  obtain ⟨X, -, d1, d2, -, -⟩ := conv_sound acc hP hnat ht he (thmsOk acc hnat hind hrec) h0 (run inp)
  obtain ⟨F, x, dF, dx, rfl⟩ := app_inv d1
  refine ⟨x, dx, fun Y hY => ?_⟩
  obtain rfl := Denotes_functional hY d2
  rw [NanoDen.tr_mainX]
  cases dF with
  | const hf hl => exact .app (.const hf hl) .bvar
end

end Bridge.Real.NanoLetDen
