/- Bridge.Real.NanoSDen: growth step `u64 ops` (`-` on UInt64), con-leche side.
Same prelude as the `ite` step (`NanoLDen.thmsP`, heads `NanoLDen.tab`); only `m_eq` differs.  The arithmetic is
done in the model: `br_mul64`/`br_add64` to `UInt64.ofNat` of Nat `*`/`+`, those by `conv_mul`/`conv_add`
(induction on literals), the byte by `put_nil`, `u8_mod` and `conv_modG`. -/
import Bridge.Real.NanoLDen
import Bridge.Real.NanoS

namespace Bridge.Real.NanoSDen
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real Bridge.ModelExists2 Bridge.Real.Engine
open Bridge.Real.NanoDen
open Bridge.Real.NanoRDen (litUC rdC u8ofC)
open Bridge.Real.NanoLDen
open Bridge.Real.Tiny (natC succC natV)

universe w
variable {V : Type w} [SetTheory V]

def bodySC (x : Expr) : Expr := putC nilC (sub64C (rdC x) (litUC 3))
def mEqS : Thm := ⟨nm "m_eq", [LU8c], L1, LU8c, .app (.const (nm "m") []) (.bvar 0), bodySC (.bvar 0)⟩
def thmsS : List Thm := mEqS :: thmsP

def recsOkS (ds : Array Declaration) : Bool :=
  ((defHeads ++ defHeadsL).all fun p => ds.any fun | .defnDecl cv _ _ => cv == ⟨p.1, p.2.ps, piV p.2.Ts p.2.B⟩ | _ => false) &&
  ((NanoRDen.opEqT :: thmsS).all fun t => ds.any fun | .thmDecl cv _ => cv == ⟨t.n, [], t.stmt⟩ | _ => false)

theorem thmsS_ok_all : thmsS.all (fun t => t.ok NanoLDen.tab NanoLDen.eqs 40) = true := by decide +kernel

theorem cong_cons1 {a a' : Expr} (ha : HasTy NanoLDen.tab NanoLDen.eqs [] a u8C) (c : C a a' u8C) :
    C (consC a nilC) (consC a' nilC) LU8c :=
  .cong (h := .const (nm2 "List" "cons") [.zero]) (Ts := [.sort L1, u8C, LU8c]) (hty_cons ha hty_nil)
    (.cons (refl' hty_u8C) (.cons c (.cons (refl' hty_nil) .nil)))

theorem cong_u8of {a a' : Expr} (ha : HasTy NanoLDen.tab NanoLDen.eqs [] a natC) (c : C a a' natC) : C (u8ofC a) (u8ofC a') u8C :=
  .cong (h := .const (nm2 "UInt8" "ofNat") []) (as := [a]) (bs := [a']) (Ts := [natC]) (hty_u8of ha) (.cons c .nil)

/-- `UInt64.ofNat n` written into a fresh byte list -/
theorem conv_out (n : Nat) : C (putC nilC (u64ofC (litC n))) (consC (u8ofC (litC (n % 256))) nilC) LU8c := by
  have c1 : C (putC nilC (u64ofC (litC n))) (consC (u8ofC (litC n)) nilC) LU8c :=
    .inst (t := putNil) (as := [litC n]) (by simp [thmsP]) (.cons .lit .nil)
  have c2 : C (u8ofC (litC n)) (u8ofC (natModC (litC n) (ofNatNatC (litC 256)))) u8C :=
    .inst (t := u8Mod) (as := [litC n]) (by simp [thmsP]) (.cons .lit .nil)
  have c3 := cong_u8of (hty_natMod .lit (hty_ofNatNat .lit)) (conv_modG n)
  exact .trans c1 (cong_cons1 (hty_u8of .lit) (.trans c2 c3))

/-- `a + (2^64 - 3 % 2^64)` on literals -/
theorem conv_subLit (a : Nat) :
    C (natAddC (litC a) (natSubC (ofNatNatC (litC big)) (natModC (litC 3) (ofNatNatC (litC big)))))
      (litC (a + (big - 3))) natC := by
  have cb : C (ofNatNatC (litC big)) (litC big) natC :=
    .inst (t := NanoDen.brLitN) (as := [litC big]) (by simp [thmsP]) (.cons .lit .nil)
  have cm : C (natModC (litC 3) (ofNatNatC (litC big))) (litC 3) natC := conv_mod 3 big (by decide)
  have hsub : HasTy NanoLDen.tab NanoLDen.eqs [] (natSubC (ofNatNatC (litC big)) (natModC (litC 3) (ofNatNatC (litC big)))) natC :=
    hty_natSub (hty_ofNatNat .lit) (hty_natMod .lit (hty_ofNatNat .lit))
  have cs : C (natSubC (ofNatNatC (litC big)) (natModC (litC 3) (ofNatNatC (litC big)))) (litC (big - 3)) natC :=
    .trans (cong_natSub (hty_ofNatNat .lit) (hty_natMod .lit (hty_ofNatNat .lit)) cb cm) (conv_nsub 3 big)
  exact .trans (cong_natAdd .lit hsub (refl' .lit) cs) (conv_add a (big - 3))

/-- **the run of `m` on any input, in the model** -/
theorem run (inp : List UInt8) :
    Conv NanoLDen.tab NanoLDen.eqs thmsS [] (.app (.const (nm "m") []) (encL inp)) (encL [NanoS.outS inp]) LU8c := by
  have hx := hty_encL inp
  have hR := hty_rd hx
  have c0 : Conv NanoLDen.tab NanoLDen.eqs thmsS [] (.app (.const (nm "m") []) (encL inp)) (bodySC (encL inp)) LU8c :=
    .inst (t := mEqS) (as := [encL inp]) (by simp [thmsS]) (.cons hx .nil)
  have cR := conv_rd inp
  have c3 : C (litUC 3) (u64ofC (litC 3)) u64C := .inst (t := lit64) (as := [litC 3]) (by simp [thmsP]) (.cons .lit .nil)
  have hS := hty_sub64 hR (hty_litU 3)
  have cS : C (sub64C (rdC (encL inp)) (litUC 3)) (u64ofC (litC ((inp.getD 0 0).toNat + (big - 3)))) u64C :=
    .trans (cong_sub64 hR (hty_litU 3) cR c3)
      (.trans (.inst (t := brSub64) (as := [litC _, litC 3]) (by simp [thmsP]) (.cons .lit (.cons .lit .nil)))
        (cong_u64of (hty_natAdd .lit (hty_natSub (hty_ofNatNat .lit) (hty_natMod .lit (hty_ofNatNat .lit))))
          (conv_subLit _)))
  have cP : C (bodySC (encL inp)) (putC nilC (u64ofC (litC ((inp.getD 0 0).toNat + (big - 3))))) LU8c :=
    cong_put hty_nil hS cS
  have e : encL [NanoS.outS inp] = consC (u8ofC (litC (((inp.getD 0 0).toNat + (big - 3)) % 256))) nilC := by
    simp only [encL, byteC, u8ofC, litC, NanoS.outS_toNat, big]
  rw [e]
  exact .trans c0 (Conv.mono (fun t ht => List.mem_cons_of_mem _ ht) (.trans cP (conv_out _)))

/-! ## the semantic side (structure as `NanoLDen`) -/

section
variable {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
  (acc : Cached.checkDecls .verified pins ds = .ok env) (hnat : natLitSupported env = true)
  (hind : IndStored env (IndHeads.blockHeads blocksL)) (hrec : recsOkS ds = true) (M : Model V env)
include acc hnat hind hrec

theorem tabOk : TabOk M NanoLDen.tab := by
  simp only [recsOkS, Bool.and_eq_true, List.all_eq_true] at hrec
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

theorem thmsOk : ThmsOk ds NanoLDen.tab NanoLDen.eqs thmsS := by
  simp only [recsOkS, Bool.and_eq_true, List.all_eq_true] at hrec
  intro t ht
  exact ⟨any_thm (hrec.2 t (List.mem_cons_of_mem _ ht)), 40, List.all_eq_true.mp thmsS_ok_all t ht⟩

theorem eqsOk (hP : CvalParams M) : EqsOk M NanoLDen.eqs := by
  intro p hp
  simp only [NanoLDen.eqs, List.mem_singleton] at hp; subst hp
  refine ⟨rfl, rfl, fun φ ρ X hX => ?_⟩
  have ht := tabOk acc hnat hind hrec M
  have h0 : EqsOk M ([] : List (Expr × Expr)) := fun _ h => by cases h
  have tyA : HasTy NanoLDen.tab [] [] (.app (.const AddOne.outParamN [AddOne.L2]) (.sort AddOne.L1)) (.sort AddOne.L2) :=
    infer_sound 40 _ _ (by decide +kernel)
  obtain ⟨Y, -, dY, -, -⟩ := sound hP hnat ht h0 (Γ := []) (φ := φ) (ρ := ρ) (fun _ _ h => by simp at h) tyA
  simp only [recsOkS, Bool.and_eq_true, List.all_eq_true] at hrec
  have hrec3 := any_thm (hrec.2 NanoRDen.opEqT List.mem_cons_self)
  have := etransfer acc hP hnat ht h0 (Ts := []) hrec3 (by decide) (by decide)
    (infer_sound 40 _ _ (by decide +kernel)) tyA (infer_sound 40 _ _ (by decide +kernel))
    φ ρ .nil dY hX
  rw [← this]; exact dY

/-- **the emitted `m` on any input denotes the encoding of `[outA inp]`** -/
theorem den_mS (hP : CvalParams M) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (inp : List UInt8) :
    ∃ x, Denotes M.cval env φ ρ (encL inp) x ∧
      ∀ Y, Denotes M.cval env φ ρ (encL [NanoS.outS inp]) Y →
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

end Bridge.Real.NanoSDen
