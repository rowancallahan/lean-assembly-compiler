/- Bridge.Real.NanoRDen: the input-dependent nano program, con-leche side.

In every `CvalParams` model of an accepted env holding the records (`recsOkR`), with the Nat pin and
`IndStored`, the emitted `m` applied to the encoding of ANY input `inp` denotes the encoding of `[outR inp]`.
The derivation splits on the input: empty (`r_nil`), or a first byte `b` (`r_cons` gives `UInt8.ofNat (succ b)`,
then `lit (b+1)` by con-leche's literal rule, or for `b = 255` the wrap `u8_wrap`). -/
import Bridge.Real.NanoDen
import Bridge.Real.NanoR
import Bridge.Real.EngineAdd

namespace Bridge.Real.NanoRDen
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real Bridge.ModelExists2 Bridge.Real.Engine
open Bridge.Real.NanoDen
open Bridge.Real.Tiny (natC succC natV)

universe w
variable {V : Type w} [SetTheory V]

def litUC (k : Nat) : Expr := ofNatC u64C (.lit (.natVal k)) (.app (.const (nm2 "UInt64" "instOfNat") []) (.lit (.natVal k)))
def rdC (x : Expr) : Expr := apps (.const (nm "rd") []) [x, litUC 0]
def instC : Expr := apps (.const (nm "instHAdd") [.zero]) [u64C, .const (nm "instAddUInt64") []]
def plusC (e : Expr) : Expr :=
  apps (.const (nm2 "HAdd" "hAdd") [.zero, .zero, .zero]) [u64C, u64C, u64C, instC, e, litUC 1]
def bodyC (x : Expr) : Expr := putC nilC (plusC (rdC x))
def u8ofC (e : Expr) : Expr := .app (.const (nm2 "UInt8" "ofNat") []) e

def defHeadsR : List (Name × Head) :=
  [(nm "rd", ⟨[], [LU8c, u64C], u64C⟩), (AddOne.hAddN, ⟨[AddOne.lu, AddOne.lv, AddOne.lw], AddOne.hAddTs, .bvar 3⟩),
   (AddOne.instHAddN, ⟨[AddOne.li], AddOne.instHAddTs, AddOne.instHAddB⟩),
   (nm "instAddUInt64", ⟨[], [], .app (.const (nm "Add") [.zero]) u64C⟩),
   (AddOne.outParamN, ⟨[AddOne.lu], [.sort AddOne.pu], .sort AddOne.pu⟩)]

def tab : Tab := fun n => (NanoDen.tabL ++ defHeadsR).lookup n
def eqs : List (Expr × Expr) := [EngineAdd.opEq]

def mEqR : Thm := ⟨nm "m_eq", [LU8c], L1, LU8c, .app (.const (nm "m") []) (.bvar 0), bodyC (.bvar 0)⟩
def rNil : Thm := ⟨nm "r_nil", [], L1, LU8c, bodyC nilC, consC (u8ofC (ofNatNatC (.lit (.natVal 1)))) nilC⟩
def rCons : Thm := ⟨nm "r_cons", [natC, LU8c], L1, LU8c, bodyC (consC (u8ofC (.bvar 1)) (.bvar 0)),
  consC (u8ofC (.app succC (.bvar 1))) nilC⟩
def u8Wrap : Thm := ⟨nm "u8_wrap", [], L1, u8C, u8ofC (ofNatNatC (.lit (.natVal 256))), u8ofC (ofNatNatC (.lit (.natVal 0)))⟩
def opEqT : Thm := ⟨nm "outParam_eq", [], AddOne.L3, .sort AddOne.L2, .app (.const AddOne.outParamN [AddOne.L2])
  (.sort AddOne.L1), .sort AddOne.L1⟩
def thms : List Thm := [mEqR, rNil, rCons, u8Wrap, NanoDen.brLitN]

/-- the records the stream must hold (decidable) -/
def recsOkR (ds : Array Declaration) : Bool :=
  (defHeads ++ defHeadsR).all (fun p => ds.any fun | .defnDecl cv _ _ => cv == ⟨p.1, p.2.ps, piV p.2.Ts p.2.B⟩ | _ => false) &&
  (opEqT :: thms).all (fun t => ds.any fun | .thmDecl cv _ => cv == ⟨t.n, [], t.stmt⟩ | _ => false)

/-! ## typing of the encodings (generic in the byte values) -/

theorem hty_u8C {Γ : List Expr} : HasTy tab eqs Γ u8C (.sort L1) :=
  HasTy.head (n := nm "UInt8") (us := []) (h := ⟨[], [], .sort L1⟩) (as := []) (by decide +kernel) rfl .nil

theorem hty_u8of {Γ : List Expr} {e : Expr} (he : HasTy tab eqs Γ e natC) : HasTy tab eqs Γ (u8ofC e) u8C :=
  HasTy.head (n := nm2 "UInt8" "ofNat") (us := []) (h := ⟨[], [natC], u8C⟩) (as := [e]) (by decide +kernel) rfl
    (.cons he .nil)

theorem hty_succ {Γ : List Expr} {e : Expr} (he : HasTy tab eqs Γ e natC) : HasTy tab eqs Γ (.app succC e) natC :=
  HasTy.head (n := natSuccName) (us := []) (h := succHead) (as := [e]) (by decide +kernel) rfl (.cons he .nil)

theorem hty_cons {Γ : List Expr} {a l : Expr} (ha : HasTy tab eqs Γ a u8C) (hl : HasTy tab eqs Γ l LU8c) :
    HasTy tab eqs Γ (consC a l) LU8c :=
  HasTy.head (n := nm2 "List" "cons") (us := [.zero])
    (h := ⟨[lu], [.sort (.succ pu), .bvar 0, .app (.const (nm "List") [pu]) (.bvar 1)], .app (.const (nm "List") [pu]) (.bvar 2)⟩)
    (as := [u8C, a, l]) (by decide +kernel) rfl
    (.cons hty_u8C (.cons ha (.cons hl .nil)))

theorem hty_nil {Γ : List Expr} : HasTy tab eqs Γ nilC LU8c :=
  HasTy.head (n := nm2 "List" "nil") (us := [.zero])
    (h := ⟨[lu], [.sort (.succ pu)], .app (.const (nm "List") [pu]) (.bvar 0)⟩)
    (as := [u8C]) (by decide +kernel) rfl (.cons hty_u8C .nil)

theorem hty_encL {Γ : List Expr} : ∀ bs : List UInt8, HasTy tab eqs Γ (encL bs) LU8c
  | [] => hty_nil
  | _ :: bs => hty_cons (hty_u8of .lit) (hty_encL bs)


/-! ## the run, as equational derivations (closed terms) -/

theorem conv_byte {a b : Expr} (ha : HasTy tab eqs [] a natC) (h : Conv tab eqs thms [] a b natC) :
    Conv tab eqs thms [] (consC (u8ofC a) nilC) (consC (u8ofC b) nilC) LU8c :=
  .cong (h := .const (nm2 "List" "cons") [.zero]) (Ts := [.sort L1, u8C, LU8c])
    (hty_cons (hty_u8of ha) hty_nil)
    (.cons (.refl hty_u8C) (.cons (.cong (h := .const (nm2 "UInt8" "ofNat") []) (Ts := [natC]) (hty_u8of ha)
      (.cons h .nil)) (.cons (.refl hty_nil) .nil)))

theorem mem_thms {t : Thm} (h : t ∈ thms := by simp [thms]) : t ∈ thms := h

theorem ty_closed {e T : Expr} (h : infer tab eqs [] 40 e = some T) : HasTy tab eqs [] e T := infer_sound 40 _ _ h

theorem run_nil : Conv tab eqs thms [] (.app (.const (nm "m") []) nilC) (encL [1]) LU8c :=
  .trans (.inst (t := mEqR) (as := [nilC]) (by simp [thms]) (.cons hty_nil .nil))
    (.trans (.inst (t := rNil) (as := []) (by simp [thms]) .nil)
      (conv_byte (ty_closed (by decide +kernel))
        (.inst (t := NanoDen.brLitN) (as := [.lit (.natVal 1)]) (by simp [thms]) (.cons .lit .nil))))

theorem run_cons (B : Nat) (rest : List UInt8) :
    Conv tab eqs thms [] (.app (.const (nm "m") []) (consC (u8ofC (.lit (.natVal B))) (encL rest)))
      (consC (u8ofC (.app succC (.lit (.natVal B)))) nilC) LU8c :=
  .trans (.inst (t := mEqR) (as := [consC (u8ofC (.lit (.natVal B))) (encL rest)]) (by simp [thms])
      (.cons (hty_cons (hty_u8of .lit) (hty_encL rest)) .nil))
    (.inst (t := rCons) (as := [.lit (.natVal B), encL rest]) (by simp [thms]) (.cons .lit (.cons (hty_encL rest) .nil)))

theorem run_lt (B : Nat) :
    Conv tab eqs thms [] (consC (u8ofC (.app succC (.lit (.natVal B)))) nilC) (consC (u8ofC (.lit (.natVal (B + 1)))) nilC) LU8c :=
  conv_byte (hty_succ .lit) (.symm .litS)

theorem run_255 :
    Conv tab eqs thms [] (consC (u8ofC (.app succC (.lit (.natVal 255)))) nilC) (consC (u8ofC (.lit (.natVal 0))) nilC) LU8c :=
  .trans (run_lt 255)
    (.trans (conv_byte .lit (.symm (.inst (t := NanoDen.brLitN) (as := [.lit (.natVal 256)]) (by simp [thms]) (.cons .lit .nil))))
      (.trans (.cong (h := .const (nm2 "List" "cons") [.zero]) (Ts := [.sort L1, u8C, LU8c]) (ty_closed (by decide +kernel))
          (.cons (.refl hty_u8C) (.cons (.inst (t := u8Wrap) (as := []) (by simp [thms]) .nil) (.cons (.refl hty_nil) .nil))))
        (conv_byte (ty_closed (by decide +kernel))
          (.inst (t := NanoDen.brLitN) (as := [.lit (.natVal 0)]) (by simp [thms]) (.cons .lit .nil)))))

theorem encL_out (inp : List UInt8) : encL [NanoR.outR inp] =
    consC (u8ofC (.lit (.natVal (if (inp.getD 0 0).toNat < 255 then (inp.getD 0 0).toNat + 1 else 0)))) nilC := by
  simp only [encL, byteC, u8ofC, NanoR.outR_toNat]

/-- **the run of `m` on any input, as an equational derivation** -/
theorem run (inp : List UInt8) :
    Conv tab eqs thms [] (.app (.const (nm "m") []) (encL inp)) (encL [NanoR.outR inp]) LU8c := by
  rw [encL_out]
  cases inp with
  | nil => simpa [encL, byteC, u8ofC] using run_nil
  | cons b rest =>
    have hb := b.toNat_lt
    simp only [List.getD_cons_zero]
    have hc := run_cons b.toNat rest
    simp only [encL, byteC] at hc ⊢
    by_cases h : b.toNat < 255
    · rw [ite_eq_left h]; exact .trans hc (run_lt _)
    · rw [ite_eq_right h]
      have h255 : b.toNat = 255 := by omega
      rw [h255] at hc ⊢; exact .trans hc run_255

/-! ## the semantic side -/

section
variable {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
  (acc : Cached.checkDecls .verified pins ds = .ok env) (hnat : natLitSupported env = true)
  (hind : IndStored env indHeads) (hrec : recsOkR ds = true) (M : Model V env) (hP : CvalParams M)
include acc hnat hind hrec

theorem tabOk : TabOk M tab := by
  simp only [recsOkR, Bool.and_eq_true, List.all_eq_true] at hrec
  have hs : ∀ p ∈ NanoDen.tabL ++ defHeadsR, HeadSem M p.1 p.2 := by
    obtain ⟨h1, h2, h3⟩ := headSem_nat M hnat
    intro p hp
    simp only [NanoDen.tabL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (((rfl | rfl | rfl) | hd) | hi) | hr
    · exact h1
    · exact h2
    · exact h3
    · exact headSem_defn acc M (any_def (hrec.1 p (List.mem_append_left _ hd))) (by
        simp only [defHeads, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    · exact headSem_ind M (hind p hi) (by
        simp only [indHeads, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
    · exact headSem_defn acc M (any_def (hrec.1 p (List.mem_append_right _ hr))) (by
        simp only [defHeadsR, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
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

theorem thmsOk : ThmsOk ds tab eqs thms := by
  simp only [recsOkR, Bool.and_eq_true, List.all_eq_true] at hrec
  intro t ht
  refine ⟨any_thm (hrec.2 t (List.mem_cons_of_mem _ ht)), 40, ?_⟩
  simp only [thms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem eqsOk (hP : CvalParams M) : EqsOk M eqs := by
  intro p hp
  simp only [eqs, List.mem_singleton] at hp; subst hp
  refine ⟨rfl, rfl, fun φ ρ X hX => ?_⟩
  have ht := tabOk acc hnat hind hrec M
  have h0 : EqsOk M ([] : List (Expr × Expr)) := fun _ h => by cases h
  have tyA : HasTy tab [] [] (.app (.const AddOne.outParamN [AddOne.L2]) (.sort AddOne.L1)) (.sort AddOne.L2) :=
    infer_sound 40 _ _ (by decide +kernel)
  obtain ⟨Y, -, dY, -, -⟩ := sound hP hnat ht h0 (Γ := []) (φ := φ) (ρ := ρ) (fun _ _ h => by simp at h) tyA
  simp only [recsOkR, Bool.and_eq_true, List.all_eq_true] at hrec
  have hrec3 := any_thm (hrec.2 opEqT List.mem_cons_self)
  have := etransfer acc hP hnat ht h0 (Ts := []) hrec3 (by decide) (by decide)
    (infer_sound 40 _ _ (by decide +kernel)) tyA (infer_sound 40 _ _ (by decide +kernel))
    φ ρ .nil dY hX
  rw [← this]; exact dY

/-- **the emitted `m` on any input denotes the encoding of `[outR inp]`** -/
theorem den_mR (hP : CvalParams M) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (inp : List UInt8) :
    ∃ x, Denotes M.cval env φ ρ (encL inp) x ∧
      ∀ Y, Denotes M.cval env φ ρ (encL [NanoR.outR inp]) Y →
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

end Bridge.Real.NanoRDen
