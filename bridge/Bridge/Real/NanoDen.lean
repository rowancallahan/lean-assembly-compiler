/- Bridge.Real.NanoDen: the tiny NANO program, con-leche side.

In every `CvalParams` model of an accepted env holding the program's records (`m`, `put`, …, `m_eq`, `put_one`,
`br_litN`), under the two named hypotheses on the env (`natLitSupported`, `IndStored` for the five inductive
members used), the emitted `m` applied to (the encoding of) ANY input denotes the encoding of `[1]`. -/
import Bridge.Real.Conv
import Bridge.Real.Tr
import Bridge.Real.NanoTiny

namespace Bridge.Real.NanoDen
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real Bridge.ModelExists2 Bridge.Real.Engine
open Bridge.Real.Tiny (natC natV)

universe w
variable {V : Type w} [SetTheory V]

def nm (s : String) : Name := .str .anonymous s
def nm2 (a b : String) : Name := .str (.str .anonymous a) b
def lu : Name := nm "u"
def pu : Level := .param lu
def L1 : Level := .succ .zero

def u8C : Expr := .const (nm "UInt8") []
def u64C : Expr := .const (nm "UInt64") []
def LU8c : Expr := .app (.const (nm "List") [.zero]) u8C
def nilC : Expr := .app (.const (nm2 "List" "nil") [.zero]) u8C
def consC (a l : Expr) : Expr := apps (.const (nm2 "List" "cons") [.zero]) [u8C, a, l]
def byteC (b : Nat) : Expr := .app (.const (nm2 "UInt8" "ofNat") []) (.lit (.natVal b))
def ofNatC (T k i : Expr) : Expr := apps (.const (nm2 "OfNat" "ofNat") [.zero]) [T, k, i]
def ofNatNatC (k : Expr) : Expr := ofNatC natC k (.app (.const (nm "instOfNatNat") []) k)
def oneC : Expr := ofNatC u64C (.lit (.natVal 1)) (.app (.const (nm2 "UInt64" "instOfNat") []) (.lit (.natVal 1)))
def putC (o v : Expr) : Expr := apps (.const (nm "put") []) [o, v]

/-- **the encoding of a byte list**: `[b₀, b₁, …]` ↦ `List.cons UInt8 (UInt8.ofNat b₀) (…(List.nil UInt8))` -/
def encL : List UInt8 → Expr
  | [] => nilC
  | b :: bs => consC (byteC b.toNat) (encL bs)

/-! ## heads -/

def defHeads : List (Name × Head) :=
  [(nm "m", ⟨[], [LU8c], LU8c⟩), (nm "put", ⟨[], [LU8c, u64C], LU8c⟩), (nm2 "UInt8" "ofNat", ⟨[], [natC], u8C⟩),
   (nm2 "OfNat" "ofNat", ⟨[lu], [.sort (.succ pu), natC, apps (.const (nm "OfNat") [pu]) [.bvar 1, .bvar 0]], .bvar 2⟩),
   (nm2 "UInt64" "instOfNat", ⟨[], [natC], apps (.const (nm "OfNat") [.zero]) [u64C, .bvar 0]⟩),
   (nm "instOfNatNat", ⟨[], [natC], apps (.const (nm "OfNat") [.zero]) [natC, .bvar 0]⟩)]

/-- the inductive members the program uses, with their declared types -/
def indHeads : List (Name × Head) :=
  [(nm "List", ⟨[lu], [.sort (.succ pu)], .sort (.succ pu)⟩),
   (nm2 "List" "nil", ⟨[lu], [.sort (.succ pu)], .app (.const (nm "List") [pu]) (.bvar 0)⟩),
   (nm2 "List" "cons", ⟨[lu], [.sort (.succ pu), .bvar 0, .app (.const (nm "List") [pu]) (.bvar 1)],
     .app (.const (nm "List") [pu]) (.bvar 2)⟩),
   (nm "UInt8", ⟨[], [], .sort L1⟩), (nm "UInt64", ⟨[], [], .sort L1⟩)]

def tabL : List (Name × Head) :=
  [(natName, natHead), (natZeroName, zeroHead), (natSuccName, succHead)] ++ defHeads ++ indHeads
def tab : Tab := fun n => tabL.lookup n

/-- **Hypothesis `IndStored`**: each listed inductive member is stored with its declared type (binder data aside).
con-leche's `checkDecls_consts` gives exactly this for defs/theorems but excludes inductive blocks. -/
def IndStored (env : Env) (hs : List (Name × Head)) : Prop :=
  ∀ p ∈ hs, ∃ ci, env.find? p.1 = some ci ∧ ci.toConstantVal.levelParams = p.2.ps ∧
    ∃ ms : List BinderMeta, ms.length = p.2.Ts.length ∧ ci.toConstantVal.type = piN (p.2.Ts.zip ms) p.2.B

def mEq : Thm := ⟨nm "m_eq", [LU8c], L1, LU8c, .app (.const (nm "m") []) (.bvar 0), putC nilC oneC⟩
def putOne : Thm := ⟨nm "put_one", [], L1, LU8c, putC nilC oneC, consC (.app (.const (nm2 "UInt8" "ofNat") [])
  (ofNatNatC (.lit (.natVal 1)))) nilC⟩
def brLitN : Thm := ⟨nm "br_litN", [natC], L1, natC, ofNatNatC (.bvar 0), .bvar 0⟩
def thms : List Thm := [mEq, putOne, brLitN]

/-- the records the stream must hold (checked by `decide` on the parsed export in `Bridge.Main`) -/
def recsOk (ds : Array Declaration) : Bool :=
  defHeads.all (fun p => ds.any fun | .defnDecl cv _ _ => cv == ⟨p.1, p.2.ps, piV p.2.Ts p.2.B⟩ | _ => false) &&
  thms.all (fun t => ds.any fun | .thmDecl cv _ => cv == ⟨t.n, [], t.stmt⟩ | _ => false)

/-! ## the semantic side -/

theorem headSem_ind {env : Env} (M : Model V env) {n : Name} {h : Head}
    (hst : ∃ ci, env.find? n = some ci ∧ ci.toConstantVal.levelParams = h.ps ∧
      ∃ ms : List BinderMeta, ms.length = h.Ts.length ∧ ci.toConstantVal.type = piN (h.Ts.zip ms) h.B)
    (hh : headSc h = true) : HeadSem M n h := by
  obtain ⟨ci, hf, hl, ms, hml, hty⟩ := hst
  refine ⟨fun φ ρ us hus => ?_, fun ψ ρ => ?_, headSc_T hh, headSc_B hh⟩
  · have := Denotes.const (cval := M.cval) (φ := φ) (ρ := ρ) (us := us) hf (by rw [hl]; exact hus)
    rwa [hl] at this
  · obtain ⟨P, hP, hm⟩ := const_mem M hf ψ ρ
    rw [hty] at hP
    exact ⟨ms, P, hml, hP, hm⟩

theorem any_def {ds : Array Declaration} {cv : ConstantVal}
    (h : (ds.any fun | .defnDecl cv' _ _ => cv' == cv | _ => false) = true) :
    ∃ v hint, Declaration.defnDecl cv v hint ∈ ds := by
  obtain ⟨d, hd, hp⟩ := Array.any_eq_true'.mp h
  match d, hp with
  | .defnDecl cv' v hint, hp => simp only [beq_iff_eq] at hp; subst hp; exact ⟨v, hint, hd⟩

theorem any_thm {ds : Array Declaration} {cv : ConstantVal}
    (h : (ds.any fun | .thmDecl cv' _ => cv' == cv | _ => false) = true) :
    ∃ v, Declaration.thmDecl cv v ∈ ds := by
  obtain ⟨d, hd, hp⟩ := Array.any_eq_true'.mp h
  match d, hp with
  | .thmDecl cv' v, hp => simp only [beq_iff_eq] at hp; subst hp; exact ⟨v, hd⟩

section
variable {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
  (acc : Cached.checkDecls .verified pins ds = .ok env) (hnat : natLitSupported env = true)
  (hind : IndStored env indHeads) (hrec : recsOk ds = true) (M : Model V env) (hP : CvalParams M)
include acc hnat hind hrec

theorem tabOk : TabOk M tab := by
  have hs : ∀ p ∈ tabL, HeadSem M p.1 p.2 := by
    obtain ⟨h1, h2, h3⟩ := headSem_nat M hnat
    simp only [recsOk, Bool.and_eq_true, List.all_eq_true] at hrec
    intro p hp
    simp only [tabL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ((rfl | rfl | rfl) | hd) | hi
    · exact h1
    · exact h2
    · exact h3
    · exact headSem_defn acc M (any_def (hrec.1 p hd)) (by
        simp only [defHeads, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    · exact headSem_ind M (hind p hi) (by
        simp only [indHeads, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
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
  exact this tabL hs hn

theorem thmsOk : ThmsOk ds tab [] thms := by
  simp only [recsOk, Bool.and_eq_true, List.all_eq_true] at hrec
  intro t ht
  refine ⟨any_thm (hrec.2 t ht), 40, ?_⟩
  simp only [thms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> decide +kernel

omit acc hnat hind hrec in
/-- every byte list's encoding has type `List UInt8` -/
theorem encL_ty : ∀ bs : List UInt8, HasTy tab [] [] (encL bs) LU8c
  | [] => infer_sound 40 _ _ (by decide +kernel)
  | b :: bs => by
    have h0 : HasTy tab [] [] u8C (.sort L1) := infer_sound 40 _ _ (by decide +kernel)
    have h1 : HasTy tab [] [] (byteC b.toNat) u8C :=
      HasTy.head (n := nm2 "UInt8" "ofNat") (us := []) (h := ⟨[], [natC], u8C⟩) (as := [.lit (.natVal b.toNat)])
        (by decide +kernel) rfl (.cons .lit .nil)
    exact HasTy.head (n := nm2 "List" "cons") (us := [.zero]) (h := (indHeads.lookup (nm2 "List" "cons")).get rfl)
      (as := [u8C, byteC b.toNat, encL bs]) (by decide +kernel) rfl
      (.cons h0 (.cons h1 (.cons (encL_ty bs) .nil)))

omit acc hnat hind hrec in
/-- the run of `m` on a symbolic input, as an equational derivation -/
theorem run : Conv tab [] thms [LU8c] (.app (.const (nm "m") []) (.bvar 0)) (encL [1]) LU8c := by
  have ty : ∀ Γ e T, infer tab [] Γ 40 e = some T → HasTy tab [] Γ e T := fun Γ => infer_sound 40
  have c1 : Conv tab [] thms [LU8c] (.app (.const (nm "m") []) (.bvar 0)) (putC nilC oneC) LU8c :=
    .inst (t := mEq) (as := [.bvar 0]) (by simp [thms]) (.cons (ty _ _ _ (by decide +kernel)) .nil)
  have c2 : Conv tab [] thms [LU8c] (putC nilC oneC) putOne.rhs LU8c :=
    .inst (t := putOne) (as := []) (by simp [thms]) .nil
  have c3 : Conv tab [] thms [LU8c] (ofNatNatC (.lit (.natVal 1))) (.lit (.natVal 1)) natC :=
    .inst (t := brLitN) (as := [.lit (.natVal 1)]) (by simp [thms]) (.cons .lit .nil)
  have c4 : Conv tab [] thms [LU8c] putOne.rhs (encL [1]) LU8c :=
    .cong (h := .const (nm2 "List" "cons") [.zero]) (Ts := [.sort L1, u8C, LU8c])
      (ty _ _ _ (by decide +kernel))
      (.cons (.refl (ty _ _ _ (by decide +kernel)))
        (.cons (.cong (h := .const (nm2 "UInt8" "ofNat") []) (Ts := [natC]) (ty _ _ _ (by decide +kernel))
          (.cons c3 .nil))
          (.cons (.refl (ty _ _ _ (by decide +kernel))) .nil)))
  exact .trans c1 (.trans c2 c4)

omit acc hnat hind hrec in
theorem tr_mainX : tr NanoTiny.mainX = .app (.const (nm "m") []) (.bvar 0) := by decide +kernel

/-- **the emitted `m` on any input denotes the encoding of `[1]`** -/
theorem den_m (hP : CvalParams M) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (inp : List UInt8) :
    ∃ x, Denotes M.cval env φ ρ (encL inp) x ∧
      ∀ Y, Denotes M.cval env φ ρ (encL [1]) Y → Denotes M.cval env φ (push x ρ) (tr NanoTiny.mainX) Y := by
  have ht := tabOk acc hnat hind hrec M
  have he : EqsOk M ([] : List (Expr × Expr)) := fun _ h => by cases h
  have h0 : GammaOk M φ ρ ([] : List Expr) := fun _ _ h => by simp at h
  obtain ⟨x, A, dx, dA, hxA⟩ := sound hP hnat ht he h0 (encL_ty inp)
  refine ⟨x, dx, fun Y hY => ?_⟩
  have hm : MemL M φ [LU8c] [x] := .cons (fun ρ' => closed_move (by decide) dA) hxA .nil
  obtain ⟨X, -, d1, d2, -, -⟩ := conv_sound acc hP hnat ht he (thmsOk acc hnat hind hrec) (hm.gamma (ρ := ρ)) run
  have e : X = Y := Denotes_functional (closed_move (by decide) d2) hY
  subst e
  rw [tr_mainX]; exact d1
end

end Bridge.Real.NanoDen
