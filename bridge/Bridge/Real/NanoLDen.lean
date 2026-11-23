/- Bridge.Real.NanoLDen: growth step `ite` (UInt64 `<`), con-leche side.

The derivation evaluates the condition in the model: `rd` of the input to `UInt64.ofNat a`, the stored `ite_lt` to a
`cond` on `Nat.ble`, and `Nat.ble`, small `%` and `+` on literals by Conv lemmas proved by induction on the
literal (`conv_add`, `conv_ble`, `conv_mod`) from the stored recursion equations — set-level Nat arithmetic. -/
import Bridge.Real.NanoRDen
import Bridge.Real.NanoL
import Bridge.Real.IndHeads

namespace Bridge.Real.NanoLDen
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real Bridge.ModelExists2 Bridge.Real.Engine
open Bridge.Real.NanoDen
open Bridge.Real.NanoRDen (litUC rdC u8ofC)
open Bridge.Real.Tiny (natC succC natV)

universe w
variable {V : Type w} [SetTheory V]

/-! ## terms -/

def litC (k : Nat) : Expr := .lit (.natVal k)
def zeroC : Expr := .const natZeroName []
def boolTy : Expr := .const (nm "Bool") []
def boolC (b : Bool) : Expr := .const (if b then nm2 "Bool" "true" else nm2 "Bool" "false") []
def natAddC (a b : Expr) : Expr := apps (.const AddOne.hAddN [.zero, .zero, .zero])
  [natC, natC, natC, apps (.const (nm "instHAdd") [.zero]) [natC, .const (nm "instAddNat") []], a, b]
def natModC (a b : Expr) : Expr := apps (.const (nm2 "HMod" "hMod") [.zero, .zero, .zero])
  [natC, natC, natC, apps (.const (nm "instHMod") [.zero]) [natC, .const (nm2 "Nat" "instMod") []], a, b]
def u64ofC (e : Expr) : Expr := .app (.const (nm2 "UInt64" "ofNat") []) e
def toU64C (e : Expr) : Expr := .app (.const (nm2 "UInt8" "toUInt64") []) e
def bleC (a b : Expr) : Expr := apps (.const (nm2 "Nat" "ble") []) [a, b]
def condC (c t e : Expr) : Expr := apps (.const (nm "cond") [L1]) [u64C, c, t, e]
def ltC (a b : Expr) : Expr := apps (.const (nm2 "LT" "lt") [.zero]) [u64C, .const (nm "instLTUInt64") [], a, b]
def decC (a b : Expr) : Expr := apps (.const (nm2 "UInt64" "decLt") []) [a, b]
def iteC (c d t e : Expr) : Expr := apps (.const (nm "ite") [L1]) [u64C, c, d, t, e]
def bodyL (x : Expr) : Expr :=
  putC nilC (iteC (ltC (rdC x) (litUC 5)) (decC (rdC x) (litUC 5)) (litUC 1) (litUC 2))
def big : Nat := 18446744073709551616

/-! ## heads -/

def lw : Name := nm "u_1"
def defHeadsL : List (Name × Head) :=
  [(nm "rd", ⟨[], [LU8c, u64C], u64C⟩), (nm2 "UInt8" "toUInt64", ⟨[], [u8C], u64C⟩),
   (nm2 "UInt64" "ofNat", ⟨[], [natC], u64C⟩),
   (nm "ite", ⟨[lu], [.sort pu, .sort .zero, .app (.const (nm "Decidable") []) (.bvar 0), .bvar 2, .bvar 3], .bvar 4⟩),
   (nm2 "LT" "lt", ⟨[lu], [.sort (.succ pu), .app (.const (nm "LT") [pu]) (.bvar 0), .bvar 1, .bvar 2], .sort .zero⟩),
   (nm "instLTUInt64", ⟨[], [], .app (.const (nm "LT") [.zero]) u64C⟩),
   (nm2 "UInt64" "decLt", ⟨[], [u64C, u64C], .app (.const (nm "Decidable") [])
      (apps (.const (nm2 "LT" "lt") [.zero]) [u64C, .const (nm "instLTUInt64") [], .bvar 1, .bvar 0])⟩),
   (nm "cond", ⟨[lu], [.sort pu, boolTy, .bvar 1, .bvar 2], .bvar 3⟩),
   (nm2 "Nat" "ble", ⟨[], [natC, natC], boolTy⟩),
   (nm2 "HMod" "hMod", ⟨[AddOne.lu, AddOne.lv, AddOne.lw], [.sort (.succ AddOne.pu), .sort (.succ AddOne.pv),
      .app (.const AddOne.outParamN [.succ (.succ AddOne.pw)]) (.sort (.succ AddOne.pw)),
      apps (.const (nm "HMod") [AddOne.pu, AddOne.pv, AddOne.pw]) [.bvar 2, .bvar 1, .bvar 0], .bvar 3, .bvar 3], .bvar 3⟩),
   (nm "instHMod", ⟨[lw], [.sort (.succ (.param lw)), .app (.const (nm "Mod") [.param lw]) (.bvar 0)],
      apps (.const (nm "HMod") [.param lw, .param lw, .param lw]) [.bvar 1, .bvar 1, .bvar 1]⟩),
   (nm2 "Nat" "instMod", ⟨[], [], .app (.const (nm "Mod") [.zero]) natC⟩),
   (AddOne.hAddN, ⟨[AddOne.lu, AddOne.lv, AddOne.lw], AddOne.hAddTs, .bvar 3⟩),
   (AddOne.instHAddN, ⟨[AddOne.li], AddOne.instHAddTs, AddOne.instHAddB⟩),
   (nm "instAddNat", ⟨[], [], .app (.const (nm "Add") [.zero]) natC⟩),
   (AddOne.outParamN, ⟨[AddOne.lu], [.sort AddOne.pu], .sort AddOne.pu⟩)]

/-- the inductive blocks used: List, UInt8, UInt64, Bool -/
def blocksL : List ((Name × Head) × List (Name × Head)) :=
  [((nm "List", ⟨[lu], [.sort (.succ pu)], .sort (.succ pu)⟩),
     [(nm2 "List" "nil", ⟨[lu], [.sort (.succ pu)], .app (.const (nm "List") [pu]) (.bvar 0)⟩),
      (nm2 "List" "cons", ⟨[lu], [.sort (.succ pu), .bvar 0, .app (.const (nm "List") [pu]) (.bvar 1)],
        .app (.const (nm "List") [pu]) (.bvar 2)⟩)]),
   ((nm "UInt8", ⟨[], [], .sort L1⟩), []), ((nm "UInt64", ⟨[], [], .sort L1⟩), []),
   ((nm "Bool", ⟨[], [], .sort L1⟩), [(nm2 "Bool" "true", ⟨[], [], boolTy⟩), (nm2 "Bool" "false", ⟨[], [], boolTy⟩)])]

def tabL : List (Name × Head) :=
  [(natName, natHead), (natZeroName, zeroHead), (natSuccName, succHead)] ++ defHeads ++ defHeadsL ++
    IndHeads.blockHeads blocksL
def tab : Tab := fun n => tabL.lookup n
def eqs : List (Expr × Expr) := [EngineAdd.opEq]

/-! ## stored equations -/

def mEqL : Thm := ⟨nm "m_eq", [LU8c], L1, LU8c, .app (.const (nm "m") []) (.bvar 0), bodyL (.bvar 0)⟩
def rdNil0 : Thm := ⟨nm "rd_nil0", [], L1, u64C, rdC nilC, u64ofC (ofNatNatC (litC 0))⟩
def rdCons0 : Thm := ⟨nm "rd_cons0", [u8C, LU8c], L1, u64C, rdC (consC (.bvar 1) (.bvar 0)), toU64C (.bvar 1)⟩
def u8u64 : Thm := ⟨nm "u8_u64", [natC], L1, u64C, toU64C (u8ofC (.bvar 0)),
  u64ofC (natModC (.bvar 0) (ofNatNatC (litC 256)))⟩
def lit64 : Thm := ⟨nm "lit64", [natC], L1, u64C, ofNatC u64C (.bvar 0) (.app (.const (nm2 "UInt64" "instOfNat") []) (.bvar 0)),
  u64ofC (.bvar 0)⟩
def iteLt : Thm := ⟨nm "ite_lt", [natC, natC, u64C, u64C], L1, u64C,
  iteC (ltC (u64ofC (.bvar 3)) (u64ofC (.bvar 2))) (decC (u64ofC (.bvar 3)) (u64ofC (.bvar 2))) (.bvar 1) (.bvar 0),
  condC (bleC (natModC (.bvar 2) (ofNatNatC (litC big))) (natModC (.bvar 3) (ofNatNatC (litC big)))) (.bvar 0) (.bvar 1)⟩
def condT : Thm := ⟨nm "cond_t", [u64C, u64C], L1, u64C, condC (boolC true) (.bvar 1) (.bvar 0), .bvar 1⟩
def condF : Thm := ⟨nm "cond_f", [u64C, u64C], L1, u64C, condC (boolC false) (.bvar 1) (.bvar 0), .bvar 0⟩
def bleZ : Thm := ⟨nm "ble_z", [natC], L1, boolTy, bleC zeroC (.bvar 0), boolC true⟩
def bleSZ : Thm := ⟨nm "ble_sz", [natC], L1, boolTy, bleC (.app succC (.bvar 0)) zeroC, boolC false⟩
def bleSS : Thm := ⟨nm "ble_ss", [natC, natC], L1, boolTy, bleC (.app succC (.bvar 1)) (.app succC (.bvar 0)),
  bleC (.bvar 1) (.bvar 0)⟩
def zeroAdd : Thm := ⟨nm "zero_add'", [natC], L1, natC, natAddC zeroC (.bvar 0), .bvar 0⟩
def succAdd : Thm := ⟨nm "succ_add'", [natC, natC], L1, natC, natAddC (.app succC (.bvar 1)) (.bvar 0),
  .app succC (natAddC (.bvar 1) (.bvar 0))⟩
def modSmall : Thm := ⟨nm "mod_small", [natC, natC], L1, natC, natModC (.bvar 1) (natAddC (.bvar 1) (.app succC (.bvar 0))),
  .bvar 1⟩
def putNil : Thm := ⟨nm "put_nil", [natC], L1, LU8c, putC nilC (u64ofC (.bvar 0)), consC (u8ofC (.bvar 0)) nilC⟩

def thms : List Thm := [mEqL, rdNil0, rdCons0, u8u64, lit64, iteLt, condT, condF, bleZ, bleSZ, bleSS, zeroAdd,
  succAdd, modSmall, NanoDen.brLitN, putNil]

/-- the records the stream must hold (decidable) -/
def recsOkL (ds : Array Declaration) : Bool :=
  ((defHeads ++ defHeadsL).all fun p => ds.any fun | .defnDecl cv _ _ => cv == ⟨p.1, p.2.ps, piV p.2.Ts p.2.B⟩ | _ => false) &&
  ((NanoRDen.opEqT :: thms).all fun t => ds.any fun | .thmDecl cv _ => cv == ⟨t.n, [], t.stmt⟩ | _ => false)

/-! ## typing (generic in the literals) -/

theorem thms_ok : ∀ t ∈ thms, t.ok tab eqs 40 = true := by
  intro t ht
  simp only [thms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem ty0 {e T : Expr} (h : infer tab eqs [] 40 e = some T) : HasTy tab eqs [] e T := infer_sound 40 _ _ h

theorem hty_succ {e : Expr} (he : HasTy tab eqs [] e natC) : HasTy tab eqs [] (.app succC e) natC :=
  HasTy.head (n := natSuccName) (us := []) (h := succHead) (as := [e]) (by decide +kernel) rfl (.cons he .nil)

theorem hty_u8of {e : Expr} (he : HasTy tab eqs [] e natC) : HasTy tab eqs [] (u8ofC e) u8C :=
  HasTy.head (n := nm2 "UInt8" "ofNat") (us := []) (h := ⟨[], [natC], u8C⟩) (as := [e]) (by decide +kernel) rfl
    (.cons he .nil)

theorem hty_u64of {e : Expr} (he : HasTy tab eqs [] e natC) : HasTy tab eqs [] (u64ofC e) u64C :=
  HasTy.head (n := nm2 "UInt64" "ofNat") (us := []) (h := ⟨[], [natC], u64C⟩) (as := [e]) (by decide +kernel) rfl
    (.cons he .nil)

theorem hty_toU64 {e : Expr} (he : HasTy tab eqs [] e u8C) : HasTy tab eqs [] (toU64C e) u64C :=
  HasTy.head (n := nm2 "UInt8" "toUInt64") (us := []) (h := ⟨[], [u8C], u64C⟩) (as := [e]) (by decide +kernel) rfl
    (.cons he .nil)

theorem hty_u8C : HasTy tab eqs [] u8C (.sort L1) := ty0 (by decide +kernel)
theorem hty_u64C : HasTy tab eqs [] u64C (.sort L1) := ty0 (by decide +kernel)
theorem hty_natC : HasTy tab eqs [] natC (.sort L1) := ty0 (by decide +kernel)
theorem hty_nil : HasTy tab eqs [] nilC LU8c := ty0 (by decide +kernel)

theorem hty_cons {a l : Expr} (ha : HasTy tab eqs [] a u8C) (hl : HasTy tab eqs [] l LU8c) :
    HasTy tab eqs [] (consC a l) LU8c :=
  HasTy.head (n := nm2 "List" "cons") (us := [.zero])
    (h := ⟨[lu], [.sort (.succ pu), .bvar 0, .app (.const (nm "List") [pu]) (.bvar 1)], .app (.const (nm "List") [pu]) (.bvar 2)⟩)
    (as := [u8C, a, l]) (by decide +kernel) rfl (.cons hty_u8C (.cons ha (.cons hl .nil)))

theorem hty_encL : ∀ bs : List UInt8, HasTy tab eqs [] (encL bs) LU8c
  | [] => hty_nil
  | _ :: bs => hty_cons (hty_u8of .lit) (hty_encL bs)

theorem hty_natAdd {a b : Expr} (ha : HasTy tab eqs [] a natC) (hb : HasTy tab eqs [] b natC) :
    HasTy tab eqs [] (natAddC a b) natC :=
  HasTy.head (n := AddOne.hAddN) (us := [.zero, .zero, .zero]) (h := ⟨[AddOne.lu, AddOne.lv, AddOne.lw], AddOne.hAddTs, .bvar 3⟩)
    (as := [natC, natC, natC, apps (.const (nm "instHAdd") [.zero]) [natC, .const (nm "instAddNat") []], a, b])
    (by decide +kernel) rfl
    (.cons hty_natC (.cons hty_natC (.cons (.conv hty_natC (by simp [eqs, EngineAdd.opEq]; decide))
      (.cons (ty0 (by decide +kernel)) (.cons ha (.cons hb .nil))))))

theorem hty_natMod {a b : Expr} (ha : HasTy tab eqs [] a natC) (hb : HasTy tab eqs [] b natC) :
    HasTy tab eqs [] (natModC a b) natC :=
  HasTy.head (n := nm2 "HMod" "hMod") (us := [.zero, .zero, .zero])
    (h := ((defHeadsL.lookup (nm2 "HMod" "hMod")).getD ⟨[], [], .bvar 0⟩))
    (as := [natC, natC, natC, apps (.const (nm "instHMod") [.zero]) [natC, .const (nm2 "Nat" "instMod") []], a, b])
    (by decide +kernel) rfl
    (.cons hty_natC (.cons hty_natC (.cons (.conv hty_natC (by simp [eqs, EngineAdd.opEq]; decide))
      (.cons (ty0 (by decide +kernel)) (.cons ha (.cons hb .nil))))))

theorem hty_ble {a b : Expr} (ha : HasTy tab eqs [] a natC) (hb : HasTy tab eqs [] b natC) :
    HasTy tab eqs [] (bleC a b) boolTy :=
  HasTy.head (n := nm2 "Nat" "ble") (us := []) (h := ⟨[], [natC, natC], boolTy⟩) (as := [a, b])
    (by decide +kernel) rfl (.cons ha (.cons hb .nil))

theorem hty_bool (b : Bool) : HasTy tab eqs [] (boolC b) boolTy := by
  cases b <;> exact ty0 (by decide +kernel)

theorem hty_ofNatNat {e : Expr} (he : HasTy tab eqs [] e natC) : HasTy tab eqs [] (ofNatNatC e) natC :=
  HasTy.head (n := nm2 "OfNat" "ofNat") (us := [.zero])
    (h := ⟨[lu], [.sort (.succ pu), natC, apps (.const (nm "OfNat") [pu]) [.bvar 1, .bvar 0]], .bvar 2⟩)
    (as := [natC, e, .app (.const (nm "instOfNatNat") []) e]) (by decide +kernel) rfl
    (.cons hty_natC (.cons he (.cons (HasTy.head (n := nm "instOfNatNat") (us := [])
      (h := ⟨[], [natC], apps (.const (nm "OfNat") [.zero]) [natC, .bvar 0]⟩) (as := [e]) (by decide +kernel) rfl
      (.cons he .nil)) .nil)))

/-! ## congruence helpers -/

abbrev C (a b T : Expr) : Prop := Conv tab eqs thms [] a b T

def instAddE : Expr := apps (.const (nm "instHAdd") [.zero]) [natC, .const (nm "instAddNat") []]
def instModE : Expr := apps (.const (nm "instHMod") [.zero]) [natC, .const (nm2 "Nat" "instMod") []]

theorem refl' {a T : Expr} (h : HasTy tab eqs [] a T) : C a a T := .refl h

theorem cong_natAdd {a b a' b' : Expr} (ha : HasTy tab eqs [] a natC) (hb : HasTy tab eqs [] b natC)
    (c1 : C a a' natC) (c2 : C b b' natC) : C (natAddC a b) (natAddC a' b') natC :=
  .cong (h := .const AddOne.hAddN [.zero, .zero, .zero])
    (Ts := [.sort L1, .sort L1, .sort L1, apps (.const (nm "HAdd") [.zero, .zero, .zero]) [natC, natC, natC], natC, natC])
    (hty_natAdd ha hb)
    (.cons (refl' hty_natC) (.cons (refl' hty_natC) (.cons (refl' hty_natC) (.cons (refl' (ty0 (by decide +kernel)))
      (.cons c1 (.cons c2 .nil))))))

theorem cong_natMod {a b a' b' : Expr} (ha : HasTy tab eqs [] a natC) (hb : HasTy tab eqs [] b natC)
    (c1 : C a a' natC) (c2 : C b b' natC) : C (natModC a b) (natModC a' b') natC :=
  .cong (h := .const (nm2 "HMod" "hMod") [.zero, .zero, .zero])
    (Ts := [.sort L1, .sort L1, .sort L1, apps (.const (nm "HMod") [.zero, .zero, .zero]) [natC, natC, natC], natC, natC])
    (hty_natMod ha hb)
    (.cons (refl' hty_natC) (.cons (refl' hty_natC) (.cons (refl' hty_natC) (.cons (refl' (ty0 (by decide +kernel)))
      (.cons c1 (.cons c2 .nil))))))

theorem cong_ble {a b a' b' : Expr} (ha : HasTy tab eqs [] a natC) (hb : HasTy tab eqs [] b natC)
    (c1 : C a a' natC) (c2 : C b b' natC) : C (bleC a b) (bleC a' b') boolTy :=
  .cong (h := .const (nm2 "Nat" "ble") []) (Ts := [natC, natC]) (hty_ble ha hb) (.cons c1 (.cons c2 .nil))

theorem cong_succ {a a' : Expr} (ha : HasTy tab eqs [] a natC) (c : C a a' natC) : C (.app succC a) (.app succC a') natC :=
  .cong (h := succC) (as := [a]) (bs := [a']) (Ts := [natC]) (hty_succ ha) (.cons c .nil)

theorem mem' {t : Thm} (h : t ∈ thms := by simp [thms]) : t ∈ thms := h

/-! ## set-level Nat arithmetic on literals -/

theorem conv_add : ∀ a b : Nat, C (natAddC (litC a) (litC b)) (litC (a + b)) natC
  | 0, b => by
    have c1 : C (natAddC (litC 0) (litC b)) (natAddC zeroC (litC b)) natC :=
      cong_natAdd .lit .lit .lit0 (refl' .lit)
    have c2 : C (natAddC zeroC (litC b)) (litC b) natC :=
      .inst (t := zeroAdd) (as := [litC b]) (by simp [thms]) (.cons .lit .nil)
    simpa using Conv.trans c1 c2
  | a + 1, b => by
    have c1 : C (natAddC (litC (a + 1)) (litC b)) (natAddC (.app succC (litC a)) (litC b)) natC :=
      cong_natAdd .lit .lit .litS (refl' .lit)
    have c2 : C (natAddC (.app succC (litC a)) (litC b)) (.app succC (natAddC (litC a) (litC b))) natC :=
      .inst (t := succAdd) (as := [litC a, litC b]) (by simp [thms]) (.cons .lit (.cons .lit .nil))
    have c3 : C (.app succC (natAddC (litC a) (litC b))) (.app succC (litC (a + b))) natC :=
      cong_succ (hty_natAdd .lit .lit) (conv_add a b)
    have c4 : C (.app succC (litC (a + b))) (litC (a + b + 1)) natC := .symm .litS
    rw [show a + 1 + b = a + b + 1 by omega]
    exact .trans c1 (.trans c2 (.trans c3 c4))

theorem conv_ble : ∀ a b : Nat, C (bleC (litC a) (litC b)) (boolC (decide (a ≤ b))) boolTy
  | 0, b => by
    have c1 : C (bleC (litC 0) (litC b)) (bleC zeroC (litC b)) boolTy := cong_ble .lit .lit .lit0 (refl' .lit)
    have c2 : C (bleC zeroC (litC b)) (boolC true) boolTy :=
      .inst (t := bleZ) (as := [litC b]) (by simp [thms]) (.cons .lit .nil)
    simpa using Conv.trans c1 c2
  | a + 1, 0 => by
    have c1 : C (bleC (litC (a + 1)) (litC 0)) (bleC (.app succC (litC a)) zeroC) boolTy :=
      cong_ble .lit .lit .litS .lit0
    have c2 : C (bleC (.app succC (litC a)) zeroC) (boolC false) boolTy :=
      .inst (t := bleSZ) (as := [litC a]) (by simp [thms]) (.cons .lit .nil)
    simpa using Conv.trans c1 c2
  | a + 1, b + 1 => by
    have c1 : C (bleC (litC (a + 1)) (litC (b + 1))) (bleC (.app succC (litC a)) (.app succC (litC b))) boolTy :=
      cong_ble .lit .lit .litS .litS
    have c2 : C (bleC (.app succC (litC a)) (.app succC (litC b))) (bleC (litC a) (litC b)) boolTy :=
      .inst (t := bleSS) (as := [litC a, litC b]) (by simp [thms]) (.cons .lit (.cons .lit .nil))
    have := Conv.trans c1 (Conv.trans c2 (conv_ble a b))
    simpa using this

theorem conv_mod (k M : Nat) (h : k < M) : C (natModC (litC k) (ofNatNatC (litC M))) (litC k) natC := by
  obtain ⟨j, rfl⟩ : ∃ j, M = k + (j + 1) := ⟨M - k - 1, by omega⟩
  have c1 : C (ofNatNatC (litC (k + (j + 1)))) (litC (k + (j + 1))) natC :=
    .inst (t := NanoDen.brLitN) (as := [litC (k + (j + 1))]) (by simp [thms]) (.cons .lit .nil)
  have c2 : C (litC (k + (j + 1))) (natAddC (litC k) (.app succC (litC j))) natC :=
    .symm (.trans (cong_natAdd .lit (hty_succ .lit) (refl' .lit) (.symm .litS)) (conv_add k (j + 1)))
  have c3 : C (natModC (litC k) (natAddC (litC k) (.app succC (litC j)))) (litC k) natC :=
    .inst (t := modSmall) (as := [litC k, litC j]) (by simp [thms]) (.cons .lit (.cons .lit .nil))
  exact .trans (cong_natMod .lit (hty_ofNatNat .lit) (refl' .lit) (.trans c1 c2)) c3

/-! ## more typing, and the run -/

theorem hty_litU (k : Nat) : HasTy tab eqs [] (litUC k) u64C :=
  HasTy.head (n := nm2 "OfNat" "ofNat") (us := [.zero])
    (h := ⟨[lu], [.sort (.succ pu), natC, apps (.const (nm "OfNat") [pu]) [.bvar 1, .bvar 0]], .bvar 2⟩)
    (as := [u64C, litC k, .app (.const (nm2 "UInt64" "instOfNat") []) (litC k)]) (by decide +kernel) rfl
    (.cons hty_u64C (.cons .lit (.cons (HasTy.head (n := nm2 "UInt64" "instOfNat") (us := [])
      (h := ⟨[], [natC], apps (.const (nm "OfNat") [.zero]) [u64C, .bvar 0]⟩) (as := [litC k]) (by decide +kernel) rfl
      (.cons .lit .nil)) .nil)))

theorem hty_rd {x : Expr} (hx : HasTy tab eqs [] x LU8c) : HasTy tab eqs [] (rdC x) u64C :=
  HasTy.head (n := nm "rd") (us := []) (h := ⟨[], [LU8c, u64C], u64C⟩) (as := [x, litUC 0]) (by decide +kernel) rfl
    (.cons hx (.cons (hty_litU 0) .nil))

theorem hty_lt {a b : Expr} (ha : HasTy tab eqs [] a u64C) (hb : HasTy tab eqs [] b u64C) :
    HasTy tab eqs [] (ltC a b) (.sort .zero) :=
  HasTy.head (n := nm2 "LT" "lt") (us := [.zero])
    (h := ⟨[lu], [.sort (.succ pu), .app (.const (nm "LT") [pu]) (.bvar 0), .bvar 1, .bvar 2], .sort .zero⟩)
    (as := [u64C, .const (nm "instLTUInt64") [], a, b]) (by decide +kernel) rfl
    (.cons hty_u64C (.cons (ty0 (by decide +kernel)) (.cons ha (.cons hb .nil))))

theorem hty_dec {a b : Expr} (ha : HasTy tab eqs [] a u64C) (hb : HasTy tab eqs [] b u64C) :
    HasTy tab eqs [] (decC a b) (.app (.const (nm "Decidable") []) (ltC a b)) :=
  HasTy.head (n := nm2 "UInt64" "decLt") (us := [])
    (h := ⟨[], [u64C, u64C], .app (.const (nm "Decidable") [])
      (apps (.const (nm2 "LT" "lt") [.zero]) [u64C, .const (nm "instLTUInt64") [], .bvar 1, .bvar 0])⟩)
    (as := [a, b]) (by decide +kernel) rfl (.cons ha (.cons hb .nil))

theorem hty_ite {c d t e : Expr} (hc : HasTy tab eqs [] c (.sort .zero))
    (hd : HasTy tab eqs [] d (.app (.const (nm "Decidable") []) c))
    (ht : HasTy tab eqs [] t u64C) (he : HasTy tab eqs [] e u64C) : HasTy tab eqs [] (iteC c d t e) u64C :=
  HasTy.head (n := nm "ite") (us := [L1])
    (h := ⟨[lu], [.sort pu, .sort .zero, .app (.const (nm "Decidable") []) (.bvar 0), .bvar 2, .bvar 3], .bvar 4⟩)
    (as := [u64C, c, d, t, e]) (by decide +kernel) rfl
    (.cons hty_u64C (.cons hc (.cons hd (.cons ht (.cons he .nil)))))

theorem hty_cond {c t e : Expr} (hc : HasTy tab eqs [] c boolTy) (ht : HasTy tab eqs [] t u64C)
    (he : HasTy tab eqs [] e u64C) : HasTy tab eqs [] (condC c t e) u64C :=
  HasTy.head (n := nm "cond") (us := [L1]) (h := ⟨[lu], [.sort pu, boolTy, .bvar 1, .bvar 2], .bvar 3⟩)
    (as := [u64C, c, t, e]) (by decide +kernel) rfl (.cons hty_u64C (.cons hc (.cons ht (.cons he .nil))))

theorem hty_put {o v : Expr} (ho : HasTy tab eqs [] o LU8c) (hv : HasTy tab eqs [] v u64C) :
    HasTy tab eqs [] (putC o v) LU8c :=
  HasTy.head (n := nm "put") (us := []) (h := ⟨[], [LU8c, u64C], LU8c⟩) (as := [o, v]) (by decide +kernel) rfl
    (.cons ho (.cons hv .nil))

theorem cong_u64of {a a' : Expr} (ha : HasTy tab eqs [] a natC) (c : C a a' natC) : C (u64ofC a) (u64ofC a') u64C :=
  .cong (h := .const (nm2 "UInt64" "ofNat") []) (as := [a]) (bs := [a']) (Ts := [natC]) (hty_u64of ha) (.cons c .nil)

theorem cong_cond {c t e c' t' e' : Expr} (hc : HasTy tab eqs [] c boolTy) (ht : HasTy tab eqs [] t u64C)
    (he : HasTy tab eqs [] e u64C) (k1 : C c c' boolTy) (k2 : C t t' u64C) (k3 : C e e' u64C) :
    C (condC c t e) (condC c' t' e') u64C :=
  .cong (h := .const (nm "cond") [L1]) (Ts := [.sort L1, boolTy, u64C, u64C]) (hty_cond hc ht he)
    (.cons (refl' hty_u64C) (.cons k1 (.cons k2 (.cons k3 .nil))))

theorem cong_put {o v v' : Expr} (ho : HasTy tab eqs [] o LU8c) (hv : HasTy tab eqs [] v u64C) (k : C v v' u64C) :
    C (putC o v) (putC o v') LU8c :=
  .cong (h := .const (nm "put") []) (Ts := [LU8c, u64C]) (hty_put ho hv) (.cons (refl' ho) (.cons k .nil))

/-- `rd x 0` on the encoded input -/
theorem conv_rd (inp : List UInt8) : C (rdC (encL inp)) (u64ofC (litC (inp.getD 0 0).toNat)) u64C := by
  cases inp with
  | nil =>
    have c1 : C (rdC nilC) (u64ofC (ofNatNatC (litC 0))) u64C := .inst (t := rdNil0) (as := []) (by simp [thms]) .nil
    have c3 : C (ofNatNatC (litC 0)) (litC 0) natC :=
      .inst (t := NanoDen.brLitN) (as := [litC 0]) (by simp [thms]) (.cons .lit .nil)
    have c2 : C (u64ofC (ofNatNatC (litC 0))) (u64ofC (litC 0)) u64C := cong_u64of (hty_ofNatNat .lit) c3
    have e : (([] : List UInt8).getD 0 0).toNat = 0 := rfl
    rw [e]; exact Conv.trans c1 c2
  | cons b l =>
    have hb := b.toNat_lt
    have c1 : C (rdC (consC (u8ofC (litC b.toNat)) (encL l))) (toU64C (u8ofC (litC b.toNat))) u64C :=
      .inst (t := rdCons0) (as := [u8ofC (litC b.toNat), encL l]) (by simp [thms])
        (.cons (hty_u8of .lit) (.cons (hty_encL l) .nil))
    have c2 : C (toU64C (u8ofC (litC b.toNat))) (u64ofC (natModC (litC b.toNat) (ofNatNatC (litC 256)))) u64C :=
      .inst (t := u8u64) (as := [litC b.toNat]) (by simp [thms]) (.cons .lit .nil)
    have c3 : C (u64ofC (natModC (litC b.toNat) (ofNatNatC (litC 256)))) (u64ofC (litC b.toNat)) u64C :=
      cong_u64of (hty_natMod .lit (hty_ofNatNat .lit)) (conv_mod b.toNat 256 hb)
    have e : (b :: l).getD 0 0 = b := rfl
    rw [e]; exact Conv.trans c1 (Conv.trans c2 c3)

def outV (a : Nat) : Nat := if 5 ≤ a then 2 else 1

/-- the `ite` on literals evaluates in the model -/
theorem conv_ite (a : Nat) (ha : a < big) :
    C (iteC (ltC (u64ofC (litC a)) (u64ofC (litC 5))) (decC (u64ofC (litC a)) (u64ofC (litC 5))) (litUC 1) (litUC 2))
      (litUC (outV a)) u64C := by
  have c1 : C (iteC (ltC (u64ofC (litC a)) (u64ofC (litC 5))) (decC (u64ofC (litC a)) (u64ofC (litC 5))) (litUC 1) (litUC 2))
      (condC (bleC (natModC (litC 5) (ofNatNatC (litC big))) (natModC (litC a) (ofNatNatC (litC big)))) (litUC 2) (litUC 1)) u64C :=
    .inst (t := iteLt) (as := [litC a, litC 5, litUC 1, litUC 2]) (by simp [thms])
      (.cons .lit (.cons .lit (.cons (hty_litU 1) (.cons (hty_litU 2) .nil))))
  have h5 : HasTy tab eqs [] (natModC (litC 5) (ofNatNatC (litC big))) natC := hty_natMod .lit (hty_ofNatNat .lit)
  have ha' : HasTy tab eqs [] (natModC (litC a) (ofNatNatC (litC big))) natC := hty_natMod .lit (hty_ofNatNat .lit)
  have c2 := cong_cond (hty_ble h5 ha') (hty_litU 2) (hty_litU 1)
    (Conv.trans (cong_ble h5 ha' (conv_mod 5 big (by decide)) (conv_mod a big ha)) (conv_ble 5 a))
    (refl' (hty_litU 2)) (refl' (hty_litU 1))
  refine .trans c1 (.trans c2 ?_)
  unfold outV
  by_cases h : 5 ≤ a
  · simp only [h, decide_true, if_true]
    exact .inst (t := condT) (as := [litUC 2, litUC 1]) (by simp [thms]) (.cons (hty_litU 2) (.cons (hty_litU 1) .nil))
  · simp only [h, decide_false, if_false]
    exact .inst (t := condF) (as := [litUC 2, litUC 1]) (by simp [thms]) (.cons (hty_litU 2) (.cons (hty_litU 1) .nil))

theorem outL_toNat (inp : List UInt8) : (NanoL.outL inp).toNat = outV (inp.getD 0 0).toNat := by
  unfold NanoL.outL outV
  generalize inp.getD 0 0 = b
  have hb := b.toNat_lt
  by_cases h : 5 ≤ b.toNat
  · have : ¬ b.toUInt64 < 5 := by
      rw [UInt64.lt_iff_toNat_lt]; simp; omega
    rw [if_neg this, if_pos h]; rfl
  · have : b.toUInt64 < 5 := by
      rw [UInt64.lt_iff_toNat_lt]; simp; omega
    rw [if_pos this, if_neg h]; rfl

/-- **the run of `m` on any input, as an equational derivation in the model** -/
theorem run (inp : List UInt8) : C (.app (.const (nm "m") []) (encL inp)) (encL [NanoL.outL inp]) LU8c := by
  have hx := hty_encL inp
  have hR := hty_rd hx
  have h5 := hty_litU 5
  have ha : (inp.getD 0 0).toNat < big := by have := (inp.getD 0 0).toNat_lt; unfold big; omega
  have c0 : C (.app (.const (nm "m") []) (encL inp)) (bodyL (encL inp)) LU8c :=
    .inst (t := mEqL) (as := [encL inp]) (by simp [thms]) (.cons hx .nil)
  have cR := conv_rd inp
  have c5 : C (litUC 5) (u64ofC (litC 5)) u64C := .inst (t := lit64) (as := [litC 5]) (by simp [thms]) (.cons .lit .nil)
  have hinst : HasTy tab eqs [] (.const (nm "instLTUInt64") []) (.app (.const (nm "LT") [.zero]) u64C) :=
    ty0 (by decide +kernel)
  have cLt : C (ltC (rdC (encL inp)) (litUC 5)) (ltC (u64ofC (litC (inp.getD 0 0).toNat)) (u64ofC (litC 5))) (.sort .zero) :=
    .cong (h := .const (nm2 "LT" "lt") [.zero]) (Ts := [.sort L1, .app (.const (nm "LT") [.zero]) u64C, u64C, u64C])
      (hty_lt hR h5) (.cons (refl' hty_u64C) (.cons (refl' hinst) (.cons cR (.cons c5 .nil))))
  have cDec : C (decC (rdC (encL inp)) (litUC 5)) (decC (u64ofC (litC (inp.getD 0 0).toNat)) (u64ofC (litC 5)))
      (.app (.const (nm "Decidable") []) (ltC (rdC (encL inp)) (litUC 5))) :=
    .cong (h := .const (nm2 "UInt64" "decLt") []) (Ts := [u64C, u64C]) (hty_dec hR h5) (.cons cR (.cons c5 .nil))
  have hIte := hty_ite (hty_lt hR h5) (hty_dec hR h5) (hty_litU 1) (hty_litU 2)
  have cIte : C (iteC (ltC (rdC (encL inp)) (litUC 5)) (decC (rdC (encL inp)) (litUC 5)) (litUC 1) (litUC 2))
      (litUC (outV (inp.getD 0 0).toNat)) u64C :=
    .trans (.cong (h := .const (nm "ite") [L1])
        (Ts := [.sort L1, .sort .zero, .app (.const (nm "Decidable") []) (ltC (rdC (encL inp)) (litUC 5)), u64C, u64C])
        hIte (.cons (refl' hty_u64C) (.cons cLt (.cons cDec (.cons (refl' (hty_litU 1)) (.cons (refl' (hty_litU 2)) .nil))))))
      (conv_ite _ ha)
  have cPut : C (bodyL (encL inp)) (putC nilC (litUC (outV (inp.getD 0 0).toNat))) LU8c := cong_put hty_nil hIte cIte
  have cL : C (putC nilC (litUC (outV (inp.getD 0 0).toNat))) (putC nilC (u64ofC (litC (outV (inp.getD 0 0).toNat)))) LU8c :=
    cong_put hty_nil (hty_litU _) (.inst (t := lit64) (as := [litC _]) (by simp [thms]) (.cons .lit .nil))
  have cN : C (putC nilC (u64ofC (litC (outV (inp.getD 0 0).toNat))))
      (consC (u8ofC (litC (outV (inp.getD 0 0).toNat))) nilC) LU8c :=
    .inst (t := putNil) (as := [litC _]) (by simp [thms]) (.cons .lit .nil)
  have e : encL [NanoL.outL inp] = consC (u8ofC (litC (outV (inp.getD 0 0).toNat))) nilC := by
    simp only [encL, byteC, u8ofC, litC, outL_toNat]
  rw [e]
  exact .trans c0 (.trans cPut (.trans cL cN))

/-! ## the semantic side -/

section
variable {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
  (acc : Cached.checkDecls .verified pins ds = .ok env) (hnat : natLitSupported env = true)
  (hind : IndStored env (IndHeads.blockHeads blocksL)) (hrec : recsOkL ds = true) (M : Model V env)
include acc hnat hind hrec

theorem tabOk : TabOk M tab := by
  simp only [recsOkL, Bool.and_eq_true, List.all_eq_true] at hrec
  have hs : ∀ p ∈ tabL, HeadSem M p.1 p.2 := by
    obtain ⟨h1, h2, h3⟩ := headSem_nat M hnat
    intro p hp
    simp only [tabL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (((rfl | rfl | rfl) | hd) | hr) | hi
    · exact h1
    · exact h2
    · exact h3
    · exact headSem_defn acc M (any_def (hrec.1 p (List.mem_append_left _ hd))) (by
        simp only [defHeads, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    · exact headSem_defn acc M (any_def (hrec.1 p (List.mem_append_right _ hr))) (by
        simp only [defHeadsL, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          decide +kernel)
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

theorem thmsOk : ThmsOk ds tab eqs thms := by
  simp only [recsOkL, Bool.and_eq_true, List.all_eq_true] at hrec
  intro t ht
  exact ⟨any_thm (hrec.2 t (List.mem_cons_of_mem _ ht)), 40, thms_ok t ht⟩

theorem eqsOk (hP : CvalParams M) : EqsOk M eqs := by
  intro p hp
  simp only [eqs, List.mem_singleton] at hp; subst hp
  refine ⟨rfl, rfl, fun φ ρ X hX => ?_⟩
  have ht := tabOk acc hnat hind hrec M
  have h0 : EqsOk M ([] : List (Expr × Expr)) := fun _ h => by cases h
  have tyA : HasTy tab [] [] (.app (.const AddOne.outParamN [AddOne.L2]) (.sort AddOne.L1)) (.sort AddOne.L2) :=
    infer_sound 40 _ _ (by decide +kernel)
  obtain ⟨Y, -, dY, -, -⟩ := sound hP hnat ht h0 (Γ := []) (φ := φ) (ρ := ρ) (fun _ _ h => by simp at h) tyA
  simp only [recsOkL, Bool.and_eq_true, List.all_eq_true] at hrec
  have hrec3 := any_thm (hrec.2 NanoRDen.opEqT List.mem_cons_self)
  have := etransfer acc hP hnat ht h0 (Ts := []) hrec3 (by decide) (by decide)
    (infer_sound 40 _ _ (by decide +kernel)) tyA (infer_sound 40 _ _ (by decide +kernel))
    φ ρ .nil dY hX
  rw [← this]; exact dY

/-- **the emitted `m` on any input denotes the encoding of `[outL inp]`** -/
theorem den_mL (hP : CvalParams M) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (inp : List UInt8) :
    ∃ x, Denotes M.cval env φ ρ (encL inp) x ∧
      ∀ Y, Denotes M.cval env φ ρ (encL [NanoL.outL inp]) Y →
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

end Bridge.Real.NanoLDen
