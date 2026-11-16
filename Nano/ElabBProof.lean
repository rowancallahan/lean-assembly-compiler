import Nano.ElabB
/- Stage 1 of nanoElabB: `decL (lexB xs) = lexT xs` for every byte list `xs`. -/
namespace Nano.B
open Nano

/-! ## The word automaton and the packed word -/

def dstep (d : UInt64) (c : UInt8) : UInt64 := DSTEP d, c
def wstep (w : UInt64) (c : UInt8) : UInt64 := WSTEP w, c
def kindOf (d w : UInt64) : UInt64 := KIND d, w
def tyu (ty w : UInt64) : UInt64 := TYU w
def dfa (u : List UInt8) : UInt64 := u.foldl dstep 0
def pk (u : List UInt8) : UInt64 := u.foldl wstep 1
def packN (u : List UInt8) : Nat := u.foldl (fun a c => a * 256 + c.toNat) 1

theorem snoc_ind {α : Type} {P : List α → Prop} (h0 : P []) (h1 : ∀ u c, P u → P (u ++ [c])) : ∀ u, P u := by
  intro u; rw [← List.reverse_reverse u]; generalize u.reverse = v
  induction v with
  | nil => exact h0
  | cons c v ih => rw [List.reverse_cons]; exact h1 _ _ ih

theorem orpack (a : UInt64) (c : UInt8) (h : a.toNat < 2^56) :
    ((a <<< 8) ||| c.toUInt64).toNat = a.toNat * 256 + c.toNat := by
  have hc := c.toNat_lt
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft]
  simp only [UInt64.toNat_ofNat, UInt8.toNat_toUInt64]
  rw [show 8 % 2 ^ 64 % 64 = 8 by rfl, Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]

theorem packN_append (u : List UInt8) (c : UInt8) : packN (u ++ [c]) = packN u * 256 + c.toNat := by
  simp [packN, List.foldl_append]

theorem packN_ge (u : List UInt8) : 256 ^ u.length ≤ packN u ∧ packN u < 256 ^ (u.length + 1) := by
  induction u using snoc_ind with
  | h0 => simp [packN]
  | h1 u c ih =>
    rw [packN_append]; have := c.toNat_lt; simp only [List.length_append, List.length_singleton, Nat.pow_succ] at ih ⊢
    omega

theorem pk_short : ∀ (u : List UInt8), u.length ≤ 7 → (pk u).toNat = packN u := by
  intro u
  induction u using snoc_ind with
  | h0 => intro; rfl
  | h1 u c ih =>
    intro h
    simp only [List.length_append, List.length_singleton] at h
    have ih := ih (by omega)
    have hb := (packN_ge u).2
    have : packN u < 2 ^ 56 := Nat.lt_of_lt_of_le hb (by
      rw [show (2:Nat) ^ 56 = 256 ^ 7 by rfl]; exact Nat.pow_le_pow_right (by omega) (by omega))
    simp only [pk, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [packN_append]
    generalize List.foldl wstep 1 u = W at ih ⊢
    unfold wstep
    rw [if_pos (by rw [UInt64.lt_iff_toNat_lt, ih]; simpa using this), orpack _ _ (by rw [ih]; exact this), ih]

theorem pk_snoc (u : List UInt8) (c : UInt8) : pk (u ++ [c]) = wstep (pk u) c := by
  simp [pk, List.foldl_append]

theorem pk_long : ∀ (u : List UInt8), 8 ≤ u.length → pk u = 0x8000000000000000 := by
  intro u
  induction u using snoc_ind with
  | h0 => intro h; simp at h
  | h1 u c ih =>
    intro h
    simp only [List.length_append, List.length_singleton] at h
    rw [pk_snoc]
    unfold wstep
    by_cases h8 : 8 ≤ u.length
    · rw [ih h8]; rfl
    · have e := pk_short u (by omega)
      have hb := (packN_ge u).1
      have : 2 ^ 56 ≤ packN u := Nat.le_trans (by
        rw [show (2:Nat) ^ 56 = 256 ^ 7 by rfl]; exact Nat.pow_le_pow_right (by omega) (by omega)) hb
      rw [if_neg (by rw [UInt64.lt_iff_toNat_lt, e]; simp; omega)]

theorem packN_nil : packN [] = 1 := rfl

theorem packN_inj : ∀ (u v : List UInt8), packN u = packN v → u = v := by
  intro u
  induction u using snoc_ind with
  | h0 =>
    intro v h
    rcases List.eq_nil_or_concat v with hv | ⟨v', e, hv⟩
    · exact hv.symm
    · subst hv; simp only [List.concat_eq_append] at *
      have := (packN_ge v').1; rw [packN_nil, packN_append] at h
      have : 1 ≤ 256 ^ v'.length := Nat.one_le_pow _ _ (by omega)
      omega
  | h1 u c ih =>
    intro v h
    rcases List.eq_nil_or_concat v with hv | ⟨v', e, hv⟩
    · subst hv; have := (packN_ge u).1; rw [packN_append, packN_nil] at h
      have : 1 ≤ 256 ^ u.length := Nat.one_le_pow _ _ (by omega)
      omega
    · subst hv; simp only [List.concat_eq_append] at *; rw [packN_append, packN_append] at h
      have hc := c.toNat_lt; have he := e.toNat_lt
      have h1 : c.toNat = e.toNat := by omega
      have h2 : packN u = packN v' := by omega
      rw [ih v' h2, UInt8.toNat_inj.mp h1]

/-- the packed word decides equality with a word of at most 6 characters -/
theorem pk_beq (u v : List UInt8) (hv : v.length ≤ 6) : (pk u == pk v) = (u == v) := by
  by_cases hu : u.length ≤ 7
  · have e1 := pk_short u hu; have e2 := pk_short v (by omega)
    by_cases h : u = v
    · subst h; simp
    · have : pk u ≠ pk v := fun h' => h (packN_inj _ _ (by rw [← e1, ← e2, h']))
      rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]
  · rw [pk_long u (by omega)]
    have e2 := pk_short v (by omega)
    have hb := (packN_ge v).2
    have : packN v < 2 ^ 56 := Nat.lt_of_lt_of_le hb (by
      rw [show (2:Nat) ^ 56 = 256 ^ 7 by rfl]; exact Nat.pow_le_pow_right (by omega) (by omega))
    have hne : (0x8000000000000000 : UInt64) ≠ pk v := by
      intro h; rw [← h] at e2; simp at e2; omega
    have hne2 : u ≠ v := by intro h; subst h; omega
    rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hne2]

/-! ## The name-shape automaton is `nameShape` -/

theorem u8_all {P : UInt8 → Prop} (h : ∀ n, n < 256 → P (UInt8.ofNat n)) : ∀ c, P c := fun c => by
  have := h c.toNat c.toNat_lt; simpa using this

def acc (s : UInt64) (r : List UInt8) : Bool := 1 ≤ r.foldl dstep s && r.foldl dstep s ≤ 4

theorem acc_cons (s : UInt64) (c : UInt8) (r : List UInt8) : acc s (c :: r) = acc (dstep s c) r := rfl

theorem dstep6 : ∀ c, dstep 6 c = 6 := u8_all (by decide +kernel)
theorem dstep4 : ∀ c, dstep 4 c = (if isDigit c then 4 else if c == 95 then 5 else 6) := u8_all (by decide +kernel)
theorem dstep5 : ∀ c, dstep 5 c = (if isDigit c then 4 else 6) := u8_all (by decide +kernel)
theorem dstep3 : ∀ c, dstep 3 c = dstep 4 c := u8_all (by decide +kernel)
theorem dstep12 : ∀ c, isLower c = false → dstep 1 c = dstep 4 c ∧ dstep 2 c = dstep 4 c := u8_all (by decide +kernel)
theorem dstepL : ∀ c, isLower c = true → dstep 1 c = 2 ∧ dstep 2 c = 3 := u8_all (by decide +kernel)
theorem dstep0 : ∀ c, dstep 0 c = (if isLower c then 1 else 6) := u8_all (by decide +kernel)
theorem nameTail1 : ∀ c, nameTail [c] = isDigit c := u8_all (by decide +kernel)

theorem dead : ∀ r, acc 6 r = false
  | [] => rfl
  | c :: r => by rw [acc_cons, dstep6]; exact dead r

theorem nameTail_cons (c : UInt8) (r : List UInt8) : nameTail (c :: r) =
    if c = 95 then (match r with | d :: r' => isDigit d && nameTail r' | [] => false) else (isDigit c && nameTail r) := by
  rcases r with _ | ⟨d, r⟩
  · by_cases h : c = 95
    · subst h; rfl
    · rw [if_neg h, nameTail1 c]; cases isDigit c <;> rfl
  · by_cases h : c = 95
    · subst h; rfl
    · rw [if_neg h]; conv => lhs; rw [nameTail.eq_def]
      split <;> simp_all

theorem acc45 : ∀ r, acc 4 r = nameTail r ∧ acc 5 r = (match r with | d :: r' => isDigit d && nameTail r' | [] => false)
  | [] => by decide
  | c :: r => by
    have ih := acc45 r
    rw [acc_cons, acc_cons, dstep4, dstep5, nameTail_cons]
    by_cases hd : isDigit c = true
    · have h95 : c ≠ 95 := by intro h; subst h; exact absurd hd (by decide)
      simp [hd, h95, ih.1]
    · simp only [hd, Bool.false_eq_true, if_false, Bool.false_and]
      by_cases h95 : c = 95
      · subst h95; simp [ih.2, dead]
      · simp [h95, dead]

theorem acc3 (r : List UInt8) : acc 3 r = nameTail r := by
  rcases r with _ | ⟨c, r⟩
  · rfl
  · rw [acc_cons, dstep3, ← acc_cons, (acc45 _).1]

theorem tailStep (d : UInt64) (c : UInt8) (r : List UInt8) (hd : d = 1 ∨ d = 2) (hc : isLower c = false) :
    acc (dstep d c) r = nameTail (c :: r) := by
  have := dstep12 c hc
  rcases hd with h | h <;> subst h <;> simp only [this.1, this.2] <;> rw [← acc_cons, (acc45 _).1]

/-- **the automaton decides `nameShape`** -/
theorem nameShape_acc (u : List UInt8) : nameShape u = acc 0 u := by
  match u with
  | [] => rfl
  | [a] => rw [acc_cons, dstep0]; by_cases h : isLower a = true <;> simp [nameShape, h, acc]
  | [a, b] =>
    rw [acc_cons, dstep0]
    by_cases h : isLower a = true
    · simp only [nameShape, h, if_true, Bool.true_and]
      by_cases hb : isLower b = true
      · rw [acc_cons, (dstepL b hb).1]; simp [hb, acc]
      · simp only [Bool.not_eq_true] at hb
        rw [acc_cons, (dstep12 b hb).1, ← acc_cons, (acc45 _).1, nameTail1, hb]; rfl
    · simp only [Bool.not_eq_true] at h; simp [nameShape, h, dead]
  | a :: b :: c :: r =>
    rw [acc_cons, dstep0]
    by_cases h : isLower a = true
    · simp only [nameShape, h, if_true, Bool.true_and]
      by_cases hb : isLower b = true
      · rw [acc_cons, (dstepL b hb).1, if_pos hb]
        by_cases hc : isLower c = true
        · rw [acc_cons, (dstepL c hc).2, if_pos hc, acc3]
        · simp only [Bool.not_eq_true] at hc; rw [if_neg (by simp [hc]), acc_cons, tailStep 2 c r (by simp) hc]
      · simp only [Bool.not_eq_true] at hb; rw [if_neg (by simp [hb]), acc_cons, tailStep 1 b _ (by simp) hb]
    · simp only [Bool.not_eq_true] at h; simp [nameShape, h, dead]

/-! ## Word classification: `KIND` is `identTok?` -/

def kindTok (k : UInt64) (u : List UInt8) : Option Tok :=
  if k = 0 then some (.id u) else if k = 1 then some .kdef else if k = 2 then some .klet
  else if k = 3 then some (.kty false) else if k = 4 then some (.kty true) else none

theorem pkConsts :
  (0x1646566 : UInt64) = pk [100, 101, 102] ∧
  (0x16c6574 : UInt64) = pk [108, 101, 116] ∧
  (0x155496e743634 : UInt64) = pk [85, 73, 110, 116, 54, 52] ∧
  (0x1496e743634 : UInt64) = pk [73, 110, 116, 54, 52] ∧
  (0x1616e64 : UInt64) = pk [97, 110, 100] ∧
  (0x16174 : UInt64) = pk [97, 116] ∧
  (0x1626966 : UInt64) = pk [98, 105, 102] ∧
  (0x1626e65 : UInt64) = pk [98, 110, 101] ∧
  (0x16279 : UInt64) = pk [98, 121] ∧
  (0x1646f : UInt64) = pk [100, 111] ∧
  (0x1656e64 : UInt64) = pk [101, 110, 100] ∧
  (0x1666f72 : UInt64) = pk [102, 111, 114] ∧
  (0x166756e : UInt64) = pk [102, 117, 110] ∧
  (0x1676574 : UInt64) = pk [103, 101, 116] ∧
  (0x16964 : UInt64) = pk [105, 100] ∧
  (0x16966 : UInt64) = pk [105, 102] ∧
  (0x1696e : UInt64) = pk [105, 110] ∧
  (0x1697465 : UInt64) = pk [105, 116, 101] ∧
  (0x16d6178 : UInt64) = pk [109, 97, 120] ∧
  (0x16d696e : UInt64) = pk [109, 105, 110] ∧
  (0x16d74 : UInt64) = pk [109, 116] ∧
  (0x16d7574 : UInt64) = pk [109, 117, 116] ∧
  (0x16e6f74 : UInt64) = pk [110, 111, 116] ∧
  (0x16f72 : UInt64) = pk [111, 114] ∧
  (0x172666c : UInt64) = pk [114, 102, 108] ∧
  (0x1736574 : UInt64) = pk [115, 101, 116] ∧
  (0x1747279 : UInt64) = pk [116, 114, 121] ∧
  (0x1786f72 : UInt64) = pk [120, 111, 114] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem classify (u : List UInt8) : kindTok (kindOf (dfa u) (pk u)) u = identTok? u := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24,
    e25, e26, e27, e28⟩ := pkConsts
  unfold kindOf
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24,
    e25, e26, e27, e28]
  simp (disch := decide) only [pk_beq]
  have hn : (1 ≤ dfa u && dfa u ≤ 4) = nameShape u := by rw [nameShape_acc]; rfl
  rw [hn]
  unfold identTok? kindTok
  by_cases h1 : u = [100, 101, 102]
  · subst h1; rfl
  by_cases h2 : u = [108, 101, 116]
  · subst h2; rfl
  by_cases h3 : u = [85, 73, 110, 116, 54, 52]
  · subst h3; rfl
  by_cases h4 : u = [73, 110, 116, 54, 52]
  · subst h4; rfl
  have k1 : (u == kwDef) = false := by simp [kwDef, h1]
  have k2 : (u == kwLet) = false := by simp [kwLet, h2]
  have k3 : (u == kwTy) = false := by simp [kwTy, h3]
  have k4 : (u == kwTyI) = false := by simp [kwTyI, h4]
  have k1' : (u == [100, 101, 102]) = false := k1
  have k2' : (u == [108, 101, 116]) = false := k2
  have k3' : (u == [85, 73, 110, 116, 54, 52]) = false := k3
  have k4' : (u == [73, 110, 116, 54, 52]) = false := k4
  simp only [k1, k2, k3, k4, k1', k2', k3', k4', Bool.false_eq_true, if_false]
  have hr : reserved.contains u = (u == [97, 110, 100] || u == [97, 116] || u == [98, 105, 102] || u == [98, 110, 101] ||
      u == [98, 121] || u == [100, 111] || u == [101, 110, 100] || u == [102, 111, 114] || u == [102, 117, 110] ||
      u == [103, 101, 116] || u == [105, 100] || u == [105, 102] || u == [105, 110] || u == [105, 116, 101] ||
      u == [109, 97, 120] || u == [109, 105, 110] || u == [109, 116] || u == [109, 117, 116] || u == [110, 111, 116] ||
      u == [111, 114] || u == [114, 102, 108] || u == [115, 101, 116] || u == [116, 114, 121] || u == [120, 111, 114]) := by
    simp only [reserved, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_assoc]
  rw [hr]
  cases (u == [97, 110, 100] || u == [97, 116] || u == [98, 105, 102] || u == [98, 110, 101] ||
      u == [98, 121] || u == [100, 111] || u == [101, 110, 100] || u == [102, 111, 114] || u == [102, 117, 110] ||
      u == [103, 101, 116] || u == [105, 100] || u == [105, 102] || u == [105, 110] || u == [105, 116, 101] ||
      u == [109, 97, 120] || u == [109, 105, 110] || u == [109, 116] || u == [109, 117, 116] || u == [110, 111, 116] ||
      u == [111, 114] || u == [114, 102, 108] || u == [115, 101, 116] || u == [116, 114, 121] || u == [120, 111, 114]) <;>
    cases nameShape u <;> simp

end Nano.B
