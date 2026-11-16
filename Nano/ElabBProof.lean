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

/-! ## The machine against `lex`, token by token -/

/-- `lex`'s fuel `F` against the rest `xs`: equal (`sp = 0`) or larger (`sp = 1`) -/
def Fu (F : Nat) (xs : List UInt8) (sp : UInt64) : Prop := (sp = 0 ∧ F = xs.length) ∨ (sp = 1 ∧ xs.length < F)
def tyOf (ty : UInt64) : Option Bool := if ty = 1 then some false else if ty = 2 then some true else none
def tcode (s : Bool) : UInt64 := if s then 2 else 1
def tyStep (ty : UInt64) : Tok → UInt64
  | .kty false => if ty = 2 then 9 else 1
  | .kty true => if ty = 1 then 9 else 2
  | _ => ty
/-- pass 1's result from a `lex` result and the type so far -/
def R1 (o : List UInt8) (r : Option (List Tok)) (ty : UInt64) : List UInt8 :=
  match r with
  | none => [0]
  | some ts => match uniTy (tyOf ty) ts with
    | none => [0]
    | some s => (tcode s).toUInt8 :: lx o o 1 0 0 0 0 0 (tcode s)

theorem lx_nil (o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx [] o m 0 sp d d0 w ty = if m == 0 then (if ty == 0 then [0] else ty.toUInt8 :: lx o o 1 0 0 0 0 0 ty) else [] := by
  rw [lx]

theorem lex_nil (F : Nat) : lex F [] = some [] := by cases F <;> rfl

theorem lx_c2 (c n : UInt8) (t o : List UInt8) (m st sp d d0 w ty : UInt64) :
    lx (c :: n :: t) o m st sp d d0 w ty = STEPN := by rw [lx]
theorem lx_c1 (c : UInt8) (o : List UInt8) (m st sp d d0 w ty : UInt64) :
    lx [c] o m st sp d d0 w ty = STEPE := by rw [lx]

/-- `REC` of the end step, in each of its three forms, is `lx []` -/
theorem fin_eq (o : List UInt8) (m sp d d0 w ty : UInt64) :
    (if m == 0 then (if ty == 0 then [0] else (ty).toUInt8 :: lx o o 1 0 0 0 0 0 ty) else []) = lx [] o m 0 sp d d0 w ty := by
  rw [lx_nil]

theorem M_ws (c : UInt8) (hc : c = 32 ∨ c = 10) (rest o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx (c :: rest) o m 0 sp d d0 w ty = lx rest o m 0 sp d d0 w ty := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1, lx_nil]; rcases hc with h | h <;> subst h <;> simp
  · rw [lx_c2]; rcases hc with h | h <;> subst h <;> simp

theorem M_punct (c : UInt8) (hc : c = 40 ∨ c = 42 ∨ c = 43 ∨ c = 59) (rest o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx (c :: rest) o m 0 sp d d0 w ty = (if m = 0 then [] else [c]) ++ lx rest o m 0 sp d d0 w ty := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1, lx_nil]; rcases hc with h | h | h | h <;> subst h <;> by_cases hm : m = 0 <;> simp [hm]
  · rw [lx_c2]; rcases hc with h | h | h | h <;> subst h <;> by_cases hm : m = 0 <;> simp [hm]

theorem M_st2 (c : UInt8) (rest o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx (c :: rest) o m 2 sp d d0 w ty = lx rest o m 0 sp d d0 w ty := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1, lx_nil]; simp
  · rw [lx_c2]; simp

/-- the next byte is a word byte or `(` / `-`: `none`-like tests of `lex` -/
def hd? (r : List UInt8) (p : UInt8 → Bool) : Bool := match r with | x :: _ => p x | [] => false

theorem M_rp (rest o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx (41 :: rest) o m 0 sp d d0 w ty =
      if hd? rest (fun x => x == 40 || isW x) then [0] else (if m = 0 then [] else [41]) ++ lx rest o m 0 sp d d0 w ty := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1, lx_nil]; by_cases hm : m = 0 <;> simp [hm, hd?]
  · rw [lx_c2]; by_cases hm : m = 0 <;> by_cases hn : (n == 40 || isW n) = true <;> simp [hm, hd?, hn] <;> simp_all

theorem M_minus (rest o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx (45 :: rest) o m 0 sp d d0 w ty =
      if hd? rest (· == 45) then [0] else (if m = 0 then [] else [45]) ++ lx rest o m 0 sp d d0 w ty := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1, lx_nil]; by_cases hm : m = 0 <;> simp [hm, hd?]
  · rw [lx_c2]; by_cases hm : m = 0 <;> by_cases hn : n = 45 <;> simp [hm, hd?, hn]

theorem M_colon (rest o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx (58 :: rest) o m 0 sp d d0 w ty =
      match rest with
      | 61 :: r => (if m = 0 then [] else [61]) ++ lx r o m 0 1 d d0 w ty
      | _ => (if m = 0 then [] else [58]) ++ lx rest o m 0 sp d d0 w ty := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1, lx_nil]; by_cases hm : m = 0 <;> simp [hm]
  · rw [lx_c2]
    by_cases hn : n = 61
    · subst hn; by_cases hm : m = 0 <;> simp [hm, M_st2]
    · by_cases hm : m = 0 <;> simp [hm, hn]

theorem M_cr (rest o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx (13 :: rest) o m 0 sp d d0 w ty =
      match rest with
      | 10 :: r => lx r o m 0 1 d d0 w ty
      | _ => [0] := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1]; simp
  · rw [lx_c2]
    by_cases hn : n = 10
    · subst hn; simp [M_ws]
    · simp [hn]

/-! ### `lex`, one step per byte class -/

theorem L_ws (c : UInt8) (hc : c = 32 ∨ c = 10) (f : Nat) (xs : List UInt8) : lex (f + 1) (c :: xs) = lex f xs := by
  rcases hc with h | h <;> subst h <;> rw [lex.eq_def] <;> simp
theorem L_cr (f : Nat) (xs : List UInt8) :
    lex (f + 1) (13 :: xs) = match xs with | 10 :: ys => lex f ys | _ => none := by
  rw [lex.eq_def];   rcases xs with _ | ⟨a, ys⟩
  · rfl
  · by_cases h : a = 10
    · subst h; rfl
    · simp [h]
theorem L_punct (c : UInt8) (f : Nat) (xs : List UInt8) (t : Tok)
    (hc : (c = 40 ∧ t = .lp) ∨ (c = 42 ∧ t = .star) ∨ (c = 43 ∧ t = .plus) ∨ (c = 59 ∧ t = .semi)) :
    lex (f + 1) (c :: xs) = (lex f xs).map (t :: ·) := by
  rcases hc with ⟨h, ht⟩ | ⟨h, ht⟩ | ⟨h, ht⟩ | ⟨h, ht⟩ <;> subst h ht <;> rw [lex.eq_def] <;> simp
theorem L_rp (f : Nat) (xs : List UInt8) :
    lex (f + 1) (41 :: xs) = if hd? xs (fun x => x == 40 || isW x) then none else (lex f xs).map (Tok.rp :: ·) := by
  rw [lex.eq_def]; rcases xs with _ | ⟨d, xs⟩
  · simp [hd?]
  · have : (d == 40 || isLetter d || isDigit d) = (d == 40 || isW d) := by
      simp only [isW, isL, isLetter, isDigit, Bool.or_assoc]
    simp only [hd?, ← this]; simp
theorem L_minus (f : Nat) (xs : List UInt8) :
    lex (f + 1) (45 :: xs) = if hd? xs (· == 45) then none else (lex f xs).map (Tok.minus :: ·) := by
  rw [lex.eq_def]; rcases xs with _ | ⟨d, xs⟩ <;> simp [hd?]
  by_cases h : d = 45 <;> simp [h]
theorem L_colon (f : Nat) (xs : List UInt8) :
    lex (f + 1) (58 :: xs) = match xs with
      | 61 :: ys => (lex f ys).map (Tok.assign :: ·)
      | _ => (lex f xs).map (Tok.colon :: ·) := by
  rw [lex.eq_def];   rcases xs with _ | ⟨a, ys⟩
  · simp
  · by_cases h : a = 61
    · subst h; simp
    · simp [h]
theorem digitFacts : ∀ c : UInt8, isDigit c = true →
    (c == 32 || c == 10) = false ∧ (c == 13) = false ∧ (c == 40) = false ∧ (c == 41) = false ∧ (c == 43) = false ∧
    (c == 45) = false ∧ (c == 42) = false ∧ (c == 59) = false ∧ (c == 58) = false ∧
    (c == 40 || c == 42 || c == 43 || c == 59) = false ∧ isL c = false := u8_all (by decide +kernel)
theorem letterFacts : ∀ c : UInt8, isL c = true →
    (c == 32 || c == 10) = false ∧ (c == 13) = false ∧ (c == 40) = false ∧ (c == 41) = false ∧ (c == 43) = false ∧
    (c == 45) = false ∧ (c == 42) = false ∧ (c == 59) = false ∧ (c == 58) = false ∧
    (c == 40 || c == 42 || c == 43 || c == 59) = false ∧ isDigit c = false := u8_all (by decide +kernel)
theorem L_digit (c : UInt8) (hc : isDigit c = true) (f : Nat) (xs : List UInt8) :
    lex (f + 1) (c :: xs) = (let r := spanNum f 0 (c :: xs)
      match r.2 with
      | d :: _ => if isLetter d || d == 40 then none else (lex f r.2).map (Tok.num r.1 :: ·)
      | [] => (lex f r.2).map (Tok.num r.1 :: ·)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _, _⟩ := digitFacts c hc
  rw [lex.eq_def]; simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hc, Bool.false_eq_true, if_false, if_true]
  generalize spanNum f 0 (c :: xs) = r; rcases r with ⟨a, _ | ⟨d, t⟩⟩ <;> rfl
theorem L_letter (c : UInt8) (hc : isL c = true) (f : Nat) (xs : List UInt8) :
    lex (f + 1) (c :: xs) = (let r := spanId f (c :: xs)
      match identTok? r.1, r.2 with
      | _, 40 :: _ => none
      | some t, _ => (lex f r.2).map (t :: ·)
      | none, _ => none) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h11⟩ := letterFacts c hc
  have hl : isLetter c = true := hc
  rw [lex.eq_def]; simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h11, hl, Bool.false_eq_true, if_false, if_true]
  generalize spanId f (c :: xs) = r; rcases r with ⟨a, _ | ⟨d, t⟩⟩
  · cases identTok? a <;> rfl
  · by_cases h : d = 40
    · subst h; cases identTok? a <;> rfl
    · cases identTok? a <;> simp [h]
theorem L_other (c : UInt8) (hc : (c == 32 || c == 10 || c == 13 || c == 40 || c == 41 || c == 43 || c == 45 || c == 42 ||
    c == 59 || c == 58 || isDigit c || isL c) = false) (f : Nat) (xs : List UInt8) : lex (f + 1) (c :: xs) = none := by
  rw [lex.eq_def]; simp only [Bool.or_eq_false_iff] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := hc
  have h12' : isLetter c = false := h12
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12']

/-! ### numerals -/

def nstep (a : UInt64) (c : UInt8) : UInt64 := a * 10 + (c - 48).toUInt64

/-- the conclusion of `step0` -/
def S0 (o xs : List UInt8) (F : Nat) (sp m d d0 w ty : UInt64) : Prop :=
    (lex F xs = none ∧ (m = 0 → lx xs o m 0 sp d d0 w ty = [0])) ∨
    (∃ F' r sp' d' d0' w', r.length < xs.length ∧ Fu F' r sp' ∧ lex F xs = lex F' r ∧
      lx xs o m 0 sp d d0 w ty = lx r o m 0 sp' d' d0' w' ty) ∨
    (∃ t bs F' r sp' d' d0' w', r.length < xs.length ∧ Fu F' r sp' ∧ lex F xs = (lex F' r).map (t :: ·) ∧
      (∀ X, dec (bs ++ X) [] none = (dec X [] none).map (t :: ·)) ∧
      (tyStep ty t ≠ 9 → lx xs o m 0 sp d d0 w ty = (if m = 0 then [] else bs) ++ lx r o m 0 sp' d' d0' w' (tyStep ty t)) ∧
      (tyStep ty t = 9 → m = 0 → lx xs o m 0 sp d d0 w ty = [0]))

theorem isDigit_iff (c : UInt8) : (48 ≤ c && c ≤ 57) = isDigit c := rfl

theorem N_start2 (c n : UInt8) (hc : isDigit c = true) (hn : isDigit n = true) (t o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx (c :: n :: t) o m 0 sp d d0 w ty = (if m = 0 then [] else [5, c]) ++ lx (n :: t) o m 3 sp d d0 0 ty := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ := digitFacts c hc
  rw [lx_c2]; simp only [h1, h2, h9, h10, h4, h6, isDigit_iff, hc, hn]; by_cases hm : m = 0 <;> simp [hm]

theorem N_adv (x y : UInt8) (hy : isDigit y = true) (t o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx (x :: y :: t) o m 3 sp d d0 w ty = (if m = 0 then [] else [x]) ++ lx (y :: t) o m 3 sp d d0 1 ty := by
  rw [lx_c2]; simp only [isDigit_iff, hy]; by_cases hm : m = 0 <;> simp [hm]

theorem N_last (x y : UInt8) (hy : isDigit y = false) (t o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx (x :: y :: t) o m 3 sp d d0 w ty =
      if isL y || y == 40 then [0] else (if m = 0 then [] else [x, 6]) ++ lx (y :: t) o m 0 1 d d0 w ty := by
  rw [lx_c2]; simp only [isDigit_iff, hy]; by_cases hm : m = 0 <;> simp [hm]

theorem N_lastE (x : UInt8) (hx : isDigit x = true) (o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx [x] o m 3 sp d d0 w ty = if sp = 0 then (if w = 0 then [0] else (if m = 0 then [] else [6]) ++ lx [x] o m 0 1 d d0 w ty)
      else (if m = 0 then [] else [x, 6]) ++ lx [] o m 0 1 d d0 w ty := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := digitFacts x hx
  have h12 : (x == 40 || x == 41 || x == 42 || x == 43 || x == 45 || x == 59) = false := by
    simp only [Bool.or_eq_false_iff]; simp_all
  rw [lx_c1, lx_c1, lx_nil]; simp only [h1, h9, h12, isDigit_iff, hx]
  by_cases hm : m = 0 <;> by_cases hs : sp = 0 <;> by_cases hw : w = 0 <;> simp [hm, hs, hw]

theorem N_single (c n : UInt8) (hc : isDigit c = true) (hn : isDigit n = false) (t o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx (c :: n :: t) o m 0 sp d d0 w ty =
      if isL n || n == 40 then [0] else (if m = 0 then [] else [5, c, 6]) ++ lx (n :: t) o m 0 sp d d0 w ty := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ := digitFacts c hc
  rw [lx_c2]; simp only [h1, h2, h9, h10, h4, h6, isDigit_iff, hc, hn]; by_cases hm : m = 0 <;> simp [hm]

theorem N_singleE (c : UInt8) (hc : isDigit c = true) (o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx [c] o m 0 sp d d0 w ty = if sp = 0 then [0] else (if m = 0 then [] else [5, c, 6]) ++ lx [] o m 0 sp d d0 w ty := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ := digitFacts c hc
  have h11 : (c == 40 || c == 41 || c == 42 || c == 43 || c == 45 || c == 59) = false := by
    simp only [Bool.or_eq_false_iff]; simp_all
  rw [lx_c1, lx_nil]; simp only [h1, h9, h11, isDigit_iff, hc]
  by_cases hm : m = 0 <;> by_cases hs : sp = 0 <;> simp [hm, hs]

theorem NumRun (o : List UInt8) (m sp d d0 ty : UInt64) : ∀ (v : List UInt8) (x z : UInt8) (t : List UInt8) (w : UInt64),
    (∀ y ∈ v, isDigit y = true) → isDigit z = true →
    lx (x :: v ++ z :: t) o m 3 sp d d0 w ty = (if m = 0 then [] else x :: v) ++ lx (z :: t) o m 3 sp d d0 1 ty
  | [], x, z, t, w, _, hz => by
    simp only [List.cons_append, List.nil_append]; rw [N_adv x z hz]
  | y :: v, x, z, t, w, hv, hz => by
    have ih := NumRun o m sp d d0 ty v y z t 1 (fun q hq => hv q (by simp [hq])) hz
    simp only [List.cons_append] at ih ⊢
    rw [N_adv x y (hv y (by simp)), ih]
    by_cases hm : m = 0 <;> simp [hm]

theorem spanNum_eq : ∀ (u : List UInt8) (f : Nat) (a : UInt64) (r : List UInt8), (∀ y ∈ u, isDigit y = true) →
    hd? r isDigit = false → spanNum f a (u ++ r) = ((u.take f).foldl nstep a, u.drop f ++ r)
  | [], f, a, r, _, hr => by
    rcases r with _ | ⟨y, r⟩ <;> rcases f with _ | f <;> simp [spanNum, hd?] at hr ⊢
    simp [hr]
  | c :: u, f, a, r, hu, hr => by
    rcases f with _ | f
    · simp [spanNum]
    · simp only [List.cons_append, spanNum, hu c (by simp), if_true, List.take_succ_cons, List.foldl_cons, List.drop_succ_cons]
      exact spanNum_eq u f _ r (fun q hq => hu q (by simp [hq])) hr

theorem dec_num : ∀ (u : List UInt8) (a : UInt64) (wd X : List UInt8), (∀ y ∈ u, isDigit y = true) →
    dec (u ++ 6 :: X) wd (some a) = (dec X [] none).map (Tok.num (u.foldl nstep a) :: ·)
  | [], a, wd, X, _ => by simp [dec]
  | c :: u, a, wd, X, hu => by
    have hc := hu c (by simp)
    have h6 : (c == 6) = false := by
      have : ∀ c : UInt8, isDigit c = true → (c == 6) = false := u8_all (by decide +kernel)
      exact this c hc
    simp only [List.cons_append, dec, h6, Bool.false_eq_true, if_false, isDigit_iff, hc, if_true, List.foldl_cons]
    exact dec_num u _ [] X (fun q hq => hu q (by simp [hq]))

theorem dec_5 (Y : List UInt8) : dec (5 :: Y) [] none = dec Y [] (some 0) := by simp [dec, isW, isL]

theorem span_exists (p : UInt8 → Bool) : ∀ xs : List UInt8, ∃ u r, xs = u ++ r ∧ (∀ y ∈ u, p y = true) ∧ hd? r p = false
  | [] => ⟨[], [], rfl, by simp, rfl⟩
  | x :: xs => by
    by_cases hx : p x = true
    · obtain ⟨u, r, h1, h2, h3⟩ := span_exists p xs
      exact ⟨x :: u, r, by simp [h1], by simp [hx, h2]; exact h2, h3⟩
    · exact ⟨[], x :: xs, rfl, by simp, by simpa [hd?] using hx⟩

theorem NumStart (o : List UInt8) (m sp d d0 ty : UInt64) (c z : UInt8) (v t : List UInt8) (w : UInt64)
    (hc : isDigit c = true) (hv : ∀ y ∈ v, isDigit y = true) (hz : isDigit z = true) :
    lx (c :: (v ++ z :: t)) o m 0 sp d d0 w ty =
      (if m = 0 then [] else 5 :: c :: v) ++ lx (z :: t) o m 3 sp d d0 (if v = [] then 0 else 1) ty := by
  rcases v with _ | ⟨y, v⟩
  · rw [List.nil_append, N_start2 c z hc hz]; by_cases hm : m = 0 <;> simp [hm]
  · have := NumRun o m sp d d0 ty v y z t 0 (fun q hq => hv q (by simp [hq])) hz
    simp only [List.cons_append] at this ⊢
    rw [N_start2 c y hc (hv y (by simp)), this]; by_cases hm : m = 0 <;> simp [hm]

theorem dec_numTok (u X : List UInt8) (hu : ∀ y ∈ u, isDigit y = true) :
    dec ((5 :: u ++ [6]) ++ X) [] none = (dec X [] none).map (Tok.num (u.foldl nstep 0) :: ·) := by
  simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]; rw [dec_5, dec_num u 0 [] X hu]

theorem isL_eq (c : UInt8) : isL c = isLetter c := rfl
theorem lex0 (c : UInt8) (xs : List UInt8) : lex 0 (c :: xs) = none := rfl

theorem step0_num (o : List UInt8) (c : UInt8) (hc : isDigit c = true) (rest : List UInt8) (f : Nat) (sp : UInt64)
    (hF : Fu (f + 1) (c :: rest) sp) (m d d0 w ty : UInt64) (hty : ty ≠ 9) : S0 o (c :: rest) (f + 1) sp m d d0 w ty := by
  obtain ⟨u, r, rfl, hu, hr⟩ := span_exists isDigit rest
  unfold S0
  rw [L_digit c hc]
  have hcu : ∀ y ∈ c :: u, isDigit y = true := by simp [hc]; exact hu
  rw [show c :: (u ++ r) = (c :: u) ++ r from rfl, spanNum_eq (c :: u) f 0 r hcu hr]
  simp only [Fu, List.length_cons, List.length_append] at hF
  rcases List.eq_nil_or_concat u with rfl | ⟨v, z, rfl⟩
  · -- one digit
    simp only [List.cons_append, List.nil_append, List.append_nil] at *
    rcases r with _ | ⟨n, t⟩
    · rcases hF with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
      · have : f = 0 := by simp at hf; omega
        subst this; left; refine ⟨by simp [isLetter, lex0], fun _ => ?_⟩; rw [N_singleE c hc]; simp
      · obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
        right; right
        refine ⟨Tok.num (nstep 0 c), [5, c, 6], f + 1, [], 1, d, d0, w, by simp, Or.inr ⟨rfl, by simp⟩, by simp, ?_, ?_, ?_⟩
        · intro X; have := dec_numTok [c] X (by simp [hc]); simpa using this
        · intro _; simp only [tyStep]; rw [N_singleE c hc]; simp
        · intro h; exact absurd h hty
    · have hn : isDigit n = false := by simpa [hd?] using hr
      have hf1 : 1 ≤ f := by rcases hF with ⟨_, hf⟩ | ⟨_, hf⟩ <;> simp at hf <;> omega
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      simp only [List.nil_append, List.take_succ_cons, List.take_nil, List.drop_succ_cons, List.drop_nil,
        List.foldl_cons, List.foldl_nil]
      rw [N_single c n hc hn, ← isL_eq]
      by_cases hb : (isL n || n == 40) = true
      · left; simp [hb]
      · right; right; simp only [hb, Bool.false_eq_true, if_false]
        refine ⟨Tok.num (nstep 0 c), [5, c, 6], g + 1, n :: t, sp, d, d0, w, by simp, ?_, rfl, ?_, ?_, ?_⟩
        · rcases hF with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left; exact ⟨h1, by simp at h2 ⊢; omega⟩
          · right; exact ⟨h1, by simp at h2 ⊢; omega⟩
        · intro X; have := dec_numTok [c] X (by simp [hc]); simpa using this
        · intro _; simp [tyStep]
        · intro h; exact absurd h hty
  · -- two or more digits
    simp only [List.concat_eq_append] at *
    have hv : ∀ y ∈ v, isDigit y = true := fun y hy => hu y (by simp [hy])
    have hz : isDigit z = true := hu z (by simp)
    have hall : ∀ y ∈ c :: (v ++ [z]), isDigit y = true := hcu
    rw [show (c :: (v ++ [z])) ++ r = c :: (v ++ z :: r) by simp, NumStart o m sp d d0 ty c z v r w hc hv hz]
    have hdec : ∀ X, dec ((5 :: (c :: (v ++ [z])) ++ [6]) ++ X) [] none =
        (dec X [] none).map (Tok.num ((c :: (v ++ [z])).foldl nstep 0) :: ·) := fun X => dec_numTok _ X hall
    rcases r with _ | ⟨n, t⟩
    · rcases hF with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
      · -- `lex`'s fuel is the rest: split before the last digit
        simp only [List.length_append, List.length_singleton, List.length_nil, List.length_cons] at hf
        rw [N_lastE z hz]
        rcases v with _ | ⟨y, v⟩ <;> simp only [List.length_nil, List.length_cons] at hf
        · have : f = 1 := by omega
          subst this; left
          refine ⟨by simp [isLetter, L_digit z hz, spanNum, hz, lex0], fun hm => by simp [hm]⟩
        · have htk : List.take f (c :: (y :: v ++ [z])) = c :: y :: v := by
            rw [show f = (c :: y :: v).length by simp; omega, show c :: (y :: v ++ [z]) = (c :: y :: v) ++ [z] by simp,
              List.take_left]
          have hdr : List.drop f (c :: (y :: v ++ [z])) = [z] := by
            rw [show f = (c :: y :: v).length by simp; omega, show c :: (y :: v ++ [z]) = (c :: y :: v) ++ [z] by simp,
              List.drop_left]
          have hzl : isLetter z = false := (digitFacts z hz).2.2.2.2.2.2.2.2.2.2
          right; right
          refine ⟨Tok.num ((c :: y :: v).foldl nstep 0), 5 :: (c :: y :: v) ++ [6], f, [z], 1, d, d0, 1,
            by simp, Or.inr ⟨rfl, by simp; omega⟩, ?_, ?_, ?_, ?_⟩
          · have h40 : (z == 40) = false := (digitFacts z hz).2.2.1
            simp only [htk, hdr, List.append_nil]; simp [hzl, h40]
          · intro X; exact dec_numTok _ X (fun q hq => hall q (by simp at hq ⊢; rcases hq with h | h | h <;> simp [h]))
          · intro _; simp only [tyStep]; simp; by_cases hm : m = 0 <;> simp [hm]
          · intro h; exact absurd h hty
      · simp only [List.length_append, List.length_singleton, List.length_nil, List.length_cons] at hf
        have htk : List.take f (c :: (v ++ [z])) = c :: (v ++ [z]) := List.take_of_length_le (by simp; omega)
        have hdr : List.drop f (c :: (v ++ [z])) = [] := List.drop_of_length_le (by simp; omega)
        rw [N_lastE z hz]
        right; right
        refine ⟨_, 5 :: (c :: (v ++ [z])) ++ [6], f, [], 1, d, d0, if v = [] then 0 else 1,
          by simp, Or.inr ⟨rfl, by simp; omega⟩, ?_, hdec, ?_, ?_⟩
        · simp only [htk, hdr, List.append_nil]
        · intro _; simp only [tyStep]; simp; by_cases hm : m = 0 <;> simp [hm]
        · intro h; exact absurd h hty
    · have hn : isDigit n = false := by simpa [hd?] using hr
      have hf : (c :: (v ++ [z])).length ≤ f := by
        rcases hF with ⟨_, hf⟩ | ⟨_, hf⟩ <;> simp only [List.length_append, List.length_cons, List.length_singleton] at hf ⊢ <;> omega
      have htk : List.take f (c :: (v ++ [z])) = c :: (v ++ [z]) := List.take_of_length_le hf
      have hdr : List.drop f (c :: (v ++ [z])) = [] := List.drop_of_length_le hf
      simp only [htk, hdr, List.nil_append]
      rw [N_last z n hn]; simp only [isL_eq]
      by_cases hb : (isLetter n || n == 40) = true
      · left; simp [hb]
      · right; right; simp only [hb, Bool.false_eq_true, if_false]
        refine ⟨_, 5 :: (c :: (v ++ [z])) ++ [6], f, n :: t, 1, d, d0, if v = [] then 0 else 1, by simp; omega,
          Or.inr ⟨rfl, ?_⟩, rfl, hdec, ?_, ?_⟩
        · rcases hF with ⟨_, h⟩ | ⟨_, h⟩ <;> simp only [List.length_append, List.length_cons, List.length_singleton] at h ⊢ <;> omega
        · intro _; simp only [tyStep]; simp; by_cases hm : m = 0 <;> simp [hm]
        · intro h; exact absurd h hty


theorem dfa_snoc (u : List UInt8) (c : UInt8) : dfa (u ++ [c]) = dstep (dfa u) c := by simp [dfa, List.foldl_append]

theorem pk2 (c n : UInt8) : ((0x10000 : UInt64) ||| (c.toUInt64 <<< 8) ||| n.toUInt64) = pk [c, n] := by
  apply UInt64.toNat_inj.mp
  have hc := c.toNat_lt; have hn := n.toNat_lt
  rw [pk_short [c, n] (by simp)]
  simp only [packN, List.foldl_cons, List.foldl_nil]
  rw [UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_shiftLeft]
  simp only [UInt64.toNat_ofNat, UInt8.toNat_toUInt64]
  rw [show 8 % 2 ^ 64 % 64 = 8 by rfl, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show c.toNat * 2 ^ 8 < 2 ^ 64 by omega)]
  have e1 : 65536 ||| c.toNat * 2 ^ 8 = 1 <<< 16 + c.toNat * 2 ^ 8 := by
    rw [Nat.shiftLeft_add_eq_or_of_lt (by omega)]; rfl
  have e2 : 1 <<< 16 + c.toNat * 2 ^ 8 = (256 + c.toNat) <<< 8 := by simp [Nat.shiftLeft_eq]; omega
  rw [e1, e2, ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]

theorem pk_snoc' (u : List UInt8) (c : UInt8) : pk (u ++ [c]) = wstep (pk u) c := pk_snoc u c

theorem dstep0_2 (c n : UInt8) : (DSTEP0 n) = dfa [c, n] := by
  simp only [dfa, List.foldl_cons, List.foldl_nil]
  rw [dstep0]
  have hl : (97 ≤ c && c ≤ 122) = isLower c := rfl
  have hn : (97 ≤ n && n ≤ 122) = isLower n := rfl
  rw [hl, hn, isDigit_iff]
  by_cases h : isLower c = true
  · simp only [h, if_true]
    by_cases h2 : isLower n = true
    · simp only [h2, if_true, (dstepL n h2).1]
    · simp only [Bool.not_eq_true] at h2; simp only [h2, Bool.false_eq_true, if_false, (dstep12 n h2).1, dstep4]
  · simp only [Bool.not_eq_true] at h; simp [h, dstep6]

theorem dfa1 (c : UInt8) : (if 97 ≤ c && c ≤ 122 then (1 : UInt64) else 6) = dfa [c] := by
  simp only [dfa, List.foldl_cons, List.foldl_nil]; rw [dstep0]; rfl

theorem isW_iff (c : UInt8) : ((65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95 || (48 ≤ c && c ≤ 57)) = isW c := rfl

theorem W_start2 (c n : UInt8) (hc : isL c = true) (hn : isW n = true) (t o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx (c :: n :: t) o m 0 sp d d0 w ty =
      (if m = 0 then [] else [c]) ++ lx (n :: t) o m 1 sp (dfa [c, n]) (dfa [c]) (pk [c, n]) ty := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := letterFacts c hc
  rw [lx_c2, dstep0_2 c n, dfa1, pk2]
  simp only [h1, h2, h9, h10, h4, h6, isDigit_iff, h11, hc, hn, Bool.false_eq_true, if_false, if_true]
  by_cases hm : m = 0 <;> simp [hm]

theorem W_adv (x y : UInt8) (hy : isW y = true) (t o : List UInt8) (m sp D D0 W ty : UInt64) :
    lx (x :: y :: t) o m 1 sp D D0 W ty = (if m = 0 then [] else [x]) ++ lx (y :: t) o m 1 sp (dstep D y) D (wstep W y) ty := by
  rw [lx_c2]; simp only [hy]; by_cases hm : m = 0 <;> simp [hm, dstep, wstep]

theorem W_last (x y : UInt8) (hy : isW y = false) (t o : List UInt8) (m sp D D0 W ty : UInt64) :
    lx (x :: y :: t) o m 1 sp D D0 W ty =
      if y == 40 || kindOf D W == 9 || tyu ty W == 9 then [0]
      else (if m = 0 then [] else [x, (kindOf D W).toUInt8]) ++ lx (y :: t) o m 0 1 D D0 W (tyu ty W) := by
  rw [lx_c2]; simp only [hy]; by_cases hm : m = 0 <;> simp [hm, kindOf, tyu]

theorem W_lastE (x : UInt8) (o : List UInt8) (m D D0 W ty : UInt64) :
    lx [x] o m 1 1 D D0 W ty =
      if kindOf D W == 9 || tyu ty W == 9 then [0]
      else (if m = 0 then [] else [x, (kindOf D W).toUInt8]) ++ lx [] o m 0 1 D D0 W (tyu ty W) := by
  rw [lx_c1, lx_nil]; by_cases hm : m = 0 <;> simp [hm, kindOf, tyu]

theorem W_quirk (x : UInt8) (hx : isDigit x = true ∨ isLower x = true) (o : List UInt8) (m D D0 W ty : UInt64) :
    lx [x] o m 1 0 D D0 W ty =
      if W < 0x1000000 || kindOf D0 (W >>> 8) == 9 || tyu ty (W >>> 8) == 9 then ([0] : List UInt8)
      else (if m = 0 then [] else [(kindOf D0 (W >>> 8)).toUInt8]) ++ lx [x] o m 0 1 D D0 W (tyu ty (W >>> 8)) := by
  have hl : (97 ≤ x && x ≤ 122) = isLower x := rfl
  rcases hx with hx | hx
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := digitFacts x hx
    have h12 : (x == 40 || x == 41 || x == 42 || x == 43 || x == 45 || x == 59) = false := by
      simp only [Bool.or_eq_false_iff]; simp_all
    rw [lx_c1, lx_c1]; simp only [h1, h9, h12, isDigit_iff, hx]
    by_cases hm : m = 0 <;> simp [hm, kindOf, tyu]
  · have hd : isDigit x = false := by
      have : ∀ c : UInt8, isLower c = true → isDigit c = false := u8_all (by decide +kernel)
      exact this x hx
    have hf : (x == 32 || x == 10) = false ∧ (x == 58) = false ∧
        (x == 40 || x == 41 || x == 42 || x == 43 || x == 45 || x == 59) = false ∧ (x < 97 || 122 < x) = false := by
      have : ∀ c : UInt8, isLower c = true → (c == 32 || c == 10) = false ∧ (c == 58) = false ∧
        (c == 40 || c == 41 || c == 42 || c == 43 || c == 45 || c == 59) = false ∧ (c < 97 || 122 < c) = false :=
        u8_all (by decide +kernel)
      exact this x hx
    rw [lx_c1, lx_c1]; simp only [hf.1, hf.2.1, hf.2.2.1, hf.2.2.2, isDigit_iff, hd, hl, hx]
    by_cases hm : m = 0 <;> simp [hm, kindOf, tyu]

theorem W_quirkBad (x : UInt8) (hx : isDigit x = false) (hl : isLower x = false) (o : List UInt8) (m D D0 W ty : UInt64) :
    lx [x] o m 1 0 D D0 W ty = [0] := by
  have hl' : (97 ≤ x && x ≤ 122) = isLower x := rfl
  have hf : (x < 97 || 122 < x) = true := by
    have : ∀ c : UInt8, isLower c = false → (c < 97 || 122 < c) = true := u8_all (by decide +kernel)
    exact this x hl
  rw [lx_c1]; simp only [isDigit_iff, hx, hf]; simp

theorem W_single (c n : UInt8) (hc : isL c = true) (hn : isW n = false) (t o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx (c :: n :: t) o m 0 sp d d0 w ty =
      if n == 40 || !isLower c then [0] else (if m = 0 then [] else [c, 0]) ++ lx (n :: t) o m 0 sp d d0 w ty := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := letterFacts c hc
  have hlc : (c < 97 || 122 < c) = !isLower c := by
    have : ∀ c : UInt8, (c < 97 || 122 < c) = !isLower c := u8_all (by decide +kernel)
    exact this c
  rw [lx_c2]; simp only [h1, h2, h9, h10, h4, h6, isDigit_iff, h11, hc, hn, hlc, Bool.false_eq_true, if_false, if_true]
  by_cases hm : m = 0 <;> simp [hm]

theorem W_singleE (c : UInt8) (hc : isL c = true) (o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx [c] o m 0 sp d d0 w ty =
      if sp = 0 || !isLower c then [0] else (if m = 0 then [] else [c, 0]) ++ lx [] o m 0 sp d d0 w ty := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := letterFacts c hc
  have h12 : (c == 40 || c == 41 || c == 42 || c == 43 || c == 45 || c == 59) = false := by
    simp only [Bool.or_eq_false_iff]; simp_all
  have hl : (97 ≤ c && c ≤ 122) = isLower c := rfl
  rw [lx_c1, lx_nil]; simp only [h1, h9, h12, isDigit_iff, h11, hl]
  by_cases hm : m = 0 <;> by_cases hs : sp = 0 <;> by_cases hlo : isLower c = true <;> simp [hm, hs, hlo]

theorem WordRun (o : List UInt8) (m sp ty : UInt64) : ∀ (v : List UInt8) (x z : UInt8) (t p : List UInt8),
    (∀ y ∈ v, isW y = true) → isW z = true →
    lx (x :: (v ++ z :: t)) o m 1 sp (dfa (p ++ [x])) (dfa p) (pk (p ++ [x])) ty =
      (if m = 0 then [] else x :: v) ++
        lx (z :: t) o m 1 sp (dfa (p ++ x :: v ++ [z])) (dfa (p ++ x :: v)) (pk (p ++ x :: v ++ [z])) ty
  | [], x, z, t, p, _, hz => by
    rw [List.nil_append, W_adv x z hz, ← dfa_snoc, ← pk_snoc]
  | y :: v, x, z, t, p, hv, hz => by
    rw [List.cons_append, W_adv x y (hv y (by simp)), ← dfa_snoc, ← pk_snoc,
      WordRun o m sp ty v y z t (p ++ [x]) (fun q hq => hv q (by simp [hq])) hz]
    by_cases hm : m = 0 <;> simp [hm]

theorem WordStart (o : List UInt8) (m sp d d0 w ty : UInt64) (c z : UInt8) (v t : List UInt8)
    (hc : isL c = true) (hv : ∀ y ∈ v, isW y = true) (hz : isW z = true) :
    lx (c :: (v ++ z :: t)) o m 0 sp d d0 w ty =
      (if m = 0 then [] else c :: v) ++
        lx (z :: t) o m 1 sp (dfa (c :: v ++ [z])) (dfa (c :: v)) (pk (c :: v ++ [z])) ty := by
  rcases v with _ | ⟨y, v⟩
  · rw [List.nil_append, W_start2 c z hc hz]; by_cases hm : m = 0 <;> simp [hm]
  · rw [List.cons_append, W_start2 c y hc (hv y (by simp))]
    have := WordRun o m sp ty v y z t [c] (fun q hq => hv q (by simp [hq])) hz
    simp only [List.singleton_append, List.cons_append, List.nil_append] at this
    rw [this]; by_cases hm : m = 0 <;> simp [hm]

theorem spanId_eq : ∀ (u : List UInt8) (f : Nat) (r : List UInt8), (∀ y ∈ u, isW y = true) →
    hd? r isW = false → spanId f (u ++ r) = (u.take f, u.drop f ++ r)
  | [], f, r, _, hr => by
    rcases r with _ | ⟨y, r⟩
    · rcases f with _ | f <;> rfl
    · have : (isLetter y || isDigit y) = false := hr
      rcases f with _ | f
      · rfl
      · simp only [List.nil_append, spanId, this, Bool.false_eq_true, if_false, List.take_nil, List.drop_nil]
  | c :: u, f, r, hu, hr => by
    rcases f with _ | f
    · simp [spanId]
    · have : (isLetter c || isDigit c) = true := hu c (by simp)
      simp only [List.cons_append, spanId, this, if_true, List.take_succ_cons, List.drop_succ_cons]
      rw [spanId_eq u f r (fun q hq => hu q (by simp [hq])) hr]

def ktok (k : UInt8) (s : List UInt8) : Tok :=
  if k = 0 then .id s else if k = 1 then .kdef else if k = 2 then .klet else if k = 3 then .kty false else .kty true

theorem dec_word : ∀ (u wd X : List UInt8) (k : UInt8), (∀ y ∈ u, isW y = true) → k ≤ 4 → wd.reverse ++ u ≠ [] →
    dec (u ++ k :: X) wd none = (dec X [] none).map (ktok k (wd.reverse ++ u) :: ·)
  | [], wd, X, k, _, hk, hne => by
    have hw : isW k = false := by
      have : ∀ c : UInt8, c ≤ 4 → isW c = false := u8_all (by decide +kernel)
      exact this k hk
    have hwd : wd.isEmpty = false := by cases wd <;> simp_all
    simp only [List.nil_append, dec, hw, Bool.false_eq_true, if_false, hwd, Bool.not_false, if_true, List.append_nil]
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
      have : ∀ c : UInt8, c ≤ 4 → (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4) := u8_all (by decide +kernel)
      exact this k hk
    rcases this with h | h | h | h | h <;> subst h <;> simp [ktok]
  | y :: u, wd, X, k, hu, hk, _ => by
    simp only [List.cons_append, dec, hu y (by simp), if_true]
    rw [dec_word u (y :: wd) X k (fun q hq => hu q (by simp [hq])) hk (by simp)]
    simp

theorem kind_vals (d w : UInt64) : kindOf d w = 0 ∨ kindOf d w = 1 ∨ kindOf d w = 2 ∨ kindOf d w = 3 ∨
    kindOf d w = 4 ∨ kindOf d w = 9 := by
  unfold kindOf; repeat' split
  all_goals simp

theorem kindTok_ok (d w : UInt64) (u : List UInt8) (h : kindOf d w ≠ 9) :
    kindTok (kindOf d w) u = some (ktok (kindOf d w).toUInt8 u) ∧ (kindOf d w).toUInt8 ≤ 4 := by
  rcases kind_vals d w with e | e | e | e | e | e <;> rw [e] at h ⊢ <;> simp_all [kindTok, ktok] <;> decide

theorem tyu_ok (d w ty : UInt64) (u : List UInt8) (h : kindOf d w ≠ 9) :
    tyu ty w = tyStep ty (ktok (kindOf d w).toUInt8 u) := by
  unfold kindOf at h ⊢; unfold tyu
  repeat' split
  all_goals simp_all [ktok, tyStep]

theorem pk_shift (q : List UInt8) (z : UInt8) (hq : q.length ≤ 6) : pk (q ++ [z]) >>> 8 = pk q := by
  apply UInt64.toNat_inj.mp
  have e1 := pk_short (q ++ [z]) (by simp; omega)
  have e2 := pk_short q (by omega)
  rw [UInt64.toNat_shiftRight, e1, e2, packN_append]
  simp only [UInt64.toNat_ofNat, show 8 % 2 ^ 64 % 64 = 8 by rfl, Nat.shiftRight_eq_div_pow]
  have := z.toNat_lt; omega

theorem pk_big (q : List UInt8) (hq : 7 ≤ q.length) : 2 ^ 56 ≤ (pk q).toNat := by
  by_cases h : 8 ≤ q.length
  · rw [pk_long q h]; decide
  · rw [pk_short q (by omega)]
    have := (packN_ge q).1
    have : 256 ^ 7 ≤ 256 ^ q.length := Nat.pow_le_pow_right (by omega) hq
    have : (2 : Nat) ^ 56 = 256 ^ 7 := by rfl
    omega

theorem kind_nc (d ty w : UInt64) (hw : w = 0x80000000000000 ∨ 2 ^ 56 ≤ w.toNat) :
    kindOf d w = (if 1 ≤ d && d ≤ 4 then 0 else 9) ∧ tyu ty w = ty := by
  have hne : ∀ C : UInt64, C.toNat < 2 ^ 55 → (w == C) = false := by
    intro C hC; rw [beq_eq_false_iff_ne]; intro h; subst h
    rcases hw with h | h
    · rw [h] at hC; simp at hC
    · omega
  unfold kindOf tyu
  simp (disch := decide) only [hne, Bool.false_eq_true, if_false, Bool.or_false, Bool.false_or]
  simp

theorem quirkK (q : List UInt8) (z : UInt8) (d ty : UInt64) :
    kindOf d (pk (q ++ [z]) >>> 8) = kindOf d (pk q) ∧ tyu ty (pk (q ++ [z]) >>> 8) = tyu ty (pk q) := by
  by_cases h : q.length ≤ 6
  · rw [pk_shift q z h]; exact ⟨rfl, rfl⟩
  · rw [pk_long (q ++ [z]) (by simp; omega)]
    have a := kind_nc d ty ((0x8000000000000000 : UInt64) >>> 8) (Or.inl (by decide))
    have b := kind_nc d ty (pk q) (Or.inr (pk_big q (by omega)))
    rw [a.1, a.2, b.1, b.2]; exact ⟨rfl, rfl⟩

theorem pk_lt2 (a b : UInt8) : pk [a, b] < 0x1000000 := by
  rw [UInt64.lt_iff_toNat_lt, pk_short _ (by simp)]
  simp only [packN, List.foldl_cons, List.foldl_nil]
  have := a.toNat_lt; have := b.toNat_lt; simp; omega

theorem pk_ge3 (u : List UInt8) (hu : 3 ≤ u.length) : ¬ pk u < 0x1000000 := by
  rw [UInt64.lt_iff_toNat_lt]
  by_cases h : 8 ≤ u.length
  · rw [pk_long u h]; decide
  · rw [pk_short u (by omega)]
    have := (packN_ge u).1
    have : 256 ^ 3 ≤ 256 ^ u.length := Nat.pow_le_pow_right (by omega) hu
    simp; omega

theorem identTok_nil : identTok? [] = none := by simp [identTok?, kwDef, kwLet, kwTy, kwTyI, nameShape]
theorem kind1 : ∀ c : UInt8, kindOf (dfa [c]) (pk [c]) = if isLower c then 0 else 9 := u8_all (by decide +kernel)
theorem identTok1 (c : UInt8) : identTok? [c] = if isLower c then some (Tok.id [c]) else none := by
  rw [← classify, kind1]; by_cases h : isLower c = true <;> simp [h, kindTok]
theorem isW_cases : ∀ c : UInt8, isW c = true → isDigit c = true ∨ (isL c = true ∧ isDigit c = false) :=
  u8_all (by decide +kernel)
theorem lowerL : ∀ c : UInt8, isLower c = true → isL c = true ∧ isDigit c = false := u8_all (by decide +kernel)
theorem isL_W : ∀ c : UInt8, isL c = true → isW c = true := u8_all (by decide +kernel)
theorem isW_n40 : ∀ c : UInt8, isW c = true → (c == 40) = false := u8_all (by decide +kernel)

/-- `lex` of a lone last word character after a split word -/
theorem lex_last (z : UInt8) (hz : isW z = true) (g : Nat) :
    lex (g + 1) [z] = if g = 0 then none else
      if isDigit z then some [Tok.num (nstep 0 z)] else if isLower z then some [Tok.id [z]] else none := by
  rcases isW_cases z hz with h | ⟨h1, h2⟩
  · rw [L_digit z h]
    have e := spanNum_eq [z] g 0 [] (by simp [h]) rfl
    simp only [List.append_nil] at e
    rw [e]
    rcases g with _ | g
    · have hl : isLetter z = false := (digitFacts z h).2.2.2.2.2.2.2.2.2.2
      have h40 : (z == 40) = false := (digitFacts z h).2.2.1
      simp [hl, h40, lex0]
    · simp [h, lex_nil]
  · rw [L_letter z h1]
    have e := spanId_eq [z] g [] (by simp [hz]) rfl
    simp only [List.append_nil] at e
    rw [e]
    rcases g with _ | g
    · simp only [List.take_zero, List.drop_zero, identTok_nil]; split <;> simp_all
    · simp only [List.take_succ_cons, List.take_nil, List.drop_succ_cons, List.drop_nil]
      rw [identTok1]; by_cases hl : isLower z = true <;> simp [hl, lex_nil, h2]

theorem dec_wordTok (U X : List UInt8) (k : UInt8) (hU : ∀ y ∈ U, isW y = true) (hk : k ≤ 4) (hne : U ≠ []) :
    dec ((U ++ [k]) ++ X) [] none = (dec X [] none).map (ktok k U :: ·) := by
  rw [List.append_assoc, List.singleton_append, dec_word U [] X k hU hk (by simpa using hne)]; simp

theorem step0_word (o : List UInt8) (c : UInt8) (hc : isL c = true) (rest : List UInt8) (f : Nat) (sp : UInt64)
    (hF : Fu (f + 1) (c :: rest) sp) (m d d0 w ty : UInt64) (hty : ty ≠ 9) : S0 o (c :: rest) (f + 1) sp m d d0 w ty := by
  obtain ⟨u, r, rfl, hu, hr⟩ := span_exists isW rest
  unfold S0
  rw [L_letter c hc]
  have hcu : ∀ y ∈ c :: u, isW y = true := by simp [isL_W c hc]; exact hu
  rw [show c :: (u ++ r) = (c :: u) ++ r from rfl, spanId_eq (c :: u) f r hcu hr]
  simp only [Fu, List.length_cons, List.length_append] at hF
  rcases List.eq_nil_or_concat u with rfl | ⟨v, z, rfl⟩
  · -- a one-character word
    simp only [List.cons_append, List.nil_append, List.append_nil] at *
    rcases r with _ | ⟨n, t⟩
    · rcases hF with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
      · have : f = 0 := by simp at hf; omega
        subst this; left
        refine ⟨by simp only [List.take_zero, List.drop_zero, identTok_nil]; split <;> simp_all, fun _ => ?_⟩
        rw [W_singleE c hc]; simp
      · obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
        simp only [List.take_succ_cons, List.take_nil, List.drop_succ_cons, List.drop_nil]
        rw [identTok1, W_singleE c hc]
        by_cases hl : isLower c = true
        · right; right
          refine ⟨Tok.id [c], [c, 0], g + 1, [], 1, d, d0, w, by simp, Or.inr ⟨rfl, by simp⟩, by simp [hl], ?_, ?_, ?_⟩
          · intro X; have := dec_wordTok [c] X 0 (by simp [isL_W c hc]) (by decide) (by simp); simpa [ktok] using this
          · intro _; simp [hl, tyStep]
          · intro h; exact absurd h hty
        · left; simp [hl]
    · have hn : isW n = false := by simpa [hd?] using hr
      have hf1 : 1 ≤ f := by rcases hF with ⟨_, hf⟩ | ⟨_, hf⟩ <;> simp at hf <;> omega
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      simp only [List.take_succ_cons, List.take_nil, List.drop_succ_cons, List.drop_nil, List.nil_append]
      rw [identTok1, W_single c n hc hn]
      by_cases h40 : n = 40
      · subst h40; left; simp
      · by_cases hl : isLower c = true
        · right; right
          have h40' : (n == 40) = false := by simpa using h40
          refine ⟨Tok.id [c], [c, 0], g + 1, n :: t, sp, d, d0, w, by simp, ?_, ?_, ?_, ?_, ?_⟩
          · rcases hF with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · left; exact ⟨h1, by simp at h2 ⊢; omega⟩
            · right; exact ⟨h1, by simp at h2 ⊢; omega⟩
          · simp [hl]; split <;> simp_all
          · intro X; have := dec_wordTok [c] X 0 (by simp [isL_W c hc]) (by decide) (by simp); simpa [ktok] using this
          · intro _; simp [hl, h40', tyStep]
          · intro h; exact absurd h hty
        · left; simp [hl]; split <;> simp_all
  · -- two or more characters
    simp only [List.concat_eq_append] at *
    have hv : ∀ y ∈ v, isW y = true := fun y hy => hu y (by simp [hy])
    have hz : isW z = true := hu z (by simp)
    have hall : ∀ y ∈ c :: (v ++ [z]), isW y = true := hcu
    rw [show (c :: (v ++ [z])) ++ r = c :: (v ++ z :: r) by simp, WordStart o m sp d d0 w ty c z v r hc hv hz]
    have hne : c :: (v ++ [z]) ≠ [] := by simp
    have hcls := classify (c :: (v ++ [z]))
    -- the whole word as one token
    have whole : ∀ (F' : Nat) (r' : List UInt8) (hr' : r'.length < (c :: (v ++ z :: r)).length) (hF' : Fu F' r' 1)
        (hlx : lx (z :: r) o m 1 sp (dfa (c :: v ++ [z])) (dfa (c :: v)) (pk (c :: v ++ [z])) ty =
          if kindOf (dfa (c :: (v ++ [z]))) (pk (c :: (v ++ [z]))) == 9 || tyu ty (pk (c :: (v ++ [z]))) == 9 then [0]
          else (if m = 0 then [] else [z, (kindOf (dfa (c :: (v ++ [z]))) (pk (c :: (v ++ [z])))).toUInt8]) ++
            lx r' o m 0 1 (dfa (c :: v ++ [z])) (dfa (c :: v)) (pk (c :: v ++ [z])) (tyu ty (pk (c :: (v ++ [z]))))),
        (∀ L : Option (List Tok), L = (match identTok? (c :: (v ++ [z])) with
          | some t => (lex F' r').map (t :: ·) | none => none) →
        (L = none ∧ (m = 0 → (if m = 0 then [] else c :: v) ++ lx (z :: r) o m 1 sp (dfa (c :: v ++ [z])) (dfa (c :: v))
          (pk (c :: v ++ [z])) ty = [0])) ∨
        (∃ F'' r'' sp' d' d0' w', r''.length < (c :: (v ++ z :: r)).length ∧ Fu F'' r'' sp' ∧ L = lex F'' r'' ∧
          (if m = 0 then [] else c :: v) ++ lx (z :: r) o m 1 sp (dfa (c :: v ++ [z])) (dfa (c :: v))
            (pk (c :: v ++ [z])) ty = lx r'' o m 0 sp' d' d0' w' ty) ∨
        (∃ t bs F'' r'' sp' d' d0' w', r''.length < (c :: (v ++ z :: r)).length ∧ Fu F'' r'' sp' ∧
          L = (lex F'' r'').map (t :: ·) ∧ (∀ X, dec (bs ++ X) [] none = (dec X [] none).map (t :: ·)) ∧
          (tyStep ty t ≠ 9 → (if m = 0 then [] else c :: v) ++ lx (z :: r) o m 1 sp (dfa (c :: v ++ [z])) (dfa (c :: v))
            (pk (c :: v ++ [z])) ty = (if m = 0 then [] else bs) ++ lx r'' o m 0 sp' d' d0' w' (tyStep ty t)) ∧
          (tyStep ty t = 9 → m = 0 → (if m = 0 then [] else c :: v) ++ lx (z :: r) o m 1 sp (dfa (c :: v ++ [z]))
            (dfa (c :: v)) (pk (c :: v ++ [z])) ty = [0]))) := by
      intro F' r' hr' hF' hlx L hL
      rw [← hcls] at hL
      simp only [List.cons_append] at hlx ⊢
      rw [hlx]
      by_cases hk : kindOf (dfa (c :: (v ++ [z]))) (pk (c :: (v ++ [z]))) = 9
      · left; rw [hk] at hL; simp [kindTok] at hL; refine ⟨hL, fun hm => ?_⟩; simp [hk, hm]
      · right; right
        obtain ⟨hkt, hk4⟩ := kindTok_ok _ _ (c :: (v ++ [z])) hk
        rw [hkt] at hL
        have htu := tyu_ok (dfa (c :: (v ++ [z]))) (pk (c :: (v ++ [z]))) ty (c :: (v ++ [z])) hk
        refine ⟨_, (c :: (v ++ [z])) ++ [(kindOf (dfa (c :: (v ++ [z]))) (pk (c :: (v ++ [z])))).toUInt8], F', r', 1,
          dfa (c :: (v ++ [z])), dfa (c :: v), pk (c :: (v ++ [z])), hr', hF', hL, fun X => dec_wordTok _ X _ hall hk4 hne, ?_, ?_⟩
        · intro h9; rw [← htu] at h9; simp only [hk, h9, Bool.false_or, beq_self_eq_true, Bool.or_false,
            beq_eq_false_iff_ne.mpr h9, beq_eq_false_iff_ne.mpr hk]; rw [htu]
          by_cases hm : m = 0 <;> simp [hm]
        · intro h9 hm; rw [← htu] at h9; simp [h9, hm]
    rcases r with _ | ⟨n, t⟩
    · rcases hF with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
      · -- `lex`'s fuel is the rest: split before the last character
        simp only [List.length_append, List.length_singleton, List.length_nil] at hf
        have htk : List.take f (c :: (v ++ [z])) = c :: v := by
          rw [show f = (c :: v).length by simp; omega, show c :: (v ++ [z]) = (c :: v) ++ [z] by simp, List.take_left]
        have hdr : List.drop f (c :: (v ++ [z])) = [z] := by
          rw [show f = (c :: v).length by simp; omega, show c :: (v ++ [z]) = (c :: v) ++ [z] by simp, List.drop_left]
        simp only [htk, hdr, List.append_nil]
        have hz40 := isW_n40 z hz
        have hz40' : z ≠ 40 := by simpa using hz40
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        have hll := lex_last z hz g
        by_cases hgood : isDigit z = true ∨ isLower z = true
        · rw [show c :: v ++ [z] = (c :: v) ++ [z] by rfl, W_quirk z hgood, (quirkK (c :: v) z (dfa (c :: v)) ty).1, (quirkK (c :: v) z (dfa (c :: v)) ty).2]
          rcases v with _ | ⟨y, v⟩
          · left
            have : g = 0 := by simp at hf; omega
            subst this
            simp only [if_pos rfl] at hll
            refine ⟨by cases identTok? [c] <;> simp [hll, hz40'], fun hm => by simp [hm, pk_lt2]⟩
          · have h3 := pk_ge3 (c :: y :: v ++ [z]) (by simp)
            have hcls2 := classify (c :: y :: v)
            have hg : g ≠ 0 := by simp only [List.length_cons] at hf; omega
            by_cases hk : kindOf (dfa (c :: y :: v)) (pk (c :: y :: v)) = 9
            · left; rw [← hcls2, hk]; refine ⟨by simp [kindTok]; split <;> simp_all, fun hm => by simp [hm, hk]⟩
            · right; right
              obtain ⟨hkt, hk4⟩ := kindTok_ok _ _ (c :: y :: v) hk
              have htu := tyu_ok (dfa (c :: y :: v)) (pk (c :: y :: v)) ty (c :: y :: v) hk
              have hall2 : ∀ q ∈ c :: y :: v, isW q = true := fun q hq => hall q (by
                simp only [List.mem_cons] at hq; rcases hq with h | h | h <;> simp [h])
              refine ⟨_, (c :: y :: v) ++ [(kindOf (dfa (c :: y :: v)) (pk (c :: y :: v))).toUInt8], g + 1, [z], 1,
                dfa (c :: y :: v ++ [z]), dfa (c :: y :: v), pk (c :: y :: v ++ [z]), by simp,
                Or.inr ⟨rfl, by simp only [List.length_cons, List.length_nil] at hf ⊢; omega⟩,
                ?_, fun X => dec_wordTok _ X _ hall2 hk4 (by simp), ?_, ?_⟩
              · rw [← hcls2, hkt]; simp [hz40']
              · intro h9; rw [← htu] at h9
                simp only [h3, decide_false, beq_eq_false_iff_ne.mpr hk, beq_eq_false_iff_ne.mpr h9, Bool.or_false,
                  Bool.false_or, Bool.false_eq_true, if_false]
                rw [htu]; by_cases hm : m = 0 <;> simp [hm]
              · intro h9 hm; rw [← htu] at h9; simp [h9, hm]
        · left
          simp only [not_or, Bool.not_eq_true] at hgood
          have : lex (g + 1) [z] = none := by rw [hll]; simp [hgood.1, hgood.2]
          refine ⟨by cases identTok? (c :: v) <;> simp [this, hz40'], fun hm => ?_⟩
          rw [show c :: v ++ [z] = (c :: v) ++ [z] by rfl, W_quirkBad z hgood.1 hgood.2]; simp [hm]
      · simp only [List.length_append, List.length_singleton, List.length_nil] at hf
        have htk : List.take f (c :: (v ++ [z])) = c :: (v ++ [z]) := List.take_of_length_le (by simp; omega)
        have hdr : List.drop f (c :: (v ++ [z])) = [] := List.drop_of_length_le (by simp; omega)
        simp only [htk, hdr, List.append_nil]
        have := whole f [] (by simp) (Or.inr ⟨rfl, by simp; omega⟩) (by rw [W_lastE z]; simp)
        exact this _ (by cases identTok? (c :: (v ++ [z])) <;> rfl)
    · have hn : isW n = false := by simpa [hd?] using hr
      have hf : (c :: (v ++ [z])).length ≤ f := by
        rcases hF with ⟨_, hf⟩ | ⟨_, hf⟩ <;> simp only [List.length_append, List.length_cons, List.length_singleton] at hf ⊢ <;> omega
      have htk : List.take f (c :: (v ++ [z])) = c :: (v ++ [z]) := List.take_of_length_le hf
      have hdr : List.drop f (c :: (v ++ [z])) = [] := List.drop_of_length_le hf
      simp only [htk, hdr, List.nil_append]
      by_cases h40 : n = 40
      · subst h40; left; refine ⟨by cases identTok? (c :: (v ++ [z])) <;> rfl, fun hm => ?_⟩
        rw [W_last z 40 hn]; simp [hm]
      · have := whole f (n :: t) (by simp; omega) (Or.inr ⟨rfl, ?_⟩) (by rw [W_last z n hn]; simp [h40])
        · exact this _ (by cases identTok? (c :: (v ++ [z])) <;> simp [h40])
        · rcases hF with ⟨_, h⟩ | ⟨_, h⟩ <;> simp only [List.length_append, List.length_cons, List.length_singleton] at h ⊢ <;> omega

theorem dec_p (b : UInt8) (t : Tok) (hb : (b = 40 ∧ t = .lp) ∨ (b = 41 ∧ t = .rp) ∨ (b = 42 ∧ t = .star) ∨
    (b = 43 ∧ t = .plus) ∨ (b = 45 ∧ t = .minus) ∨ (b = 58 ∧ t = .colon) ∨ (b = 59 ∧ t = .semi) ∨ (b = 61 ∧ t = .assign))
    (X : List UInt8) : dec ([b] ++ X) [] none = (dec X [] none).map (t :: ·) := by
  rcases hb with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> subst h h' <;>
    simp [dec, isW, isL]

theorem Fu_tail (f : Nat) (c : UInt8) (rest : List UInt8) (sp : UInt64) (h : Fu (f + 1) (c :: rest) sp) : Fu f rest sp := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨h1, by simp at h2; omega⟩
  · right; exact ⟨h1, by simp at h2; omega⟩

theorem otherFacts : ∀ c : UInt8, (c == 32 || c == 10 || c == 13 || c == 40 || c == 41 || c == 43 || c == 45 || c == 42 ||
    c == 59 || c == 58 || isDigit c || isL c) = false →
    (c == 32 || c == 10) = false ∧ (c == 13) = false ∧ (c == 58) = false ∧ (c == 40 || c == 42 || c == 43 || c == 59) = false ∧
    (c == 41) = false ∧ (c == 45) = false ∧ isDigit c = false ∧ isL c = false ∧ (97 ≤ c && c ≤ 122) = false ∧
    (c == 40 || c == 41 || c == 42 || c == 43 || c == 45 || c == 59) = false := u8_all (by decide +kernel)

theorem M_other (c : UInt8) (hc : (c == 32 || c == 10 || c == 13 || c == 40 || c == 41 || c == 43 || c == 45 || c == 42 ||
    c == 59 || c == 58 || isDigit c || isL c) = false) (rest o : List UInt8) (m sp d d0 w ty : UInt64) :
    lx (c :: rest) o m 0 sp d d0 w ty = [0] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := otherFacts c hc
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1]; simp only [h1, h3, h10, isDigit_iff, h7, h9]; simp
  · rw [lx_c2]; simp only [h1, h2, h3, h4, h5, h6, isDigit_iff, h7, h8]; simp

theorem step0' (o xs : List UInt8) (hxs : xs ≠ []) (F : Nat) (sp : UInt64) (hF : Fu F xs sp)
    (m d d0 w ty : UInt64) (hty : ty ≠ 9) : S0 o xs F sp m d d0 w ty := by
  rcases xs with _ | ⟨c, rest⟩
  · exact absurd rfl hxs
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by rcases hF with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h <;> omega⟩
  have hFt := Fu_tail f c rest sp hF
  have hlen : ∀ r : List UInt8, r.length ≤ rest.length → r.length < (c :: rest).length := fun r h => by simp; omega
  -- punctuation tokens: one byte, one token
  have punct : ∀ (t : Tok) (bs : List UInt8), (∀ X, dec (bs ++ X) [] none = (dec X [] none).map (t :: ·)) →
      tyStep ty t = ty → lex (f + 1) (c :: rest) = (lex f rest).map (t :: ·) →
      lx (c :: rest) o m 0 sp d d0 w ty = (if m = 0 then [] else bs) ++ lx rest o m 0 sp d d0 w ty →
      S0 o (c :: rest) (f + 1) sp m d d0 w ty := by
    intro t bs hd hts hl hx
    right; right
    exact ⟨t, bs, f, rest, sp, d, d0, w, hlen rest (Nat.le_refl _), hFt, hl, hd, fun _ => by rw [hts]; exact hx,
      fun h => absurd (hts ▸ h) hty⟩
  by_cases hws : c = 32 ∨ c = 10
  · right; left
    exact ⟨f, rest, sp, d, d0, w, hlen rest (Nat.le_refl _), hFt, L_ws c hws f rest, M_ws c hws rest o m sp d d0 w ty⟩
  by_cases h13 : c = 13
  · subst h13
    rcases rest with _ | ⟨n, t⟩
    · left; exact ⟨by rw [L_cr], fun _ => by rw [M_cr]⟩
    · by_cases hn : n = 10
      · subst hn; right; left
        refine ⟨f, t, 1, d, d0, w, by simp only [List.length_cons]; omega, Or.inr ⟨rfl, ?_⟩, by rw [L_cr]; simp,
          by rw [M_cr]; simp⟩
        rcases hF with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h <;> omega
      · left; exact ⟨by rw [L_cr]; simp [hn], fun _ => by rw [M_cr]; simp [hn]⟩
  by_cases h58 : c = 58
  · subst h58
    rcases rest with _ | ⟨n, t⟩
    · exact punct .colon [58] (dec_p 58 .colon (by simp)) rfl (by rw [L_colon]) (by rw [M_colon])
    · by_cases hn : n = 61
      · subst hn; right; right
        refine ⟨.assign, [61], f, t, 1, d, d0, w, by simp only [List.length_cons]; omega, Or.inr ⟨rfl, ?_⟩,
          by rw [L_colon]; simp, dec_p 61 .assign (by simp), fun _ => by rw [M_colon]; simp [tyStep], fun h => absurd h hty⟩
        rcases hF with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h <;> omega
      · exact punct .colon [58] (dec_p 58 .colon (by simp)) rfl (by rw [L_colon]; simp [hn]) (by rw [M_colon]; simp [hn])
  by_cases hp : c = 40 ∨ c = 42 ∨ c = 43 ∨ c = 59
  · rcases hp with h | h | h | h <;> subst h
    · exact punct .lp [40] (dec_p 40 .lp (by simp)) rfl (L_punct 40 f rest .lp (by simp)) (M_punct 40 (by simp) rest o m sp d d0 w ty)
    · exact punct .star [42] (dec_p 42 .star (by simp)) rfl (L_punct 42 f rest .star (by simp)) (M_punct 42 (by simp) rest o m sp d d0 w ty)
    · exact punct .plus [43] (dec_p 43 .plus (by simp)) rfl (L_punct 43 f rest .plus (by simp)) (M_punct 43 (by simp) rest o m sp d d0 w ty)
    · exact punct .semi [59] (dec_p 59 .semi (by simp)) rfl (L_punct 59 f rest .semi (by simp)) (M_punct 59 (by simp) rest o m sp d d0 w ty)
  by_cases h41 : c = 41
  · subst h41
    by_cases hb : hd? rest (fun x => x == 40 || isW x) = true
    · left; exact ⟨by rw [L_rp]; simp [hb], fun _ => by rw [M_rp]; simp [hb]⟩
    · exact punct .rp [41] (dec_p 41 .rp (by simp)) rfl (by rw [L_rp]; simp [hb]) (by rw [M_rp]; simp [hb])
  by_cases h45 : c = 45
  · subst h45
    by_cases hb : hd? rest (· == 45) = true
    · left; exact ⟨by rw [L_minus]; simp [hb], fun _ => by rw [M_minus]; simp [hb]⟩
    · exact punct .minus [45] (dec_p 45 .minus (by simp)) rfl (by rw [L_minus]; simp [hb]) (by rw [M_minus]; simp [hb])
  by_cases hd : isDigit c = true
  · exact step0_num o c hd rest f sp hF m d d0 w ty hty
  by_cases hl : isL c = true
  · exact step0_word o c hl rest f sp hF m d d0 w ty hty
  have hc : (c == 32 || c == 10 || c == 13 || c == 40 || c == 41 || c == 43 || c == 45 || c == 42 ||
      c == 59 || c == 58 || isDigit c || isL c) = false := by
    simp only [not_or] at hws hp; simp_all
  left; exact ⟨L_other c hc f rest, fun _ => M_other c hc rest o m sp d d0 w ty⟩


theorem R1_cons (o : List UInt8) (t : Tok) (r : Option (List Tok)) (ty : UInt64) (hty : ty = 0 ∨ ty = 1 ∨ ty = 2) :
    R1 o (r.map (t :: ·)) ty = if tyStep ty t = 9 then [0] else R1 o r (tyStep ty t) := by
  rcases r with _ | ts
  · simp only [Option.map_none, R1]; split <;> rfl
  · simp only [Option.map_some, R1]
    rcases hty with h | h | h <;> subst h <;> cases t <;> (try rename_i s; cases s) <;> simp [tyStep, uniTy, tyOf]

theorem tyStep_ok (ty : UInt64) (t : Tok) (hty : ty = 0 ∨ ty = 1 ∨ ty = 2) (h : tyStep ty t ≠ 9) :
    tyStep ty t = 0 ∨ tyStep ty t = 1 ∨ tyStep ty t = 2 := by
  cases t <;> (try rename_i s; cases s) <;> simp only [tyStep] at h ⊢ <;> (try split at h) <;> (try split) <;> simp_all

/-- **pass 1**: the machine computes `lex`, then the type check, then starts pass 2 -/
theorem pass1 (o : List UInt8) : ∀ (n : Nat) (xs : List UInt8), xs.length ≤ n → ∀ F sp d d0 w ty, Fu F xs sp →
    (ty = 0 ∨ ty = 1 ∨ ty = 2) → lx xs o 0 0 sp d d0 w ty = R1 o (lex F xs) ty := by
  intro n
  induction n with
  | zero =>
    intro xs hl F sp d d0 w ty _ hty
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; rw [lx_nil, lex_nil]
    rcases hty with h | h | h <;> subst h <;> rfl
  | succ n ih =>
    intro xs hl F sp d d0 w ty hF hty
    rcases xs with _ | ⟨c, xs⟩
    · rw [lx_nil, lex_nil]; rcases hty with h | h | h <;> subst h <;> rfl
    have hty9 : ty ≠ 9 := by rcases hty with h | h | h <;> subst h <;> decide
    rcases step0' o (c :: xs) (by simp) F sp hF 0 d d0 w ty hty9 with ⟨hn, hl0⟩ | ⟨F', r, sp', d', d0', w', hr, hF', he, hx⟩ |
      ⟨t, bs, F', r, sp', d', d0', w', hr, hF', he, _, hx, hx9⟩
    · rw [hl0 rfl, hn]; rfl
    · rw [hx, he]; exact ih r (by simp only [List.length_cons] at hl hr; omega) F' sp' d' d0' w' ty hF' hty
    · rw [he, R1_cons o t _ ty hty]
      split
      · exact hx9 ‹_› rfl
      · rw [hx ‹_›]; simp only [if_true, List.nil_append]
        exact ih r (by simp only [List.length_cons] at hl hr; omega) F' sp' d' d0' w' _ hF' (tyStep_ok ty t hty ‹_›)

theorem uniTy_some (s : Bool) : ∀ (ts : List Tok) (s' : Bool), uniTy (some s) ts = some s' → s' = s
  | [], _, h => by simp [uniTy] at h; exact h.symm
  | t :: ts, s', h => by
    cases t <;> simp only [uniTy] at h <;> (try exact uniTy_some s ts s' h)
    rename_i b; split at h
    · simp at *; subst_vars; exact uniTy_some _ ts s' h
    · cases h

/-- **pass 2**: the machine's bytes decode to `lex`'s tokens -/
theorem pass2 (o : List UInt8) (s : Bool) : ∀ (n : Nat) (xs : List UInt8), xs.length ≤ n → ∀ F sp d d0 w ts, Fu F xs sp →
    lex F xs = some ts → uniTy (some s) ts = some s → dec (lx xs o 1 0 sp d d0 w (tcode s)) [] none = some ts := by
  intro n
  induction n with
  | zero =>
    intro xs hl F sp d d0 w ts _ hlex _
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; rw [lex_nil] at hlex; cases hlex; rw [lx_nil]; rfl
  | succ n ih =>
    intro xs hl F sp d d0 w ts hF hlex hu
    rcases xs with _ | ⟨c, xs⟩
    · rw [lex_nil] at hlex; cases hlex; rw [lx_nil]; rfl
    rcases step0' o (c :: xs) (by simp) F sp hF 1 d d0 w (tcode s) (by cases s <;> decide) with ⟨hn, _⟩ |
      ⟨F', r, sp', d', d0', w', hr, hF', he, hx⟩ | ⟨t, bs, F', r, sp', d', d0', w', hr, hF', he, hdec, hx, _⟩
    · rw [hn] at hlex; cases hlex
    · rw [hx]; rw [he] at hlex; exact ih r (by simp only [List.length_cons] at hl hr; omega) F' sp' d' d0' w' ts hF' hlex hu
    · rw [he] at hlex
      rcases hl' : lex F' r with _ | ts'
      · rw [hl'] at hlex; cases hlex
      rw [hl'] at hlex; simp only [Option.map_some, Option.some.injEq] at hlex; subst hlex
      have hts : tyStep (tcode s) t = tcode s := by
        cases t <;> (try rfl)
        rename_i b; simp only [uniTy] at hu; split at hu
        · simp at *; subst_vars; rename_i sg; cases sg <;> rfl
        · cases hu
      have hu' : uniTy (some s) ts' = some s := by
        cases t <;> simp only [uniTy] at hu <;> (try exact hu)
        split at hu
        · simp at *; subst_vars; exact hu
        · cases hu
      rw [hx (by rw [hts]; cases s <;> decide), hts]
      simp only [show (1 : UInt64) ≠ 0 by decide, if_false]
      rw [hdec, ih r (by simp only [List.length_cons] at hl hr; omega) F' sp' d' d0' w' ts' hF' hl' hu']; rfl

theorem uniTy_none (s : Bool) : ∀ (ts : List Tok), uniTy none ts = some s → uniTy (some s) ts = some s
  | [], h => by simp [uniTy] at h
  | t :: ts, h => by
    cases t <;> simp only [uniTy] at h ⊢ <;> (try exact uniTy_none s ts h)
    rename_i b
    have := uniTy_some b ts s h; subst this; simp [h]

/-- **stage 1 is the lexer of `nanoElab`**: for every byte list -/
theorem lexB_eq (xs : List UInt8) : decL (lexB xs) = lexT xs := by
  unfold lexB lexT
  rw [pass1 xs xs.length xs (Nat.le_refl _) xs.length 0 0 0 0 0 (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl)]
  rcases hl : lex xs.length xs with _ | ts
  · rfl
  · simp only [R1, tyOf, show (0 : UInt64) ≠ 1 by decide, show (0 : UInt64) ≠ 2 by decide, if_false]
    rcases hu : uniTy none ts with _ | s
    · rfl
    · have h2 := pass2 xs s xs.length xs (Nat.le_refl _) xs.length 0 0 0 0 ts (Or.inl ⟨rfl, rfl⟩) hl (uniTy_none s ts hu)
      cases s <;> simp only [tcode, decL] at h2 ⊢ <;> simp at h2 ⊢ <;> rw [h2] <;> rfl

end Nano.B
