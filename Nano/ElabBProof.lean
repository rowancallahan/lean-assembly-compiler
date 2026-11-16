import Nano.ElabB
/- Stage 1 of nanoElabB: `decL (lexB xs) = lexT xs` for every byte list `xs`. -/
namespace Nano.B
open Nano

/-! ## The word automaton and the packed word -/

def dstep (d : UInt64) (c : UInt8) : UInt64 := DSTEP d, c
def wstep (w : UInt64) (c : UInt8) : UInt64 := WSTEP w, c
def kindOf (d w : UInt64) : UInt64 := KIND d, w
def kindC (d w cz : UInt64) : UInt64 := KINDC d, w, cz
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

/-! ## The word automaton and `wordTok` -/

theorem u8_all {P : UInt8 → Prop} (h : ∀ n, n < 256 → P (UInt8.ofNat n)) : ∀ c, P c := fun c => by
  have := h c.toNat c.toNat_lt; simpa using this

def isLower' (c : UInt8) : Bool := 97 ≤ c && c ≤ 122
def tailC (c : UInt8) : Bool := isDigit c || c == 95

theorem dstep6 : ∀ c, dstep 6 c = 6 := u8_all (by decide +kernel)
theorem dstep2 : ∀ c, dstep 2 c = if isDigit c then 2 else 6 := u8_all (by decide +kernel)
theorem dstep1 : ∀ c, dstep 1 c = if tailC c then 1 else 6 := u8_all (by decide +kernel)
theorem dstep0 : ∀ c, dstep 0 c = if isDigit c then 2 else if isLower' c then 1 else 6 := u8_all (by decide +kernel)

theorem fold6 : ∀ u : List UInt8, u.foldl dstep 6 = 6
  | [] => rfl
  | c :: u => by rw [List.foldl_cons, dstep6]; exact fold6 u
theorem fold2 : ∀ u : List UInt8, u.foldl dstep 2 = if u.all isDigit then 2 else 6
  | [] => rfl
  | c :: u => by
    rw [List.foldl_cons, dstep2]; by_cases h : isDigit c = true
    · simp only [h, if_true, List.all_cons, Bool.true_and]; exact fold2 u
    · simp only [h, Bool.false_eq_true, if_false, List.all_cons, Bool.false_and, fold6]
theorem fold1 : ∀ u : List UInt8, u.foldl dstep 1 = if u.all tailC then 1 else 6
  | [] => rfl
  | c :: u => by
    rw [List.foldl_cons, dstep1]; by_cases h : tailC c = true
    · simp only [h, if_true, List.all_cons, Bool.true_and]; exact fold1 u
    · simp only [h, Bool.false_eq_true, if_false, List.all_cons, Bool.false_and, fold6]

def nstep (a : UInt64) (c : UInt8) : UInt64 := a * 10 + (c - 48).toUInt64

/-- a word's kind as a token (6: a numeral, its value folded from the digits) -/
def kindTok (k : UInt64) (u : List UInt8) : Option Tok :=
  if k = 0 then some (.id u) else if k = 1 then some .kdef else if k = 2 then some .klet
  else if k = 3 then some (.kty false) else if k = 4 then some (.kty true)
  else if k = 6 then some (.num (u.foldl nstep 0)) else none

theorem pkConsts : (0x1646566 : UInt64) = pk [100, 101, 102] ∧ (0x16c6574 : UInt64) = pk [108, 101, 116] ∧
    (0x155496e743634 : UInt64) = pk [85, 73, 110, 116, 54, 52] ∧ (0x1496e743634 : UInt64) = pk [73, 110, 116, 54, 52] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem kwFacts : ∀ c : UInt8, isDigit c = true → c ≠ 100 ∧ c ≠ 108 ∧ c ≠ 85 ∧ c ≠ 73 := u8_all (by decide +kernel)

/-- **`KIND` is `wordTok`** on every word -/
theorem classify (u : List UInt8) : kindTok (kindOf (dfa u) (pk u)) u = wordTok u := by
  obtain ⟨e1, e2, e3, e4⟩ := pkConsts
  unfold kindOf; rw [e1, e2, e3, e4]
  simp (disch := decide) only [pk_beq]
  rcases u with _ | ⟨c, u⟩
  · rfl
  · have hd : dfa (c :: u) = u.foldl dstep (dstep 0 c) := rfl
    rw [hd, dstep0]
    unfold wordTok
    by_cases h1 : c :: u = [100, 101, 102]
    · rw [h1]; rfl
    by_cases h2 : c :: u = [108, 101, 116]
    · rw [h2]; rfl
    by_cases h3 : c :: u = [85, 73, 110, 116, 54, 52]
    · rw [h3]; rfl
    by_cases h4 : c :: u = [73, 110, 116, 54, 52]
    · rw [h4]; rfl
    have k1 : (c :: u == [100, 101, 102]) = false := by simpa using h1
    have k2 : (c :: u == [108, 101, 116]) = false := by simpa using h2
    have k3 : (c :: u == [85, 73, 110, 116, 54, 52]) = false := by simpa using h3
    have k4 : (c :: u == [73, 110, 116, 54, 52]) = false := by simpa using h4
    have k1' : (c :: u == kwDef) = false := k1
    have k2' : (c :: u == kwLet) = false := k2
    have k3' : (c :: u == kwTy) = false := k3
    have k4' : (c :: u == kwTyI) = false := k4
    simp only [k1, k2, k3, k4, k1', k2', k3', k4', Bool.false_eq_true, if_false]
    by_cases hd : isDigit c = true
    · simp only [hd, if_true, fold2, List.all_cons, Bool.true_and]
      by_cases ha : u.all isDigit = true
      · simp only [ha, if_true]; rfl
      · simp only [ha, Bool.false_eq_true, if_false]; rfl
    · simp only [hd, Bool.false_eq_true, if_false]
      unfold identOk
      by_cases hl : isLower' c = true
      · have hl' : (97 ≤ c && c ≤ 122) = true := hl
        simp only [hl, if_true, fold1, hl', Bool.true_and]
        have : u.all tailC = u.all (fun d => isDigit d || d == 95) := rfl
        rw [this]; by_cases ha : (u.all fun d => isDigit d || d == 95) = true <;> simp [ha, kindTok]
      · have hl' : (97 ≤ c && c ≤ 122) = false := by simpa [isLower'] using hl
        simp [hl, fold6, hl', kindTok]

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
    | some s => (tcode s).toUInt8 :: lx o o 1 0 0 0 0 0 (tcode s) 0

theorem lx_nil (o : List UInt8) (m st sp d d0 w ty cz : UInt64) (hm : (m == 5) = false) :
    lx [] o m st sp d d0 w ty cz =
      if m == 0 then (if ty == 0 then [0] else ty.toUInt8 :: lx o o 1 0 0 0 0 0 ty 0) else [] := by
  rw [lx]; simp only [hm, Bool.false_eq_true, if_false]

theorem lex_nil (F : Nat) : lex F [] = some [] := by cases F <;> rfl

theorem lx_c2 (c n : UInt8) (t o : List UInt8) (m st sp d d0 w ty cz : UInt64) :
    lx (c :: n :: t) o m st sp d d0 w ty cz = STEPN := by rw [lx]
theorem lx_c1 (c : UInt8) (o : List UInt8) (m st sp d d0 w ty cz : UInt64) :
    lx [c] o m st sp d d0 w ty cz = STEPE := by rw [lx]

def hd? (r : List UInt8) (p : UInt8 → Bool) : Bool := match r with | x :: _ => p x | [] => false

/-! ### `lex`, one step per byte class -/

theorem isW_eq (c : UInt8) : isWordC c = isW c := rfl
theorem isDigit_iff (c : UInt8) : (48 ≤ c && c ≤ 57) = isDigit c := rfl

/-- column 0 after a newline: a space, a newline, the end, or `def` not followed by a word character -/
def colOk (xs : List UInt8) : Bool :=
  match xs with
  | [] => true
  | 32 :: _ => true
  | 10 :: _ => true
  | 100 :: 101 :: 102 :: z => !(hd? z isW)
  | _ => false

theorem L_sp (f : Nat) (xs : List UInt8) : lex (f + 1) (32 :: xs) = lex f xs := by rw [lex.eq_def]; simp
theorem L_nl (f : Nat) (xs : List UInt8) : lex (f + 1) (10 :: xs) = if colOk xs then lex f xs else none := by
  rw [lex.eq_def]; simp only []
  rcases xs with _ | ⟨a, xs⟩
  · simp [colOk, lex_nil]
  · by_cases h32 : a = 32
    · subst h32; simp [colOk]
    by_cases h10 : a = 10
    · subst h10; simp [colOk]
    by_cases h100 : a = 100
    · subst h100
      rcases xs with _ | ⟨b, xs⟩
      · simp [colOk]
      by_cases h101 : b = 101
      · subst h101
        rcases xs with _ | ⟨e, xs⟩
        · simp [colOk]
        by_cases h102 : e = 102
        · subst h102
          rcases xs with _ | ⟨z, xs⟩
          · simp [colOk, hd?]
          · simp [colOk, hd?, isW_eq]; by_cases hz : isW z = true <;> simp [hz]
        · simp [colOk, h102]
      · simp [colOk, h101]
    · simp [colOk, h32, h10, h100]

theorem L_punct (c : UInt8) (f : Nat) (xs : List UInt8) (t : Tok)
    (hc : (c = 40 ∧ t = .lp) ∨ (c = 41 ∧ t = .rp) ∨ (c = 42 ∧ t = .star) ∨ (c = 43 ∧ t = .plus) ∨ (c = 59 ∧ t = .semi)) :
    lex (f + 1) (c :: xs) = (lex f xs).map (t :: ·) := by
  rcases hc with ⟨h, ht⟩ | ⟨h, ht⟩ | ⟨h, ht⟩ | ⟨h, ht⟩ | ⟨h, ht⟩ <;> subst h ht <;> rw [lex.eq_def] <;> simp
theorem L_minus (f : Nat) (xs : List UInt8) :
    lex (f + 1) (45 :: xs) = if hd? xs (· == 45) then none else (lex f xs).map (Tok.minus :: ·) := by
  rw [lex.eq_def]; rcases xs with _ | ⟨d, xs⟩ <;> simp [hd?]
  by_cases h : d = 45 <;> simp [h]
theorem L_colon (f : Nat) (xs : List UInt8) :
    lex (f + 1) (58 :: xs) = match xs with
      | 61 :: ys => (lex f ys).map (Tok.assign :: ·)
      | _ => (lex f xs).map (Tok.colon :: ·) := by
  rw [lex.eq_def]
  rcases xs with _ | ⟨a, ys⟩
  · simp
  · by_cases h : a = 61
    · subst h; simp
    · simp [h]
theorem wordFacts : ∀ c : UInt8, isW c = true →
    (c == 32) = false ∧ (c == 10) = false ∧ (c == 40) = false ∧ (c == 41) = false ∧ (c == 43) = false ∧
    (c == 45) = false ∧ (c == 42) = false ∧ (c == 59) = false ∧ (c == 58) = false ∧
    (c == 40 || c == 41 || c == 42 || c == 43 || c == 59) = false ∧
    (c == 40 || c == 41 || c == 42 || c == 43 || c == 45 || c == 59) = false := u8_all (by decide +kernel)
theorem L_word (c : UInt8) (hc : isW c = true) (f : Nat) (xs : List UInt8) :
    lex (f + 1) (c :: xs) = (let r := spanId f (c :: xs)
      match wordTok r.1 with
      | some t => (lex f r.2).map (t :: ·)
      | none => none) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _, _⟩ := wordFacts c hc
  have hw : isWordC c = true := hc
  rw [lex.eq_def]; simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hw, Bool.false_eq_true, if_false, if_true]
  generalize spanId f (c :: xs) = r; rcases r with ⟨a, b⟩; cases wordTok a <;> rfl
theorem L_other (c : UInt8) (hc : (c == 32 || c == 10 || c == 40 || c == 41 || c == 43 || c == 45 || c == 42 ||
    c == 59 || c == 58 || isW c) = false) (f : Nat) (xs : List UInt8) : lex (f + 1) (c :: xs) = none := by
  rw [lex.eq_def]; simp only [Bool.or_eq_false_iff] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
  have h10' : isWordC c = false := h10
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10']

/-! ### the machine in state 0, per byte class (passes 1 and 2: `m ≠ 5`) -/

theorem M_sp (rest o : List UInt8) (m sp d d0 w ty cz : UInt64) (hm : (m == 5) = false) :
    lx (32 :: rest) o m 0 sp d d0 w ty cz = lx rest o m 0 sp d d0 w ty 0 := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1, lx_nil _ _ _ _ _ _ _ _ _ hm]; simp [hm, isW, isL]
  · rw [lx_c2]; simp [hm, isW, isL]

theorem M_nl (rest o : List UInt8) (m sp d d0 w ty cz : UInt64) (hm : (m == 5) = false) :
    lx (10 :: rest) o m 0 sp d d0 w ty cz = lx rest o m 4 sp d d0 w ty 0 := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1, lx_nil _ _ _ _ _ _ _ _ _ hm]; simp [hm, isW, isL]
  · rw [lx_c2]; simp [hm, isW, isL]

theorem M_st2 (c : UInt8) (rest o : List UInt8) (m sp d d0 w ty cz : UInt64) (hm : (m == 5) = false) :
    lx (c :: rest) o m 2 sp d d0 w ty cz = lx rest o m 0 sp d d0 w ty 0 := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1, lx_nil _ _ _ _ _ _ _ _ _ hm]; simp [hm, isW, isL]
  · rw [lx_c2]; simp [hm, isW, isL]

theorem M_punct (c : UInt8) (hc : c = 40 ∨ c = 41 ∨ c = 42 ∨ c = 43 ∨ c = 59) (rest o : List UInt8)
    (m sp d d0 w ty cz : UInt64) (hm : (m == 5) = false) :
    lx (c :: rest) o m 0 sp d d0 w ty cz = (if m = 0 then [] else [c]) ++ lx rest o m 0 sp d d0 w ty 0 := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1, lx_nil _ _ _ _ _ _ _ _ _ hm]
    rcases hc with h | h | h | h | h <;> subst h <;> by_cases h0 : m = 0 <;> simp [h0, hm, isW, isL]
  · rw [lx_c2]; rcases hc with h | h | h | h | h <;> subst h <;> by_cases h0 : m = 0 <;> simp [h0, hm, isW, isL]

theorem M_minus (rest o : List UInt8) (m sp d d0 w ty cz : UInt64) (hm : (m == 5) = false) :
    lx (45 :: rest) o m 0 sp d d0 w ty cz =
      if hd? rest (· == 45) then [0] else (if m = 0 then [] else [45]) ++ lx rest o m 0 sp d d0 w ty 0 := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1, lx_nil _ _ _ _ _ _ _ _ _ hm]; by_cases h0 : m = 0 <;> simp [h0, hm, hd?, isW, isL]
  · rw [lx_c2]; by_cases h0 : m = 0 <;> by_cases hn : n = 45 <;> simp [h0, hm, hd?, hn, isW, isL]

theorem M_colon (rest o : List UInt8) (m sp d d0 w ty cz : UInt64) (hm : (m == 5) = false) :
    lx (58 :: rest) o m 0 sp d d0 w ty cz =
      match rest with
      | 61 :: r => (if m = 0 then [] else [61]) ++ lx r o m 0 1 d d0 w ty 0
      | _ => (if m = 0 then [] else [58]) ++ lx rest o m 0 sp d d0 w ty 0 := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1, lx_nil _ _ _ _ _ _ _ _ _ hm]; by_cases h0 : m = 0 <;> simp [h0, hm, isW, isL]
  · rw [lx_c2]
    by_cases hn : n = 61
    · subst hn; have e := M_st2 61 t o m 1 d d0 w ty 0 hm
      by_cases h0 : m = 0 <;> simp [h0, hm, isW, isL] <;> simp [h0] at e <;> exact e
    · by_cases h0 : m = 0 <;> simp [h0, hm, hn, isW, isL]

theorem otherFacts : ∀ c : UInt8, (c == 32 || c == 10 || c == 40 || c == 41 || c == 43 || c == 45 || c == 42 ||
    c == 59 || c == 58 || isW c) = false →
    (c == 32) = false ∧ (c == 10) = false ∧ (c == 32 || c == 10) = false ∧ (c == 58) = false ∧
    (c == 40 || c == 41 || c == 42 || c == 43 || c == 59) = false ∧ (c == 45) = false ∧ isW c = false ∧
    (48 ≤ c && c ≤ 57) = false ∧ (97 ≤ c && c ≤ 122) = false ∧
    (c == 40 || c == 41 || c == 42 || c == 43 || c == 45 || c == 59) = false := u8_all (by decide +kernel)

theorem M_other (c : UInt8) (hc : (c == 32 || c == 10 || c == 40 || c == 41 || c == 43 || c == 45 || c == 42 ||
    c == 59 || c == 58 || isW c) = false) (rest o : List UInt8) (m sp d d0 w ty cz : UInt64) (hm : (m == 5) = false) :
    lx (c :: rest) o m 0 sp d d0 w ty cz = [0] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := otherFacts c hc
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1]; simp only [hm, h3, h4, h10, h8, h9]; simp
  · rw [lx_c2]; simp only [hm, h1, h2, h4, h5, h6, h7]; simp

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


theorem dfa2 (c n : UInt8) : dfa [c, n] = dstep (dstep 0 c) n := rfl
theorem dfa1' (c : UInt8) : dfa [c] = dstep 0 c := rfl
theorem pk_snoc' (u : List UInt8) (c : UInt8) : pk (u ++ [c]) = wstep (pk u) c := pk_snoc u c

theorem W_start2 (c n : UInt8) (hc : isW c = true) (hn : isW n = true) (t o : List UInt8) (m s0 sp d d0 w ty cz : UInt64)
    (hm : (m == 5) = false) (hs : s0 = 0 ∨ s0 = 4) :
    lx (c :: n :: t) o m s0 sp d d0 w ty cz =
      (if m = 0 then [] else if isDigit c then [5, c] else [c]) ++
        lx (n :: t) o m 1 sp (dfa [c, n]) (dfa [c]) (pk [c, n]) ty (if s0 = 4 then 1 else 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ := wordFacts c hc
  rw [lx_c2, pk2]
  by_cases hd : isDigit c = true
  · have e2 : dfa [c] = 2 := by rw [dfa1', dstep0, if_pos hd]
    have e1 : dfa [c, n] = if isDigit n = true then 2 else 6 := by rw [dfa2, dstep0, if_pos hd, dstep2]
    rw [e1, e2]
    rcases hs with h | h <;> subst h <;> by_cases h0 : m = 0 <;> simp [hm, h1, h2, hc, hn, hd, h0, isDigit_iff] <;> rfl
  · have hd' : (48 ≤ c && c ≤ 57) = false := by simpa [isDigit] using hd
    have e2 : dfa [c] = if (97 ≤ c && c ≤ 122) = true then 1 else 6 := by
      rw [dfa1', dstep0, if_neg hd]; rfl
    have e1 : dfa [c, n] = if (97 ≤ c && c ≤ 122) = true then
        (if ((48 ≤ n && n ≤ 57) || n == 95) = true then 1 else 6) else 6 := by
      rw [dfa2, dstep0, if_neg hd]
      by_cases hl : isLower' c = true
      · have hl' : (97 ≤ c && c ≤ 122) = true := hl
        rw [if_pos hl, dstep1, if_pos hl']; rfl
      · have hl' : (97 ≤ c && c ≤ 122) = false := by simpa [isLower'] using hl
        rw [if_neg hl, dstep6, hl']; rfl
    rw [e1, e2]
    rcases hs with h | h <;> subst h <;> by_cases h0 : m = 0 <;> simp [hm, h1, h2, hc, hn, hd, hd', h0] <;> rfl

theorem W_adv (x y : UInt8) (hy : isW y = true) (t o : List UInt8) (m sp D D0 W ty cz : UInt64) (hm : (m == 5) = false) :
    lx (x :: y :: t) o m 1 sp D D0 W ty cz =
      (if m = 0 then [] else [x]) ++ lx (y :: t) o m 1 sp (dstep D y) D (wstep W y) ty cz := by
  rw [lx_c2]; simp only [hm, hy]; by_cases h0 : m = 0 <;> simp [h0, dstep, wstep]

theorem W_last (x y : UInt8) (hy : isW y = false) (t o : List UInt8) (m sp D D0 W ty cz : UInt64) (hm : (m == 5) = false) :
    lx (x :: y :: t) o m 1 sp D D0 W ty cz =
      if kindC D W cz == 9 || tyu ty W == 9 then [0]
      else (if m = 0 then [] else [x, (kindC D W cz).toUInt8]) ++ lx (y :: t) o m 0 1 D D0 W (tyu ty W) 0 := by
  rw [lx_c2]; simp only [hm, hy]; by_cases h0 : m = 0 <;> simp [h0, kindC, kindOf, tyu]

theorem W_lastE (x : UInt8) (o : List UInt8) (m D D0 W ty cz : UInt64) (hm : (m == 5) = false) :
    lx [x] o m 1 1 D D0 W ty cz =
      if kindC D W cz == 9 || tyu ty W == 9 then [0]
      else (if m = 0 then [] else [x, (kindC D W cz).toUInt8]) ++ lx [] o m 0 1 D D0 W (tyu ty W) 0 := by
  rw [lx_c1, lx_nil _ _ _ _ _ _ _ _ _ hm]; by_cases h0 : m = 0 <;> simp [h0, hm, kindC, kindOf, tyu]

theorem lowerFacts : ∀ c : UInt8, isLower' c = true → isW c = true ∧ isDigit c = false ∧ (97 ≤ c && c ≤ 122) = true ∧
    (c < 97 || 122 < c) = false := u8_all (by decide +kernel)

theorem W_quirk (x : UInt8) (hx : isDigit x = true ∨ isLower' x = true) (o : List UInt8) (m D D0 W ty cz : UInt64)
    (hm : (m == 5) = false) :
    lx [x] o m 1 0 D D0 W ty cz =
      if cz == 1 || W < 0x1000000 || kindOf D0 (W >>> 8) == 9 || tyu ty (W >>> 8) == 9 then ([0] : List UInt8)
      else (if m = 0 then [] else [(kindOf D0 (W >>> 8)).toUInt8]) ++ lx [x] o m 0 1 D D0 W (tyu ty (W >>> 8)) 0 := by
  rcases hx with hx | hx
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := wordFacts x (by simp [isW, isL]; simp_all [isDigit])
    rw [lx_c1, lx_c1]; simp only [hm, isDigit_iff, hx, h9, h11, h1, h2]
    by_cases h0 : m = 0 <;> simp [h0, kindOf, tyu]
  · obtain ⟨hw, hd, hl, hl2⟩ := lowerFacts x hx
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := wordFacts x hw
    rw [lx_c1, lx_c1]; simp only [hm, isDigit_iff, hd, hl, hl2, h9, h11, h1, h2]
    by_cases h0 : m = 0 <;> simp [h0, kindOf, tyu]

theorem W_quirkBad (x : UInt8) (hx : isDigit x = false) (hl : isLower' x = false) (o : List UInt8) (m D D0 W ty cz : UInt64)
    (hm : (m == 5) = false) : lx [x] o m 1 0 D D0 W ty cz = [0] := by
  have hf : (x < 97 || 122 < x) = true := by
    have : ∀ c : UInt8, isLower' c = false → (c < 97 || 122 < c) = true := u8_all (by decide +kernel)
    exact this x hl
  rw [lx_c1]; simp only [hm, isDigit_iff, hx, hf]; simp

theorem W_single (c n : UInt8) (hc : isW c = true) (hn : isW n = false) (t o : List UInt8) (m sp d d0 w ty cz : UInt64)
    (hm : (m == 5) = false) :
    lx (c :: n :: t) o m 0 sp d d0 w ty cz =
      if isDigit c then (if m = 0 then [] else [5, c, 6]) ++ lx (n :: t) o m 0 sp d d0 w ty 0
      else if isLower' c then (if m = 0 then [] else [c, 0]) ++ lx (n :: t) o m 0 sp d d0 w ty 0 else [0] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := wordFacts c hc
  have hlc : (c < 97 || 122 < c) = !isLower' c := by
    have : ∀ c : UInt8, (c < 97 || 122 < c) = !isLower' c := u8_all (by decide +kernel)
    exact this c
  rw [lx_c2]; simp only [hm, h1, h2, hc, hn, isDigit_iff, hlc]
  by_cases hd : isDigit c = true <;> by_cases hl : isLower' c = true <;> by_cases h0 : m = 0 <;> simp [hd, hl, h0]

theorem W_single4 (c n : UInt8) (hc : isW c = true) (hn : isW n = false) (t o : List UInt8) (m sp d d0 w ty cz : UInt64)
    (hm : (m == 5) = false) : lx (c :: n :: t) o m 4 sp d d0 w ty cz = [0] := by
  obtain ⟨h1, h2, _⟩ := wordFacts c hc
  rw [lx_c2]; simp only [hm, h1, h2, hc, hn]; simp

theorem W_singleE (c : UInt8) (hc : isW c = true) (o : List UInt8) (m sp d d0 w ty cz : UInt64) (hm : (m == 5) = false) :
    lx [c] o m 0 sp d d0 w ty cz =
      if sp = 0 then [0]
      else if isDigit c then (if m = 0 then [] else [5, c, 6]) ++ lx [] o m 0 sp d d0 w ty 0
      else if isLower' c then (if m = 0 then [] else [c, 0]) ++ lx [] o m 0 sp d d0 w ty 0 else [0] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := wordFacts c hc
  have hl : (97 ≤ c && c ≤ 122) = isLower' c := rfl
  have h12 : (c == 32 || c == 10) = false := by simp_all
  rw [lx_c1, lx_nil _ _ _ _ _ _ _ _ _ hm]; simp only [hm, h12, h9, h11, isDigit_iff, hl]
  by_cases hd : isDigit c = true
  · have : isLower' c = false := by
      have : ∀ c : UInt8, isDigit c = true → isLower' c = false := u8_all (by decide +kernel)
      exact this c hd
    by_cases hs : sp = 0 <;> by_cases h0 : m = 0 <;> simp [hd, this, hs, h0, hm]
  · by_cases hs : sp = 0 <;> by_cases hlo : isLower' c = true <;> by_cases h0 : m = 0 <;> simp [hd, hlo, hs, h0, hm]

theorem W_singleE4 (c : UInt8) (hc : isW c = true) (o : List UInt8) (m sp d d0 w ty cz : UInt64) (hm : (m == 5) = false) :
    lx [c] o m 4 sp d d0 w ty cz = [0] := by
  obtain ⟨h1, h2, _⟩ := wordFacts c hc
  have h12 : (c == 32 || c == 10) = false := by simp_all
  rw [lx_c1]; simp only [hm, h12]; simp

theorem WordRun (o : List UInt8) (m sp ty cz : UInt64) (hm : (m == 5) = false) : ∀ (v : List UInt8) (x z : UInt8) (t p : List UInt8),
    (∀ y ∈ v, isW y = true) → isW z = true →
    lx (x :: (v ++ z :: t)) o m 1 sp (dfa (p ++ [x])) (dfa p) (pk (p ++ [x])) ty cz =
      (if m = 0 then [] else x :: v) ++
        lx (z :: t) o m 1 sp (dfa (p ++ x :: v ++ [z])) (dfa (p ++ x :: v)) (pk (p ++ x :: v ++ [z])) ty cz
  | [], x, z, t, p, _, hz => by
    rw [List.nil_append, W_adv x z hz _ _ _ _ _ _ _ _ _ hm, ← dfa_snoc, ← pk_snoc]
  | y :: v, x, z, t, p, hv, hz => by
    rw [List.cons_append, W_adv x y (hv y (by simp)) _ _ _ _ _ _ _ _ _ hm, ← dfa_snoc, ← pk_snoc,
      WordRun o m sp ty cz hm v y z t (p ++ [x]) (fun q hq => hv q (by simp [hq])) hz]
    by_cases h0 : m = 0 <;> simp [h0]

theorem WordStart (o : List UInt8) (m s0 sp d d0 w ty cz : UInt64) (c z : UInt8) (v t : List UInt8)
    (hc : isW c = true) (hv : ∀ y ∈ v, isW y = true) (hz : isW z = true) (hm : (m == 5) = false) (hs : s0 = 0 ∨ s0 = 4) :
    lx (c :: (v ++ z :: t)) o m s0 sp d d0 w ty cz =
      (if m = 0 then [] else (if isDigit c then [5, c] else [c]) ++ v) ++
        lx (z :: t) o m 1 sp (dfa (c :: v ++ [z])) (dfa (c :: v)) (pk (c :: v ++ [z])) ty (if s0 = 4 then 1 else 0) := by
  rcases v with _ | ⟨y, v⟩
  · rw [List.nil_append, W_start2 c z hc hz _ _ _ _ _ _ _ _ _ _ hm hs]; by_cases h0 : m = 0 <;> simp [h0]
  · rw [List.cons_append, W_start2 c y hc (hv y (by simp)) _ _ _ _ _ _ _ _ _ _ hm hs]
    have := WordRun o m sp ty (if s0 = 4 then 1 else 0) hm v y z t [c] (fun q hq => hv q (by simp [hq])) hz
    simp only [List.singleton_append, List.cons_append, List.nil_append] at this
    rw [this]; by_cases h0 : m = 0 <;> simp [h0]

end Nano.B
