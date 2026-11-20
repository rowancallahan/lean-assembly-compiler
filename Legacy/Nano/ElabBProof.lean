import Legacy.Nano.ElabB
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
theorem span_exists (p : UInt8 → Bool) : ∀ xs : List UInt8, ∃ u r, xs = u ++ r ∧ (∀ y ∈ u, p y = true) ∧ hd? r p = false
  | [] => ⟨[], [], rfl, by simp, rfl⟩
  | x :: xs => by
    by_cases hx : p x = true
    · obtain ⟨u, r, h1, h2, h3⟩ := span_exists p xs
      exact ⟨x :: u, r, by simp [h1], by simp [hx, h2]; exact h2, h3⟩
    · exact ⟨[], x :: xs, rfl, by simp, by simpa [hd?] using hx⟩

theorem dec_5 (Y : List UInt8) : dec (5 :: Y) [] none = dec Y [] (some 0) := by simp [dec, isW, isL]

theorem spanId_eq : ∀ (u : List UInt8) (f : Nat) (r : List UInt8), (∀ y ∈ u, isW y = true) →
    hd? r isW = false → spanId f (u ++ r) = (u.take f, u.drop f ++ r)
  | [], f, r, _, hr => by
    rcases r with _ | ⟨y, r⟩
    · rcases f with _ | f <;> rfl
    · have : isWordC y = false := hr
      rcases f with _ | f
      · rfl
      · simp only [List.nil_append, spanId, this, Bool.false_eq_true, if_false, List.take_nil, List.drop_nil]
  | c :: u, f, r, hu, hr => by
    rcases f with _ | f
    · simp [spanId]
    · have : isWordC c = true := hu c (by simp)
      simp only [List.cons_append, spanId, this, if_true, List.take_succ_cons, List.drop_succ_cons]
      rw [spanId_eq u f r (fun q hq => hu q (by simp [hq])) hr]

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

theorem dec_numTok (u X : List UInt8) (hu : ∀ y ∈ u, isDigit y = true) :
    dec ((5 :: u ++ [6]) ++ X) [] none = (dec X [] none).map (Tok.num (u.foldl nstep 0) :: ·) := by
  simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]; rw [dec_5, dec_num u 0 [] X hu]

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


theorem kind_vals (d w : UInt64) : kindOf d w = 0 ∨ kindOf d w = 1 ∨ kindOf d w = 2 ∨ kindOf d w = 3 ∨
    kindOf d w = 4 ∨ kindOf d w = 6 ∨ kindOf d w = 9 := by
  unfold kindOf; repeat' split
  all_goals simp

theorem dec_wordTok (U X : List UInt8) (k : UInt8) (hU : ∀ y ∈ U, isW y = true) (hk : k ≤ 4) (hne : U ≠ []) :
    dec ((U ++ [k]) ++ X) [] none = (dec X [] none).map (ktok k U :: ·) := by
  rw [List.append_assoc, List.singleton_append, dec_word U [] X k hU hk (by simpa using hne)]; simp

theorem digit_W : ∀ c : UInt8, isDigit c = true → isW c = true := u8_all (by decide +kernel)

def tokK (k : UInt64) (U : List UInt8) : Tok := if k = 6 then .num (U.foldl nstep 0) else ktok k.toUInt8 U

theorem kindTok_some (k : UInt64) (U : List UInt8) (h : k ≠ 9) (hv : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6 ∨ k = 9) :
    kindTok k U = some (tokK k U) := by
  rcases hv with e | e | e | e | e | e | e <;> subst e <;> simp_all [kindTok, tokK, ktok] <;> decide

theorem tyu_ok (d w ty : UInt64) (U : List UInt8) (h : kindOf d w ≠ 9) : tyu ty w = tyStep ty (tokK (kindOf d w) U) := by
  unfold kindOf at h ⊢; unfold tyu
  repeat' split
  all_goals simp_all [tokK, ktok, tyStep]

theorem allDigits (c : UInt8) (u : List UInt8) (hc : isDigit c = true) (t : Tok) (h : wordTok (c :: u) = some t) :
    (∀ y ∈ c :: u, isDigit y = true) ∧ t = .num ((c :: u).foldl nstep 0) := by
  unfold wordTok at h; simp only [hc, if_true] at h
  by_cases ha : (c :: u).all isDigit = true
  · simp only [ha, if_true, Option.some.injEq] at h
    exact ⟨by simpa using ha, h.symm⟩
  · simp [ha] at h

/-- a valid word: its kind gives `wordTok`'s token, its bytes decode to it, and the type update is `tyStep`'s -/
theorem word_ok (c : UInt8) (u : List UInt8) (hu : ∀ y ∈ c :: u, isW y = true) (ty : UInt64)
    (h : kindOf (dfa (c :: u)) (pk (c :: u)) ≠ 9) :
    wordTok (c :: u) = some (tokK (kindOf (dfa (c :: u)) (pk (c :: u))) (c :: u)) ∧
      (∀ X, dec (((if isDigit c then 5 :: c :: u else c :: u) ++ [(kindOf (dfa (c :: u)) (pk (c :: u))).toUInt8]) ++ X) [] none =
        (dec X [] none).map (tokK (kindOf (dfa (c :: u)) (pk (c :: u))) (c :: u) :: ·)) ∧
      tyu ty (pk (c :: u)) = tyStep ty (tokK (kindOf (dfa (c :: u)) (pk (c :: u))) (c :: u)) := by
  have hcl := classify (c :: u)
  have hw : wordTok (c :: u) = some (tokK (kindOf (dfa (c :: u)) (pk (c :: u))) (c :: u)) := by
    rw [← hcl]; exact kindTok_some _ _ h (kind_vals _ _)
  refine ⟨hw, ?_, tyu_ok _ _ ty _ h⟩
  intro X
  by_cases hd : isDigit c = true
  · obtain ⟨hall, ht⟩ := allDigits c u hd _ hw
    have h6 : kindOf (dfa (c :: u)) (pk (c :: u)) = 6 := by
      unfold tokK at ht; split at ht
      · assumption
      · exfalso; revert ht; unfold ktok
        split <;> (try split) <;> (try split) <;> (try split) <;> intro ht <;> cases ht
    rw [ht, h6, if_pos hd]
    have := dec_numTok (c :: u) X hall
    simpa using this
  · rw [if_neg hd]
    have h6 : kindOf (dfa (c :: u)) (pk (c :: u)) ≠ 6 := by
      intro e; rw [e] at hw; simp only [tokK, if_pos rfl] at hw
      unfold wordTok at hw; simp only [hd, Bool.false_eq_true, if_false, ite_true] at hw
      revert hw
      split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> intro hw <;> simp at hw
    have hk4 : (kindOf (dfa (c :: u)) (pk (c :: u))).toUInt8 ≤ 4 := by
      rcases kind_vals (dfa (c :: u)) (pk (c :: u)) with e | e | e | e | e | e | e <;> rw [e] at h h6 ⊢ <;>
        first | decide | exact absurd rfl h | exact absurd rfl h6
    rw [dec_wordTok (c :: u) X _ hu hk4 (by simp)]
    simp only [tokK, if_neg h6]

theorem kind_nc (d ty w : UInt64) (hw : w = 0x80000000000000 ∨ 2 ^ 56 ≤ w.toNat) :
    kindOf d w = (if d = 1 then 0 else if d = 2 then 6 else 9) ∧ tyu ty w = ty := by
  have hne : ∀ C : UInt64, C.toNat < 2 ^ 55 → (w == C) = false := by
    intro C hC; rw [beq_eq_false_iff_ne]; intro h; subst h
    rcases hw with h | h
    · rw [h] at hC; simp at hC
    · omega
  unfold kindOf tyu
  simp (disch := decide) only [hne, Bool.false_eq_true, if_false]
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


theorem wordTok_nil : wordTok [] = none := rfl
theorem kind1 : ∀ c : UInt8, kindOf (dfa [c]) (pk [c]) = if isDigit c then 6 else if isLower' c then 0 else 9 :=
  u8_all (by decide +kernel)
theorem wordTok1 (c : UInt8) : wordTok [c] =
    if isDigit c then some (Tok.num (nstep 0 c)) else if isLower' c then some (Tok.id [c]) else none := by
  rw [← classify, kind1]
  by_cases hd : isDigit c = true
  · simp [hd, kindTok]
  · by_cases hl : isLower' c = true <;> simp [hd, hl, kindTok]

/-- `lex` of a lone last word character after a split word -/
theorem lex_last (z : UInt8) (hz : isW z = true) (g : Nat) :
    lex (g + 1) [z] = if g = 0 then none else
      if isDigit z then some [Tok.num (nstep 0 z)] else if isLower' z then some [Tok.id [z]] else none := by
  rw [L_word z hz]
  have e := spanId_eq [z] g [] (by simp [hz]) rfl
  simp only [List.append_nil] at e
  rw [e]
  rcases g with _ | g
  · simp only [List.take_zero, List.drop_zero, wordTok_nil]; simp
  · simp only [List.take_succ_cons, List.take_nil, List.drop_succ_cons, List.drop_nil]
    rw [wordTok1]
    by_cases hd : isDigit z = true
    · simp [hd, lex_nil]
    · by_cases hl : isLower' z = true <;> simp [hd, hl, lex_nil]

/-- one `lex` step `L` against the machine's output `MX` (`N`: the length of the input of the step) -/
def S0g (o : List UInt8) (N : Nat) (L : Option (List Tok)) (MX : List UInt8) (m ty : UInt64) : Prop :=
    (L = none ∧ (m = 0 → MX = [0])) ∨
    (∃ F' r sp' d' d0' w' cz', r.length < N ∧ Fu F' r sp' ∧ L = lex F' r ∧ MX = lx r o m 0 sp' d' d0' w' ty cz') ∨
    (∃ t bs F' r sp' d' d0' w' cz', r.length < N ∧ Fu F' r sp' ∧ L = (lex F' r).map (t :: ·) ∧
      (∀ X, dec (bs ++ X) [] none = (dec X [] none).map (t :: ·)) ∧
      (tyStep ty t ≠ 9 → MX = (if m = 0 then [] else bs) ++ lx r o m 0 sp' d' d0' w' (tyStep ty t) cz') ∧
      (tyStep ty t = 9 → m = 0 → MX = [0]))

def S0 (o xs : List UInt8) (F : Nat) (sp m d d0 w ty cz : UInt64) : Prop :=
  S0g o xs.length (lex F xs) (lx xs o m 0 sp d d0 w ty cz) m ty

theorem kindC0 (d w : UInt64) : kindC d w 0 = kindOf d w := by simp [kindC, kindOf]

/-- a whole word `c :: u` followed by `r'` (the machine's verdict at its last character) -/
theorem wholeWord (o : List UInt8) (m ty : UInt64) (c : UInt8) (u : List UInt8) (hu : ∀ y ∈ c :: u, isW y = true)
    (N F' : Nat) (r' : List UInt8) (hr' : r'.length < N) (hF' : Fu F' r' 1) (D D0 W : UInt64) (MX : List UInt8)
    (h1 : kindOf (dfa (c :: u)) (pk (c :: u)) ≠ 9 → tyu ty (pk (c :: u)) ≠ 9 →
      MX = (if m = 0 then [] else (if isDigit c then 5 :: c :: u else c :: u) ++ [(kindOf (dfa (c :: u)) (pk (c :: u))).toUInt8]) ++
        lx r' o m 0 1 D D0 W (tyu ty (pk (c :: u))) 0)
    (h2 : (kindOf (dfa (c :: u)) (pk (c :: u)) = 9 ∨ tyu ty (pk (c :: u)) = 9) → m = 0 → MX = [0]) :
    S0g o N (match wordTok (c :: u) with | some t => (lex F' r').map (t :: ·) | none => none) MX m ty := by
  by_cases hk : kindOf (dfa (c :: u)) (pk (c :: u)) = 9
  · left
    have : wordTok (c :: u) = none := by rw [← classify, hk]; rfl
    rw [this]; exact ⟨rfl, h2 (Or.inl hk)⟩
  · right; right
    obtain ⟨hw, hdec, hty⟩ := word_ok c u hu ty hk
    rw [hw]
    refine ⟨_, _, F', r', 1, D, D0, W, 0, hr', hF', rfl, hdec, ?_, ?_⟩
    · intro h9; rw [← hty] at h9 ⊢; exact h1 hk h9
    · intro h9 h0; rw [← hty] at h9; exact h2 (Or.inr h9) h0

theorem Fu_tail (f : Nat) (c : UInt8) (rest : List UInt8) (sp : UInt64) (h : Fu (f + 1) (c :: rest) sp) : Fu f rest sp := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨h1, by simp at h2; omega⟩
  · right; exact ⟨h1, by simp at h2; omega⟩

theorem digitLower : ∀ c : UInt8, isDigit c = true → isLower' c = false := u8_all (by decide +kernel)

theorem step0_word (o : List UInt8) (c : UInt8) (hc : isW c = true) (rest : List UInt8) (f : Nat) (sp : UInt64)
    (hF : Fu (f + 1) (c :: rest) sp) (m d d0 w ty cz : UInt64) (hm : (m == 5) = false) (hty : ty ≠ 9) :
    S0 o (c :: rest) (f + 1) sp m d d0 w ty cz := by
  obtain ⟨u, r, rfl, hu, hr⟩ := span_exists isW rest
  unfold S0 S0g
  rw [L_word c hc]
  have hcu : ∀ y ∈ c :: u, isW y = true := by simp [hc]; exact hu
  rw [show c :: (u ++ r) = (c :: u) ++ r from rfl, spanId_eq (c :: u) f r hcu hr]
  simp only [Fu, List.length_cons, List.length_append] at hF
  rcases List.eq_nil_or_concat u with rfl | ⟨v, z, rfl⟩
  · -- a one-character word
    simp only [List.cons_append, List.nil_append, List.append_nil] at *
    rcases r with _ | ⟨n, t⟩
    · rcases hF with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
      · have : f = 0 := by simp at hf; omega
        subst this; left
        refine ⟨by simp only [List.take_zero, List.drop_zero, wordTok_nil], fun _ => ?_⟩
        rw [W_singleE c hc _ _ _ _ _ _ _ _ hm]; simp
      · obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
        simp only [List.take_succ_cons, List.take_nil, List.drop_succ_cons, List.drop_nil]
        rw [wordTok1, W_singleE c hc _ _ _ _ _ _ _ _ hm]
        by_cases hd : isDigit c = true
        · right; right
          refine ⟨Tok.num (nstep 0 c), [5, c, 6], g + 1, [], 1, d, d0, w, 0, by simp, Or.inr ⟨rfl, by simp⟩,
            by simp [hd], ?_, ?_, ?_⟩
          · intro X; have := dec_numTok [c] X (by simp [hd]); simpa using this
          · intro _; simp [hd, tyStep]
          · intro h; exact absurd (by simpa [tyStep] using h) hty
        · by_cases hl : isLower' c = true
          · right; right
            refine ⟨Tok.id [c], [c, 0], g + 1, [], 1, d, d0, w, 0, by simp, Or.inr ⟨rfl, by simp⟩, by simp [hd, hl], ?_, ?_, ?_⟩
            · intro X; have := dec_wordTok [c] X 0 (by simp [hc]) (by decide) (by simp); simpa [ktok] using this
            · intro _; simp [hd, hl, tyStep]
            · intro h; exact absurd (by simpa [tyStep] using h) hty
          · left; simp [hd, hl]
    · have hn : isW n = false := by simpa [hd?] using hr
      have hf1 : 1 ≤ f := by rcases hF with ⟨_, hf⟩ | ⟨_, hf⟩ <;> simp at hf <;> omega
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      simp only [List.take_succ_cons, List.take_nil, List.drop_succ_cons, List.drop_nil, List.nil_append]
      rw [wordTok1, W_single c n hc hn _ _ _ _ _ _ _ _ _ hm]
      have hFt : Fu (g + 1) (n :: t) sp := by
        rcases hF with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨h1, by simp at h2 ⊢; omega⟩
        · right; exact ⟨h1, by simp at h2 ⊢; omega⟩
      by_cases hd : isDigit c = true
      · right; right
        refine ⟨Tok.num (nstep 0 c), [5, c, 6], g + 1, n :: t, sp, d, d0, w, 0, by simp, hFt, by simp [hd], ?_, ?_, ?_⟩
        · intro X; have := dec_numTok [c] X (by simp [hd]); simpa using this
        · intro _; simp [hd, tyStep]
        · intro h; exact absurd (by simpa [tyStep] using h) hty
      · by_cases hl : isLower' c = true
        · right; right
          refine ⟨Tok.id [c], [c, 0], g + 1, n :: t, sp, d, d0, w, 0, by simp, hFt, by simp [hd, hl], ?_, ?_, ?_⟩
          · intro X; have := dec_wordTok [c] X 0 (by simp [hc]) (by decide) (by simp); simpa [ktok] using this
          · intro _; simp [hd, hl, tyStep]
          · intro h; exact absurd (by simpa [tyStep] using h) hty
        · left; simp [hd, hl]
  · -- two or more characters
    simp only [List.concat_eq_append] at *
    have hv : ∀ y ∈ v, isW y = true := fun y hy => hu y (by simp [hy])
    have hz : isW z = true := hu z (by simp)
    have hall : ∀ y ∈ c :: (v ++ [z]), isW y = true := hcu
    rw [show (c :: (v ++ [z])) ++ r = c :: (v ++ z :: r) by simp,
      WordStart o m 0 sp d d0 w ty cz c z v r hc hv hz hm (Or.inl rfl)]
    simp only [show ((0 : UInt64) = 4) = False by decide, if_false]
    have pre : ∀ (Y : List UInt8), (if m = 0 then [] else (if isDigit c then [5, c] else [c]) ++ v) ++
        ((if m = 0 then [] else [z, (kindOf (dfa (c :: (v ++ [z]))) (pk (c :: (v ++ [z])))).toUInt8]) ++ Y) =
        (if m = 0 then [] else (if isDigit c then 5 :: c :: (v ++ [z]) else c :: (v ++ [z])) ++
          [(kindOf (dfa (c :: (v ++ [z]))) (pk (c :: (v ++ [z])))).toUInt8]) ++ Y := by
      intro Y; by_cases h0 : m = 0 <;> by_cases hd : isDigit c = true <;> simp [h0, hd]
    rcases r with _ | ⟨n, t⟩
    · rcases hF with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
      · -- `lex`'s fuel is the rest: split before the last character
        simp only [List.length_append, List.length_singleton, List.length_nil] at hf
        have htk : List.take f (c :: (v ++ [z])) = c :: v := by
          rw [show f = (c :: v).length by simp; omega, show c :: (v ++ [z]) = (c :: v) ++ [z] by simp, List.take_left]
        have hdr : List.drop f (c :: (v ++ [z])) = [z] := by
          rw [show f = (c :: v).length by simp; omega, show c :: (v ++ [z]) = (c :: v) ++ [z] by simp, List.drop_left]
        simp only [htk, hdr, List.append_nil]
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        have hll := lex_last z hz g
        by_cases hgood : isDigit z = true ∨ isLower' z = true
        · rw [show c :: v ++ [z] = (c :: v) ++ [z] by rfl, W_quirk z hgood _ _ _ _ _ _ _ hm,
            (quirkK (c :: v) z (dfa (c :: v)) ty).1, (quirkK (c :: v) z (dfa (c :: v)) ty).2]
          rcases v with _ | ⟨y, v⟩
          · left
            have : g = 0 := by simp at hf; omega
            subst this
            simp only [if_pos rfl] at hll
            refine ⟨by cases wordTok [c] <;> simp [hll], fun h0 => by simp [h0, pk_lt2]⟩
          · have h3 := pk_ge3 (c :: y :: v ++ [z]) (by simp)
            have hg : g ≠ 0 := by simp only [List.length_cons] at hf; omega
            have hzt : lex (g + 1) [z] = some [if isDigit z then Tok.num (nstep 0 z) else Tok.id [z]] := by
              rw [hll, if_neg hg]; rcases hgood with h | h
              · simp [h]
              · simp [h, digitLower]; by_cases hd : isDigit z = true
                · simp [hd]
                · simp [hd]
            have hall2 : ∀ q ∈ c :: y :: v, isW q = true := fun q hq => hall q (by
              simp only [List.mem_cons] at hq; rcases hq with h | h | h <;> simp [h])
            have hk2 : ((0 : UInt64) == 1 || pk (c :: y :: v ++ [z]) < 0x1000000) = false := by
              simp only [Bool.or_eq_false_iff]; exact ⟨by decide, by simpa using h3⟩
            refine wholeWord o m ty c (y :: v) hall2 _ (g + 1) [z] (by simp) (Or.inr ⟨rfl, by
              simp only [List.length_cons, List.length_nil] at hf ⊢; omega⟩)
              (dfa (c :: y :: v ++ [z])) (dfa (c :: y :: v)) (pk (c :: y :: v ++ [z])) _ ?_ ?_
            · intro hk h9
              simp only [Bool.or_assoc] at hk2 ⊢
              simp only [Bool.or_eq_false_iff] at hk2
              simp only [hk2.1, hk2.2, beq_eq_false_iff_ne.mpr hk, beq_eq_false_iff_ne.mpr h9, Bool.false_or,
                Bool.false_eq_true, if_false]
              by_cases h0 : m = 0 <;> by_cases hd : isDigit c = true <;> simp [h0, hd]
            · intro h9 h0; subst h0
              rcases h9 with h9 | h9 <;> simp [h9]
        · left
          simp only [not_or, Bool.not_eq_true] at hgood
          have : lex (g + 1) [z] = none := by rw [hll]; simp [hgood.1, hgood.2]
          refine ⟨by cases wordTok (c :: v) <;> simp [this], fun h0 => ?_⟩
          rw [show c :: v ++ [z] = (c :: v) ++ [z] by rfl, W_quirkBad z hgood.1 hgood.2 _ _ _ _ _ _ _ hm]; simp [h0]
      · simp only [List.length_append, List.length_singleton, List.length_nil] at hf
        have htk : List.take f (c :: (v ++ [z])) = c :: (v ++ [z]) := List.take_of_length_le (by simp; omega)
        have hdr : List.drop f (c :: (v ++ [z])) = [] := List.drop_of_length_le (by simp; omega)
        simp only [htk, hdr, List.append_nil]
        rw [W_lastE z _ _ _ _ _ _ _ hm, kindC0]
        refine wholeWord o m ty c (v ++ [z]) hall _ f [] (by simp) (Or.inr ⟨rfl, by simp; omega⟩)
          (dfa (c :: v ++ [z])) (dfa (c :: v)) (pk (c :: v ++ [z])) _ ?_ ?_
        · intro hk h9
          simp only [List.cons_append] at hk h9 ⊢
          simp only [beq_eq_false_iff_ne.mpr hk, beq_eq_false_iff_ne.mpr h9, Bool.false_or, Bool.false_eq_true, if_false]
          rw [pre]
        · intro h9 h0; subst h0; simp only [List.cons_append] at h9 ⊢
          rcases h9 with h9 | h9 <;> simp [h9]
    · have hn : isW n = false := by simpa [hd?] using hr
      have hf : (c :: (v ++ [z])).length ≤ f := by
        rcases hF with ⟨_, hf⟩ | ⟨_, hf⟩ <;> simp only [List.length_append, List.length_cons, List.length_singleton] at hf ⊢ <;> omega
      have htk : List.take f (c :: (v ++ [z])) = c :: (v ++ [z]) := List.take_of_length_le hf
      have hdr : List.drop f (c :: (v ++ [z])) = [] := List.drop_of_length_le hf
      simp only [htk, hdr, List.nil_append]
      rw [W_last z n hn _ _ _ _ _ _ _ _ _ hm, kindC0]
      refine wholeWord o m ty c (v ++ [z]) hall _ f (n :: t) (by simp; omega) (Or.inr ⟨rfl, ?_⟩)
        (dfa (c :: v ++ [z])) (dfa (c :: v)) (pk (c :: v ++ [z])) _ ?_ ?_
      · rcases hF with ⟨_, h⟩ | ⟨_, h⟩ <;> simp only [List.length_append, List.length_cons, List.length_singleton] at h ⊢ <;> omega
      · intro hk h9
        simp only [List.cons_append] at hk h9 ⊢
        simp only [beq_eq_false_iff_ne.mpr hk, beq_eq_false_iff_ne.mpr h9, Bool.false_or, Bool.false_eq_true, if_false]
        rw [pre]
      · intro h9 h0; subst h0; simp only [List.cons_append] at h9 ⊢
        rcases h9 with h9 | h9 <;> simp [h9]

/-! ### column 0 (after a newline) -/

theorem defW : (∀ y ∈ [100, 101, 102], isW (y : UInt8) = true) := by decide
theorem kindDef : kindC (dfa [100, 101, 102]) (pk [100, 101, 102]) 1 = kindC (dfa [100, 101, 102]) (pk [100, 101, 102]) 0 := by
  decide

/-- the word `def` at column 0 behaves as anywhere else -/
theorem C4def (z o : List UInt8) (hz : hd? z isW = false) (m sp d d0 w ty cz cz' : UInt64) (hm : (m == 5) = false)
    (hsp : sp = 0 ∨ sp = 1) :
    lx (100 :: 101 :: 102 :: z) o m 4 sp d d0 w ty cz = lx (100 :: 101 :: 102 :: z) o m 0 sp d d0 w ty cz' := by
  have e4 := WordStart o m 4 sp d d0 w ty cz 100 102 [101] z (by decide) (by decide) (by decide) hm (Or.inr rfl)
  have e0 := WordStart o m 0 sp d d0 w ty cz' 100 102 [101] z (by decide) (by decide) (by decide) hm (Or.inl rfl)
  simp only [List.singleton_append, List.cons_append, List.nil_append] at e4 e0
  rw [e4, e0]; simp only [if_true, show ((0 : UInt64) = 4) = False by decide, if_false]
  congr 1
  rcases z with _ | ⟨n, t⟩
  · rcases hsp with h | h <;> subst h
    · rw [W_quirk 102 (Or.inr (by decide)) _ _ _ _ _ _ _ hm, W_quirk 102 (Or.inr (by decide)) _ _ _ _ _ _ _ hm]
      have : kindOf (dfa [100, 101]) (pk [100, 101, 102] >>> 8) = 9 := by decide
      simp [this]
    · rw [W_lastE 102 _ _ _ _ _ _ _ hm, W_lastE 102 _ _ _ _ _ _ _ hm]
      have kd := kindDef
      simp only [List.cons_append, List.nil_append, List.singleton_append] at kd ⊢
      rw [kd]
  · have hn : isW n = false := by simpa [hd?] using hz
    rw [W_last 102 n hn _ _ _ _ _ _ _ _ _ hm, W_last 102 n hn _ _ _ _ _ _ _ _ _ hm]
    have kd := kindDef
    simp only [List.cons_append, List.nil_append, List.singleton_append] at kd ⊢
    rw [kd]

theorem M_sp4 (rest o : List UInt8) (m sp d d0 w ty cz : UInt64) (hm : (m == 5) = false) :
    lx (32 :: rest) o m 4 sp d d0 w ty cz = lx rest o m 0 sp d d0 w ty 0 := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1, lx_nil _ _ _ _ _ _ _ _ _ hm]; simp [hm]
  · rw [lx_c2]; simp [hm]

theorem M_nl4 (rest o : List UInt8) (m sp d d0 w ty cz : UInt64) (hm : (m == 5) = false) :
    lx (10 :: rest) o m 4 sp d d0 w ty cz = lx rest o m 4 sp d d0 w ty 0 := by
  rcases rest with _ | ⟨n, t⟩
  · rw [lx_c1, lx_nil _ _ _ _ _ _ _ _ _ hm]; simp [hm]
  · rw [lx_c2]; simp [hm]

theorem lx_nil_eq (o : List UInt8) (m st sp d d0 w ty cz st' sp' d' d0' w' cz' : UInt64) (hm : (m == 5) = false) :
    lx [] o m st sp d d0 w ty cz = lx [] o m st' sp' d' d0' w' ty cz' := by
  rw [lx_nil _ _ _ _ _ _ _ _ _ hm, lx_nil _ _ _ _ _ _ _ _ _ hm]

theorem C4pos (xs o : List UInt8) (h : colOk xs = true) (m sp d d0 w ty cz cz' : UInt64) (hm : (m == 5) = false)
    (hsp : sp = 0 ∨ sp = 1) : lx xs o m 4 sp d d0 w ty cz = lx xs o m 0 sp d d0 w ty cz' := by
  rcases xs with _ | ⟨c, rest⟩
  · exact lx_nil_eq o m 4 sp d d0 w ty cz 0 sp d d0 w cz' hm
  by_cases h32 : c = 32
  · subst h32; rw [M_sp4 _ _ _ _ _ _ _ _ _ hm, M_sp _ _ _ _ _ _ _ _ _ hm]
  by_cases h10 : c = 10
  · subst h10; rw [M_nl4 _ _ _ _ _ _ _ _ _ hm, M_nl _ _ _ _ _ _ _ _ _ hm]
  have : c = 100 ∧ ∃ z, rest = 101 :: 102 :: z ∧ hd? z isW = false := by
    unfold colOk at h; split at h <;> simp_all
  obtain ⟨rfl, z, rfl, hz⟩ := this
  exact C4def z o hz m sp d d0 w ty cz cz' hm hsp

theorem kindC1 (D : UInt64) (U : List UInt8) (h : U ≠ [100, 101, 102]) : kindC D (pk U) 1 = 9 := by
  have e : (0x1646566 : UInt64) = pk [100, 101, 102] := by decide
  unfold kindC; rw [e, pk_beq U _ (by decide)]; simp [h]

theorem C4neg (xs o : List UInt8) (h : colOk xs = false) (sp d d0 w ty cz : UInt64) (hsp : sp = 0 ∨ sp = 1) :
    lx xs o 0 4 sp d d0 w ty cz = [0] := by
  have hm : ((0 : UInt64) == 5) = false := by decide
  rcases xs with _ | ⟨c, rest⟩
  · simp [colOk] at h
  have h32 : c ≠ 32 := by intro e; subst e; simp [colOk] at h
  have h10 : c ≠ 10 := by intro e; subst e; simp [colOk] at h
  by_cases hc : isW c = true
  · obtain ⟨u, r, rfl, hu, hr⟩ := span_exists isW rest
    rcases List.eq_nil_or_concat u with rfl | ⟨v, z, rfl⟩
    · rcases r with _ | ⟨n, t⟩
      · exact W_singleE4 c hc _ _ _ _ _ _ _ _ hm
      · exact W_single4 c n hc (by simpa [hd?] using hr) _ _ _ _ _ _ _ _ _ hm
    · simp only [List.concat_eq_append] at *
      have hv : ∀ y ∈ v, isW y = true := fun y hy => hu y (by simp [hy])
      have hz : isW z = true := hu z (by simp)
      have hne : c :: v ++ [z] ≠ [100, 101, 102] := by
        intro e
        have : c = 100 ∧ v = [101] ∧ z = 102 := by
          rcases v with _ | ⟨a, _ | ⟨b, v⟩⟩ <;> simp_all
        obtain ⟨rfl, rfl, rfl⟩ := this
        simp [colOk] at h; rw [hr] at h; simp at h
      rw [show c :: (v ++ [z] ++ r) = c :: (v ++ z :: r) by simp, WordStart o 0 4 sp d d0 w ty cz c z v r hc hv hz hm (Or.inr rfl)]
      simp only [if_true, List.nil_append]
      rcases r with _ | ⟨n, t⟩
      · rcases hsp with rfl | rfl
        · by_cases hg : isDigit z = true ∨ isLower' z = true
          · rw [W_quirk z hg _ _ _ _ _ _ _ hm]; simp
          · simp only [not_or, Bool.not_eq_true] at hg; exact W_quirkBad z hg.1 hg.2 _ _ _ _ _ _ _ hm
        · rw [W_lastE z _ _ _ _ _ _ _ hm, kindC1 _ _ hne]; simp
      · rw [W_last z n (by simpa [hd?] using hr) _ _ _ _ _ _ _ _ _ hm, kindC1 _ _ hne]; simp
  · have hcf : (c == 32) = false ∧ (c == 10) = false ∧ isW c = false := ⟨by simpa using h32, by simpa using h10, by simpa using hc⟩
    rcases rest with _ | ⟨n, t⟩
    · rw [lx_c1]; simp only [hm, hcf.1, hcf.2.1]; simp
    · rw [lx_c2]; simp only [hm, hcf.1, hcf.2.1, hcf.2.2]; simp
theorem dec_p (b : UInt8) (t : Tok) (hb : (b = 40 ∧ t = .lp) ∨ (b = 41 ∧ t = .rp) ∨ (b = 42 ∧ t = .star) ∨
    (b = 43 ∧ t = .plus) ∨ (b = 45 ∧ t = .minus) ∨ (b = 58 ∧ t = .colon) ∨ (b = 59 ∧ t = .semi) ∨ (b = 61 ∧ t = .assign))
    (X : List UInt8) : dec ([b] ++ X) [] none = (dec X [] none).map (t :: ·) := by
  rcases hb with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> subst h h' <;>
    simp [dec, isW, isL]


theorem Fu_sp (F : Nat) (xs : List UInt8) (sp : UInt64) (h : Fu F xs sp) : sp = 0 ∨ sp = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

theorem step0 (o xs : List UInt8) (hxs : xs ≠ []) (F : Nat) (sp : UInt64) (hF : Fu F xs sp)
    (m d d0 w ty cz : UInt64) (hm : (m == 5) = false) (hty : ty ≠ 9) : S0 o xs F sp m d d0 w ty cz := by
  rcases xs with _ | ⟨c, rest⟩
  · exact absurd rfl hxs
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by rcases hF with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h <;> omega⟩
  have hFt := Fu_tail f c rest sp hF
  have hlen : ∀ r : List UInt8, r.length ≤ rest.length → r.length < (c :: rest).length := fun r h => by simp; omega
  unfold S0 S0g
  -- punctuation tokens: one byte, one token
  have punct : ∀ (t : Tok) (bs : List UInt8), (∀ X, dec (bs ++ X) [] none = (dec X [] none).map (t :: ·)) →
      tyStep ty t = ty → lex (f + 1) (c :: rest) = (lex f rest).map (t :: ·) →
      lx (c :: rest) o m 0 sp d d0 w ty cz = (if m = 0 then [] else bs) ++ lx rest o m 0 sp d d0 w ty 0 →
      S0g o (c :: rest).length (lex (f + 1) (c :: rest)) (lx (c :: rest) o m 0 sp d d0 w ty cz) m ty := by
    intro t bs hd hts hl hx
    right; right
    exact ⟨t, bs, f, rest, sp, d, d0, w, 0, hlen rest (Nat.le_refl _), hFt, hl, hd, fun _ => by rw [hts]; exact hx,
      fun h => absurd (hts ▸ h) hty⟩
  by_cases h32 : c = 32
  · subst h32; right; left
    exact ⟨f, rest, sp, d, d0, w, 0, hlen rest (Nat.le_refl _), hFt, L_sp f rest, M_sp _ _ _ _ _ _ _ _ _ hm⟩
  by_cases h10 : c = 10
  · subst h10
    rw [L_nl, M_nl _ _ _ _ _ _ _ _ _ hm]
    by_cases hc : colOk rest = true
    · right; left
      exact ⟨f, rest, sp, d, d0, w, 0, hlen rest (Nat.le_refl _), hFt, by simp [hc],
        C4pos rest o hc m sp d d0 w ty 0 0 hm (Fu_sp _ _ _ hF)⟩
    · left; simp only [Bool.not_eq_true] at hc
      refine ⟨by simp [hc], fun h0 => ?_⟩
      subst h0; exact C4neg rest o hc sp d d0 w ty 0 (Fu_sp _ _ _ hF)
  by_cases h58 : c = 58
  · subst h58
    rcases rest with _ | ⟨n, t⟩
    · exact punct .colon [58] (dec_p 58 .colon (by simp)) rfl (by rw [L_colon]) (by rw [M_colon _ _ _ _ _ _ _ _ _ hm])
    · by_cases hn : n = 61
      · subst hn; right; right
        refine ⟨.assign, [61], f, t, 1, d, d0, w, 0, by simp only [List.length_cons]; omega, Or.inr ⟨rfl, ?_⟩,
          by rw [L_colon]; simp, dec_p 61 .assign (by simp), fun _ => by rw [M_colon _ _ _ _ _ _ _ _ _ hm]; simp [tyStep],
          fun h => absurd h hty⟩
        rcases hF with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h <;> omega
      · exact punct .colon [58] (dec_p 58 .colon (by simp)) rfl (by rw [L_colon]; simp [hn])
          (by rw [M_colon _ _ _ _ _ _ _ _ _ hm]; simp [hn])
  by_cases hp : c = 40 ∨ c = 41 ∨ c = 42 ∨ c = 43 ∨ c = 59
  · rcases hp with h | h | h | h | h <;> subst h
    · exact punct .lp [40] (dec_p 40 .lp (by simp)) rfl (L_punct 40 f rest .lp (by simp)) (M_punct 40 (by simp) rest o m sp d d0 w ty cz hm)
    · exact punct .rp [41] (dec_p 41 .rp (by simp)) rfl (L_punct 41 f rest .rp (by simp)) (M_punct 41 (by simp) rest o m sp d d0 w ty cz hm)
    · exact punct .star [42] (dec_p 42 .star (by simp)) rfl (L_punct 42 f rest .star (by simp)) (M_punct 42 (by simp) rest o m sp d d0 w ty cz hm)
    · exact punct .plus [43] (dec_p 43 .plus (by simp)) rfl (L_punct 43 f rest .plus (by simp)) (M_punct 43 (by simp) rest o m sp d d0 w ty cz hm)
    · exact punct .semi [59] (dec_p 59 .semi (by simp)) rfl (L_punct 59 f rest .semi (by simp)) (M_punct 59 (by simp) rest o m sp d d0 w ty cz hm)
  by_cases h45 : c = 45
  · subst h45
    by_cases hb : hd? rest (· == 45) = true
    · left; exact ⟨by rw [L_minus]; simp [hb], fun _ => by rw [M_minus _ _ _ _ _ _ _ _ _ hm]; simp [hb]⟩
    · exact punct .minus [45] (dec_p 45 .minus (by simp)) rfl (by rw [L_minus]; simp [hb])
        (by rw [M_minus _ _ _ _ _ _ _ _ _ hm]; simp [hb])
  by_cases hw : isW c = true
  · have := step0_word o c hw rest f sp hF m d d0 w ty cz hm hty
    unfold S0 S0g at this; exact this
  have hc : (c == 32 || c == 10 || c == 40 || c == 41 || c == 43 || c == 45 || c == 42 ||
      c == 59 || c == 58 || isW c) = false := by
    simp only [not_or] at hp; simp_all
  left; exact ⟨L_other c hc f rest, fun _ => M_other c hc rest o m sp d d0 w ty cz hm⟩

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
theorem pass1 (o : List UInt8) : ∀ (n : Nat) (xs : List UInt8), xs.length ≤ n → ∀ F sp d d0 w ty cz, Fu F xs sp →
    (ty = 0 ∨ ty = 1 ∨ ty = 2) → lx xs o 0 0 sp d d0 w ty cz = R1 o (lex F xs) ty := by
  intro n
  induction n with
  | zero =>
    intro xs hl F sp d d0 w ty cz _ hty
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; rw [lx_nil _ _ _ _ _ _ _ _ _ (by decide), lex_nil]
    rcases hty with h | h | h <;> subst h <;> rfl
  | succ n ih =>
    intro xs hl F sp d d0 w ty cz hF hty
    rcases xs with _ | ⟨c, xs⟩
    · rw [lx_nil _ _ _ _ _ _ _ _ _ (by decide), lex_nil]; rcases hty with h | h | h <;> subst h <;> rfl
    have hty9 : ty ≠ 9 := by rcases hty with h | h | h <;> subst h <;> decide
    have h0 := step0 o (c :: xs) (by simp) F sp hF 0 d d0 w ty cz (by decide) hty9
    unfold S0 S0g at h0
    rcases h0 with ⟨hn, hl0⟩ | ⟨F', r, sp', d', d0', w', cz', hr, hF', he, hx⟩ |
      ⟨t, bs, F', r, sp', d', d0', w', cz', hr, hF', he, _, hx, hx9⟩
    · rw [hl0 rfl, hn]; rfl
    · rw [hx, he]; exact ih r (by simp only [List.length_cons] at hl hr; omega) F' sp' d' d0' w' ty cz' hF' hty
    · rw [he, R1_cons o t _ ty hty]
      split
      · exact hx9 ‹_› rfl
      · rw [hx ‹_›]; simp only [if_true, List.nil_append]
        exact ih r (by simp only [List.length_cons] at hl hr; omega) F' sp' d' d0' w' _ cz' hF' (tyStep_ok ty t hty ‹_›)

theorem uniTy_some (s : Bool) : ∀ (ts : List Tok) (s' : Bool), uniTy (some s) ts = some s' → s' = s
  | [], _, h => by simp [uniTy] at h; exact h.symm
  | t :: ts, s', h => by
    cases t <;> simp only [uniTy] at h <;> (try exact uniTy_some s ts s' h)
    rename_i b; split at h
    · simp at *; subst_vars; exact uniTy_some _ ts s' h
    · cases h

/-- **pass 2**: the machine's bytes decode to `lex`'s tokens -/
theorem pass2 (o : List UInt8) (s : Bool) : ∀ (n : Nat) (xs : List UInt8), xs.length ≤ n → ∀ F sp d d0 w cz ts, Fu F xs sp →
    lex F xs = some ts → uniTy (some s) ts = some s → dec (lx xs o 1 0 sp d d0 w (tcode s) cz) [] none = some ts := by
  intro n
  induction n with
  | zero =>
    intro xs hl F sp d d0 w cz ts _ hlex _
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; rw [lex_nil] at hlex; cases hlex; rw [lx_nil _ _ _ _ _ _ _ _ _ (by decide)]; rfl
  | succ n ih =>
    intro xs hl F sp d d0 w cz ts hF hlex hu
    rcases xs with _ | ⟨c, xs⟩
    · rw [lex_nil] at hlex; cases hlex; rw [lx_nil _ _ _ _ _ _ _ _ _ (by decide)]; rfl
    have h0 := step0 o (c :: xs) (by simp) F sp hF 1 d d0 w (tcode s) cz (by decide) (by cases s <;> decide)
    unfold S0 S0g at h0
    rcases h0 with ⟨hn, _⟩ |
      ⟨F', r, sp', d', d0', w', cz', hr, hF', he, hx⟩ | ⟨t, bs, F', r, sp', d', d0', w', cz', hr, hF', he, hdec, hx, _⟩
    · rw [hn] at hlex; cases hlex
    · rw [hx]; rw [he] at hlex; exact ih r (by simp only [List.length_cons] at hl hr; omega) F' sp' d' d0' w' cz' ts hF' hlex hu
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
      rw [hdec, ih r (by simp only [List.length_cons] at hl hr; omega) F' sp' d' d0' w' cz' ts' hF' hl' hu']; rfl

theorem uniTy_none (s : Bool) : ∀ (ts : List Tok), uniTy none ts = some s → uniTy (some s) ts = some s
  | [], h => by simp [uniTy] at h
  | t :: ts, h => by
    cases t <;> simp only [uniTy] at h ⊢ <;> (try exact uniTy_none s ts h)
    rename_i b
    have := uniTy_some b ts s h; subst this; simp [h]

/-- the adjacency pass: `adjOk` of the rest, then pass 1 from the start -/
theorem adjPass (o : List UInt8) : ∀ (xs : List UInt8) (st sp d d0 w ty cz : UInt64),
    lx xs o 5 st sp d d0 w ty cz = if adjOk xs then lx o o 0 0 0 0 0 0 0 0 else [0]
  | [], _, _, _, _, _, _, _ => by rw [lx]; simp [adjOk]
  | [c], _, _, _, _, _, _, _ => by rw [lx_c1]; simp [adjOk]
  | c :: n :: t, st, sp, d, d0, w, ty, cz => by
    rw [lx_c2]; simp only [show ((5 : UInt64) == 5) = true by decide, if_true]
    rw [adjPass o (n :: t) 0 sp d d0 w ty cz]
    have ha : adjOk (c :: n :: t) = (!((isW c || c == 41) && n == 40) && !(c == 41 && isW n) && adjOk (n :: t)) := by
      simp only [adjOk, isW_eq]
    rw [ha]
    by_cases h40 : n = 40
    · subst h40; by_cases hc : (isW c || c == 41) = true
      · simp [hc]
      · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hc
        have : c ≠ 41 := by simpa using hc.2
        simp [hc.1, this]
    · have : (n == 40) = false := by simpa using h40
      by_cases h41 : c = 41
      · subst h41; by_cases hn : isW n = true <;> simp [hn, this]
      · have : (c == 41) = false := by simpa using h41
        simp [*]

/-- **stage 1 is the front of `nanoElab`** (adjacency check, lexer, type check): for every byte list -/
theorem lexB_eq (xs : List UInt8) : decL (lexB xs) = lexT xs := by
  unfold lexB lexT
  rw [adjPass xs xs 0 0 0 0 0 0 0]
  by_cases ha : adjOk xs = true
  · simp only [ha, if_true]
    rw [pass1 xs xs.length xs (Nat.le_refl _) xs.length 0 0 0 0 0 0 (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl)]
    rcases hl : lex xs.length xs with _ | ts
    · rfl
    · simp only [R1, tyOf, show (0 : UInt64) ≠ 1 by decide, show (0 : UInt64) ≠ 2 by decide, if_false]
      rcases hu : uniTy none ts with _ | s
      · rfl
      · have h2 := pass2 xs s xs.length xs (Nat.le_refl _) xs.length 0 0 0 0 0 ts (Or.inl ⟨rfl, rfl⟩) hl (uniTy_none s ts hu)
        cases s <;> simp only [tcode, decL] at h2 ⊢ <;> simp at h2 ⊢ <;> rw [h2] <;> rfl
  · simp only [Bool.not_eq_true] at ha; simp [ha, decL]

end Nano.B
