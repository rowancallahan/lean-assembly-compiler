/- Stage 1 and parser stage 2a in ONE S3 stage (branch nano-final): `lexA xs = encT (lexT xs)` (the tag format of
`Nano/ParseS3B.lean` applied to the specification of stage 1), written in the form the S3 front end accepts:
explicit recursion instead of `List.all`/`foldl`, `consO` instead of `Option.map`, no byte-literal patterns, no `UInt8`
subtraction.  Bridge `lexA_eq : lexA xs = stage2a (lexB xs)` on every input (through `lexB_eq`). -/
import Legacy.Nano.ParseS3B
import Legacy.Nano.ElabBProof

namespace Nano.LS
open Nano Nano.B Nano.PS

def consP (c : UInt8) : List UInt8 × List UInt8 → List UInt8 × List UInt8
  | (a, b) => (c :: a, b)

/-- `spanId` -/
def spanS : Nat → List UInt8 → List UInt8 × List UInt8
  | 0, xs => ([], xs)
  | _ + 1, [] => ([], [])
  | f + 1, c :: xs => if isWordC c then consP c (spanS f xs) else ([], c :: xs)

/-- `w.all isDigit` -/
def allDig : List UInt8 → Bool
  | [] => true
  | d :: r => isDigit d && allDig r

/-- `cs.all fun d => isDigit d || d == 95` -/
def allDU : List UInt8 → Bool
  | [] => true
  | d :: r => (isDigit d || d == 95) && allDU r

/-- the numeral's value (`foldl` on digits) -/
def numW : UInt64 → List UInt8 → UInt64
  | a, [] => a
  | a, d :: r => numW (a * 10 + (d.toUInt64 - 48)) r

def identOkS : List UInt8 → Bool
  | c :: cs => (97 ≤ c && c ≤ 122) && allDU cs
  | [] => false

/-- the word is `def` -/
def isDef : List UInt8 → Bool
  | a :: b :: c :: r => a == 100 && b == 101 && c == 102 && r.isEmpty
  | _ => false
/-- the word is `let` -/
def isLet : List UInt8 → Bool
  | a :: b :: c :: r => a == 108 && b == 101 && c == 116 && r.isEmpty
  | _ => false
/-- the word is `UInt64` -/
def isU64 : List UInt8 → Bool
  | a :: b :: c :: d :: e :: g :: r => a == 85 && b == 73 && c == 110 && d == 116 && e == 54 && g == 52 && r.isEmpty
  | _ => false
/-- the word is `Int64` -/
def isI64 : List UInt8 → Bool
  | a :: b :: c :: d :: e :: r => a == 73 && b == 110 && c == 116 && d == 54 && e == 52 && r.isEmpty
  | _ => false

/-- the next byte is a word character -/
def nextW : List UInt8 → Bool
  | h :: _ => isWordC h
  | [] => false

def wordTokS (w : List UInt8) : Option Tok :=
  match w with
  | [] => none
  | c :: _ =>
    if isDigit c then (if allDig w then some (Tok.num (numW 0 w)) else none)
    else if isDef w then some Tok.kdef else if isLet w then some Tok.klet
    else if isU64 w then some (Tok.kty false)
    else if isI64 w then some (Tok.kty true)
    else if identOkS w then some (Tok.id w) else none

/-- `lex` -/
def lexS : Nat → List UInt8 → Option (List Tok)
  | 0, xs => match xs with
    | [] => some []
    | _ :: _ => none
  | _ + 1, [] => some []
  | f + 1, c :: xs =>
    if c == 32 then lexS f xs
    else if c == 10 then
      match xs with
      | [] => some []
      | d :: z =>
        if d == 32 then lexS f xs
        else if d == 10 then lexS f xs
        else if d == 100 then
          match z with
          | e :: z2 =>
            if e == 101 then
              match z2 with
              | g :: z3 =>
                if g == 102 then
                  (if nextW z3 then none else lexS f xs)
                else none
              | [] => none
            else none
          | [] => none
        else none
    else if c == 40 then consO Tok.lp (lexS f xs)
    else if c == 41 then consO Tok.rp (lexS f xs)
    else if c == 43 then consO Tok.plus (lexS f xs)
    else if c == 45 then
      match xs with
      | d :: _ => if d == 45 then none else consO Tok.minus (lexS f xs)
      | [] => consO Tok.minus (lexS f xs)
    else if c == 42 then consO Tok.star (lexS f xs)
    else if c == 59 then consO Tok.semi (lexS f xs)
    else if c == 58 then
      match xs with
      | d :: ys => if d == 61 then consO Tok.assign (lexS f ys) else consO Tok.colon (lexS f xs)
      | [] => consO Tok.colon (lexS f xs)
    else if isWordC c then
      match spanS f (c :: xs) with
      | (w, r) =>
        match wordTokS w with
        | some t => consO t (lexS f r)
        | none => none
    else none

/-- a type token's code: 1 `UInt64`, 2 `Int64`; 0 other tokens -/
def tyCode : Tok → UInt64
  | .kty s => if s then 2 else 1
  | _ => 0

/-- `uniTy` on a code: 0 no type yet, 1 / 2 the type, 3 a conflict -/
def uniW : UInt64 → List Tok → UInt64
  | t, [] => t
  | t, x :: r =>
    if tyCode x == 0 then uniW t r
    else if t == 0 then uniW (tyCode x) r
    else if t == tyCode x then uniW t r
    else 3

/-- the type codes of the tokens -/
def codes : List Tok → List UInt64
  | [] => []
  | x :: r => tyCode x :: codes r

/-- `uniW` on the codes (the form S3 compiles) -/
def uniC : UInt64 → List UInt64 → UInt64
  | t, [] => t
  | t, c :: r => if c == 0 then uniC t r else if t == 0 then uniC c r else if t == c then uniC c r else 3

def decT (c : UInt64) : Option Bool := if c == 1 then some false else if c == 2 then some true else none

def pairT : Option Bool → List Tok → Option (Bool × List Tok)
  | some b, ts => some (b, ts)
  | none, _ => none

def lexTS (xs : List UInt8) : Option (Bool × List Tok) :=
  if adjOk xs then
    (match lexS xs.length xs with
     | some ts => pairT (decT (uniC 0 (codes ts))) ts
     | none => none)
  else none

/-- **stage 1 + 2a** -/
def lexA (xs : List UInt8) : List UInt8 := encT (lexTS xs)

/-- a byte of a word, in the normal form the S3 certificates reach (for `le8`) -/
theorem le8_byte (x : UInt64) (k : Nat) :
    BitVec.setWidth 64 (UInt8.ofNat (x.toNat >>> k)).toBitVec = x.toBitVec >>> k &&& 255#64 := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (255#64).toNat = 2 ^ 8 - 1 := rfl
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ushiftRight, UInt8.toNat_toBitVec,
    UInt64.toNat_toBitVec, h1, Nat.and_two_pow_sub_one_eq_mod, UInt8.toNat_ofNat']
  have : (x.toNat >>> k) % 2 ^ 8 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt (by simpa using this)]

/-! ## the bridge -/

theorem spanS_eq : ∀ f xs, spanS f xs = spanId f xs
  | 0, xs => by simp [spanS, spanId]
  | _ + 1, [] => by simp [spanS, spanId]
  | f + 1, c :: xs => by
    simp only [spanS, spanId, spanS_eq f xs]
    split
    · cases spanId f xs; rfl
    · rfl

theorem allDig_eq : ∀ w, allDig w = w.all isDigit
  | [] => rfl
  | d :: r => by simp [allDig, allDig_eq r]

theorem allDU_eq : ∀ w, allDU w = w.all fun d => isDigit d || d == 95
  | [] => rfl
  | d :: r => by simp [allDU, allDU_eq r]

theorem numW_eq : ∀ (a : UInt64) (w : List UInt8), w.all isDigit = true →
    numW a w = w.foldl (fun a d => a * 10 + (d - 48).toUInt64) a
  | a, [] => fun _ => rfl
  | a, d :: r => fun h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [numW, List.foldl_cons, sub48 d h.1]
    exact numW_eq _ r h.2

theorem identOkS_eq (w : List UInt8) : identOkS w = identOk w := by
  cases w with
  | nil => rfl
  | cons c cs => simp [identOkS, identOk, allDU_eq]

theorem isDef_eq (w : List UInt8) : isDef w = (w == [100, 101, 102]) := by
  match w with
  | a :: b :: c :: r => cases r <;> simp [isDef, Bool.and_assoc]
  | [] | [_] | [_, _] => simp [isDef]
theorem isLet_eq (w : List UInt8) : isLet w = (w == [108, 101, 116]) := by
  match w with
  | a :: b :: c :: r => cases r <;> simp [isLet, Bool.and_assoc]
  | [] | [_] | [_, _] => simp [isLet]
theorem isU64_eq (w : List UInt8) : isU64 w = (w == [85, 73, 110, 116, 54, 52]) := by
  match w with
  | a :: b :: c :: d :: e :: g :: r => cases r <;> simp [isU64, Bool.and_assoc]
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] => simp [isU64]
theorem isI64_eq (w : List UInt8) : isI64 w = (w == [73, 110, 116, 54, 52]) := by
  match w with
  | a :: b :: c :: d :: e :: r => cases r <;> simp [isI64, Bool.and_assoc]
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] => simp [isI64]

theorem wordTokS_eq (w : List UInt8) : wordTokS w = wordTok w := by
  cases w with
  | nil => rfl
  | cons c r =>
    simp only [wordTokS, wordTok, identOkS_eq, kwDef, kwLet, kwTy, kwTyI, isDef_eq, isLet_eq, isU64_eq, isI64_eq]
    split
    · rw [allDig_eq]; split
      · rw [numW_eq 0 _ ‹_›]
      · rfl
    · rfl

theorem consO_eq' (t : Tok) (o : Option (List Tok)) : consO t o = o.map (t :: ·) := by cases o <;> rfl

theorem lexS_eq : ∀ f xs, lexS f xs = lex f xs
  | 0, [] => rfl
  | 0, _ :: _ => rfl
  | _ + 1, [] => rfl
  | f + 1, c :: xs => by
    have ih := lexS_eq f
    unfold lexS lex
    simp only [consO_eq', ih]
    by_cases h32 : c = 32
    · simp [h32]
    by_cases h10 : c = 10
    · subst h10
      simp only [show ((10 : UInt8) == 32) = false from rfl, Bool.false_eq_true, if_false, beq_self_eq_true, if_true]
      rcases xs with _ | ⟨d, z⟩
      · rfl
      by_cases d32 : d = 32
      · subst d32; simp [ih]
      by_cases d10 : d = 10
      · subst d10; simp [ih]
      by_cases d100 : d = 100
      · subst d100
        rcases z with _ | ⟨e, z2⟩
        · rfl
        by_cases e101 : e = 101
        · subst e101
          rcases z2 with _ | ⟨g, z3⟩
          · rfl
          by_cases g102 : g = 102
          · subst g102; simp only [beq_self_eq_true, if_true]; rcases z3 with _ | ⟨h, t⟩ <;> simp [nextW]
          · simp [g102]
        · simp [e101]
      · simp [d32, d10, d100]
    simp only [beq_iff_eq, h32, h10, if_false]
    by_cases h40 : c = 40
    · simp [h40]
    by_cases h41 : c = 41
    · simp [h41]
    by_cases h43 : c = 43
    · simp [h43]
    by_cases h45 : c = 45
    · subst h45
      simp only [show ((45 : UInt8) = 40) = False by decide, show ((45 : UInt8) = 41) = False by decide,
        show ((45 : UInt8) = 43) = False by decide, if_false, if_true]
      rcases xs with _ | ⟨d, z⟩
      · rfl
      by_cases d45 : d = 45
      · subst d45; rfl
      · simp [d45]
    by_cases h42 : c = 42
    · simp [h42]
    by_cases h59 : c = 59
    · simp [h59]
    by_cases h58 : c = 58
    · subst h58
      simp only [show ((58 : UInt8) = 40) = False by decide, show ((58 : UInt8) = 41) = False by decide,
        show ((58 : UInt8) = 43) = False by decide, show ((58 : UInt8) = 45) = False by decide,
        show ((58 : UInt8) = 42) = False by decide, show ((58 : UInt8) = 59) = False by decide, if_false, if_true]
      rcases xs with _ | ⟨d, z⟩
      · rfl
      by_cases d61 : d = 61
      · subst d61; rfl
      · simp [d61]
    simp only [h40, h41, h43, h45, h42, h59, h58, if_false]
    split
    · rw [spanS_eq]
      rcases hs : spanId (f + 1) (c :: xs) with ⟨w, r⟩
      simp only [wordTokS_eq]
      split <;> simp_all
    · rfl

def codeT : Option Bool → UInt64
  | none => 0
  | some false => 1
  | some true => 2

theorem uniW3 : ∀ ts, uniW 3 ts = 3
  | [] => rfl
  | x :: r => by cases x <;> simp [uniW, tyCode, uniW3 r] <;> (rename_i s; cases s <;> simp)

theorem uniW_eq : ∀ t ts, decT (uniW (codeT t) ts) = uniTy t ts
  | t, [] => by cases t with | none => rfl | some b => cases b <;> rfl
  | t, x :: r => by
    have ih : ∀ t, decT (uniW (codeT t) r) = uniTy t r := fun t => uniW_eq t r
    have ih1 : decT (uniW 1 r) = uniTy (some false) r := ih (some false)
    have ih2 : decT (uniW 2 r) = uniTy (some true) r := ih (some true)
    have ih1' := ih1
    have ih2' := ih2
    simp only [decT, beq_iff_eq] at ih1' ih2' 
    cases x
    case kty s =>
      cases t with
      | none => cases s <;> simp only [uniW, tyCode, codeT, uniTy] <;> simp <;>
          first | exact ih1 | exact ih2 | exact ih1' | exact ih2'
      | some b => cases b <;> cases s <;> simp [uniW, tyCode, codeT, uniTy, decT, uniW3] <;>
          first | exact ih1 | exact ih2 | exact ih1' | exact ih2'
    all_goals (simp only [uniW, tyCode, beq_self_eq_true, if_true, uniTy]; exact ih t)

theorem uniC_codes : ∀ t ts, uniC t (codes ts) = uniW t ts
  | t, [] => rfl
  | t, x :: r => by
    simp only [codes, uniC, uniW, uniC_codes _ r]
    by_cases h0 : tyCode x = 0
    · simp [h0]
    by_cases ht : t = 0
    · simp [h0, ht]
    by_cases he : t = tyCode x
    · subst he; simp [h0]
    · simp [h0, ht, he]

theorem lexTS_eq (xs : List UInt8) : lexTS xs = lexT xs := by
  unfold lexTS lexT
  by_cases h : adjOk xs = true
  · simp only [h, if_true, lexS_eq]
    cases lex xs.length xs with
    | none => rfl
    | some ts => simp only [uniC_codes, show (0 : UInt64) = codeT none from rfl, uniW_eq]; cases uniTy none ts <;> rfl
  · simp only [h, if_false, Bool.false_eq_true]

/-- **stage 1 + 2a, bridge** -/
theorem lexA_eq (xs : List UInt8) : lexA xs = stage2a (lexB xs) := by
  rw [lexA, stage2a, lexB_eq, lexTS_eq]

end Nano.LS
