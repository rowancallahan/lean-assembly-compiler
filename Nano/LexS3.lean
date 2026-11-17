/- Stage 1 and parser stage 2a in ONE S3 stage (branch nano-final): `lexA xs = encT (lexT xs)` (the tag format of
`Nano/ParseS3B.lean` applied to the specification of stage 1), written in the form the S3 front end accepts:
explicit recursion instead of `List.all`/`foldl`, `consO` instead of `Option.map`, no byte-literal patterns, no `UInt8`
subtraction.  Bridge `lexA_eq : lexA xs = stage2a (lexB xs)` on every input (through `lexB_eq`). -/
import Nano.ParseS3B
import Nano.ElabBProof

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

def wordTokS (w : List UInt8) : Option Tok :=
  match w with
  | [] => none
  | c :: _ =>
    if isDigit c then (if allDig w then some (Tok.num (numW 0 w)) else none)
    else if w == [100, 101, 102] then some Tok.kdef else if w == [108, 101, 116] then some Tok.klet
    else if w == [85, 73, 110, 116, 54, 52] then some (Tok.kty false)
    else if w == [73, 110, 116, 54, 52] then some (Tok.kty true)
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
                  (if (match z3 with | h :: _ => isWordC h | [] => false) then none else lexS f xs)
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

def uniTyS : Option Bool → List Tok → Option Bool
  | t, [] => t
  | none, Tok.kty s :: ts => uniTyS (some s) ts
  | some t, Tok.kty s :: ts =>
    if t then (if s then uniTyS (some t) ts else none) else (if s then none else uniTyS (some t) ts)
  | t, _ :: ts => uniTyS t ts

def pairT : Option Bool → List Tok → Option (Bool × List Tok)
  | some b, ts => some (b, ts)
  | none, _ => none

def lexTS (xs : List UInt8) : Option (Bool × List Tok) :=
  if adjOk xs then
    (match lexS xs.length xs with
     | some ts => pairT (uniTyS none ts) ts
     | none => none)
  else none

/-- **stage 1 + 2a** -/
def lexA (xs : List UInt8) : List UInt8 := encT (lexTS xs)

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

theorem wordTokS_eq (w : List UInt8) : wordTokS w = wordTok w := by
  cases w with
  | nil => rfl
  | cons c r =>
    simp only [wordTokS, wordTok, identOkS_eq, kwDef, kwLet, kwTy, kwTyI]
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
          · subst g102; simp only [beq_self_eq_true, if_true]; rcases z3 with _ | ⟨h, t⟩ <;> rfl
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

theorem uniTyS_eq : ∀ t ts, uniTyS t ts = uniTy t ts
  | t, [] => by cases t <;> rfl
  | none, Tok.kty s :: ts => by simp [uniTyS, uniTy, uniTyS_eq _ ts]
  | some t, Tok.kty s :: ts => by
    simp only [uniTyS, uniTy, uniTyS_eq _ ts]
    cases t <;> cases s <;> rfl
  | t, Tok.kdef :: ts | t, Tok.klet :: ts | t, Tok.id _ :: ts | t, Tok.num _ :: ts | t, Tok.lp :: ts
  | t, Tok.rp :: ts | t, Tok.colon :: ts | t, Tok.assign :: ts | t, Tok.plus :: ts | t, Tok.minus :: ts
  | t, Tok.star :: ts | t, Tok.semi :: ts => by cases t <;> simp [uniTyS, uniTy, uniTyS_eq _ ts]

theorem lexTS_eq (xs : List UInt8) : lexTS xs = lexT xs := by
  unfold lexTS lexT
  by_cases h : adjOk xs = true
  · simp only [h, if_true, lexS_eq]
    cases lex xs.length xs with
    | none => rfl
    | some ts => simp only [uniTyS_eq]; cases uniTy none ts <;> rfl
  · simp only [h, if_false, Bool.false_eq_true]

/-- **stage 1 + 2a, bridge** -/
theorem lexA_eq (xs : List UInt8) : lexA xs = stage2a (lexB xs) := by
  rw [lexA, stage2a, lexB_eq, lexTS_eq]

end Nano.LS
