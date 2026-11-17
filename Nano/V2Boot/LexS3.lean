/- B₁: the v2 lexer `lexV` (Nano/V2S/Lex.lean, stage 1 + 2a) in S3 form (Nano/V2Boot/Prelude.lean) and the bridge
`lexVS_eq : lexVS xs = lexV xs` (inputs of length < 2^64). `isWC`, `tyK`, `uni` are the v2 originals. -/
import Nano.V2S.Lex
import Nano.V2Boot.Prelude

namespace Nano.V2B
open Nano.V2S

def wordEndS (f : UInt64) (xs : List UInt8) (p : UInt64) : UInt64 :=
  if h : f = 0 then p
  else if p < lenS xs then (if isWC (rdS xs p) == 1 then wordEndS (f - 1) xs (p + 1) else p) else p
termination_by f.toNat
decreasing_by exact dec_lt h

/-- 1 if `c` is a digit (the compound test as a function: S3 certificates refute only atomic loop conditions) -/
def digW (c : UInt64) : UInt64 := if 48 ≤ c && c ≤ 57 then 1 else 0
/-- 1 if `c` is a digit or `_` -/
def digUW (c : UInt64) : UInt64 := if (48 ≤ c && c ≤ 57) || c == 95 then 1 else 0
/-- 1 if the adjacent pair `a b` is rejected by `adjOk` -/
def adjBad (a b : UInt64) : UInt64 :=
  if (isWC a == 1 || a == 41) && b == 40 then 1 else if a == 41 && isWC b == 1 then 1 else 0

def allDigRS (f : UInt64) (xs : List UInt8) (i e : UInt64) : UInt64 :=
  if h : f = 0 then 1
  else if i < e then (if digW (rdS xs i) == 1 then allDigRS (f - 1) xs (i + 1) e else 0) else 1
termination_by f.toNat
decreasing_by exact dec_lt h

def allDURS (f : UInt64) (xs : List UInt8) (i e : UInt64) : UInt64 :=
  if h : f = 0 then 1
  else if i < e then
    (if digUW (rdS xs i) == 1 then allDURS (f - 1) xs (i + 1) e else 0)
  else 1
termination_by f.toNat
decreasing_by exact dec_lt h

def numRS (f : UInt64) (xs : List UInt8) (i e a : UInt64) : UInt64 :=
  if h : f = 0 then a
  else if i < e then numRS (f - 1) xs (i + 1) e (a * 10 + (rdS xs i - 48)) else a
termination_by f.toNat
decreasing_by exact dec_lt h

def wordKS (n : UInt64) (xs : List UInt8) (p e : UInt64) : UInt64 :=
  if e ≤ p then 0
  else
    let c := rdS xs p
    if 48 ≤ c && c ≤ 57 then (if allDigRS n xs p e == 1 then 7 else 0)
    else if e - p == 3 && c == 100 && rdS xs (p + 1) == 101 && rdS xs (p + 2) == 102 then 3
    else if e - p == 3 && c == 108 && rdS xs (p + 1) == 101 && rdS xs (p + 2) == 116 then 4
    else if e - p == 6 && c == 85 && rdS xs (p + 1) == 73 && rdS xs (p + 2) == 110 && rdS xs (p + 3) == 116 &&
      rdS xs (p + 4) == 54 && rdS xs (p + 5) == 52 then 5
    else if e - p == 5 && c == 73 && rdS xs (p + 1) == 110 && rdS xs (p + 2) == 116 && rdS xs (p + 3) == 54 &&
      rdS xs (p + 4) == 52 then 6
    else if 97 ≤ c && c ≤ 122 && allDURS n xs (p + 1) e == 1 then 16
    else 0

def stepKS (f : UInt64) (xs : List UInt8) (p : UInt64) : UInt64 :=
  if p < lenS xs then
    let c := rdS xs p
    if c == 32 then 2
    else if c == 10 then
      if p + 1 < lenS xs then
        let d := rdS xs (p + 1)
        if d == 32 || d == 10 then 2
        else if d == 100 && p + 3 < lenS xs && rdS xs (p + 2) == 101 && rdS xs (p + 3) == 102 then
          (if p + 4 < lenS xs && isWC (rdS xs (p + 4)) == 1 then 0 else 2)
        else 0
      else 1
    else if c == 40 then 8
    else if c == 41 then 9
    else if c == 43 then 12
    else if c == 45 then (if p + 1 < lenS xs && rdS xs (p + 1) == 45 then 0 else 13)
    else if c == 42 then 14
    else if c == 59 then 15
    else if c == 58 then (if p + 1 < lenS xs && rdS xs (p + 1) == 61 then 11 else 10)
    else if isWC c == 1 then wordKS f xs p (wordEndS f xs p)
    else 0
  else 1

def stepNS (f : UInt64) (xs : List UInt8) (p : UInt64) : UInt64 :=
  let c := rdS xs p
  if c == 58 && p + 1 < lenS xs && rdS xs (p + 1) == 61 then p + 2
  else if isWC c == 1 then wordEndS f xs p
  else p + 1

def lexChkS (f : UInt64) (xs : List UInt8) (p t : UInt64) : UInt64 :=
  if h : f = 0 then (if p < lenS xs then 4 else t)
  else
    if stepKS (f - 1) xs p == 0 then 4
    else if stepKS (f - 1) xs p == 1 then t
    else lexChkS (f - 1) xs (stepNS (f - 1) xs p) (uni t (tyK (stepKS (f - 1) xs p)))
termination_by f.toNat
decreasing_by exact dec_lt h

def emitIdS (f : UInt64) (xs : List UInt8) (i e : UInt64) (o : List UInt8) : List UInt8 :=
  if h : f = 0 then putR o 0
  else if i < e then emitIdS (f - 1) xs (i + 1) e (putR (putR o 1) (rdS xs i)) else putR o 0
termination_by f.toNat
decreasing_by exact dec_lt h

def emitWR (o : List UInt8) (v : UInt64) : List UInt8 :=
  putR (putR (putR (putR (putR (putR (putR (putR o v) (v >>> 8)) (v >>> 16)) (v >>> 24)) (v >>> 32)) (v >>> 40))
    (v >>> 48)) (v >>> 56)

def emitTokS (f : UInt64) (xs : List UInt8) (k p e : UInt64) (o : List UInt8) : List UInt8 :=
  if k == 7 then emitWR (putR o 5) (numRS f xs p e 0)
  else if k == 16 then emitIdS f xs p e (putR o 14)
  else putR o (k - 2)

def lexEmitS (f : UInt64) (xs : List UInt8) (p : UInt64) (o : List UInt8) : List UInt8 :=
  if h : f = 0 then o
  else
    if stepKS (f - 1) xs p == 0 then o
    else if stepKS (f - 1) xs p == 1 then o
    else if stepKS (f - 1) xs p == 2 then lexEmitS (f - 1) xs (stepNS (f - 1) xs p) o
    else lexEmitS (f - 1) xs (stepNS (f - 1) xs p) (emitTokS (f - 1) xs (stepKS (f - 1) xs p) p (stepNS (f - 1) xs p) o)
termination_by f.toNat
decreasing_by all_goals exact dec_lt h

def adjLS (f : UInt64) (xs : List UInt8) (i : UInt64) : UInt64 :=
  if h : f = 0 then 1
  else if i + 1 < lenS xs then
    if adjBad (rdS xs i) (rdS xs (i + 1)) == 1 then 0 else adjLS (f - 1) xs (i + 1)
  else 1
termination_by f.toNat
decreasing_by exact dec_lt h

def lexVS (xs : List UInt8) : List UInt8 :=
  if adjLS (lenS xs) xs 0 == 1 then
    let t := lexChkS (lenS xs) xs 0 0
    if t == 1 || t == 2 then (lexEmitS (lenS xs) xs 0 (putR [] t)).reverse else []
  else []

/-! ## bridge -/

section
variable (xs : List UInt8)

theorem wordEndS_eq : ∀ (n : Nat) (p : UInt64), n < 2 ^ 64 → wordEndS n.toUInt64 xs p = wordEnd n xs p
  | 0, _, _ => by rw [wordEndS, dif_pos fuel_zero, wordEnd]
  | n + 1, p, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := fun p => wordEndS_eq n p (by omega)
    rw [wordEndS, dif_neg h1, wordEnd]; simp only [rdS_eq, lenS_eq, h2, ih]
    by_cases ha : p < len xs <;> simp [ha]

theorem allDigRS_eq : ∀ (n : Nat) (i e : UInt64), n < 2 ^ 64 → allDigRS n.toUInt64 xs i e = allDigR n xs i e
  | 0, _, _, _ => by rw [allDigRS, dif_pos fuel_zero, allDigR]
  | n + 1, i, e, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := fun i => allDigRS_eq n i e (by omega)
    rw [allDigRS, dif_neg h1, allDigR]; simp only [rdS_eq, h2, ih, digW]
    split <;> simp

theorem allDURS_eq : ∀ (n : Nat) (i e : UInt64), n < 2 ^ 64 → allDURS n.toUInt64 xs i e = allDUR n xs i e
  | 0, _, _, _ => by rw [allDURS, dif_pos fuel_zero, allDUR]
  | n + 1, i, e, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := fun i => allDURS_eq n i e (by omega)
    rw [allDURS, dif_neg h1, allDUR]; simp only [rdS_eq, h2, ih, digUW]
    split
    · by_cases hd : (48 ≤ rd xs i && rd xs i ≤ 57) || rd xs i == 95 <;> simp only [hd, if_true, if_false] <;> rfl
    · rfl

theorem numRS_eq : ∀ (n : Nat) (i e a : UInt64), n < 2 ^ 64 → numRS n.toUInt64 xs i e a = numR n xs i e a
  | 0, _, _, _, _ => by rw [numRS, dif_pos fuel_zero, numR]
  | n + 1, i, e, a, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := fun i a => numRS_eq n i e a (by omega)
    rw [numRS, dif_neg h1, numR]; simp only [rdS_eq, h2, ih]

theorem wordKS_eq (n : Nat) (p e : UInt64) (h : n < 2 ^ 64) : wordKS n.toUInt64 xs p e = wordK n xs p e := by
  simp only [wordKS, wordK, rdS_eq, allDigRS_eq xs n _ _ h, allDURS_eq xs n _ _ h]

theorem stepKS_eq (n : Nat) (p : UInt64) (h : n < 2 ^ 64) : stepKS n.toUInt64 xs p = stepK n xs p := by
  simp only [stepKS, stepK, rdS_eq, lenS_eq, wordKS_eq xs n _ _ h, wordEndS_eq xs n _ h]

theorem stepNS_eq (n : Nat) (p : UInt64) (h : n < 2 ^ 64) : stepNS n.toUInt64 xs p = stepN n xs p := by
  simp only [stepNS, stepN, rdS_eq, lenS_eq, wordEndS_eq xs n _ h]

theorem lexChkS_eq : ∀ (n : Nat) (p t : UInt64), n < 2 ^ 64 → lexChkS n.toUInt64 xs p t = lexChk n xs p t
  | 0, _, _, _ => by rw [lexChkS, dif_pos fuel_zero, lexChk, lenS_eq]
  | n + 1, p, t, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := fun p t => lexChkS_eq n p t (by omega)
    rw [lexChkS, dif_neg h1, lexChk]
    simp only [h2, stepKS_eq xs n _ (by omega), stepNS_eq xs n _ (by omega), ih]

theorem emitIdS_eq : ∀ (n : Nat) (i e : UInt64) (o : List UInt8), n < 2 ^ 64 →
    emitIdS n.toUInt64 xs i e o.reverse = (emitId n xs i e o).reverse
  | 0, _, _, _, _ => by rw [emitIdS, dif_pos fuel_zero, emitId, putR_rev]
  | n + 1, i, e, o, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := fun i o => emitIdS_eq n i e o (by omega)
    rw [emitIdS, dif_neg h1, emitId]
    simp only [h2, rdS_eq, putR_rev, ih, apply_ite List.reverse]

theorem emitWR_rev (o : List UInt8) (v : UInt64) : emitWR o.reverse v = (emitW o v).reverse := by
  simp only [emitWR, emitW, putR_rev]

theorem emitTokS_eq (n : Nat) (k p e : UInt64) (o : List UInt8) (h : n < 2 ^ 64) :
    emitTokS n.toUInt64 xs k p e o.reverse = (emitTok n xs k p e o).reverse := by
  simp only [emitTokS, emitTok, putR_rev, emitWR_rev, numRS_eq xs n _ _ _ h, emitIdS_eq xs n _ _ _ h,
    apply_ite List.reverse]

theorem lexEmitS_eq : ∀ (n : Nat) (p : UInt64) (o : List UInt8), n < 2 ^ 64 →
    lexEmitS n.toUInt64 xs p o.reverse = (lexEmit n xs p o).reverse
  | 0, _, _, _ => by rw [lexEmitS, dif_pos fuel_zero, lexEmit]
  | n + 1, p, o, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := fun p o => lexEmitS_eq n p o (by omega)
    rw [lexEmitS, dif_neg h1, lexEmit]
    simp only [h2, stepKS_eq xs n _ (by omega), stepNS_eq xs n _ (by omega), emitTokS_eq xs n _ _ _ _ (by omega),
      ih, apply_ite List.reverse, Bool.or_eq_true]
    by_cases h0 : (stepK n xs p == 0) = true <;> simp [h0]

theorem adjLS_eq : ∀ (n : Nat) (i : UInt64), n < 2 ^ 64 → adjLS n.toUInt64 xs i = adjL n xs i
  | 0, _, _ => by rw [adjLS, dif_pos fuel_zero, adjL]
  | n + 1, i, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := fun i => adjLS_eq n i (by omega)
    rw [adjLS, dif_neg h1, adjL]; simp only [rdS_eq, lenS_eq, h2, ih, adjBad]
    split <;> (repeat' split) <;> simp_all

end

/-- **the bridge**: the S3 form is the v2 lexer on every input of length < 2^64 -/
theorem lexVS_eq (xs : List UInt8) (h : xs.length < 2 ^ 64) : lexVS xs = lexV xs := by
  have e0 : putR [] = fun t => (put [] t).reverse := funext fun t => putR_rev [] t
  simp only [lexVS, lexV, lenS_eq, show len xs = xs.length.toUInt64 from rfl, adjLS_eq xs _ _ h,
    lexChkS_eq xs _ _ _ h, e0, lexEmitS_eq xs _ _ _ h, List.reverse_reverse]

end Nano.V2B
