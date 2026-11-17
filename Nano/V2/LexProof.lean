/- Bridge of the nano v2 lexer (Nano/V2/Lex.lean): `lexV_eq : lexV xs = lexA xs` for every input of length
< 2^32. -/
import Nano.V2.Lex
import Nano.V2.InlProof

namespace Nano.V2.LexP
open Nano Nano.B Nano.PS Nano.LS Nano.V2 Nano.V2.InlP

/-! ## bytes as words -/

theorem beqL (a : UInt8) (n : Nat) (h : n < 256) :
    (a.toUInt64 == (OfNat.ofNat n : UInt64)) = (a == (OfNat.ofNat n : UInt8)) := Nano.V2.beq8 a n h
theorem leL (a : UInt8) (n : Nat) (h : n < 256) :
    ((OfNat.ofNat n : UInt64) ≤ a.toUInt64) = ((OfNat.ofNat n : UInt8) ≤ a) := by
  apply propext; rw [UInt64.le_iff_toNat_le, UInt8.le_iff_toNat_le]
  show (UInt64.ofNat n).toNat ≤ _ ↔ (UInt8.ofNat n).toNat ≤ _
  simp; omega
theorem leR (a : UInt8) (n : Nat) (h : n < 256) :
    (a.toUInt64 ≤ (OfNat.ofNat n : UInt64)) = (a ≤ (OfNat.ofNat n : UInt8)) := by
  apply propext; rw [UInt64.le_iff_toNat_le, UInt8.le_iff_toNat_le]
  show _ ≤ (UInt64.ofNat n).toNat ↔ _ ≤ (UInt8.ofNat n).toNat
  simp; omega

theorem isWC_eq (c : UInt8) : (isWC c.toUInt64 == 1) = isWordC c := by
  unfold isWC isWordC isLetter isDigit
  simp only [beqL c (nat_lit 95) (by decide), leL c (nat_lit 65) (by decide), leR c (nat_lit 90) (by decide),
    leL c (nat_lit 97) (by decide), leR c (nat_lit 122) (by decide), leL c (nat_lit 48) (by decide),
    leR c (nat_lit 57) (by decide)]
  split <;> simp_all

theorem ltL (xs : List UInt8) (p : Nat) (hx : xs.length < 2 ^ 32) (hp : p ≤ xs.length) :
    (p.toUInt64 < len xs) ↔ p < xs.length := by
  unfold len; rw [UInt64.lt_iff_toNat_lt]; simp; omega

theorem addN (p k : Nat) : p.toUInt64 + (OfNat.ofNat k : UInt64) = (p + k).toUInt64 := by
  show p.toUInt64 + UInt64.ofNat k = _; simp

/-! ## the word span -/

theorem wordEnd_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n p : Nat), p ≤ xs.length →
    ∃ e, wordEnd n xs p.toUInt64 = e.toUInt64 ∧ p ≤ e ∧ e ≤ xs.length ∧ e - p ≤ n ∧
      spanS n (xs.drop p) = ((xs.drop p).take (e - p), xs.drop e)
  | 0, p, hp => ⟨p, rfl, Nat.le_refl _, hp, by omega, by simp [spanS]⟩
  | n + 1, p, hp => by
    rw [wordEnd]
    by_cases hl : p < xs.length
    · rw [rdN xs p hl hx, isWC_eq, List.drop_eq_getElem_cons hl, spanS]
      by_cases hw : isWordC xs[p] = true
      · obtain ⟨e, h1, h2, h3, h4, h5⟩ := wordEnd_eq xs hx n (p + 1) (by omega)
        refine ⟨e, ?_, by omega, h3, by omega, ?_⟩
        · rw [if_pos (by simp [hw, (ltL xs p hx hp).mpr hl]), show p.toUInt64 + 1 = (p + 1).toUInt64 by simp, h1]
        · rw [if_pos hw, h5, show e - p = (e - (p + 1)) + 1 by omega]; simp [consP]; rw [List.drop_eq_getElem_cons hl, List.take_succ_cons]
      · refine ⟨p, ?_, Nat.le_refl _, hp, by omega, ?_⟩
        · rw [if_neg (by simp [hw])]
        · rw [if_neg hw, List.drop_eq_getElem_cons hl]; simp
    · have hd : xs.drop p = [] := by simp; omega
      refine ⟨p, ?_, Nat.le_refl _, hp, by omega, ?_⟩
      · rw [if_neg (by simp [(ltL xs p hx hp)]; omega)]
      · rw [hd]; simp [spanS]

/-! ## loops over a range `[i, e)` -/

/-- the bytes `[i, e)` -/
def seg (xs : List UInt8) (i e : Nat) : List UInt8 := (xs.drop i).take (e - i)

theorem seg_cons (xs : List UInt8) (i e : Nat) (h1 : i < e) (h2 : e ≤ xs.length) :
    seg xs i e = xs[i] :: seg xs (i + 1) e := by
  unfold seg; rw [List.drop_eq_getElem_cons (by omega), show e - i = (e - (i + 1)) + 1 by omega, List.take_succ_cons]

theorem seg_nil (xs : List UInt8) (i e : Nat) (h : e ≤ i) : seg xs i e = [] := by
  unfold seg; simp; omega

theorem ltR (i e : Nat) (he : e < 2 ^ 32) (hi : i ≤ e) : (i.toUInt64 < e.toUInt64) ↔ i < e := by
  rw [UInt64.lt_iff_toNat_lt]; simp; omega

theorem isDigit_eq (c : UInt8) : (48 ≤ c.toUInt64 && c.toUInt64 ≤ 57) = isDigit c := by
  unfold isDigit; simp only [leL c (nat_lit 48) (by decide), leR c (nat_lit 57) (by decide)]

theorem allDigR_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n i e : Nat), i ≤ e → e ≤ xs.length →
    e - i ≤ n → allDigR n xs i.toUInt64 e.toUInt64 = if allDig (seg xs i e) then 1 else 0
  | 0, i, e, h1, h2, h3 => by rw [seg_nil xs i e (by omega)]; rfl
  | n + 1, i, e, h1, h2, h3 => by
    rw [allDigR]
    by_cases hc : i < e
    · rw [if_pos ((ltR i e (by omega) h1).mpr hc), rdN xs i (by omega) hx, seg_cons xs i e hc h2, allDig,
        isDigit_eq, show i.toUInt64 + 1 = (i + 1).toUInt64 by simp,
        allDigR_eq xs hx n (i + 1) e (by omega) h2 (by omega)]
      cases isDigit xs[i] <;> simp
    · rw [if_neg (fun q => hc ((ltR i e (by omega) h1).mp q)), seg_nil xs i e (by omega)]; rfl

theorem allDUR_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n i e : Nat), i ≤ e → e ≤ xs.length →
    e - i ≤ n → allDUR n xs i.toUInt64 e.toUInt64 = if allDU (seg xs i e) then 1 else 0
  | 0, i, e, h1, h2, h3 => by rw [seg_nil xs i e (by omega)]; rfl
  | n + 1, i, e, h1, h2, h3 => by
    rw [allDUR]
    by_cases hc : i < e
    · rw [if_pos ((ltR i e (by omega) h1).mpr hc), rdN xs i (by omega) hx, seg_cons xs i e hc h2, allDU,
        isDigit_eq, beqL _ (nat_lit 95) (by decide), show i.toUInt64 + 1 = (i + 1).toUInt64 by simp,
        allDUR_eq xs hx n (i + 1) e (by omega) h2 (by omega)]
      cases (isDigit xs[i] || xs[i] == 95) <;> simp
    · rw [if_neg (fun q => hc ((ltR i e (by omega) h1).mp q)), seg_nil xs i e (by omega)]; rfl

theorem numR_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n i e : Nat) (a : UInt64), i ≤ e → e ≤ xs.length →
    e - i ≤ n → numR n xs i.toUInt64 e.toUInt64 a = numW a (seg xs i e)
  | 0, i, e, a, h1, h2, h3 => by rw [seg_nil xs i e (by omega)]; rfl
  | n + 1, i, e, a, h1, h2, h3 => by
    rw [numR]
    by_cases hc : i < e
    · rw [if_pos ((ltR i e (by omega) h1).mpr hc), rdN xs i (by omega) hx, seg_cons xs i e hc h2, numW,
        show i.toUInt64 + 1 = (i + 1).toUInt64 by simp, numR_eq xs hx n (i + 1) e _ (by omega) h2 (by omega)]
    · rw [if_neg (fun q => hc ((ltR i e (by omega) h1).mp q)), seg_nil xs i e (by omega)]; rfl

theorem emitId_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n i e : Nat) (o : List UInt8), i ≤ e →
    e ≤ xs.length → e - i ≤ n → emitId n xs i.toUInt64 e.toUInt64 o = o ++ encId (seg xs i e)
  | 0, i, e, o, h1, h2, h3 => by rw [seg_nil xs i e (by omega)]; simp [emitId, encId, put]
  | n + 1, i, e, o, h1, h2, h3 => by
    rw [emitId]
    by_cases hc : i < e
    · rw [if_pos ((ltR i e (by omega) h1).mpr hc), rdN xs i (by omega) hx, seg_cons xs i e hc h2, encId,
        show i.toUInt64 + 1 = (i + 1).toUInt64 by simp, emitId_eq xs hx n (i + 1) e _ (by omega) h2 (by omega)]
      simp [put]
    · rw [if_neg (fun q => hc ((ltR i e (by omega) h1).mp q)), seg_nil xs i e (by omega)]; simp [encId, put]

/-! ## the word classifier -/

/-- the token of kind `k` (word `w` for numerals and identifiers) -/
def tokK (k : Nat) (w : List UInt8) : Option Tok :=
  if k = 3 then some .kdef else if k = 4 then some .klet else if k = 5 then some (.kty false)
  else if k = 6 then some (.kty true) else if k = 7 then some (.num (numW 0 w)) else if k = 8 then some .lp
  else if k = 9 then some .rp else if k = 10 then some .colon else if k = 11 then some .assign
  else if k = 12 then some .plus else if k = 13 then some .minus else if k = 14 then some .star
  else if k = 15 then some .semi else if k = 16 then some (.id w) else none

theorem subW (e p : Nat) (h : p ≤ e) (he : e < 2 ^ 32) (m : Nat) (hm : m < 2 ^ 32) :
    (e.toUInt64 - p.toUInt64 == (OfNat.ofNat m : UInt64)) = decide (e - p = m) := by
  have : e.toUInt64 - p.toUInt64 = (e - p).toUInt64 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
    simp; omega
  rw [this]
  by_cases h' : e - p = m
  · rw [h']; simp; show (UInt64.ofNat m) = (UInt64.ofNat m); rfl
  · have : (e - p).toUInt64 ≠ (OfNat.ofNat m : UInt64) := by
      intro q; have := congrArg UInt64.toNat q
      simp at this; rw [show (OfNat.ofNat m : UInt64).toNat = m by show (UInt64.ofNat m).toNat = m; simp; omega] at this
      omega
    simp [h', this]

theorem isDef_len (w : List UInt8) (h : isDef w = true) : w.length = 3 := by
  match w, h with
  | [_, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _, h => simp [isDef] at h
theorem isLet_len (w : List UInt8) (h : isLet w = true) : w.length = 3 := by
  match w, h with
  | [_, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _, h => simp [isLet] at h
theorem isU64_len (w : List UInt8) (h : isU64 w = true) : w.length = 6 := by
  match w, h with
  | [_, _, _, _, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => simp [isU64] at h
theorem isI64_len (w : List UInt8) (h : isI64 w = true) : w.length = 5 := by
  match w, h with
  | [_, _, _, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h => simp [isI64] at h

theorem seg_len (xs : List UInt8) (p e : Nat) (h : e ≤ xs.length) : (seg xs p e).length = e - p := by
  unfold seg; simp; omega

theorem seg_get (xs : List UInt8) (hx : xs.length < 2 ^ 32) (p e i : Nat) (h : p + i < e) (he : e ≤ xs.length) :
    rd xs (p.toUInt64 + (OfNat.ofNat i : UInt64)) = ((seg xs p e).getD i 0).toUInt64 := by
  rw [addN, rdN xs _ (by omega) hx]; unfold seg
  simp [List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_getElem (by simp; omega)]; simp

theorem len3 : ∀ w : List UInt8, w.length = 3 → ∃ a b c, w = [a, b, c]
  | [a, b, c], _ => ⟨a, b, c, rfl⟩
  | [], h | [_], h | [_, _], h | _ :: _ :: _ :: _ :: _, h => by simp at h <;> omega

theorem len5 : ∀ w : List UInt8, w.length = 5 → ∃ a b c d f, w = [a, b, c, d, f]
  | [a, b, c, d, f], _ => ⟨a, b, c, d, f, rfl⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h | _ :: _ :: _ :: _ :: _ :: _ :: _, h => by
    simp at h <;> omega
theorem len6 : ∀ w : List UInt8, w.length = 6 → ∃ a b c d f g, w = [a, b, c, d, f, g]
  | [a, b, c, d, f, g], _ => ⟨a, b, c, d, f, g, rfl⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h | [_, _, _, _, _], h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => by simp at h <;> omega

theorem wordK_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) (n p e : Nat) (hpe : p < e) (he : e ≤ xs.length)
    (hn : e - p ≤ n) : wordTokS (seg xs p e) = tokK (wordK n xs p.toUInt64 e.toUInt64).toNat (seg xs p e) := by
  have hlen := seg_len xs p e he
  have g := fun i (h : p + i < e) => seg_get xs hx p e i h he
  have g0 : rd xs p.toUInt64 = ((seg xs p e).getD 0 0).toUInt64 := by
    have := g 0 (by omega); simpa using this
  have hd := allDigR_eq xs hx n p e (by omega) he hn
  have hu := allDUR_eq xs hx n (p + 1) e (by omega) he (by omega)
  have hr : seg xs (p + 1) e = (seg xs p e).tail := by rw [seg_cons xs p e hpe he]; rfl
  unfold wordK
  rw [if_neg (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
  simp only []
  rw [g0, hd, show p.toUInt64 + 1 = (p + 1).toUInt64 by simp, hu, hr, subW e p (by omega) (by omega) 3 (by decide),
    subW e p (by omega) (by omega) 5 (by decide), subW e p (by omega) (by omega) 6 (by decide)]
  rw [show (p + 1).toUInt64 = p.toUInt64 + 1 by simp]
  by_cases h3 : e - p = 3
  · rw [g 1 (by omega), g 2 (by omega)]
    generalize seg xs p e = w at *
    obtain ⟨a, b, c, rfl⟩ := len3 w (by omega)
    · simp only [h3, decide_true, decide_false, List.getD_cons_zero, List.getD_cons_succ, isDigit_eq,
        beqL a (nat_lit 100) (by decide), beqL b (nat_lit 101) (by decide), beqL c (nat_lit 102) (by decide),
        beqL a (nat_lit 108) (by decide), beqL c (nat_lit 116) (by decide), leL a (nat_lit 97) (by decide),
        leR a (nat_lit 122) (by decide), show decide (3 = 6) = false from rfl, show decide (3 = 5) = false from rfl,
        Bool.false_and, Bool.true_and]
      unfold wordTokS isDef isLet isU64 isI64 identOkS
      by_cases hd : isDigit a = true
      · simp only [hd, if_true]; split <;> simp_all [tokK]
      · simp only [hd, if_false, Bool.false_eq_true]
        repeat' split
        all_goals simp_all [tokK]
  by_cases h5 : e - p = 5
  · rw [g 1 (by omega), g 2 (by omega), g 3 (by omega), g 4 (by omega)]
    generalize seg xs p e = w at *
    obtain ⟨a, b, c, d, f, rfl⟩ := len5 w (by omega)
    simp only [h5, decide_true, List.getD_cons_zero, List.getD_cons_succ, isDigit_eq,
      beqL a (nat_lit 73) (by decide), beqL b (nat_lit 110) (by decide), beqL c (nat_lit 116) (by decide),
      beqL d (nat_lit 54) (by decide), beqL f (nat_lit 52) (by decide), leL a (nat_lit 97) (by decide),
      leR a (nat_lit 122) (by decide), show decide (5 = 6) = false from rfl, show decide (5 = 3) = false from rfl,
      Bool.false_and, Bool.true_and]
    unfold wordTokS isDef isLet isU64 isI64 identOkS
    by_cases hd : isDigit a = true
    · simp only [hd, if_true]; split <;> simp_all [tokK]
    · simp only [hd, if_false, Bool.false_eq_true]
      repeat' split
      all_goals simp_all [tokK]
  by_cases h6 : e - p = 6
  · rw [g 1 (by omega), g 2 (by omega), g 3 (by omega), g 4 (by omega), g 5 (by omega)]
    generalize seg xs p e = w at *
    obtain ⟨a, b, c, d, f, k, rfl⟩ := len6 w (by omega)
    simp only [h6, decide_true, List.getD_cons_zero, List.getD_cons_succ, isDigit_eq,
      beqL a (nat_lit 85) (by decide), beqL b (nat_lit 73) (by decide), beqL c (nat_lit 110) (by decide),
      beqL d (nat_lit 116) (by decide), beqL f (nat_lit 54) (by decide), beqL k (nat_lit 52) (by decide),
      leL a (nat_lit 97) (by decide),
      leR a (nat_lit 122) (by decide), show decide (6 = 5) = false from rfl, show decide (6 = 3) = false from rfl,
      Bool.false_and, Bool.true_and]
    unfold wordTokS isDef isLet isU64 isI64 identOkS
    by_cases hd : isDigit a = true
    · simp only [hd, if_true]; split <;> simp_all [tokK]
    · simp only [hd, if_false, Bool.false_eq_true]
      repeat' split
      all_goals simp_all [tokK]
  · generalize seg xs p e = w at *
    obtain ⟨a, r, rfl⟩ : ∃ a r, w = a :: r := by
      cases w with
      | nil => simp at hlen; omega
      | cons a r => exact ⟨a, r, rfl⟩
    have nd : isDef (a :: r) = false := by
      cases q : isDef (a :: r)
      · rfl
      · have := isDef_len _ q; omega
    have nl : isLet (a :: r) = false := by
      cases q : isLet (a :: r)
      · rfl
      · have := isLet_len _ q; omega
    have nu : isU64 (a :: r) = false := by
      cases q : isU64 (a :: r)
      · rfl
      · have := isU64_len _ q; omega
    have ni : isI64 (a :: r) = false := by
      cases q : isI64 (a :: r)
      · rfl
      · have := isI64_len _ q; omega
    simp only [h3, h5, h6, decide_false, Bool.false_and, List.getD_cons_zero, isDigit_eq,
      leL a (nat_lit 97) (by decide), leR a (nat_lit 122) (by decide), List.tail_cons]
    unfold wordTokS
    simp only [nd, nl, nu, ni, Bool.false_eq_true, if_false]
    unfold identOkS
    clear g g0 hu hd hr
    by_cases hdg : isDigit a = true
    · simp only [hdg, if_true]; split <;> simp_all [tokK]
    · simp only [hdg, if_false, Bool.false_eq_true]
      by_cases h1 : 97 ≤ a <;> by_cases h2 : a ≤ 122 <;> by_cases h7 : allDU r = true <;> simp [h1, h2, h7, tokK]

end Nano.V2.LexP
