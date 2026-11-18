import Nano.V2Self.C.Lex2
import Nano.V2Self.C.Lex2Spec
namespace LexSpec
open C


theorem drop_cons {x : List UInt8} {n : Nat} (h : n < x.length) : x.drop n = x.getD n 0 :: x.drop (n + 1) := by
  rw [List.drop_eq_getElem_cons h]; simp [List.getD_eq_getElem?_getD, h]

theorem s0_eq (b : UInt8) : s0 b.toUInt64 = if isW b then 1 else 0 := by
  have : ∀ v : BitVec 8, s0 (UInt8.ofBitVec v).toUInt64 = if isW (UInt8.ofBitVec v) then 1 else 0 := by decide
  exact this b.toBitVec

theorem len_toNat {x : List UInt8} (h : x.length < 2 ^ 32) : (len x).toNat = x.length := by
  simp [len]; omega

theorem lt_len {x : List UInt8} {p : UInt64} (h : x.length < 2 ^ 32) :
    (p < len x) ↔ p.toNat < x.length := by
  rw [UInt64.lt_iff_toNat_lt, len_toNat h]

theorem rd_eq (x : List UInt8) (p : UInt64) : rd x p = (x.getD p.toNat 0).toUInt64 := rfl

/-- s1 consumes the maximal word -/
theorem s1_eq : ∀ (n : Nat) (x : List UInt8) (p : UInt64), x.length < 2 ^ 32 → p.toNat ≤ x.length →
    x.length - p.toNat ≤ n →
    (s1 n x p).toNat = p.toNat + ((x.drop p.toNat).takeWhile isW).length
  | 0, x, p, hx, hp, hn => by
      have : p.toNat = x.length := by omega
      simp [s1, this]
  | n + 1, x, p, hx, hp, hn => by
      simp only [s1]
      by_cases hl : p.toNat < x.length
      · have hlt : p < len x := (lt_len hx).2 hl
        rw [drop_cons hl]
        have h0 : s0 (rd x p) = if isW (x.getD p.toNat 0) then 1 else 0 := by rw [rd_eq]; exact s0_eq _
        generalize x.getD p.toNat 0 = b at h0 ⊢
        by_cases hw : isW b
        · have key : (decide (p < len x) && s0 (rd x p) == 1) = true := by simp [h0, hw, hlt]
          have hp1 : (p + 1).toNat = p.toNat + 1 := by
            rw [UInt64.toNat_add]; simp; omega
          have := s1_eq n x (p + 1) hx (by omega) (by omega)
          rw [hp1] at this
          simp only [key, if_true, this, hp1, List.takeWhile_cons, hw]
          simp; omega
        · have key : ¬ (decide (p < len x) && s0 (rd x p) == 1) = true := by simp [h0, hw, hlt]
          simp only [key, if_false, List.takeWhile_cons, hw]
          simp
      · have : p.toNat = x.length := by omega
        have : ¬ p < len x := by rw [lt_len hx]; omega
        simp [*]

theorem isD_eq (b : UInt8) : (48 ≤ b.toUInt64 && b.toUInt64 ≤ 57) = isD b := by
  have : ∀ v : BitVec 8, (48 ≤ (UInt8.ofBitVec v).toUInt64 && (UInt8.ofBitVec v).toUInt64 ≤ 57) = isD (UInt8.ofBitVec v) := by decide
  exact this b.toBitVec

theorem isD_nat (b : UInt8) (h : isD b = true) : 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
  have : ∀ v : BitVec 8, isD (UInt8.ofBitVec v) = true → 48 ≤ v.toNat ∧ v.toNat ≤ 57 := by decide
  exact this b.toBitVec h

theorem sub48 (b : UInt8) (h : 48 ≤ b.toNat) : (b.toUInt64 - 48).toNat = b.toNat - 48 := by
  have : ∀ v : BitVec 8, 48 ≤ v.toNat → ((UInt8.ofBitVec v).toUInt64 - 48).toNat = v.toNat - 48 := by decide
  exact this b.toBitVec h

theorem and255 (b : UInt8) : b.toUInt64 &&& 255 = b.toUInt64 := by
  have : ∀ v : BitVec 8, (UInt8.ofBitVec v).toUInt64 &&& 255 = (UInt8.ofBitVec v).toUInt64 := by decide
  exact this b.toBitVec

theorem inc_toNat {p : UInt64} {n : Nat} (h : p.toNat < n) (hn : n < 2 ^ 32) : (p + 1).toNat = p.toNat + 1 := by
  rw [UInt64.toNat_add]; simp; omega

theorem take_step {x : List UInt8} {i : Nat} {m : Nat} (hi : i < x.length) :
    (x.drop i).take (m + 1) = x.getD i 0 :: (x.drop (i + 1)).take m := by
  rw [drop_cons hi]; rfl

theorem s2_eq : ∀ (n : Nat) (x : List UInt8) (i e : UInt64), x.length < 2 ^ 32 → e.toNat ≤ x.length → i.toNat ≤ e.toNat →
    e.toNat - i.toNat ≤ n →
    s2 n x i e = if ((x.drop i.toNat).take (e.toNat - i.toNat)).all isD then 1 else 0
  | 0, x, i, e, hx, he, hi, hn => by
      have : e.toNat - i.toNat = 0 := by omega
      simp [s2, this]
  | n + 1, x, i, e, hx, he, hi, hn => by
      simp only [s2]
      by_cases hlt : i < e
      · have hlt' : i.toNat < e.toNat := UInt64.lt_iff_toNat_lt.1 hlt
        have hl : i.toNat < x.length := by omega
        have e1 : e.toNat - i.toNat = (e.toNat - (i.toNat + 1)) + 1 := by omega
        have hd : (48 ≤ rd x i && rd x i ≤ 57) = isD (x.getD i.toNat 0) := by rw [rd_eq]; exact isD_eq _
        have hr : rd x i = (x.getD i.toNat 0).toUInt64 := rd_eq x i
        have ih := s2_eq n x (i + 1) e hx he (by rw [inc_toNat (by omega) hx]; omega)
          (by rw [inc_toNat (by omega) hx]; omega)
        rw [inc_toNat (by omega) hx] at ih
        rw [e1, take_step hl]
        simp only [hlt, if_true, hd]
        generalize x.getD i.toNat 0 = b at hd ⊢
        by_cases hb : isD b
        · simp [hb, ih]
        · simp [hb]
      · have : e.toNat - i.toNat = 0 := by
          have := UInt64.le_iff_toNat_le.1 (UInt64.not_lt.1 hlt); omega
        simp [hlt, this]

/-- the value accumulated by s6 -/
theorem s6_eq : ∀ (n : Nat) (x : List UInt8) (i e a : UInt64), x.length < 2 ^ 32 → e.toNat ≤ x.length → i.toNat ≤ e.toNat →
    e.toNat - i.toNat ≤ n → ((x.drop i.toNat).take (e.toNat - i.toNat)).all isD = true →
    (s6 n x i e a).toNat = ((x.drop i.toNat).take (e.toNat - i.toNat)).foldl
      (fun a b => (a * 10 + (b.toNat - 48)) % 2 ^ 64) a.toNat
  | 0, x, i, e, a, hx, he, hi, hn, hd => by
      have : e.toNat - i.toNat = 0 := by omega
      simp [s6, this]
  | n + 1, x, i, e, a, hx, he, hi, hn, hd => by
      simp only [s6]
      by_cases hlt : i < e
      · have hlt' : i.toNat < e.toNat := UInt64.lt_iff_toNat_lt.1 hlt
        have hl : i.toNat < x.length := by omega
        have e1 : e.toNat - i.toNat = (e.toNat - (i.toNat + 1)) + 1 := by omega
        rw [e1, take_step hl] at hd ⊢
        simp only [List.all_cons, Bool.and_eq_true] at hd
        have hge : 48 ≤ (x.getD i.toNat 0).toNat := by
          exact (isD_nat _ hd.1).1
        have hi1 := inc_toNat (p := i) (n := x.length) hl hx
        have hr : rd x i = (x.getD i.toNat 0).toUInt64 := rd_eq x i
        have ih := s6_eq n x (i + 1) e (a * 10 + (rd x i - 48)) hx he (by omega) (by omega)
          (by rw [hi1]; simpa using hd.2)
        rw [hi1] at ih
        simp only [hlt, if_true, ih, List.foldl_cons]
        congr 1
        rw [hr]
        generalize x.getD i.toNat 0 = b at hge ⊢
        simp [UInt64.toNat_add, UInt64.toNat_mul, sub48 b hge]
      · have : e.toNat - i.toNat = 0 := by
          have := UInt64.le_iff_toNat_le.1 (UInt64.not_lt.1 hlt); omega
        simp [hlt, this]

theorem andm (n : Nat) : n &&& 255 = n % 256 := by
  have : (255:Nat) = 2^8-1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
theorem sh (v : UInt64) (k : Nat) (m : UInt64) (hm : m.toNat = 8 * k) (hk : k < 8) : ((v >>> m) &&& 255) = ((v.toNat / 256 ^ k) % 256).toUInt64 := by
  apply UInt64.toNat.inj
  have h1 : 256 ^ k = 2 ^ (8 * k) := by rw [Nat.pow_mul]
  have h8 : 8 * k % 64 = 8 * k := Nat.mod_eq_of_lt (by omega)
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hm, h8, Nat.toUInt64_eq]
  simp only [UInt64.toNat_ofNat, UInt64.toNat_ofNat']
  have h255 : (255 : Nat) % 2 ^ 64 = 255 := by decide
  rw [h255, andm, Nat.shiftRight_eq_div_pow, ← h1]
  omega

theorem q0_eq (o : Buf) (v : UInt64) : q0 o v = o ++ [v &&& 255] := by simp [q0, bpush, k255]

theorem s8_eq (v : UInt64) (o : Buf) : s8 v o = o ++ le8 v.toNat := by
  have h0 : v &&& 255 = ((v.toNat / 256 ^ 0) % 256).toUInt64 := by
    have := sh v 0 0 rfl (by omega); simpa using this
  simp only [s8, q0_eq, le8, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.append_assoc, List.cons_append]
  rw [h0, sh v 1 8 rfl (by omega), sh v 2 16 rfl (by omega), sh v 3 24 rfl (by omega), sh v 4 32 rfl (by omega),
    sh v 5 40 rfl (by omega), sh v 6 48 rfl (by omega), sh v 7 56 rfl (by omega)]

theorem s7_eq : ∀ (n : Nat) (x : List UInt8) (i e : UInt64) (o : Buf), x.length < 2 ^ 32 → e.toNat ≤ x.length →
    i.toNat ≤ e.toNat → e.toNat - i.toNat ≤ n →
    s7 n x i e o = o ++ (((x.drop i.toNat).take (e.toNat - i.toNat)).flatMap fun b => [1, b.toUInt64]) ++ [0]
  | 0, x, i, e, o, hx, he, hi, hn => by
      have : e.toNat - i.toNat = 0 := by omega
      simp [s7, this, q0_eq]
  | n + 1, x, i, e, o, hx, he, hi, hn => by
      simp only [s7]
      by_cases hlt : i < e
      · have hlt' : i.toNat < e.toNat := UInt64.lt_iff_toNat_lt.1 hlt
        have hl : i.toNat < x.length := by omega
        have e1 : e.toNat - i.toNat = (e.toNat - (i.toNat + 1)) + 1 := by omega
        have hi1 := inc_toNat (p := i) (n := x.length) hl hx
        have ih := s7_eq n x (i + 1) e (q0 (q0 o 1) (rd x i)) hx he (by omega) (by omega)
        rw [hi1] at ih
        have hr : rd x i = (x.getD i.toNat 0).toUInt64 := rd_eq x i
        simp only [hr, q0_eq] at ih
        simp only [hlt, if_true, hr, q0_eq]
        rw [ih, e1, take_step hl]
        generalize x.getD i.toNat 0 = b
        have : (1 : UInt64) &&& 255 = 1 := by decide
        simp [this, and255]
      · have : e.toNat - i.toNat = 0 := by
          have := UInt64.le_iff_toNat_le.1 (UInt64.not_lt.1 hlt); omega
        simp [hlt, this, q0_eq]
