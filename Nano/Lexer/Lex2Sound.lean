import Nano.Lexer.Lex2
import Nano.Lexer.Lex2Spec
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
        · have key : (s0 (rd x p) == 1) = true := by simp [h0, hw]
          have hp1 : (p + 1).toNat = p.toNat + 1 := by
            rw [UInt64.toNat_add]; simp; omega
          have := s1_eq n x (p + 1) hx (by omega) (by omega)
          rw [hp1] at this
          rw [if_pos hlt, if_pos key]
          simp only [this, hp1, List.takeWhile_cons, hw]
          simp; omega
        · have key : ¬ (s0 (rd x p) == 1) = true := by simp [h0, hw]
          rw [if_pos hlt, if_neg key]
          simp only [List.takeWhile_cons, hw]
          simp
      · have : p.toNat = x.length := by omega
        have : ¬ p < len x := by rw [lt_len hx]; omega
        simp [*]

theorem isD_eq (b : UInt8) : (48 ≤ b.toUInt64 && b.toUInt64 ≤ 57) = isD b := by
  have : ∀ v : BitVec 8, (48 ≤ (UInt8.ofBitVec v).toUInt64 && (UInt8.ofBitVec v).toUInt64 ≤ 57) = isD (UInt8.ofBitVec v) := by decide
  exact this b.toBitVec

theorem isD_lt (b : UInt8) : isD b = true ↔ (¬ b.toUInt64 < 48 ∧ ¬ 57 < b.toUInt64) := by
  have : ∀ v : BitVec 8, isD (UInt8.ofBitVec v) = true ↔ (¬ (UInt8.ofBitVec v).toUInt64 < 48 ∧ ¬ 57 < (UInt8.ofBitVec v).toUInt64) := by decide
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
        have hr : rd x i = (x.getD i.toNat 0).toUInt64 := rd_eq x i
        have ih := s2_eq n x (i + 1) e hx he (by rw [inc_toNat (by omega) hx]; omega)
          (by rw [inc_toNat (by omega) hx]; omega)
        rw [inc_toNat (by omega) hx] at ih
        rw [e1, take_step hl]
        rw [if_pos hlt, hr]
        generalize x.getD i.toNat 0 = b
        by_cases hb : isD b
        · obtain ⟨h1, h2⟩ := (isD_lt b).1 hb
          simp [hb, ih, h1, h2]
        · have := mt (isD_lt b).2 hb
          by_cases h1 : b.toUInt64 < 48
          · simp [hb, h1]
          · have h2 : 57 < b.toUInt64 := by by_cases h2 : 57 < b.toUInt64 <;> simp_all
            simp [hb, h1, h2]
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

/-! ### keyword classification (s3) -/


theorem tu (a : UInt8) (n : Nat) (h : n < 256) : a.toUInt64 = UInt64.ofNat n ↔ a = UInt8.ofNat n := by
  constructor
  · intro e; have := congrArg UInt64.toNat e
    apply UInt8.toNat.inj; simp at this ⊢; omega
  · intro e; subst e; apply UInt64.toNat.inj; simp; omega
theorem tu2 (a : UInt8) (n : Nat) (h : n < 256) :
    a.toUInt64 = (no_index (OfNat.ofNat n : UInt64)) ↔ a = (no_index (OfNat.ofNat n : UInt8)) := tu a n h

/-- the keyword table s3 implements: `kwTable` plus the trivia words (92: skip the line, 93: drop) -/
def kwX : List (List UInt8 × UInt64) :=
  kwTable ++ [([101, 110, 100], 97), ([111, 112, 101, 110], 0), ([115, 101, 99, 116, 105, 111, 110], 98),
    ([110, 97, 109, 101, 115, 112, 97, 99, 101], 92), ([112, 114, 105, 118, 97, 116, 101], 93)]

/-- s3 with its reads made parameters (definitionally the same body) -/
def s3' (d c c1 c2 c3 c4 c5 c6 c7 c8 : UInt64) : UInt64 :=
  let r0 := 14;
  let r1 := if d == 4 then if c == 101 then if c1 == 108 then if c2 == 115 then if c3 == 101 then 34 else r0 else r0 else r0 else r0 else r0;
  let r2 := if d == 4 then if c == 116 then if c1 == 104 then if c2 == 101 then if c3 == 110 then 33 else r1 else r1 else r1 else r1 else r1;
  let r3 := if d == 2 then if c == 105 then if c1 == 102 then 32 else r2 else r2 else r2;
  let r4 := if d == 3 then if c == 108 then if c1 == 101 then if c2 == 116 then 2 else r3 else r3 else r3 else r3;
  let r5 := if d == 3 then if c == 100 then if c1 == 101 then if c2 == 102 then 1 else r4 else r4 else r4 else r4;
  let r6 := if d == 4 then if c == 76 then if c1 == 105 then if c2 == 115 then if c3 == 116 then 37 else r5 else r5 else r5 else r5 else r5;
  let r7 := if d == 3 then if c == 66 then if c1 == 117 then if c2 == 102 then 36 else r6 else r6 else r6 else r6;
  let r8 := if d == 3 then if c == 78 then if c1 == 97 then if c2 == 116 then 35 else r7 else r7 else r7 else r7;
  let r9 := if d == 5 then if c == 85 then if c1 == 73 then if c2 == 110 then if c3 == 116 then if c4 == 56 then 38 else r8 else r8 else r8 else r8 else r8 else r8;
  let r10 := if d == 6 then if c == 85 then if c1 == 73 then if c2 == 110 then if c3 == 116 then if c4 == 54 then if c5 == 52 then 3 else r9 else r9 else r9 else r9 else r9 else r9 else r9;
  let r11 := if d == 2 then if c == 114 then if c1 == 100 then 40 else r10 else r10 else r10;
  let r12 := if d == 3 then if c == 108 then if c1 == 101 then if c2 == 110 then 41 else r11 else r11 else r11 else r11;
  let r13 := if d == 4 then if c == 108 then if c1 == 101 then if c2 == 110 then if c3 == 39 then 39 else r12 else r12 else r12 else r12 else r12;
  let r14 := if d == 3 then if c == 112 then if c1 == 117 then if c2 == 116 then 42 else r13 else r13 else r13 else r13;
  let r15 := if d == 4 then if c == 98 then if c1 == 110 then if c2 == 101 then if c3 == 119 then 43 else r14 else r14 else r14 else r14 else r14;
  let r16 := if d == 5 then if c == 98 then if c1 == 115 then if c2 == 105 then if c3 == 122 then if c4 == 101 then 44 else r15 else r15 else r15 else r15 else r15 else r15;
  let r17 := if d == 4 then if c == 98 then if c1 == 103 then if c2 == 101 then if c3 == 116 then 45 else r16 else r16 else r16 else r16 else r16;
  let r18 := if d == 4 then if c == 98 then if c1 == 115 then if c2 == 101 then if c3 == 116 then 46 else r17 else r17 else r17 else r17 else r17;
  let r19 := if d == 5 then if c == 98 then if c1 == 112 then if c2 == 117 then if c3 == 115 then if c4 == 104 then 47 else r18 else r18 else r18 else r18 else r18 else r18;
  let r20 := if d == 3 then if c == 101 then if c1 == 110 then if c2 == 100 then 97 else r19 else r19 else r19 else r19;
  let r21 := if d == 4 then if c == 111 then if c1 == 112 then if c2 == 101 then if c3 == 110 then 0 else r20 else r20 else r20 else r20 else r20;
  let r22 := if d == 7 then if c == 115 then if c1 == 101 then if c2 == 99 then if c3 == 116 then if c4 == 105 then if c5 == 111 then if c6 == 110 then 98 else r21 else r21 else r21 else r21 else r21 else r21 else r21 else r21;
  let r23 := if d == 9 then if c == 110 then if c1 == 97 then if c2 == 109 then if c3 == 101 then if c4 == 115 then if c5 == 112 then if c6 == 97 then if c7 == 99 then if c8 == 101 then 92 else r22 else r22 else r22 else r22 else r22 else r22 else r22 else r22 else r22 else r22;
  let r24 := if d == 7 then if c == 112 then if c1 == 114 then if c2 == 105 then if c3 == 118 then if c4 == 97 then if c5 == 116 then if c6 == 101 then 93 else r23 else r23 else r23 else r23 else r23 else r23 else r23 else r23;
  r24

theorem s3_eq_s3' (x : List UInt8) (p e : UInt64) :
    s3 x p e = s3' (e - p) (rd x p) (rd x (p + 1)) (rd x (p + 2)) (rd x (p + 3)) (rd x (p + 4)) (rd x (p + 5))
      (rd x (p + 6)) (rd x (p + 7)) (rd x (p + 8)) := rfl

theorem nest {α : Type} (p q : Prop) [Decidable p] [Decidable q] (x y : α) :
    (if p then (if q then x else y) else y) = (if p ∧ q then x else y) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

set_option maxHeartbeats 4000000 in
theorem s3'_eq (w : List UInt8) (c0 c1 c2 c3 c4 c5 c6 c7 c8 : UInt64) (hl : w.length < 2 ^ 32)
    (h : ∀ j, j < 9 → j < w.length → [c0, c1, c2, c3, c4, c5, c6, c7, c8].getD j 0 = (w.getD j 0).toUInt64) :
    s3' w.length.toUInt64 c0 c1 c2 c3 c4 c5 c6 c7 c8 = (kwX.lookup w).getD 14 := by
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨i, _ | ⟨j, _ | ⟨k, r⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  · clear h
    simp (config := {zeta := false}) only [s3', nest]
    try simp [kwX, kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    simp at h0
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s3', nest]
    try simp [kwX, kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    simp at h0 h1
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s3', nest]
    try simp [kwX, kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    simp at h0 h1 h2
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s3', nest]
    try simp [kwX, kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    simp at h0 h1 h2 h3
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s3', nest]
    try simp [kwX, kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s3', nest]
    try simp [kwX, kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    have h5 := h 5 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4 h5
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s3', nest]
    try simp [kwX, kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    have h5 := h 5 (by decide) (by simp)
    have h6 := h 6 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4 h5 h6
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s3', nest]
    try simp [kwX, kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    have h5 := h 5 (by decide) (by simp)
    have h6 := h 6 (by decide) (by simp)
    have h7 := h 7 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4 h5 h6 h7
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s3', nest]
    try simp [kwX, kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    have h5 := h 5 (by decide) (by simp)
    have h6 := h 6 (by decide) (by simp)
    have h7 := h 7 (by decide) (by simp)
    have h8 := h 8 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4 h5 h6 h7 h8
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s3', nest]
    try simp [kwX, kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    have h5 := h 5 (by decide) (by simp)
    have h6 := h 6 (by decide) (by simp)
    have h7 := h 7 (by decide) (by simp)
    have h8 := h 8 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4 h5 h6 h7 h8
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s3', nest]
    have hd : (a :: b :: c :: d :: e :: f :: g :: i :: j :: k :: r).length = r.length + 10 := by simp
    obtain ⟨N, hN⟩ : ∃ N, N = r.length + 10 := ⟨_, rfl⟩
    rw [hd, ← hN]
    rw [hd] at hl
    have hl' : N < 2 ^ 32 := by omega
    have n2 : N.toUInt64 ≠ 2 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have n3 : N.toUInt64 ≠ 3 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have n4 : N.toUInt64 ≠ 4 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have n5 : N.toUInt64 ≠ 5 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have n6 : N.toUInt64 ≠ 6 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have n7 : N.toUInt64 ≠ 7 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have n9 : N.toUInt64 ≠ 9 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    simp [kwX, kwTable, List.lookup, n2, n3, n4, n5, n6, n7, n9]

theorem rd_seg (x : List UInt8) (p q : UInt64) (m j : Nat) (hj : j < m) (hq : q.toNat = p.toNat + j) :
    rd x q = (((x.drop p.toNat).take m).getD j 0).toUInt64 := by
  rw [rd_eq, hq]
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, hj, Nat.add_comm]

theorem s3_eq (x : List UInt8) (p e : UInt64) (hx : x.length < 2 ^ 32) (he : e.toNat ≤ x.length) (hp : p.toNat ≤ e.toNat) :
    s3 x p e = (kwX.lookup ((x.drop p.toNat).take (e.toNat - p.toNat))).getD 14 := by
  rw [s3_eq_s3']
  have hw : ((x.drop p.toNat).take (e.toNat - p.toNat)).length = e.toNat - p.toNat := by simp; omega
  have hd : e - p = ((x.drop p.toNat).take (e.toNat - p.toNat)).length.toUInt64 := by
    apply UInt64.toNat.inj; rw [hw]; simp [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 hp)]
    omega
  rw [hd]
  apply s3'_eq _ _ _ _ _ _ _ _ _ _ (by rw [hw]; omega)
  intro j hj hjw
  rw [hw] at hjw
  have hrd : ∀ q : UInt64, q.toNat = p.toNat + j → rd x q = _ := fun q hq => rd_seg x p q _ j hjw hq
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  · simp; exact hrd p (by omega)
  · simp; exact hrd (p + 1) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 2) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 3) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 4) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 5) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 6) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 7) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 8) (by simp [UInt64.toNat_add]; omega)


/-! ### attribute names (s16), the same technique as s3 -/

/-- s16 with its reads made parameters (definitionally the same body) -/
def s16' (d c c1 c2 c3 c4 c5 c6 c7 c8 : UInt64) : UInt64 :=
  if d == 6 then
    if c == 105 then if c1 == 110 then if c2 == 108 then if c3 == 105 then if c4 == 110 then if c5 == 101 then 1 else 0 else 0 else 0 else 0 else 0 else 0
  else if d == 9 then
    if c == 114 then if c1 == 101 then if c2 == 100 then if c3 == 117 then if c4 == 99 then if c5 == 105 then if c6 == 98 then if c7 == 108 then if c8 == 101 then 1 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0
  else 0

theorem s16_eq_s16' (x : List UInt8) (p e : UInt64) :
    s16 x p e = s16' (e - p) (rd x p) (rd x (p + 1)) (rd x (p + 2)) (rd x (p + 3)) (rd x (p + 4)) (rd x (p + 5))
      (rd x (p + 6)) (rd x (p + 7)) (rd x (p + 8)) := rfl

set_option maxHeartbeats 4000000 in
theorem s16'_eq (w : List UInt8) (c0 c1 c2 c3 c4 c5 c6 c7 c8 : UInt64) (hl : w.length < 2 ^ 32)
    (h : ∀ j, j < 9 → j < w.length → [c0, c1, c2, c3, c4, c5, c6, c7, c8].getD j 0 = (w.getD j 0).toUInt64) :
    s16' w.length.toUInt64 c0 c1 c2 c3 c4 c5 c6 c7 c8 = if attrNames.contains w then 1 else 0 := by
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨i, _ | ⟨j, _ | ⟨k, r⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  · clear h
    simp (config := {zeta := false}) only [s16', nest]
    try simp [attrNames, tu2]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    simp at h0
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s16', nest]
    try simp [attrNames, tu2]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    simp at h0 h1
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s16', nest]
    try simp [attrNames, tu2]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    simp at h0 h1 h2
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s16', nest]
    try simp [attrNames, tu2]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    simp at h0 h1 h2 h3
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s16', nest]
    try simp [attrNames, tu2]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s16', nest]
    try simp [attrNames, tu2]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    have h5 := h 5 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4 h5
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s16', nest]
    try simp [attrNames, tu2]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    have h5 := h 5 (by decide) (by simp)
    have h6 := h 6 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4 h5 h6
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s16', nest]
    try simp [attrNames, tu2]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    have h5 := h 5 (by decide) (by simp)
    have h6 := h 6 (by decide) (by simp)
    have h7 := h 7 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4 h5 h6 h7
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s16', nest]
    try simp [attrNames, tu2]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    have h5 := h 5 (by decide) (by simp)
    have h6 := h 6 (by decide) (by simp)
    have h7 := h 7 (by decide) (by simp)
    have h8 := h 8 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4 h5 h6 h7 h8
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s16', nest]
    try simp [attrNames, tu2]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    have h5 := h 5 (by decide) (by simp)
    have h6 := h 6 (by decide) (by simp)
    have h7 := h 7 (by decide) (by simp)
    have h8 := h 8 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4 h5 h6 h7 h8
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s16', nest]
    have hd : (a :: b :: c :: d :: e :: f :: g :: i :: j :: k :: r).length = r.length + 10 := by simp
    obtain ⟨N, hN⟩ : ∃ N, N = r.length + 10 := ⟨_, rfl⟩
    rw [hd, ← hN]
    rw [hd] at hl
    have hl' : N < 2 ^ 32 := by omega
    have n6 : N.toUInt64 ≠ 6 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have n9 : N.toUInt64 ≠ 9 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    simp [attrNames, n6, n9]

theorem s16_eq (x : List UInt8) (p e : UInt64) (hx : x.length < 2 ^ 32) (he : e.toNat ≤ x.length) (hp : p.toNat ≤ e.toNat) :
    s16 x p e = if attrNames.contains ((x.drop p.toNat).take (e.toNat - p.toNat)) then 1 else 0 := by
  rw [s16_eq_s16']
  have hw : ((x.drop p.toNat).take (e.toNat - p.toNat)).length = e.toNat - p.toNat := by simp; omega
  have hd : e - p = ((x.drop p.toNat).take (e.toNat - p.toNat)).length.toUInt64 := by
    apply UInt64.toNat.inj; rw [hw]; simp [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 hp)]
    omega
  rw [hd]
  apply s16'_eq _ _ _ _ _ _ _ _ _ _ (by rw [hw]; omega)
  intro j hj hjw
  rw [hw] at hjw
  have hrd : ∀ q : UInt64, q.toNat = p.toNat + j → rd x q = _ := fun q hq => rd_seg x p q _ j hjw hq
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  · simp; exact hrd p (by omega)
  · simp; exact hrd (p + 1) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 2) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 3) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 4) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 5) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 6) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 7) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 8) (by simp [UInt64.toNat_add]; omega)


/-! ### the token kind (s4) -/

/-- s4 with its reads/inner calls made parameters (definitionally the same body) -/
def s4' (c d f A B : UInt64) : UInt64 :=
    if c == 32 then 90
    else if c == 10 then 90
    else if c == 40 then 6
    else if c == 41 then 7
    else if c == 43 then 10
    else if c == 45 then if d == 45 then 94 else 11
    else if c == 42 then 12
    else if c == 59 then 13
    else if c == 44 then 15
    else if c == 91 then 30
    else if c == 93 then 31
    else if c == 58 then if d == 61 then 9 else 8
    else if c == 61 then if d == 61 then 23 else if d == 62 then 19 else 0
    else if c == 38 then if d == 38 then if f == 38 then 26 else 0 else 0
    else if c == 124 then if d == 124 then if f == 124 then 27 else 18 else 18
    else if c == 60 then if d == 60 then if f == 60 then 28 else 20 else 20
    else if c == 62 then if d == 62 then if f == 62 then 29 else 0 else 0
    else if c == 195 then if d == 151 then 16 else 0
    else if c == 226 then if d == 134 then if f == 146 then 17 else 0 else 0
    else if c == 47 then if d == 45 then 95 else 0
    else if c == 64 then if d == 91 then 96 else 0
    else if c < 48 then (if c == 39 then B else 0)
    else if c < 58 then (if A == 1 then 5 else 0)
    else if s0 c == 1 then B
    else 0

theorem bcomm (a b : UInt8) : (a == b) = (b == a) := by
  cases h : a == b <;> cases h2 : b == a <;> simp_all (config := {decide := true}) [isD, isW]

theorem isD_iff (c : UInt8) : (48 ≤ c.toUInt64 ∧ c.toUInt64 ≤ 57) ↔ isD c = true := by
  rw [← isD_eq]; simp


theorem tailc (c : UInt8) (A B : UInt64) :
    (if c.toUInt64 < 48 then if c = 39 then B else 0
      else if c.toUInt64 < 58 then if A = 1 then 5 else 0
      else if s0 c.toUInt64 = 1 then B else 0) =
    (if isD c = true then (if A = 1 then 5 else 0) else if isW c = true then B else 0) := by
  have e1 : ∀ v : BitVec 8, ((UInt8.ofBitVec v).toUInt64 < 48 ↔ v.toNat < 48) := by decide
  have e2 : ∀ v : BitVec 8, ((UInt8.ofBitVec v).toUInt64 < 58 ↔ v.toNat < 58) := by decide
  have e3 : ∀ v : BitVec 8, (v.toNat < 48 → (isW (UInt8.ofBitVec v) = true ↔ v.toNat = 39)) ∧ isD (UInt8.ofBitVec v) = decide (48 ≤ v.toNat ∧ v.toNat < 58) := by decide
  have h1 := e1 c.toBitVec
  have h2 := e2 c.toBitVec
  have h3 := e3 c.toBitVec
  have hc : c = UInt8.ofBitVec c.toBitVec := rfl
  have hn : c.toBitVec.toNat = c.toNat := rfl
  rw [hn] at h1 h2 h3
  have hs := s0_eq c
  by_cases a1 : c.toUInt64 < 48
  · have a1' := h1.1 a1
    rw [if_pos a1]
    have hd : isD c = false := by rw [hc]; rw [h3.2]; simp; omega
    rw [hd]
    have : isW c = true ↔ c = 39 := by
      rw [hc] at *; rw [h3.1 a1']; constructor
      · intro h; apply UInt8.toNat.inj; simpa using h
      · intro h; have := congrArg UInt8.toNat h; simpa using this
    by_cases a3 : c = 39
    · simp [a3] at this ⊢; simp [this]
    · have : ¬ isW c = true := fun h => a3 (this.1 h)
      simp [a3, this]
  · have a1' : ¬ c.toBitVec.toNat < 48 := fun h => a1 (h1.2 h)
    rw [if_neg a1]
    by_cases a2 : c.toUInt64 < 58
    · have a2' := h2.1 a2
      have hd : isD c = true := by rw [hc]; rw [h3.2]; simp; omega
      rw [if_pos a2, hd]; simp
    · have a2' : ¬ c.toBitVec.toNat < 58 := fun h => a2 (h2.2 h)
      have hd : isD c = false := by rw [hc]; rw [h3.2]; simp; omega
      rw [if_neg a2, hd, hs]; simp

theorem s4'_eq (c d f : UInt8) (A B : UInt64) :
    s4' c.toUInt64 d.toUInt64 f.toUInt64 A B =
      if c = 32 ∨ c = 10 then 90
      else if c = 45 ∧ d = 45 then 94
      else if c = 47 ∧ d = 45 then 95
      else if c = 64 ∧ d = 91 then 96
      else match opTable.find? (fun e => e.1.isPrefixOf [c, d, f]) with
      | some (_, t) => t
      | none => if isD c then (if A == 1 then 5 else 0) else if isW c then B else 0 := by
  by_cases h32 : c = 32
  · subst h32; simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm]
  by_cases h10 : c = 10
  · subst h10; simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm]
  by_cases h40 : c = 40
  · subst h40; simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm]
  by_cases h41 : c = 41
  · subst h41; simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm]
  by_cases h43 : c = 43
  · subst h43; simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm]
  by_cases h45 : c = 45
  · subst h45
    cases d45 : (d == 45) <;> simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm, d45] <;> simp_all (config := {decide := true}) [isD, isW]
  by_cases h42 : c = 42
  · subst h42; simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm]
  by_cases h59 : c = 59
  · subst h59; simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm]
  by_cases h44 : c = 44
  · subst h44; simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm]
  by_cases h91 : c = 91
  · subst h91; simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm]
  by_cases h93 : c = 93
  · subst h93; simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm]
  by_cases h58 : c = 58
  · subst h58
    cases d61 : (d == 61) <;> simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm, d61] <;> simp_all (config := {decide := true}) [isD, isW]
  by_cases h61 : c = 61
  · subst h61
    cases d61 : (d == 61) <;> cases d62 : (d == 62) <;> simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm, d61, d62] <;> simp_all (config := {decide := true}) [isD, isW]
  by_cases h38 : c = 38
  · subst h38
    cases d38 : (d == 38) <;> cases f38 : (f == 38) <;> simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm, d38, f38] <;> simp_all (config := {decide := true}) [isD, isW]
  by_cases h124 : c = 124
  · subst h124
    cases d124 : (d == 124) <;> cases f124 : (f == 124) <;> simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm, d124, f124] <;> simp_all (config := {decide := true}) [isD, isW]
  by_cases h60 : c = 60
  · subst h60
    cases d60 : (d == 60) <;> cases f60 : (f == 60) <;> simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm, d60, f60] <;> simp_all (config := {decide := true}) [isD, isW]
  by_cases h62 : c = 62
  · subst h62
    cases d62 : (d == 62) <;> cases f62 : (f == 62) <;> simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm, d62, f62] <;> simp_all (config := {decide := true}) [isD, isW]
  by_cases h195 : c = 195
  · subst h195
    cases d151 : (d == 151) <;> simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm, d151] <;> simp_all (config := {decide := true}) [isD, isW]
  by_cases h226 : c = 226
  · subst h226
    cases d134 : (d == 134) <;> cases f146 : (f == 146) <;> simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm, d134, f146] <;> simp_all (config := {decide := true}) [isD, isW]
  by_cases h47 : c = 47
  · subst h47
    cases d45 : (d == 45) <;> simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm, d45] <;> simp_all (config := {decide := true}) [isD, isW]
  by_cases h64 : c = 64
  · subst h64
    cases d91 : (d == 91) <;> simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm, d91] <;> simp_all (config := {decide := true}) [isD, isW]
  have b32 : (c == 32) = false := by simpa using h32
  have b10 : (c == 10) = false := by simpa using h10
  have b40 : (c == 40) = false := by simpa using h40
  have b41 : (c == 41) = false := by simpa using h41
  have b43 : (c == 43) = false := by simpa using h43
  have b45 : (c == 45) = false := by simpa using h45
  have b42 : (c == 42) = false := by simpa using h42
  have b59 : (c == 59) = false := by simpa using h59
  have b44 : (c == 44) = false := by simpa using h44
  have b91 : (c == 91) = false := by simpa using h91
  have b93 : (c == 93) = false := by simpa using h93
  have b58 : (c == 58) = false := by simpa using h58
  have b61 : (c == 61) = false := by simpa using h61
  have b38 : (c == 38) = false := by simpa using h38
  have b124 : (c == 124) = false := by simpa using h124
  have b60 : (c == 60) = false := by simpa using h60
  have b62 : (c == 62) = false := by simpa using h62
  have b195 : (c == 195) = false := by simpa using h195
  have b226 : (c == 226) = false := by simpa using h226
  have b47 : (c == 47) = false := by simpa using h47
  have b64 : (c == 64) = false := by simpa using h64
  simp [s4', opTable, List.find?, List.isPrefixOf, tu2, bcomm, b32, b10, b40, b41, b43, b45, b42, b59, b44, b91, b93, b58, b61, b38, b124, b60, b62, b195, b226, b47, b64, h32, h10, h40, h41, h43, h45, h42, h59, h44, h91, h93, h58, h61, h38, h124, h60, h62, h195, h226, h47, h64]
  exact tailc c A B

/-! ### s4 = spec kind -/

def kind (l : List UInt8) : UInt64 :=
  match l with
  | [] => 91
  | c :: r =>
    if c = 32 ∨ c = 10 then 90
    else if c = 45 ∧ r.getD 0 0 = 45 then 94
    else if c = 47 ∧ r.getD 0 0 = 45 then 95
    else if c = 64 ∧ r.getD 0 0 = 91 then 96
    else match opTable.find? (fun e => e.1.isPrefixOf (c :: r)) with
    | some (_, t) => t
    | none =>
      if isD c then (if ((c :: r).takeWhile isW).all isD then 5 else 0)
      else if isW c then (kwX.lookup ((c :: r).takeWhile isW)).getD 14 else 0

theorem find_pad (l : List UInt8) :
    opTable.find? (fun e => e.1.isPrefixOf l) = opTable.find? (fun e => e.1.isPrefixOf [l.getD 0 0, l.getD 1 0, l.getD 2 0]) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;>
    simp [opTable, List.find?, List.isPrefixOf, bcomm]

theorem s4_eq_s4' (x : List UInt8) (p : UInt64) :
    s4 x p = if p < len x then s4' (rd x p) (rd x (p + 1)) (rd x (p + 2)) (s2 (len' x) x p (s1 (len' x) x p))
      (s3 x p (s1 (len' x) x p)) else 91 := rfl

theorem tw_len (l : List UInt8) : (l.takeWhile isW).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.takeWhile_cons]; split <;> simp <;> omega

theorem take_takeWhile (l : List UInt8) : l.take (l.takeWhile isW).length = l.takeWhile isW := by
  have h := List.takeWhile_append_dropWhile (p := isW) (l := l)
  calc l.take (l.takeWhile isW).length = ((l.takeWhile isW) ++ (l.dropWhile isW)).take (l.takeWhile isW).length := by rw [h]
    _ = l.takeWhile isW := List.take_left' rfl

theorem s4_kind (x : List UInt8) (p : UInt64) (hx : x.length < 2 ^ 32) (hp : p.toNat ≤ x.length) :
    s4 x p = kind (x.drop p.toNat) := by
  rw [s4_eq_s4']
  by_cases hlt : p < len x
  · have hl : p.toNat < x.length := (lt_len hx).1 hlt
    simp only [hlt, if_true]
    -- the word end
    have he := s1_eq (len' x) x p hx hp (by unfold len'; omega)
    generalize hed : s1 (len' x) x p = e at *
    have htw : ((x.drop p.toNat).takeWhile isW).length ≤ x.length - p.toNat := by
      have := tw_len (x.drop p.toNat); simp at this; omega
    have he1 : e.toNat ≤ x.length := by omega
    have he2 : p.toNat ≤ e.toNat := by omega
    have hw : (x.drop p.toNat).take (e.toNat - p.toNat) = (x.drop p.toNat).takeWhile isW := by
      rw [← take_takeWhile]; congr 1; omega
    have hA := s2_eq (len' x) x p e hx he1 he2 (by unfold len'; omega)
    have hB := s3_eq x p e hx he1 he2
    rw [hw] at hA hB
    have hc : rd x p = (((x.drop p.toNat).take 3).getD 0 0).toUInt64 := rd_seg x p p 3 0 (by omega) (by simp)
    have hd : rd x (p + 1) = (((x.drop p.toNat).take 3).getD 1 0).toUInt64 :=
      rd_seg x p _ 3 1 (by omega) (by simp [UInt64.toNat_add]; omega)
    have hf : rd x (p + 2) = (((x.drop p.toNat).take 3).getD 2 0).toUInt64 :=
      rd_seg x p _ 3 2 (by omega) (by simp [UInt64.toNat_add]; omega)
    rw [hc, hd, hf, hA, hB, s4'_eq]
    obtain ⟨c, r, hcr⟩ : ∃ c r, x.drop p.toNat = c :: r := ⟨_, _, drop_cons hl⟩
    rw [hcr]
    have e1 : ((c :: r).take 3).getD 1 0 = (c :: r).getD 1 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_take]
    have e2 : ((c :: r).take 3).getD 2 0 = (c :: r).getD 2 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_take]
    have e0 : ((c :: r).take 3).getD 0 0 = (c :: r).getD 0 0 := by simp
    rw [e0, e1, e2, ← find_pad (c :: r)]
    simp only [kind]
    by_cases hall : ((c :: r).takeWhile isW).all isD = true <;> simp [hall]
  · have : p.toNat = x.length := by
      have := (not_congr (lt_len hx (p := p))).1 hlt; omega
    simp [hlt, this, kind]

/-! ### the main loop s9 -/

theorem op_props : ∀ e ∈ opTable, e.2 ≠ 0 ∧ e.2 ≠ 5 ∧ e.2 ≠ 14 ∧ e.2 ≠ 90 ∧ e.2 ≠ 91 ∧ e.2 < 256 := by decide
theorem kw_props : ∀ e ∈ kwTable, e.2 ≠ 0 ∧ e.2 ≠ 5 ∧ e.2 ≠ 14 ∧ e.2 ≠ 90 ∧ e.2 ≠ 91 ∧ e.2 < 256 := by decide

theorem s5_op : ∀ e ∈ opTable, ∀ (x : List UInt8) (p : UInt64), s5 x p e.2 = p + e.1.length.toUInt64 := by
  intro e he x p
  simp only [opTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [s5]

theorem op_props2 : ∀ e ∈ opTable, e.2 ≠ 92 ∧ e.2 ≠ 93 ∧ e.2 ≠ 94 ∧ e.2 ≠ 95 ∧ e.2 ≠ 96 ∧ e.2 ≠ 97 ∧ e.2 ≠ 98 := by decide
theorem op_s23 : ∀ e ∈ opTable, s23 e.2 = 0 := by decide
theorem kw_s23 : ∀ e ∈ kwTable, s23 e.2 = 0 := by decide
theorem kw_props2 : ∀ e ∈ kwTable, e.2 ≠ 92 ∧ e.2 ≠ 93 ∧ e.2 ≠ 94 ∧ e.2 ≠ 95 ∧ e.2 ≠ 96 ∧ e.2 ≠ 97 ∧ e.2 ≠ 98 := by decide
theorem s5_92 (x : List UInt8) (p : UInt64) : s5 x p 92 = s1 (len' x) x p := by simp [s5]
theorem s5_93 (x : List UInt8) (p : UInt64) : s5 x p 93 = s1 (len' x) x p := by simp [s5]

theorem op_len : ∀ e ∈ opTable, e.1.length ≤ 3 := by decide

theorem s5_word (x : List UInt8) (p k : UInt64) (hk : k = 5 ∨ k = 14 ∨ ∃ e ∈ kwTable, e.2 = k) :
    s5 x p k = s1 (len' x) x p := by
  have : k ≠ 9 ∧ k ≠ 16 ∧ k ≠ 19 ∧ k ≠ 23 ∧ k ≠ 17 ∧ k ≠ 26 ∧ k ≠ 27 ∧ k ≠ 28 ∧ k ≠ 29 ∧ k ≠ 6 ∧ k ≠ 7 ∧ k ≠ 8 ∧ k ≠ 10 ∧
      k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 13 ∧ k ≠ 15 ∧ k ≠ 18 ∧ k ≠ 20 ∧ k ≠ 30 ∧ k ≠ 31 ∧ k ≠ 90 := by
    rcases hk with rfl | rfl | ⟨e, he, rfl⟩
    · decide
    · decide
    · revert e; decide
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩ := this
  simp [s5, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]

theorem lookup_mem : ∀ (L : List (List UInt8 × UInt64)) (w : List UInt8) (k : UInt64), L.lookup w = some k →
    ∃ e ∈ L, e.2 = k
  | [], w, k, h => by simp [List.lookup] at h
  | (a, b) :: L, w, k, h => by
      simp only [List.lookup] at h
      split at h
      · exact ⟨(a, b), by simp, by simpa using h⟩
      · obtain ⟨e, he, h2⟩ := lookup_mem L w k h
        exact ⟨e, by simp [he], h2⟩

theorem lookup_key : ∀ (L : List (List UInt8 × UInt64)) (w : List UInt8) (k : UInt64), L.lookup w = some k →
    ∃ e ∈ L, e.1 = w ∧ e.2 = k
  | [], w, k, h => by simp [List.lookup] at h
  | (a, b) :: L, w, k, h => by
      simp only [List.lookup] at h
      split at h
      · rename_i hw; exact ⟨(a, b), by simp, by simpa using (beq_iff_eq.1 hw).symm, by simpa using h⟩
      · obtain ⟨e, he, h2⟩ := lookup_key L w k h
        exact ⟨e, by simp [he], h2⟩

theorem lookup_app : ∀ (L M : List (List UInt8 × UInt64)) (w : List UInt8),
    (L ++ M).lookup w = (L.lookup w).or (M.lookup w)
  | [], M, w => by simp [List.lookup]
  | (a, b) :: L, M, w => by
      simp only [List.cons_append, List.lookup]
      split <;> simp [lookup_app L M w]

theorem kwX_open : kwX.lookup OPEN = some 0 := by decide
theorem kwX_ns : kwX.lookup NS = some 92 := by decide
theorem kwX_sec : kwX.lookup SEC = some 98 := by decide
theorem kwX_end : kwX.lookup END = some 97 := by decide

theorem kwX_drop (w : List UInt8) (h : dropKw.contains w = true) : kwX.lookup w = some 93 := by
  have : w ∈ dropKw := by simpa using h
  simp only [dropKw, List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl <;> decide

theorem lookupN_key : ∀ (L : List (List UInt8 × Nat)) (w : List UInt8) (k : Nat), L.lookup w = some k →
    ∃ e ∈ L, e.1 = w ∧ e.2 = k
  | [], w, k, h => by simp [List.lookup] at h
  | (a, b) :: L, w, k, h => by
      simp only [List.lookup] at h
      split at h
      · rename_i hw; exact ⟨(a, b), by simp, by simpa using (beq_iff_eq.1 hw).symm, by simpa using h⟩
      · obtain ⟨e, he, h2⟩ := lookupN_key L w k h
        exact ⟨e, by simp [he], h2⟩

theorem kwX_old (w : List UInt8) (h1 : ¬ (w = OPEN ∨ w = NS ∨ w = SEC ∨ w = END)) (h2 : ¬ dropKw.contains w = true) :
    kwX.lookup w = kwTable.lookup w := by
  rw [kwX, lookup_app]
  rcases hm : List.lookup w [([101, 110, 100], 97), ([111, 112, 101, 110], 0), ([115, 101, 99, 116, 105, 111, 110], 98),
    ([110, 97, 109, 101, 115, 112, 97, 99, 101], 92), ([112, 114, 105, 118, 97, 116, 101], 93)] with _ | k
  · simp
  · exfalso
    obtain ⟨e, he, rfl, -⟩ := lookup_key _ _ _ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> simp_all (config := {decide := true}) [OPEN, NS, SEC, END, dropKw]

theorem head_getD (r : List UInt8) (b : UInt8) (hb : b ≠ 0) : (r.head? = some b) ↔ (r.getD 0 0 = b) := by
  cases r with
  | nil => simp; exact fun e => hb e.symm
  | cons a r => simp

theorem kind_spec (c : UInt8) (r : List UInt8) :
    (kind (c :: r) = 90 ∧ step (c :: r) = some ([], r)) ∨
    (kind (c :: r) = 94 ∧ c = 45 ∧ r.head? = some 45 ∧ step (c :: r) = some ([], r.tail.dropWhile (· != 10))) ∨
    (kind (c :: r) = 95 ∧ c = 47 ∧ r.head? = some 45 ∧ step (c :: r) =
      (if r.tail.head? == some 45 || r.tail.head? == some 33 then (docWs r.length r.tail.tail).bind (blockEnd 0)
       else blockEnd 0 r.tail.tail).bind fun t => if r.tail.head? == some 45 && !declNext 2 t then none
         else if r.tail.head? == some 33 && !cmdNext t then none else some ([], t)) ∨
    (kind (c :: r) = 96 ∧ c = 64 ∧ r.head? = some 91 ∧
      step (c :: r) = (attrEnd r.tail [] false).bind fun t => if declNext 1 t then some ([], t) else none) ∨
    (∃ e ∈ opTable, kind (c :: r) = e.2 ∧ step (c :: r) = some ([e.2], (c :: r).drop e.1.length) ∧
        e.1.isPrefixOf (c :: r) = true) ∨
    (kind (c :: r) = 5 ∧ ((c :: r).takeWhile isW).all isD = true ∧ step (c :: r) = some (5 :: le8 (numVal ((c :: r).takeWhile isW)), (c :: r).dropWhile isW)) ∨
    kind (c :: r) = 0 ∨
    (∃ e ∈ kwTable, kind (c :: r) = e.2 ∧ step (c :: r) = some ([e.2], (c :: r).dropWhile isW)) ∨
    (kind (c :: r) = 14 ∧ step (c :: r) = some (14 :: (((c :: r).takeWhile isW).flatMap fun b => [1, b.toUInt64]) ++ [0],
      (c :: r).dropWhile isW)) ∨
    (kind (c :: r) = 92 ∧ step (c :: r) = (scopeLine 0 ((c :: r).dropWhile isW)).map fun (n, e) => (scopeTok true n, e)) ∨
    (kind (c :: r) = 98 ∧ step (c :: r) = (scopeLine 1 ((c :: r).dropWhile isW)).map fun (n, e) => (scopeTok true n, e)) ∨
    (kind (c :: r) = 97 ∧ step (c :: r) = (scopeLine 2 ((c :: r).dropWhile isW)).map fun (n, e) => (scopeTok false n, e)) ∨
    (kind (c :: r) = 93 ∧ step (c :: r) =
      if declNext 0 ((c :: r).dropWhile isW) then some ([], (c :: r).dropWhile isW) else none) := by
  unfold kind step
  by_cases hws : c = 32 ∨ c = 10
  · have : (c == 32 || c == 10) = true := by simpa using hws
    simp [hws, this]
  have : ¬ (c == 32 || c == 10) = true := by simpa using hws
  simp only [hws, this, if_false, Bool.false_eq_true]
  have e45 := head_getD r 45 (by decide)
  have e91 := head_getD r 91 (by decide)
  by_cases a1 : c = 45 ∧ r.head? = some 45
  · have k1 : c = 45 ∧ r.getD 0 0 = 45 := ⟨a1.1, e45.1 a1.2⟩
    have b1 : (c == 45 && r.head? == some 45) = true := by simp [a1]
    right; left; rw [if_pos k1, if_pos b1]; exact ⟨rfl, a1.1, a1.2, rfl⟩
  have k1 : ¬ (c = 45 ∧ r.getD 0 0 = 45) := fun h => a1 ⟨h.1, e45.2 h.2⟩
  have b1 : ¬ (c == 45 && r.head? == some 45) = true := by simpa using a1
  rw [if_neg k1, if_neg b1]
  by_cases a2 : c = 47 ∧ r.head? = some 45
  · have k2 : c = 47 ∧ r.getD 0 0 = 45 := ⟨a2.1, e45.1 a2.2⟩
    have b2 : (c == 47 && r.head? == some 45) = true := by simp [a2]
    right; right; left; rw [if_pos k2, if_pos b2]; exact ⟨rfl, a2.1, a2.2, rfl⟩
  have k2 : ¬ (c = 47 ∧ r.getD 0 0 = 45) := fun h => a2 ⟨h.1, e45.2 h.2⟩
  have b2 : ¬ (c == 47 && r.head? == some 45) = true := by simpa using a2
  rw [if_neg k2, if_neg b2]
  by_cases a3 : c = 64 ∧ r.head? = some 91
  · have k3 : c = 64 ∧ r.getD 0 0 = 91 := ⟨a3.1, e91.1 a3.2⟩
    have b3 : (c == 64 && r.head? == some 91) = true := by simp [a3]
    right; right; right; left; rw [if_pos k3, if_pos b3]
    exact ⟨rfl, a3.1, a3.2, rfl⟩
  have k3 : ¬ (c = 64 ∧ r.getD 0 0 = 91) := fun h => a3 ⟨h.1, e91.2 h.2⟩
  have b3 : ¬ (c == 64 && r.head? == some 91) = true := by simpa using a3
  rw [if_neg k3, if_neg b3]
  right; right; right; right
  rcases hf : opTable.find? (fun e => e.1.isPrefixOf (c :: r)) with _ | ⟨s, t⟩
  · simp only [hf]
    by_cases hd : isD c = true
    · by_cases ha : ((c :: r).takeWhile isW).all isD = true
      · simp [hd, ha]
      · simp [hd, ha]
    · by_cases hw : isW c = true
      · simp only [hd, hw, if_true, if_false, Bool.false_eq_true]
        by_cases hop : (c :: r).takeWhile isW = OPEN
        · rw [hop, kwX_open]; simp
        have b1 : ((c :: r).takeWhile isW == OPEN) = false := by simpa using hop
        rw [if_neg (by simp [b1])]
        rcases hsk : scopeKw.lookup ((c :: r).takeWhile isW) with _ | kk
        · have hne : ∀ w, w ∈ [NS, SEC, END] → (c :: r).takeWhile isW ≠ w := fun w hw e0 => by
            rw [e0] at hsk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
            rcases hw with rfl | rfl | rfl <;> simp (config := {decide := true}) [scopeKw, List.lookup] at hsk
          have hlk : ¬ ((c :: r).takeWhile isW = OPEN ∨ (c :: r).takeWhile isW = NS ∨ (c :: r).takeWhile isW = SEC ∨
            (c :: r).takeWhile isW = END) := fun h => h.elim hop (fun h => h.elim (hne NS (by simp)) (fun h => h.elim
              (hne SEC (by simp)) (hne END (by simp))))
          simp only []
          by_cases hdk : dropKw.contains ((c :: r).takeWhile isW) = true
          · rw [kwX_drop _ hdk, if_pos hdk]; simp
          rw [if_neg hdk, kwX_old _ hlk hdk]
          rcases hl : kwTable.lookup ((c :: r).takeWhile isW) with _ | k
          · simp
          · obtain ⟨e, he, rfl⟩ := lookup_mem _ _ _ hl
            simp only [Option.getD_some]
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, rfl, rfl⟩)))
        · obtain ⟨e, he, h1, h2⟩ := lookupN_key _ _ _ hsk
          simp only [scopeKw, List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl <;> simp only at h1 h2 <;> subst h2 <;> rw [← h1]
          · rw [kwX_ns]; simp
          · rw [kwX_sec]; simp
          · rw [kwX_end]; simp
      · simp [hd, hw]
  · have hmem := List.mem_of_find?_eq_some hf
    have hpre := List.find?_some hf
    simp only [hf]
    left
    exact ⟨(s, t), hmem, rfl, rfl, by simpa using hpre⟩

theorem dw_eq (l : List UInt8) : l.dropWhile isW = l.drop (l.takeWhile isW).length := by
  have h := List.takeWhile_append_dropWhile (p := isW) (l := l)
  calc l.dropWhile isW = ((l.takeWhile isW) ++ (l.dropWhile isW)).drop (l.takeWhile isW).length := (List.drop_left' rfl).symm
    _ = _ := by rw [h]

theorem and255' : (∀ e ∈ opTable, e.2 &&& 255 = e.2) ∧ (∀ e ∈ kwTable, e.2 &&& 255 = e.2) := by decide


theorem word_end (x : List UInt8) (p : UInt64) (hx : x.length < 2 ^ 32) (c : UInt8) (r : List UInt8)
    (hdp : x.drop p.toNat = c :: r) :
    (s1 (len' x) x p).toNat = p.toNat + ((c :: r).takeWhile isW).length ∧
    (s1 (len' x) x p).toNat ≤ x.length ∧
    x.drop (s1 (len' x) x p).toNat = (c :: r).dropWhile isW ∧
    (x.drop p.toNat).take ((s1 (len' x) x p).toNat - p.toNat) = (c :: r).takeWhile isW := by
  have hl : p.toNat < x.length := by
    have := congrArg List.length hdp; simp at this; omega
  have he := s1_eq (len' x) x p hx (by omega) (by unfold len'; omega)
  rw [hdp] at he
  have htw := tw_len (c :: r)
  have hlen : (c :: r).length = x.length - p.toNat := by rw [← hdp]; simp
  refine ⟨he, by omega, ?_, ?_⟩
  · rw [he, dw_eq, ← hdp, List.drop_drop]
  · rw [hdp, he, Nat.add_sub_cancel_left]; exact take_takeWhile _

/-! ### trivia scanners (s12: first byte `b`; s11: nested block comment end) -/

theorem u8_beq (a b : UInt8) : (a.toUInt64 == b.toUInt64) = (a == b) := by
  cases h : a == b
  · have : a ≠ b := by simpa using h
    have : a.toUInt64 ≠ b.toUInt64 := fun e => this (UInt8.toUInt64_inj.1 e)
    simpa using this
  · have : a = b := by simpa using h
    simp [this]

/-- s12 stops at the first byte `b` (or the end) -/
theorem s12_eq : ∀ (n : Nat) (x : List UInt8) (p : UInt64) (b : UInt8), x.length < 2 ^ 32 → p.toNat ≤ x.length →
    x.length - p.toNat ≤ n →
    (s12 n x p b.toUInt64).toNat = p.toNat + ((x.drop p.toNat).takeWhile (· != b)).length
  | 0, x, p, b, hx, hp, hn => by
      have : p.toNat = x.length := by omega
      simp [s12, this]
  | n + 1, x, p, b, hx, hp, hn => by
      simp only [s12]
      by_cases hl : p.toNat < x.length
      · have hlt : p < len x := (lt_len hx).2 hl
        rw [drop_cons hl, if_pos hlt, rd_eq, u8_beq]
        generalize x.getD p.toNat 0 = a
        by_cases ha : (a == b) = true
        · have := beq_iff_eq.1 ha; subst this; rw [if_pos ha]; simp [List.takeWhile_cons]
        · have hp1 : (p + 1).toNat = p.toNat + 1 := inc_toNat hl hx
          have := s12_eq n x (p + 1) b hx (by omega) (by omega)
          rw [hp1] at this
          rw [if_neg ha, this]
          simp at ha; simp [List.takeWhile_cons, ha]; omega
      · have : p.toNat = x.length := by omega
        have : ¬ p < len x := by rw [lt_len hx]; omega
        simp [*]

theorem dropWhile_eq_drop {p : UInt8 → Bool} (l : List UInt8) : l.dropWhile p = l.drop (l.takeWhile p).length := by
  have h := List.takeWhile_append_dropWhile (p := p) (l := l)
  calc l.dropWhile p = ((l.takeWhile p) ++ (l.dropWhile p)).drop (l.takeWhile p).length := (List.drop_left' rfl).symm
    _ = _ := by rw [h]

theorem s12_drop (x : List UInt8) (p : UInt64) (b : UInt8) (hx : x.length < 2 ^ 32) (hp : p.toNat ≤ x.length) :
    (s12 (len' x) x p b.toUInt64).toNat ≤ x.length ∧
    x.drop (s12 (len' x) x p b.toUInt64).toNat = (x.drop p.toNat).dropWhile (· != b) := by
  have he := s12_eq (len' x) x p b hx hp (by unfold len'; omega)
  have htw : ((x.drop p.toNat).takeWhile (· != b)).length ≤ (x.drop p.toNat).length := by
    exact (List.takeWhile_prefix _).length_le
  refine ⟨by simp at htw; omega, ?_⟩
  rw [he, dropWhile_eq_drop, List.drop_drop]

theorem s11_end (m : Nat) (x : List UInt8) (q d : UInt64) (hx : x.length < 2 ^ 32) (hq : q.toNat = x.length) :
    s11 m x q d = 0 := by
  cases m with
  | zero => rfl
  | succ m => have : ¬ q < len x := by rw [lt_len hx]; omega
              simp [s11, this]

theorem u64_lit (a : UInt8) (k : UInt8) : (a.toUInt64 == k.toUInt64) = true ↔ a = k := by rw [u8_beq]; simp

/-- s11 (when it does not reject) finds the end of the nested block comment -/
theorem s11_sound : ∀ (n : Nat) (x : List UInt8) (i d : UInt64), x.length < 2 ^ 32 → i.toNat ≤ x.length →
    d.toNat ≤ i.toNat → s11 n x i d ≠ 0 →
    (s11 n x i d).toNat ≤ x.length ∧ blockEnd d.toNat (x.drop i.toNat) = some (x.drop (s11 n x i d).toNat)
  | 0, x, i, d, hx, hi, hd, h => by simp [s11] at h
  | n + 1, x, i, d, hx, hi, hd, h => by
      have hlt : i < len x := by
        cases Decidable.em (i < len x) with
        | inl h' => exact h'
        | inr h' => simp only [s11, if_neg h'] at h; exact absurd rfl h
      have hl : i.toNat < x.length := (lt_len hx).1 hlt
      have hi1 := inc_toNat hl hx
      have IH1 : s11 n x (i + 1) d ≠ 0 → (s11 n x (i + 1) d).toNat ≤ x.length ∧
          blockEnd d.toNat (x.drop (i.toNat + 1)) = some (x.drop (s11 n x (i + 1) d).toNat) := by
        intro h2; have := s11_sound n x (i + 1) d hx (by omega) (by omega) h2; rwa [hi1] at this
      have hs : s11 (n + 1) x i d = if rd x i == 45 then if rd x (i + 1) == 47 then if d == 0 then i + 2 else s11 n x (i + 2) (d - 1) else s11 n x (i + 1) d
          else if rd x i == 47 then if rd x (i + 1) == 45 then s11 n x (i + 2) (d + 1) else s11 n x (i + 1) d
          else s11 n x (i + 1) d := by simp only [s11, if_pos hlt]
      rw [hs] at h ⊢
      rw [drop_cons hl]
      have hra : rd x i = (x.getD i.toNat 0).toUInt64 := rd_eq x i
      generalize x.getD i.toNat 0 = a at hra
      rw [hra] at h ⊢
      have l45 : (45 : UInt64) = (45 : UInt8).toUInt64 := rfl
      have l47 : (47 : UInt64) = (47 : UInt8).toUInt64 := rfl
      rcases hr : x.drop (i.toNat + 1) with _ | ⟨a', r'⟩
      · have hend : i.toNat + 1 = x.length := by
          have := congrArg List.length hr; simp at this; omega
        have hrd1 : rd x (i + 1) = 0 := by
          rw [rd_eq, hi1]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : x.length ≤ i.toNat + 1)]
        have hz := s11_end n x (i + 1) d hx (by omega)
        rw [hrd1] at h; simp [hz] at h
      have hl1 : i.toNat + 1 < x.length := by
        have := congrArg List.length hr; simp at this; omega
      have hi2 : (i + 2).toNat = i.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
      have hd2 : drop_cons hl1 = drop_cons hl1 := rfl
      have hr2 := drop_cons hl1
      rw [hr] at hr2
      simp only [List.cons.injEq] at hr2
      obtain ⟨ea', er'⟩ := hr2
      have hrb : rd x (i + 1) = a'.toUInt64 := by rw [rd_eq, hi1, ea']
      have er2 : x.drop (i.toNat + 2) = r' := by rw [show i.toNat + 2 = i.toNat + 1 + 1 by omega]; exact er'.symm
      rw [hrb] at h ⊢
      have IH2 : ∀ d' : UInt64, d'.toNat ≤ i.toNat + 2 → s11 n x (i + 2) d' ≠ 0 → (s11 n x (i + 2) d').toNat ≤ x.length ∧
          blockEnd d'.toNat r' = some (x.drop (s11 n x (i + 2) d').toNat) := by
        intro d' h1 h2; have := s11_sound n x (i + 2) d' hx (by omega) (by omega) h2; rwa [hi2, er2] at this
      rw [l45, l47] at h ⊢
      simp only [blockEnd]
      by_cases c45 : a = 45
      · subst c45
        by_cases c47 : a' = 47
        · subst c47
          simp only [u64_lit, if_true, true_and, and_self] at h ⊢
          by_cases d0 : d = 0
          · subst d0; simp [hi2, er2]; omega
          · have d0' : d.toNat ≠ 0 := fun e => d0 (UInt64.toNat.inj (by simpa using e))
            rw [if_neg d0'] at ⊢; simp only [d0', beq_iff_eq, if_false, d0] at h ⊢
            have hsub : (d - 1).toNat = d.toNat - 1 := by
              rw [UInt64.toNat_sub_of_le]; · simp
              · rw [UInt64.le_iff_toNat_le]; simp; omega
            have := IH2 (d - 1) (by omega) h; rwa [hsub] at this
        · have : ¬ (a'.toUInt64 == (47 : UInt8).toUInt64) = true := by rw [u64_lit]; exact c47
          simp only [u64_lit, if_true, true_and, this, if_false, c47] at h ⊢
          have := IH1 h; rw [hr] at this; simpa using this
      · have n45 : ¬ (a.toUInt64 == (45 : UInt8).toUInt64) = true := by rw [u64_lit]; exact c45
        simp only [n45, if_false, c45, false_and] at h ⊢
        by_cases c47 : a = 47
        · subst c47
          by_cases c45' : a' = 45
          · subst c45'
            simp only [u64_lit, if_true, and_self] at h ⊢
            have := IH2 (d + 1) (by rw [UInt64.toNat_add]; simp; omega) h
            have hadd : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
            rwa [hadd] at this
          · have : ¬ (a'.toUInt64 == (45 : UInt8).toUInt64) = true := by rw [u64_lit]; exact c45'
            simp only [u64_lit, if_true, this, if_false, c45', and_false] at h ⊢
            have := IH1 h; rw [hr] at this; simpa using this
        · have n47 : ¬ (a.toUInt64 == (47 : UInt8).toUInt64) = true := by rw [u64_lit]; exact c47
          simp only [n47, if_false, c47, false_and] at h ⊢
          have := IH1 h; rw [hr] at this; simpa using this

/-! ### trivia checks (s13: a skipped line; s14: an attribute; s15: Lean's whitespace after a doc opener) -/

theorem rd_at (x : List UInt8) (i k : UInt64) (hx : x.length < 2 ^ 32) (hi : i.toNat ≤ x.length) (hk : k.toNat < 16) :
    rd x (i + k) = ((x.drop i.toNat).getD k.toNat 0).toUInt64 := by
  rw [rd_eq]
  have : (i + k).toNat = i.toNat + k.toNat := by rw [UInt64.toNat_add]; omega
  rw [this]; simp [List.getD_eq_getElem?_getD]

theorem rd_at0 (x : List UInt8) (i : UInt64) : rd x i = ((x.drop i.toNat).getD 0 0).toUInt64 := by
  rw [rd_eq]; simp [List.getD_eq_getElem?_getD]

theorem drop_tail (x : List UInt8) (i : UInt64) (hx : x.length < 2 ^ 32) (hl : i.toNat < x.length) :
    x.drop (i + 1).toNat = (x.drop i.toNat).tail := by
  rw [inc_toNat hl hx, List.tail_drop]

theorem blockEnd_le : ∀ (d : Nat) (l t : List UInt8), blockEnd d l = some t → t.length ≤ l.length
  | _, [], _, h => by simp [blockEnd] at h
  | _, [_], _, h => by simp [blockEnd] at h
  | d, c :: c' :: r, t, h => by
    simp only [blockEnd] at h
    split at h
    · split at h
      · cases h; simp; omega
      · have := blockEnd_le _ r t h; simp; omega
    · split at h
      · have := blockEnd_le _ r t h; simp; omega
      · have := blockEnd_le _ (c' :: r) t h; simp at this ⊢; omega

theorem lt_or_end (x : List UInt8) (i : UInt64) (hx : x.length < 2 ^ 32) (hi : i.toNat ≤ x.length) :
    (i < len x ∧ i.toNat < x.length) ∨ (¬ i < len x ∧ x.drop i.toNat = []) := by
  by_cases h : i.toNat < x.length
  · exact .inl ⟨(lt_len hx).2 h, h⟩
  · exact .inr ⟨fun h' => h ((lt_len hx).1 h'), by simp; omega⟩

/-! ### scope lines (s13 spaces, s21 small letters, s20 the name's form, s22 the line) and module docs (s24, s25) -/

theorem s13_eq : ∀ (n : Nat) (x : List UInt8) (p : UInt64), x.length < 2 ^ 32 → p.toNat ≤ x.length →
    x.length - p.toNat ≤ n →
    (s13 n x p).toNat = p.toNat + ((x.drop p.toNat).takeWhile (· == 32)).length
  | 0, x, p, hx, hp, hn => by
      have : p.toNat = x.length := by omega
      simp [s13, this]
  | n + 1, x, p, hx, hp, hn => by
      simp only [s13]
      by_cases hl : p.toNat < x.length
      · have hlt : p < len x := (lt_len hx).2 hl
        rw [drop_cons hl, if_pos hlt, rd_eq]
        have l32 : (32 : UInt64) = (32 : UInt8).toUInt64 := rfl
        rw [l32, u8_beq]
        generalize x.getD p.toNat 0 = a
        by_cases ha : (a == 32) = true
        · have hp1 : (p + 1).toNat = p.toNat + 1 := inc_toNat hl hx
          have := s13_eq n x (p + 1) hx (by omega) (by omega)
          rw [hp1] at this
          rw [if_pos ha, this]
          simp at ha; simp [List.takeWhile_cons, ha]; omega
        · rw [if_neg ha]; simp at ha; simp [List.takeWhile_cons, ha]
      · have : p.toNat = x.length := by omega
        have : ¬ p < len x := by rw [lt_len hx]; omega
        simp [*]

theorem s13_drop (x : List UInt8) (p : UInt64) (hx : x.length < 2 ^ 32) (hp : p.toNat ≤ x.length) :
    p.toNat ≤ (s13 (len' x) x p).toNat ∧ (s13 (len' x) x p).toNat ≤ x.length ∧
    x.drop (s13 (len' x) x p).toNat = (x.drop p.toNat).dropWhile (· == 32) := by
  have he := s13_eq (len' x) x p hx hp (by unfold len'; omega)
  have htw : ((x.drop p.toNat).takeWhile (· == 32)).length ≤ (x.drop p.toNat).length :=
    (List.takeWhile_prefix _).length_le
  refine ⟨by omega, by simp at htw; omega, ?_⟩
  rw [he, dropWhile_eq_drop, List.drop_drop]

theorem low_eq (b : UInt8) : (96 < b.toUInt64 ∧ b.toUInt64 < 123) ↔ (97 ≤ b && b ≤ 122) = true := by
  have : ∀ v : BitVec 8, (96 < (UInt8.ofBitVec v).toUInt64 ∧ (UInt8.ofBitVec v).toUInt64 < 123) ↔
      (97 ≤ UInt8.ofBitVec v && UInt8.ofBitVec v ≤ 122) = true := by decide
  exact this b.toBitVec

theorem cap_eq (b : UInt8) : (64 < b.toUInt64 ∧ b.toUInt64 < 91) → (65 ≤ b && b ≤ 90) = true := by
  have : ∀ v : BitVec 8, (64 < (UInt8.ofBitVec v).toUInt64 ∧ (UInt8.ofBitVec v).toUInt64 < 91) →
      (65 ≤ UInt8.ofBitVec v && UInt8.ofBitVec v ≤ 90) = true := by decide
  exact this b.toBitVec

theorem s21_eq : ∀ (n : Nat) (x : List UInt8) (p : UInt64), x.length < 2 ^ 32 → p.toNat ≤ x.length →
    x.length - p.toNat ≤ n →
    (s21 n x p).toNat = p.toNat + ((x.drop p.toNat).takeWhile fun b => 97 ≤ b && b ≤ 122).length
  | 0, x, p, hx, hp, hn => by
      have : p.toNat = x.length := by omega
      simp [s21, this]
  | n + 1, x, p, hx, hp, hn => by
      simp only [s21]
      by_cases hl : p.toNat < x.length
      · have hlt : p < len x := (lt_len hx).2 hl
        rw [drop_cons hl, if_pos hlt, rd_eq]
        have hp1 : (p + 1).toNat = p.toNat + 1 := inc_toNat hl hx
        have IH := s21_eq n x (p + 1) hx (by omega) (by omega)
        rw [hp1] at IH
        generalize x.getD p.toNat 0 = a
        by_cases ha : (97 ≤ a && a ≤ 122) = true
        · obtain ⟨h1, h2⟩ := (low_eq a).2 ha
          rw [if_pos h1, if_pos h2, IH]; simp only [List.takeWhile_cons, ha, if_true, List.length_cons]; omega
        · have hn : ¬ (96 < a.toUInt64 ∧ a.toUInt64 < 123) := fun e => ha ((low_eq a).1 e)
          have : (List.takeWhile (fun b => 97 ≤ b && b ≤ 122) (a :: x.drop (p.toNat + 1))).length = 0 := by
            simp only [List.takeWhile_cons, ha, Bool.false_eq_true, if_false, List.length_nil]
          rw [this]
          by_cases h1 : 96 < a.toUInt64
          · rw [if_pos h1, if_neg (fun h2 => hn ⟨h1, h2⟩)]; simp
          · rw [if_neg h1]; simp
      · have : p.toNat = x.length := by omega
        have : ¬ p < len x := by rw [lt_len hx]; omega
        simp [*]

theorem takeWhile_take_lt {p : UInt8 → Bool} : ∀ (l : List UInt8) (m : Nat), (l.takeWhile p).length < m →
    (l.take m).takeWhile p = l.takeWhile p
  | [], _, _ => by simp
  | _ :: _, 0, h => by simp at h
  | a :: l, m + 1, h => by
    by_cases ha : p a = true
    · simp only [List.takeWhile_cons, ha, if_true, List.length_cons] at h ⊢
      simp only [List.take_succ_cons, List.takeWhile_cons, ha, if_true]
      rw [takeWhile_take_lt l m (by omega)]
    · simp [List.takeWhile_cons, ha]

theorem g8 (a : UInt8) (n : Nat) (hn : n < 256) (e : (a.toUInt64 == (no_index (OfNat.ofNat n : UInt64))) = true) :
    a = (no_index (OfNat.ofNat n : UInt8)) := (tu2 a n hn).1 (by simpa using e)

set_option maxHeartbeats 2000000 in
/-- s20 (when it accepts) checks a scope name's form -/
theorem s20_sound (x : List UInt8) (a b : UInt64) (hx : x.length < 2 ^ 32) (hab : a.toNat < b.toNat)
    (hb : b.toNat ≤ x.length) (h : s20 x a b = 1) : nsName ((x.drop a.toNat).take (b.toNat - a.toNat)) = true := by
  obtain ⟨c, r, hcr⟩ : ∃ c r, x.drop a.toNat = c :: r := ⟨_, _, drop_cons (by omega)⟩
  have ha1 : (a + 1).toNat = a.toNat + 1 := inc_toNat (n := x.length) (by omega) hx
  have hr : x.drop (a.toNat + 1) = r := by rw [← List.tail_drop, hcr]; rfl
  have hrl : r.length = x.length - a.toNat - 1 := by have := congrArg List.length hcr; simp at this; omega
  have hj := s21_eq (len' x) x (a + 1) hx (by omega) (by unfold len'; omega)
  rw [ha1, hr] at hj
  unfold s20 at h
  simp only at h
  generalize hJ : s21 (len' x) x (a + 1) = j at h hj
  have hc0 : rd x a = c.toUInt64 := by rw [rd_at0, hcr]; rfl
  rw [hc0] at h
  have hm : b.toNat - a.toNat = (b.toNat - a.toNat - 1) + 1 := by omega
  rw [hcr, hm, List.take_succ_cons]
  split at h <;> try (cases h)
  rename_i c1; split at h <;> try (cases h)
  rename_i c2; split at h <;> try (cases h)
  rename_i c3; split at h <;> try (cases h)
  rename_i c4
  have hjb : j.toNat < b.toNat := UInt64.lt_iff_toNat_lt.1 c3
  obtain ⟨A, hA⟩ : ∃ A, A = r.takeWhile fun b => 97 ≤ b && b ≤ 122 := ⟨_, rfl⟩
  rw [← hA] at hj
  have hAt : (r.take (b.toNat - a.toNat - 1)).takeWhile (fun b => 97 ≤ b && b ≤ 122) = A := by
    rw [hA]; exact takeWhile_take_lt r _ (by rw [← hA]; omega)
  have hDt : (r.take (b.toNat - a.toNat - 1)).dropWhile (fun b => 97 ≤ b && b ≤ 122) =
      (x.drop j.toNat).take (b.toNat - j.toNat) := by
    rw [dropWhile_eq_drop, hAt, List.drop_take, ← hr, List.drop_drop]
    rw [hj, show b.toNat - (a.toNat + 1 + A.length) = b.toNat - a.toNat - 1 - A.length by omega]
  have hs2 := s2_eq (len' x) x j b hx hb (by omega) (by unfold len'; omega)
  rw [hs2] at c4
  have hall : ((x.drop j.toNat).take (b.toNat - j.toNat)).all isD = true := by
    exact Decidable.byContradiction fun hn => by simp [hn] at c4
  have hne : (x.drop j.toNat).take (b.toNat - j.toNat) ≠ [] := by
    intro e; have := congrArg List.length e; simp at this; omega
  have hcap := cap_eq c ⟨c1, c2⟩
  simp only [nsName, hAt, hDt]
  simp only [Bool.and_eq_true, hcap, true_and, bne_iff_ne, ne_eq, hne, not_false_eq_true, hall, Bool.not_eq_true',
    beq_eq_false_iff_ne]
  have hAl : A.length = j.toNat - a.toNat - 1 := by omega
  have rdA : ∀ k, k < A.length → rd x (a + 1 + k.toUInt64) = (A.getD k 0).toUInt64 := fun k hk => by
    have hk' : (a + 1 + k.toUInt64).toNat = a.toNat + 1 + k := by
      simp [UInt64.toNat_add]; omega
    rw [rd_eq, hk']
    have : A.getD k 0 = r.getD k 0 := by
      have hp : A <+: r := by rw [hA]; exact List.takeWhile_prefix _
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hk hp.length_le), hp.getElem hk]
    rw [this, ← hr]; simp [List.getD_eq_getElem?_getD]
  constructor
  · intro e
    have hl3 : A.length = 2 := by have := congrArg List.length e; simp at this; omega
    have hj3 : j = a + 3 := by apply UInt64.toNat.inj; simp [UInt64.toNat_add]; omega
    have e0 : c = 73 := by simp at e; exact e.1
    have e1 : A.getD 0 0 = 110 := by simp at e; rw [e.2]; rfl
    have e2 : A.getD 1 0 = 116 := by simp at e; rw [e.2]; rfl
    have r1 := rdA 0 (by omega); have r2 := rdA 1 (by omega)
    simp at r1 r2
    rw [show (a + 1 + 1 : UInt64) = a + 2 by ac_rfl] at r2
    simp only [List.getD_eq_getElem?_getD] at e1 e2
    simp [hj3, e0, r1, r2] at h; rw [e1, e2] at h; exact h rfl rfl
  · intro e
    have hl5 : A.length = 4 := by have := congrArg List.length e; simp at this; omega
    have hj3 : ¬ j = a + 3 := fun h3 => by rw [h3] at hjb hAl; simp [UInt64.toNat_add] at hAl; omega
    have hj5 : j = a + 5 := by apply UInt64.toNat.inj; simp [UInt64.toNat_add]; omega
    have e0 : c = 70 := by simp at e; exact e.1
    simp at e
    have r1 := rdA 0 (by omega); have r2 := rdA 1 (by omega); have r3 := rdA 2 (by omega); have r4 := rdA 3 (by omega)
    simp at r1 r2 r3 r4
    rw [show (a + 1 + 1 : UInt64) = a + 2 by ac_rfl] at r2
    rw [show (a + 1 + 2 : UInt64) = a + 3 by ac_rfl] at r3
    rw [show (a + 1 + 3 : UInt64) = a + 4 by ac_rfl] at r4
    simp [hj3, hj5, e0, r1, r2, r3, r4, e.2] at h

theorem s12_ge (x : List UInt8) (p : UInt64) (b : UInt8) (hx : x.length < 2 ^ 32) (hp : p.toNat ≤ x.length) :
    p.toNat ≤ (s12 (len' x) x p b.toUInt64).toNat := by
  have := s12_eq (len' x) x p b hx hp (by unfold len'; omega); omega

theorem head1 (r : List UInt8) (b : UInt8) (hb : b ≠ 0) : (r.tail.head? = some b) ↔ (r.getD 1 0 = b) := by
  cases r with
  | nil => simp; exact fun e => hb e.symm
  | cons a r => rw [List.tail_cons, head_getD r b hb]; simp

/-- s15 (when it does not reject) skips Lean's whitespace after a doc opener -/
theorem s15_sound : ∀ (n : Nat) (x : List UInt8) (i : UInt64), x.length < 2 ^ 32 → i.toNat ≤ x.length →
    s15 n x i ≠ 0 → (s15 n x i).toNat ≤ x.length ∧
      ∀ F, x.length - i.toNat < F → docWs F (x.drop i.toNat) = some (x.drop (s15 n x i).toNat)
  | 0, x, i, hx, hi, h => by simp [s15] at h
  | n + 1, x, i, hx, hi, h => by
    rcases lt_or_end x i hx hi with ⟨hlt, hl⟩ | ⟨hlt, he⟩
    · have IH : ∀ j : UInt64, i.toNat < j.toNat → j.toNat ≤ x.length → s15 n x j ≠ 0 →
          (s15 n x j).toNat ≤ x.length ∧
          ∀ f, x.length - i.toNat ≤ f → docWs f (x.drop j.toNat) = some (x.drop (s15 n x j).toNat) := by
        intro j h1 h2 h3
        obtain ⟨a, b⟩ := s15_sound n x j hx h2 h3
        exact ⟨a, fun f hf => b f (by omega)⟩
      have hi1 := inc_toNat hl hx
      have hd := drop_cons hl
      have e1 : rd x (i + 1) = ((x.drop (i.toNat + 1)).getD 0 0).toUInt64 := by
        rw [rd_at x i 1 hx hi (by decide), hd]; simp
      have e2 : rd x (i + 2) = ((x.drop (i.toNat + 1)).getD 1 0).toUInt64 := by
        rw [rd_at x i 2 hx hi (by decide), hd]; simp
      have e0 : rd x i = (x.getD i.toNat 0).toUInt64 := rd_eq x i
      have hb := IH (i + 1) (by omega) (by omega)
      rw [hi1] at hb
      -- the line comment: from the newline on
      have hlc : ∀ (hne : s15 n x (s12 (len' x) x (i + 1) 10) ≠ 0),
          (s15 n x (s12 (len' x) x (i + 1) 10)).toNat ≤ x.length ∧ ∀ f, x.length - i.toNat ≤ f →
          docWs f ((x.drop (i.toNat + 1)).dropWhile (· != 10)) = some (x.drop (s15 n x (s12 (len' x) x (i + 1) 10)).toNat) := by
        intro hne
        have l10 : (10 : UInt64) = (10 : UInt8).toUInt64 := rfl
        rw [l10] at hne ⊢
        obtain ⟨q1, q2⟩ := s12_drop x (i + 1) 10 hx (by omega)
        have q3 := s12_ge x (i + 1) 10 hx (by omega)
        rw [hi1] at q2 q3
        rw [← q2]; exact IH _ (by omega) q1 hne
      -- the plain block comment: from its end on
      have hbc : ∀ (hne : s11 (len' x) x (i + 3) 0 ≠ 0) (hne2 : s15 n x (s11 (len' x) x (i + 3) 0) ≠ 0),
          (s15 n x (s11 (len' x) x (i + 3) 0)).toNat ≤ x.length ∧ ∀ f, x.length - i.toNat ≤ f →
          (blockEnd 0 (x.drop (i.toNat + 1)).tail.tail).bind (docWs f) = some (x.drop (s15 n x (s11 (len' x) x (i + 3) 0)).toNat) := by
        intro hne hne2
        have hl1 : i.toNat + 3 ≤ x.length ∨ x.length < i.toNat + 3 := by omega
        rcases hl1 with hl1 | hl1
        · have hi2 : (i + 3).toNat = i.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
          obtain ⟨q1, q2⟩ := s11_sound _ x (i + 3) 0 hx (by omega) (by simp) hne
          rw [hi2, show (0 : UInt64).toNat = 0 from rfl] at q2
          have q3 := blockEnd_le _ _ _ q2
          simp at q3
          have ht : (x.drop (i.toNat + 1)).tail.tail = x.drop (i.toNat + 3) := by rw [List.tail_drop, List.tail_drop]
          rw [ht, q2]
          exact IH _ (by omega) q1 hne2
        · have hn : ¬ (i + 3 < len x) := by rw [lt_len hx, UInt64.toNat_add]; simp; omega
          exact absurd (by generalize len' x = m; cases m <;> simp [s11, hn]) hne
      simp only [s15, if_pos hlt] at h ⊢
      simp only [e1, e2] at h ⊢
      simp only [e0] at h ⊢
      rw [hd]
      generalize hr : x.drop (i.toNat + 1) = r at h hb hlc hbc hd ⊢
      generalize x.getD i.toNat 0 = a at h hd ⊢
      have l10 : (10 : UInt64) = (10 : UInt8).toUInt64 := rfl
      have l13 : (13 : UInt64) = (13 : UInt8).toUInt64 := rfl
      have l9 : (9 : UInt64) = (9 : UInt8).toUInt64 := rfl
      have l32 : (32 : UInt64) = (32 : UInt8).toUInt64 := rfl
      have l33 : (33 : UInt64) = (33 : UInt8).toUInt64 := rfl
      have l45 : (45 : UInt64) = (45 : UInt8).toUInt64 := rfl
      have l47 : (47 : UInt64) = (47 : UInt8).toUInt64 := rfl
      rw [l10, l13, l9, l32, l33, l45, l47] at h ⊢
      simp only [u64_lit] at h ⊢
      have r10 := head_getD r 10 (by decide)
      have r45 := head_getD r 45 (by decide)
      have t45 := head1 r 45 (by decide)
      have t33 := head1 r 33 (by decide)
      have dz : ∀ f, x.length - i.toNat < f → ∃ g, f = g + 1 ∧ x.length - i.toNat ≤ g := fun f hf =>
        ⟨f - 1, by omega, by omega⟩
      by_cases c32 : a = 32
      · subst c32; simp (config := {decide := true}) only [if_true] at h ⊢
        obtain ⟨b1, b2⟩ := hb h
        refine ⟨b1, fun f hf => ?_⟩
        obtain ⟨g, rfl, hg⟩ := dz f hf
        simp only [docWs]; rw [if_pos (by simp)]; exact b2 g (by omega)
      by_cases c10 : a = 10
      · subst c10; simp (config := {decide := true}) only [if_true, if_false] at h ⊢
        obtain ⟨b1, b2⟩ := hb h
        refine ⟨b1, fun f hf => ?_⟩
        obtain ⟨g, rfl, hg⟩ := dz f hf
        simp only [docWs]; rw [if_pos (by simp)]; exact b2 g (by omega)
      by_cases c13 : a = 13
      · subst c13; simp (config := {decide := true}) only [if_true, if_false] at h ⊢
        by_cases d10 : r.getD 0 0 = 10
        · simp only [d10, if_true] at h ⊢
          obtain ⟨b1, b2⟩ := hb h
          refine ⟨b1, fun f hf => ?_⟩
          obtain ⟨g, rfl, hg⟩ := dz f hf
          simp only [docWs]; rw [if_pos (by simp [r10.2 d10])]; exact b2 g (by omega)
        · simp only [d10, if_false] at h ⊢; exact absurd rfl h
      by_cases c9 : a = 9
      · subst c9; simp (config := {decide := true}) only [if_true, if_false] at h
      by_cases c45 : a = 45
      · subst c45; simp (config := {decide := true}) only [if_true, if_false] at h ⊢
        by_cases d45 : r.getD 0 0 = 45
        · simp only [d45, if_true] at h ⊢
          obtain ⟨b1, b2⟩ := hlc h
          refine ⟨b1, fun f hf => ?_⟩
          obtain ⟨g, rfl, hg⟩ := dz f hf
          simp only [docWs]; rw [if_neg (by simp (config := {decide := true})), if_neg (by simp (config := {decide := true})), if_pos (by simp (config := {decide := true}) [r45.2 d45])]; exact b2 g (by omega)
        · simp only [d45, if_false] at h ⊢
          refine ⟨by omega, fun f hf => ?_⟩
          obtain ⟨g, rfl, hg⟩ := dz f hf
          simp only [docWs]
          rw [if_neg (by simp (config := {decide := true})), if_neg (by simp (config := {decide := true})), if_neg (fun e => d45 (r45.1 e.2)), if_neg (by simp (config := {decide := true})), hd]
      by_cases c47 : a = 47
      · subst c47; simp (config := {decide := true}) only [if_true, if_false] at h ⊢
        by_cases d45 : r.getD 0 0 = 45
        · simp only [d45, if_true] at h ⊢
          by_cases e45 : r.getD 1 0 = 45
          · simp only [e45, if_true] at h ⊢
            refine ⟨by omega, fun f hf => ?_⟩
            obtain ⟨g, rfl, hg⟩ := dz f hf
            simp only [docWs]
            rw [if_neg (by simp (config := {decide := true})), if_neg (by simp (config := {decide := true})), if_neg (by simp (config := {decide := true})), if_neg (fun e => e.2.2.1 (t45.2 e45)), hd]
          by_cases e33 : r.getD 1 0 = 33
          · simp only [e45, e33, if_true, if_false, ite_self] at h ⊢
            refine ⟨by omega, fun f hf => ?_⟩
            obtain ⟨g, rfl, hg⟩ := dz f hf
            simp only [docWs]
            rw [if_neg (by simp (config := {decide := true})), if_neg (by simp (config := {decide := true})), if_neg (by simp (config := {decide := true})), if_neg (fun e => e.2.2.2 (t33.2 e33)), hd]
          simp only [e45, e33, if_false] at h ⊢
          by_cases z : s11 (len' x) x (i + 3) 0 = 0
          · simp [z] at h
          simp only [beq_iff_eq, z, if_false] at h ⊢
          obtain ⟨b1, b2⟩ := hbc z h
          refine ⟨b1, fun f hf => ?_⟩
          obtain ⟨g, rfl, hg⟩ := dz f hf
          simp only [docWs]
          rw [if_neg (by simp (config := {decide := true})), if_neg (by simp (config := {decide := true})), if_neg (by simp (config := {decide := true})),
            if_pos (by simp (config := {decide := true}) only [true_and, r45.2 d45]
                       exact ⟨fun e => e45 (t45.1 e), fun e => e33 (t33.1 e)⟩)]
          exact b2 g (by omega)
        · simp only [d45, if_false] at h ⊢
          refine ⟨by omega, fun f hf => ?_⟩
          obtain ⟨g, rfl, hg⟩ := dz f hf
          simp only [docWs]
          rw [if_neg (by simp (config := {decide := true})), if_neg (by simp (config := {decide := true})), if_neg (by simp (config := {decide := true})), if_neg (fun e => d45 (r45.1 e.2.1)), hd]
      simp only [c32, c10, c13, c9, c45, c47, if_false] at h ⊢
      refine ⟨by omega, fun f hf => ?_⟩
      obtain ⟨g, rfl, hg⟩ := dz f hf
      simp only [docWs]
      rw [if_neg (by simp [c32, c10, c13]), if_neg (by simp [c9, c13]), if_neg (by simp [c45]), if_neg (by simp [c47]), hd]
    · simp only [s15, if_neg hlt]
      refine ⟨hi, fun f hf => ?_⟩
      rw [he]; cases f with
      | zero => omega
      | succ g => simp [docWs]

theorem getD_drop (x : List UInt8) (j k : Nat) : (x.drop j).getD k 0 = x.getD (j + k) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- the name s14 is reading: the bytes from `ws` (0: none) up to `i`, reversed (as `attrEnd` keeps it) -/
def nameAt (x : List UInt8) (ws i : UInt64) : List UInt8 :=
  if ws = 0 then [] else ((x.drop ws.toNat).take (i.toNat - ws.toNat)).reverse

theorem take_succ_rev (l : List UInt8) (k : Nat) (hk : k < l.length) :
    (l.take (k + 1)).reverse = l.getD k 0 :: (l.take k).reverse := by
  rw [List.take_succ, List.getElem?_eq_getElem hk]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

/-- s14 (when it does not reject) ends an attribute, as Lean's attribute grammar -/
theorem s14_sound : ∀ (n : Nat) (x : List UInt8) (i ws d : UInt64), x.length < 2 ^ 32 → i.toNat ≤ x.length →
    0 < i.toNat → ws.toNat ≤ i.toNat → (d = 0 ∨ d = 1) → s14 n x i ws d ≠ 0 →
    (s14 n x i ws d).toNat ≤ x.length ∧
      attrEnd (x.drop i.toNat) (nameAt x ws i) (d == 1) = some (x.drop (s14 n x i ws d).toNat)
  | 0, x, i, ws, d, hx, hi, hi0, hws, hd, h => by simp [s14] at h
  | n + 1, x, i, ws, d, hx, hi, hi0, hws, hd, h => by
    rcases lt_or_end x i hx hi with ⟨hlt, hl⟩ | ⟨hlt, _⟩
    · have hi1 := inc_toNat hl hx
      have hdc := drop_cons hl
      generalize hv : s14 (n + 1) x i ws d = v at h ⊢
      simp only [s14, if_pos hlt, rd_eq] at hv
      rw [hdc]
      simp only [attrEnd]
      obtain ⟨a, ha⟩ : ∃ a, x.getD i.toNat 0 = a := ⟨_, rfl⟩
      simp only [ha] at hv ⊢
      have IH := fun ws' d' h1 h2 h3 => s14_sound n x (i + 1) ws' d' hx (by omega) (by omega) h1 h2 h3
      rw [hi1] at IH
      by_cases cw : isW a = true
      · rw [s0_eq, if_pos cw] at hv
        simp only [if_pos cw, beq_self_eq_true, if_true] at hv ⊢
        rcases hd with rfl | rfl
        · simp only [show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false] at hv ⊢
          subst hv
          have hws' : (if ws == 0 then i else ws).toNat ≤ i.toNat + 1 := by split <;> omega
          obtain ⟨a1, a2⟩ := IH _ 0 hws' (.inl rfl) h
          refine ⟨a1, ?_⟩
          have hname : nameAt x (if ws == 0 then i else ws) (i + 1) = a :: nameAt x ws i := by
            subst ha
            by_cases w0 : ws = 0
            · subst w0
              have hi0' : i ≠ 0 := fun e => by subst e; simp at hi0
              simp [nameAt, hi0', hi1, List.take_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
            · have hw0 : (ws == 0) = false := by simpa using w0
              simp only [nameAt, hw0, if_false, w0, Bool.false_eq_true, if_false, hi1]
              rw [show i.toNat + 1 - ws.toNat = (i.toNat - ws.toNat) + 1 by omega]
              rw [take_succ_rev _ _ (by simp; omega), getD_drop, show ws.toNat + (i.toNat - ws.toNat) = i.toNat by omega]
          rw [hname] at a2; simpa using a2
        · subst hv; simp at h
      · rw [s0_eq, if_neg cw] at hv
        simp only [if_neg cw, Bool.false_eq_true, if_false, show ((0 : UInt64) == 1) = false from rfl] at hv ⊢
        have hs16 : ws ≠ 0 → s16 x ws i = 1 → attrNames.contains (nameAt x ws i).reverse = true := fun w0 e => by
          rw [s16_eq x ws i hx hi hws] at e
          simp only [nameAt, w0, if_false, List.reverse_reverse]
          split at e
          · assumption
          · cases e
        generalize hd2 : (if ws == 0 then d else if s16 x ws i == 1 then 1 else 2) = d2 at hv
        by_cases d2' : d2 = 2
        · subst d2'; subst hv; simp at h
        have hspec : (d2 = 0 ∨ d2 = 1) ∧ ¬ (nameAt x ws i ≠ [] ∧ attrNames.contains (nameAt x ws i).reverse = false) ∧
            ((d == 1) || decide (nameAt x ws i ≠ [])) = (d2 == 1) := by
          subst hd2
          by_cases w0 : ws = 0
          · subst w0; simp [nameAt]; rcases hd with rfl | rfl <;> simp
          · have hw0 : (ws == 0) = false := by simpa using w0
            simp only [hw0, Bool.false_eq_true, if_false] at d2' ⊢
            by_cases e1 : s16 x ws i = 1
            · have hc := hs16 w0 e1
              have hne : nameAt x ws i ≠ [] := fun e => by rw [e] at hc; simp [attrNames] at hc
              simp [e1, hne] <;> simpa using hc
            · simp [e1] at d2'
        obtain ⟨h01, h2, h3⟩ := hspec
        rw [if_neg (by simpa using h2)]
        simp only [h3, show (d2 == 2) = false from by simpa using d2', Bool.false_eq_true, if_false] at hv ⊢
        have l32 : (32 : UInt64) = (32 : UInt8).toUInt64 := rfl
        have l44 : (44 : UInt64) = (44 : UInt8).toUInt64 := rfl
        have l93 : (93 : UInt64) = (93 : UInt8).toUInt64 := rfl
        rw [l32, l44, l93] at hv
        simp only [u64_lit] at hv
        have nil0 : nameAt x 0 (i + 1) = [] := by simp [nameAt]
        by_cases c32 : a = 32
        · subst c32; simp only [beq_self_eq_true, if_true] at hv ⊢
          subst hv
          obtain ⟨a1, a2⟩ := IH 0 d2 (by simp) h01 h
          rw [nil0] at a2; exact ⟨a1, a2⟩
        have b32 : (a == 32) = false := by simpa using c32
        simp only [c32, b32, if_false, Bool.false_eq_true] at hv ⊢
        by_cases c44 : a = 44
        · subst c44; simp only [beq_self_eq_true, if_true] at hv ⊢
          rcases h01 with rfl | rfl
          · subst hv; simp at h
          · simp only [beq_self_eq_true, if_true] at hv ⊢
            subst hv
            obtain ⟨a1, a2⟩ := IH 0 0 (by simp) (.inl rfl) h
            rw [nil0] at a2; exact ⟨a1, by simpa using a2⟩
        have b44 : (a == 44) = false := by simpa using c44
        simp only [c44, b44, if_false, Bool.false_eq_true] at hv ⊢
        by_cases c93 : a = 93
        · subst c93; simp only [beq_self_eq_true, if_true] at hv ⊢
          rcases h01 with rfl | rfl
          · subst hv; simp at h
          · simp only [beq_self_eq_true, if_true] at hv ⊢
            subst hv; exact ⟨by omega, by rw [hi1]⟩
        have b93 : (a == 93) = false := by simpa using c93
        simp only [c93, b93, if_false, Bool.false_eq_true] at hv
        subst hv; simp at h
    · simp [s14, hlt] at h

theorem pre_of : ∀ (w l : List UInt8), (∀ b ∈ w, b ≠ 0) → (∀ k < w.length, l.getD k 0 = w.getD k 0) →
    w.isPrefixOf l = true
  | [], _, _, _ => by simp [List.isPrefixOf]
  | b :: w, l, hw, h => by
    have h0 := h 0 (by simp); simp at h0
    cases l with
    | nil => simp at h0; exact absurd h0.symm (hw b (by simp))
    | cons a l =>
      simp at h0; subst h0
      simp only [List.isPrefixOf, beq_self_eq_true, Bool.true_and]
      exact pre_of w l (fun c hc => hw c (by simp [hc])) (fun k hk => by have := h (k + 1) (by simp; omega); simpa using this)

theorem headW (l : List UInt8) (k : Nat) : ((l.drop k).head?.map isW).getD false = isW (l.getD k 0) := by
  rw [List.head?_drop]; simp only [List.getD_eq_getElem?_getD]
  cases l[k]? <;> simp [isW]

/-- s19: `def` as a word at `j` -/
theorem s19_sound (x : List UInt8) (j : UInt64) (hx : x.length < 2 ^ 32) (hj : j.toNat ≤ x.length) (h : s19 x j = 1) :
    startsWord DEF (x.drop j.toNat) = true := by
  simp only [s19, rd_at x j 1 hx hj (by decide), rd_at x j 2 hx hj (by decide), rd_at x j 3 hx hj (by decide)] at h
  simp only [rd_at0] at h
  generalize x.drop j.toNat = l at h ⊢
  have g : ∀ (a : UInt8) (n : Nat), n < 256 → (a.toUInt64 == (no_index (OfNat.ofNat n : UInt64))) = true →
      a = (no_index (OfNat.ofNat n : UInt8)) := fun a n hn e => (tu2 a n hn).1 (by simpa using e)
  split at h <;> try (cases h)
  rename_i e0; split at h <;> try (cases h)
  rename_i e1; split at h <;> try (cases h)
  rename_i e2; split at h <;> try (cases h)
  rename_i e3
  rw [s0_eq] at e3
  simp only [startsWord, DEF, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨pre_of _ _ (by decide) (fun k hk => ?_), ?_⟩
  · simp at hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exact g _ _ (by decide) e0
    · exact g _ _ (by decide) (by simpa using e1)
    · exact g _ _ (by decide) (by simpa using e2)
  · rw [headW]; simp_all [List.getD_eq_getElem?_getD]

theorem chain8 (b1 b2 b3 b4 b5 b6 b7 b8 : Bool) (y : UInt64)
    (h : (if b1 = true then if b2 = true then if b3 = true then if b4 = true then if b5 = true then if b6 = true then
      if b7 = true then if b8 = true then (1 : UInt64) else y else y else y else y else y else y else y else y) = 1) :
    (b1 && b2 && b3 && b4 && b5 && b6 && b7 && b8) = true ∨ y = 1 := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> cases b8 <;> simp_all

/-- s18: `private` as a word at `j` (when `0 < k`), else s19 -/
theorem s18_sound (x : List UInt8) (j k : UInt64) (hx : x.length < 2 ^ 32) (hj : j.toNat ≤ x.length) (h : s18 x j k = 1) :
    ((decide (1 ≤ k.toNat) && startsWord PRIV (x.drop j.toNat)) || startsWord DEF (x.drop j.toNat)) = true := by
  have hD : s19 x j = 1 → ((decide (1 ≤ k.toNat) && startsWord PRIV (x.drop j.toNat)) || startsWord DEF (x.drop j.toNat)) = true :=
    fun e => by simp [s19_sound x j hx hj e]
  unfold s18 at h
  split at h
  · rename_i hk
    have hk1 : 1 ≤ k.toNat := by rw [UInt64.lt_iff_toNat_lt] at hk; simp at hk; omega
    simp only [rd_at x j 1 hx hj (by decide), rd_at x j 2 hx hj (by decide), rd_at x j 3 hx hj (by decide),
      rd_at x j 4 hx hj (by decide), rd_at x j 5 hx hj (by decide), rd_at x j 6 hx hj (by decide),
      rd_at x j 7 hx hj (by decide)] at h
    simp only [rd_at0] at h
    have pv : ∀ (e : (((x.drop j.toNat).getD 0 0).toUInt64 == 112 && ((x.drop j.toNat).getD 1 0).toUInt64 == 114 &&
        ((x.drop j.toNat).getD 2 0).toUInt64 == 105 && ((x.drop j.toNat).getD 3 0).toUInt64 == 118 &&
        ((x.drop j.toNat).getD 4 0).toUInt64 == 97 && ((x.drop j.toNat).getD 5 0).toUInt64 == 116 &&
        ((x.drop j.toNat).getD 6 0).toUInt64 == 101 && s0 ((x.drop j.toNat).getD 7 0).toUInt64 == 0) = true),
        startsWord PRIV (x.drop j.toNat) = true := fun e => by
      generalize x.drop j.toNat = l at e ⊢
      rw [s0_eq] at e
      simp only [Bool.and_eq_true, beq_iff_eq] at e
      obtain ⟨⟨⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩ := e
      simp only [startsWord, PRIV, Bool.and_eq_true, Bool.not_eq_true']
      have g : ∀ (a : UInt8) (n : Nat), n < 256 → a.toUInt64 = (no_index (OfNat.ofNat n : UInt64)) → a = (no_index (OfNat.ofNat n : UInt8)) :=
        fun a n hn e => (tu2 a n hn).1 e
      refine ⟨pre_of _ _ (by decide) (fun k hk => ?_), ?_⟩
      · simp at hk
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact g _ _ (by decide) e0
        · exact g _ _ (by decide) e1
        · exact g _ _ (by decide) e2
        · exact g _ _ (by decide) e3
        · exact g _ _ (by decide) e4
        · exact g _ _ (by decide) e5
        · exact g _ _ (by decide) e6
      · rw [headW]; split at e7 <;> simp_all
    rcases chain8 _ _ _ _ _ _ _ _ _ h with e | e
    · simp [pv e, hk1]
    · exact hD e
  · exact hD h

/-- s17 (when it accepts) checks what follows a declaration modifier -/
theorem s17_sound (x : List UInt8) (i k : UInt64) (hx : x.length < 2 ^ 32) (hi : i.toNat ≤ x.length) (h : s17 x i k = 1) :
    declNext k.toNat (x.drop i.toNat) = true := by
  unfold s17 at h
  simp only at h
  split at h
  · cases h
  rename_i hj
  have hj' : s15 (len' x) x i ≠ 0 := by simpa using hj
  obtain ⟨q1, q2⟩ := s15_sound _ x i hx hi hj'
  have hd := q2 ((x.drop i.toNat).length + 1) (by simp <;> omega)
  simp only [declNext, hd]
  generalize hJ : s15 (len' x) x i = j at h q1 ⊢
  have hs : s18 x j k = 1 → ((k.toNat == 2 && [64, 91].isPrefixOf (x.drop j.toNat)) ||
      (decide (1 ≤ k.toNat) && startsWord PRIV (x.drop j.toNat)) || startsWord DEF (x.drop j.toNat)) = true := fun e => by
    have := s18_sound x j k hx q1 e
    simp only [Bool.or_eq_true] at this ⊢
    rcases this with b | c
    · exact .inl (.inr b)
    · exact .inr c
  split at h
  · rename_i hk2
    have hk : k.toNat = 2 := by simp at hk2; subst hk2; rfl
    split at h
    · split at h
      · rename_i e0 e1
        rw [rd_at0] at e0; rw [rd_at x j 1 hx q1 (by decide)] at e1
        have g : ∀ (a : UInt8) (n : Nat), n < 256 → (a.toUInt64 == (no_index (OfNat.ofNat n : UInt64))) = true → a = (no_index (OfNat.ofNat n : UInt8)) :=
          fun a n hn e => (tu2 a n hn).1 (by simpa using e)
        have p : [64, 91].isPrefixOf (x.drop j.toNat) = true := pre_of _ _ (by decide) (fun m hm => by
          simp at hm; rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
          · exact g _ _ (by decide) e0
          · exact g _ _ (by decide) e1)
        simp [hk, p]
      · exact hs h
    · exact hs h
  · exact hs h

theorem dw_head : ∀ l : List UInt8, ((l.dropWhile isW).head?.map isW).getD false = false
  | [] => rfl
  | a :: l => by
    by_cases ha : isW a = true
    · rw [List.dropWhile_cons_of_pos ha]; exact dw_head l
    · rw [List.dropWhile_cons_of_neg ha]; simp [ha]

theorem startsWord_tw (l : List UInt8) : startsWord (l.takeWhile isW) l = true := by
  simp only [startsWord, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨List.isPrefixOf_iff_prefix.2 (List.takeWhile_prefix _), ?_⟩
  rw [← dw_eq]; simpa using dw_head l

theorem kwX_92 : ∀ e ∈ kwX, e.2 = 92 → e.1 = NS := by decide
theorem kwX_97 : ∀ e ∈ kwX, e.2 = 97 → e.1 = END := by decide
theorem kwX_98 : ∀ e ∈ kwX, e.2 = 98 → e.1 = SEC := by decide

/-- s25: a scope word at `j` -/
theorem s25_sound (x : List UInt8) (j : UInt64) (hx : x.length < 2 ^ 32) (hj : j.toNat < x.length) (h : s25 x j = 1) :
    (startsWord NS (x.drop j.toNat) || startsWord SEC (x.drop j.toNat) || startsWord END (x.drop j.toNat)) = true := by
  obtain ⟨c, r, hcr⟩ : ∃ c r, x.drop j.toNat = c :: r := ⟨_, _, drop_cons hj⟩
  obtain ⟨wb1, wb2, wb3, wb4⟩ := word_end x j hx c r hcr
  have hs3 := s3_eq x j (s1 (len' x) x j) hx wb2 (by omega)
  rw [wb4] at hs3
  unfold s25 at h; simp only at h
  rw [hs3] at h
  rw [hcr]
  have key : ∀ (k : UInt64) (w : List UInt8), (kwX.lookup ((c :: r).takeWhile isW)).getD 14 = k → k ≠ 14 →
      (∀ e ∈ kwX, e.2 = k → e.1 = w) → (c :: r).takeWhile isW = w := by
    intro k w hk hk14 hw
    rcases hl : kwX.lookup ((c :: r).takeWhile isW) with _ | v
    · rw [hl] at hk; simp at hk; exact absurd hk.symm hk14
    · rw [hl] at hk; simp at hk; subst hk
      obtain ⟨e, he, h1, h2⟩ := lookup_key _ _ _ hl
      rw [← h1]; exact hw e he h2
  have sw : ∀ w, (c :: r).takeWhile isW = w → startsWord w (c :: r) = true := fun w e => by
    rw [← e]; exact startsWord_tw _
  split at h
  · rename_i e1; have := key 92 NS (by simpa using e1) (by decide) kwX_92; simp [sw NS this]
  split at h
  · rename_i e1; have := key 97 END (by simpa using e1) (by decide) kwX_97; simp [sw END this]
  split at h
  · rename_i e1; have := key 98 SEC (by simpa using e1) (by decide) kwX_98; simp [sw SEC this]
  · cases h

/-- s24 (when it accepts) checks what follows a module doc comment -/
theorem s24_sound (x : List UInt8) (i : UInt64) (hx : x.length < 2 ^ 32) (hi : i.toNat ≤ x.length) (h : s24 x i = 1) :
    cmdNext (x.drop i.toNat) = true := by
  unfold s24 at h
  simp only at h
  split at h
  · cases h
  rename_i hj
  have hj' : s15 (len' x) x i ≠ 0 := by simpa using hj
  obtain ⟨q1, q2⟩ := s15_sound _ x i hx hi hj'
  have hd := q2 ((x.drop i.toNat).length + 1) (by simp <;> omega)
  simp only [cmdNext, hd]
  generalize hJ : s15 (len' x) x i = j at h q1 ⊢
  split at h
  · rename_i hlt
    have hl : j.toNat < x.length := (lt_len hx).1 hlt
    split at h
    · split at h
      · rename_i e0 e1
        rw [rd_at0] at e0; rw [rd_at x j 1 hx q1 (by decide)] at e1
        have : [47, 45].isPrefixOf (x.drop j.toNat) = true := pre_of _ _ (by decide) (fun m hm => by
          simp at hm; rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
          · exact g8 _ _ (by decide) e0
          · exact g8 _ _ (by decide) e1)
        simp [this]
      · cases h
    split at h
    · split at h
      · rename_i e0 e1
        rw [rd_at0] at e0; rw [rd_at x j 1 hx q1 (by decide)] at e1
        have : [64, 91].isPrefixOf (x.drop j.toNat) = true := pre_of _ _ (by decide) (fun m hm => by
          simp at hm; rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
          · exact g8 _ _ (by decide) e0
          · exact g8 _ _ (by decide) e1)
        simp [this]
      · cases h
    split at h
    · rename_i hs18
      have := s18_sound x j 1 hx q1 (by simpa using hs18)
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this ⊢
      rcases this with ⟨-, a⟩ | a <;> simp [a]
    · have := s25_sound x j hx hl h
      simp only [Bool.or_eq_true] at this ⊢
      rcases this with (a | a) | a <;> simp [a]
  · cases h

/-- s22 (when it accepts, with the positions s9 computes) checks a scope line -/
theorem s22_sound (x : List UInt8) (q a b e k : UInt64) (kk : Nat) (hx : x.length < 2 ^ 32) (hq : q.toNat ≤ x.length)
    (ha : a = s13 (len' x) x q) (hb : b = s1 (len' x) x a) (he : e = s13 (len' x) x b)
    (hkk : (k = 92 ∧ kk = 0) ∨ (k = 98 ∧ kk = 1) ∨ (k = 97 ∧ kk = 2)) (h : s22 x q a b e k = 1) :
    a.toNat ≤ b.toNat ∧ b.toNat ≤ x.length ∧ e.toNat ≤ x.length ∧
    scopeLine kk (x.drop q.toNat) = some ((x.drop a.toNat).take (b.toNat - a.toNat), x.drop e.toNat) := by
  obtain ⟨a1, a2, a3⟩ := s13_drop x q hx hq
  rw [← ha] at a1 a2 a3
  have b1 := s1_eq (len' x) x a hx a2 (by unfold len'; omega)
  rw [← hb] at b1
  have htw := tw_len (x.drop a.toNat)
  have hlen : (x.drop a.toNat).length = x.length - a.toNat := by simp
  have b2 : b.toNat ≤ x.length := by omega
  have b3 : x.drop b.toNat = (x.drop a.toNat).dropWhile isW := by rw [b1, dw_eq, List.drop_drop]
  have b4 : (x.drop a.toNat).take (b.toNat - a.toNat) = (x.drop a.toNat).takeWhile isW := by
    rw [b1, Nat.add_sub_cancel_left]; exact take_takeWhile _
  obtain ⟨e1, e2, e3⟩ := s13_drop x b hx b2
  rw [← he] at e1 e2 e3
  refine ⟨by omega, b2, e2, ?_⟩
  unfold scopeLine
  simp only []
  rw [← a3, ← b4, ← b3, ← e3]
  unfold s22 at h
  simp only at h
  have hv : ((x.drop e.toNat).head? = none ∨ (x.drop e.toNat).head? = some 10) ∧
      (if (a == b) = true then (if (k == 92) = true then (0 : UInt64) else 1)
       else if (k == 98) = true then 0 else if (rd x q == 32) = true then s20 x a b else 0) = 1 := by
    by_cases hlt : e < len x
    · have hl : e.toNat < x.length := (lt_len hx).1 hlt
      obtain ⟨c, r, hcr⟩ : ∃ c r, x.drop e.toNat = c :: r := ⟨_, _, drop_cons hl⟩
      have hc : rd x e = c.toUInt64 := by rw [rd_at0, hcr]; rfl
      simp only [hlt, if_true, hc] at h
      by_cases h10 : (c.toUInt64 == 10) = true
      · simp only [h10, if_true] at h
        exact ⟨.inr (by rw [hcr, g8 c 10 (by decide) h10]; rfl), by simpa using h⟩
      · simp [h10] at h
    · have : e.toNat = x.length := by have := (not_congr (lt_len hx (p := e))).1 hlt; omega
      simp only [hlt, if_false] at h
      exact ⟨.inl (by simp [this]), by simpa using h⟩
  obtain ⟨hv, h⟩ := hv
  have hlen0 : ((x.drop a.toNat).take (b.toNat - a.toNat)).length = b.toNat - a.toNat := by simp; omega
  by_cases hab : a = b
  · subst hab
    have k0 : kk ≠ 0 := fun e0 => by
      rcases hkk with ⟨rfl, -⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · simp at h
      · cases e0
      · cases e0
    simp only [Nat.sub_self, List.take_zero]
    rw [if_pos ⟨hv, by simp [k0]⟩]
  · have hab' : (a == b) = false := by simpa using hab
    simp only [hab', Bool.false_eq_true, if_false] at h
    have hlt : a.toNat < b.toNat := by
      have : a.toNat ≠ b.toNat := fun e0 => hab (UInt64.toNat.inj e0)
      omega
    have hne : (x.drop a.toNat).take (b.toNat - a.toNat) ≠ [] := by
      intro e0; have := congrArg List.length e0; simp at this; omega
    have k1 : kk ≠ 1 ∧ (k == 98) = false := by
      rcases hkk with ⟨rfl, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, rfl⟩
      · exact ⟨by decide, by decide⟩
      · simp at h
      · exact ⟨by decide, by decide⟩
    simp only [k1.2, Bool.false_eq_true, if_false] at h
    by_cases h32 : (rd x q == 32) = true
    · simp only [h32, if_true] at h
      have hql : q.toNat < x.length := by omega
      have h32' : (x.drop q.toNat).head? = some 32 := by
        obtain ⟨c, r, hcr⟩ : ∃ c r, x.drop q.toNat = c :: r := ⟨_, _, drop_cons hql⟩
        rw [rd_at0, hcr] at h32; rw [hcr, g8 c 32 (by decide) h32]; rfl
      have hns := s20_sound x a b hx hlt b2 h
      rw [if_pos ⟨hv, by simp [hne, k1.1, h32', hns]⟩]
    · simp [h32] at h

theorem s9_sound : ∀ (n : Nat) (x : List UInt8) (p : UInt64) (o t : Buf), x.length < 2 ^ 32 → p.toNat ≤ x.length →
    s9 n x p o = t → t ≠ [] → ∃ t', Lexes (x.drop p.toNat) t' ∧ t = o ++ t'
  | 0, x, p, o, t, hx, hp, h, ht => by
      exact absurd (by simpa [s9, bnew] using h.symm) ht
  | n + 1, x, p, o, t, hx, hp, h, ht => by
      have hk := s4_kind x p hx hp
      simp only [s9] at h
      rw [hk] at h
      rcases hdp : x.drop p.toNat with _ | ⟨c, r⟩
      · rw [hdp] at h
        have : kind [] = 91 := by simp [kind]
        simp [this] at h
        exact ⟨[], Lexes.nil, by simp [h]⟩
      · rw [hdp] at h
        have hl : p.toNat < x.length := by
          have := congrArg List.length hdp; simp at this; omega
        have hr : ∀ m, x.drop (p.toNat + m) = (c :: r).drop m := fun m => by rw [← hdp, List.drop_drop]
        have hlenc : (c :: r).length = x.length - p.toNat := by rw [← hdp]; simp
        have l10 : (10 : UInt64) = (10 : UInt8).toUInt64 := rfl
        have l93 : (93 : UInt64) = (93 : UInt8).toUInt64 := rfl
        have two : ∀ b : UInt8, r.head? = some b → (p + 2).toNat = p.toNat + 2 ∧ p.toNat + 2 ≤ x.length ∧
            x.drop (p.toNat + 2) = r.tail := fun b hb => by
          clear h
          cases r with
          | nil => simp at hb
          | cons a r' =>
            simp only [List.length_cons] at hlenc
            refine ⟨by rw [UInt64.toNat_add]; simp; omega, by omega, ?_⟩
            rw [hr 2]; simp
        rcases kind_spec c r with ⟨hk90, hst⟩ | ⟨hk94, -, hr0, hst⟩ | ⟨hk95, -, hr0, hst⟩ | ⟨hk96, -, hr0, hst⟩ |
            ⟨e, he, hke, hst, hpre⟩ | ⟨hk5, hall, hst⟩ | hk0 | ⟨e, he, hke, hst⟩ | ⟨hk14, hst⟩ | ⟨hk92, hst⟩ | ⟨hk98, hst⟩ | ⟨hk97, hst⟩ | ⟨hk93, hst⟩
        · simp [s23, hk90] at h
          have hp1 := inc_toNat (p := p) (n := x.length) hl hx
          obtain ⟨t', hL, ht'⟩ := s9_sound n x (p + 1) o t hx (by omega) h ht
          rw [hp1, hr 1] at hL
          exact ⟨[] ++ t', Lexes.cons hst (by simpa using hL), by simpa using ht'⟩
        · simp [s23, hk94] at h
          obtain ⟨hp2, hp2l, hr2⟩ := two 45 hr0
          rw [l10] at h
          obtain ⟨hq1, hq2⟩ := s12_drop x (p + 2) 10 hx (by omega)
          obtain ⟨t', hL, ht'⟩ := s9_sound n x _ o t hx hq1 h ht
          rw [hq2, hp2, hr2] at hL
          exact ⟨[] ++ t', Lexes.cons hst hL, by simpa using ht'⟩
        · simp [s23, hk95] at h
          obtain ⟨hp2, hp2l, hr2⟩ := two 45 hr0
          have hlenr : r.length = x.length - p.toNat - 1 := by simp at hlenc; omega
          have e2 : rd x (p + 2) = (r.tail.getD 0 0).toUInt64 := by
            rw [rd_eq, hp2, ← hr2]; simp [List.getD_eq_getElem?_getD]
          simp only [e2] at h
          have h45 := head_getD r.tail 45 (by decide)
          have h33 := head_getD r.tail 33 (by decide)
          have nlit : ∀ (a k : UInt8), a ≠ k → ¬ a.toUInt64 = k.toUInt64 := fun a k hk e =>
            hk ((u64_lit a k).1 (by simp [e]))
          have l45 : (45 : UInt64) = (45 : UInt8).toUInt64 := rfl
          have l33 : (33 : UInt64) = (33 : UInt8).toUInt64 := rfl
          by_cases d45 : r.tail.getD 0 0 = 45
          · have y45 : (r.tail.getD 0 0).toUInt64 = 45 := by rw [d45]; rfl
            simp only [y45, if_true] at h
            have dc : r.tail.head? = some 45 := h45.2 d45
            have hc : (r.tail.head? == some 45 || r.tail.head? == some 33) = true := by simp [dc]
            split at h
            · exact absurd (by simpa [bnew] using h.symm) ht
            rename_i hne
            split at h
            · exact absurd (by simpa [bnew] using h.symm) ht
            rename_i hne2
            obtain ⟨a2, r2, hrt⟩ : ∃ a2 r2, r.tail = a2 :: r2 := by
              cases hrt : r.tail with
              | nil => simp [hrt] at dc
              | cons a2 r2 => exact ⟨_, _, rfl⟩
            have hlx := congrArg List.length hr2; rw [hrt] at hlx; simp at hlx
            have hp3 : (p + 3).toNat = p.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
            have hr3 : x.drop (p.toNat + 3) = r.tail.tail := by
              rw [show p.toNat + 3 = p.toNat + 2 + 1 by omega, ← List.tail_drop, hr2]
            obtain ⟨q1, q2⟩ := s15_sound _ x (p + 3) hx (by omega) hne
            obtain ⟨w1, w2⟩ := s11_sound _ x _ 0 hx q1 (by simp) hne2
            have hd := q2 r.length (by rw [hp3]; omega)
            rw [hp3, hr3] at hd
            split at h
            · rename_i hs17
              have hdn := s17_sound x _ 2 hx w1 (by simpa using hs17)
              simp at hdn
              obtain ⟨t', hL, ht'⟩ := s9_sound n x _ o t hx w1 h ht
              refine ⟨[] ++ t', Lexes.cons (by rw [hst, if_pos hc, hd]; simp at w2; simp [w2, dc, hdn]) hL, by simpa using ht'⟩
            · exact absurd (by simpa [bnew] using h.symm) ht
          by_cases d33 : r.tail.getD 0 0 = 33
          · have y33 : (r.tail.getD 0 0).toUInt64 = 33 := by rw [d33]; rfl
            simp (config := {decide := true}) only [y33, if_true, if_false] at h
            have dc : r.tail.head? = some 33 := h33.2 d33
            have hc : (r.tail.head? == some 45 || r.tail.head? == some 33) = true := by simp [dc]
            split at h
            · exact absurd (by simpa [bnew] using h.symm) ht
            rename_i hne
            split at h
            · exact absurd (by simpa [bnew] using h.symm) ht
            rename_i hne2
            obtain ⟨a2, r2, hrt⟩ : ∃ a2 r2, r.tail = a2 :: r2 := by
              cases hrt : r.tail with
              | nil => simp [hrt] at dc
              | cons a2 r2 => exact ⟨_, _, rfl⟩
            have hlx := congrArg List.length hr2; rw [hrt] at hlx; simp at hlx
            have hp3 : (p + 3).toNat = p.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
            have hr3 : x.drop (p.toNat + 3) = r.tail.tail := by
              rw [show p.toNat + 3 = p.toNat + 2 + 1 by omega, ← List.tail_drop, hr2]
            obtain ⟨q1, q2⟩ := s15_sound _ x (p + 3) hx (by omega) hne
            obtain ⟨w1, w2⟩ := s11_sound _ x _ 0 hx q1 (by simp) hne2
            have hd := q2 r.length (by rw [hp3]; omega)
            rw [hp3, hr3] at hd
            split at h
            · rename_i hs24
              have hcn := s24_sound x _ hx w1 (by simpa using hs24)
              obtain ⟨t', hL, ht'⟩ := s9_sound n x _ o t hx w1 h ht
              refine ⟨[] ++ t', Lexes.cons (by rw [hst, if_pos hc, hd]; simp at w2; simp [w2, dc, hcn]) hL, by simpa using ht'⟩
            · exact absurd (by simpa [bnew] using h.symm) ht
          have n45 : ¬ (r.tail.getD 0 0).toUInt64 = 45 := by rw [l45]; exact nlit _ _ d45
          have n33 : ¬ (r.tail.getD 0 0).toUInt64 = 33 := by rw [l33]; exact nlit _ _ d33
          simp only [n45, n33, if_false] at h
          have hc : ¬ (r.tail.head? == some 45 || r.tail.head? == some 33) = true := by
            simp only [Bool.or_eq_true, beq_iff_eq, not_or]; exact ⟨fun e => d45 (h45.1 e), fun e => d33 (h33.1 e)⟩
          split at h
          · exact absurd (by simpa [bnew] using h.symm) ht
          split at h
          · exact absurd (by simpa [bnew] using h.symm) ht
          rename_i hne
          have hl3 : p.toNat + 3 ≤ x.length := by
            refine Decidable.byContradiction fun hc3 => ?_
            have hn : ¬ (p + 3 < len x) := by rw [lt_len hx, UInt64.toNat_add]; simp; omega
            exact hne (by generalize len' x = m; cases m <;> simp [s11, hn])
          have hp3 : (p + 3).toNat = p.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
          have hr3 : x.drop (p.toNat + 3) = r.tail.tail := by
            rw [show p.toNat + 3 = p.toNat + 2 + 1 by omega, ← List.tail_drop, hr2]
          obtain ⟨hq1, hq2⟩ := s11_sound _ x (p + 3) 0 hx (by omega) (by simp) hne
          rw [hp3, hr3] at hq2
          obtain ⟨t', hL, ht'⟩ := s9_sound n x _ o t hx hq1 h ht
          have nd : (r.tail.head? == some 45) = false := by simpa using fun e => d45 (h45.1 e)
          have nd3 : (r.tail.head? == some 33) = false := by simpa using fun e => d33 (h33.1 e)
          refine ⟨[] ++ t', Lexes.cons (by
            rw [hst, if_neg hc]; simp at hq2
            simp only [hq2, Option.bind_some, nd, nd3, Bool.false_and, Bool.false_eq_true, if_false]) hL, by simpa using ht'⟩
        · simp [s23, hk96] at h
          obtain ⟨hp2, hp2l, hr2⟩ := two 91 hr0
          split at h
          · exact absurd (by simpa [bnew] using h.symm) ht
          rename_i hne
          split at h
          · rename_i hs17
            obtain ⟨hq1, hq2⟩ := s14_sound _ x (p + 2) 0 0 hx (by omega) (by omega) (by simp) (.inl rfl) hne
            have hdn := s17_sound x _ 1 hx hq1 (by simpa using hs17)
            simp at hdn
            rw [hp2, hr2] at hq2
            simp [nameAt] at hq2
            obtain ⟨t', hL, ht'⟩ := s9_sound n x _ o t hx hq1 h ht
            exact ⟨[] ++ t', Lexes.cons (by rw [hst, hq2]; simp [hdn]) hL, by simpa using ht'⟩
          · exact absurd (by simpa [bnew] using h.symm) ht
        · obtain ⟨h0, h5, h14, h90, h91, h256⟩ := op_props e he
          obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := op_props2 e he
          simp [s23, hke, h0, h5, h14, h90, h91, g1, g2, g3, g4, g5, g6, g7] at h
          rw [s5_op e he x p] at h
          have hpre' := (List.isPrefixOf_iff_prefix.1 hpre).length_le
          have hlen3 := op_len e he
          have hlenc : (c :: r).length = x.length - p.toNat := by rw [← hdp]; simp
          have hq : (p + e.1.length.toUInt64).toNat = p.toNat + e.1.length := by
            simp [UInt64.toNat_add]; omega
          obtain ⟨t', hL, ht'⟩ := s9_sound n x _ _ t hx (by rw [hq]; omega) h ht
          rw [hq, hr] at hL
          refine ⟨[e.2] ++ t', Lexes.cons hst hL, ?_⟩
          rw [ht', q0_eq, (and255'.1 e he)]; simp
        · simp [s23, hk5] at h
          obtain ⟨wb1, wb2, wb3, wb4⟩ := word_end x p hx c r hdp
          rw [s5_word x p 5 (Or.inl rfl)] at h
          generalize hed : s1 (len' x) x p = ee at *
          have hm : p.toNat ≤ ee.toNat := by omega
          have hv := s6_eq (len' x) x p ee 0 hx wb2 hm (by unfold len'; omega) (by rw [wb4]; exact hall)
          rw [wb4] at hv
          obtain ⟨t', hL, ht'⟩ := s9_sound n x ee _ t hx wb2 h ht
          rw [wb3] at hL
          refine ⟨(5 :: le8 (numVal ((c :: r).takeWhile isW))) ++ t', Lexes.cons hst hL, ?_⟩
          rw [ht', s8_eq, q0_eq]
          have hnv : (s6 (len' x) x p ee 0).toNat = numVal ((c :: r).takeWhile isW) := by rw [hv]; simp [numVal]
          have h5' : (5 : UInt64) &&& 255 = 5 := by decide
          rw [hnv, h5']; simp
        · simp [s23, hk0] at h; exact absurd h.symm ht
        · obtain ⟨h0, h5, h14, h90, h91, h256⟩ := kw_props e he
          obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := kw_props2 e he
          simp [s23, hke, h0, h5, h14, h90, h91, g1, g2, g3, g4, g5, g6, g7] at h
          obtain ⟨wb1, wb2, wb3, wb4⟩ := word_end x p hx c r hdp
          rw [s5_word x p e.2 (Or.inr (Or.inr ⟨e, he, rfl⟩))] at h
          generalize hed : s1 (len' x) x p = ee at *
          obtain ⟨t', hL, ht'⟩ := s9_sound n x ee _ t hx wb2 h ht
          rw [wb3] at hL
          refine ⟨[e.2] ++ t', Lexes.cons hst hL, ?_⟩
          rw [ht', q0_eq, (and255'.2 e he)]; simp
        · simp [s23, hk14] at h
          obtain ⟨wb1, wb2, wb3, wb4⟩ := word_end x p hx c r hdp
          rw [s5_word x p 14 (Or.inr (Or.inl rfl))] at h
          generalize hed : s1 (len' x) x p = ee at *
          have hm : p.toNat ≤ ee.toNat := by omega
          have hv := s7_eq (len' x) x p ee (q0 o 14) hx wb2 hm (by unfold len'; omega)
          rw [wb4] at hv
          rw [hv] at h
          obtain ⟨t', hL, ht'⟩ := s9_sound n x ee _ t hx wb2 h ht
          rw [wb3] at hL
          refine ⟨(14 :: (((c :: r).takeWhile isW).flatMap fun b => [1, b.toUInt64]) ++ [0]) ++ t', Lexes.cons hst hL, ?_⟩
          rw [ht', q0_eq]
          have h14' : (14 : UInt64) &&& 255 = 14 := by decide
          rw [h14']; simp
        · simp [s23, hk92] at h
          obtain ⟨wb1, wb2, wb3, wb4⟩ := word_end x p hx c r hdp
          rw [show s5 x p 92 = s1 (len' x) x p by simp [s5]] at h
          generalize hq : s1 (len' x) x p = q at *
          generalize ha : s13 (len' x) x q = a at h
          generalize hb : s1 (len' x) x a = b at h
          generalize he : s13 (len' x) x b = e at h
          split at h
          · rename_i h22
            obtain ⟨z1, z2, z3, z4⟩ := s22_sound x q a b e 92 0 hx wb2 ha.symm hb.symm he.symm (by decide) (by simpa using h22)
            rw [wb3] at z4
            rw [z4] at hst
            simp only [Option.map_some] at hst
            split at h
            · rename_i hab
              have hab' : a = b := by simpa using hab
              obtain ⟨t', hL, ht'⟩ := s9_sound n x e _ t hx z3 h ht
              refine ⟨scopeTok true ((x.drop a.toNat).take (b.toNat - a.toNat)) ++ t', Lexes.cons hst hL, ?_⟩
              rw [ht', q0_eq]; subst hab'; simp (config := {decide := true}) [scopeTok]
            · rename_i hab
              have hab' : a ≠ b := by simpa using hab
              have hlt : a.toNat < b.toNat := by
                have : a.toNat ≠ b.toNat := fun e0 => hab' (UInt64.toNat.inj e0)
                omega
              have hne : (x.drop a.toNat).take (b.toNat - a.toNat) ≠ [] := by
                intro e0; have := congrArg List.length e0; simp at this; omega
              have hv := s7_eq (len' x) x a b (q0 (q0 o 48) 14) hx z2 z1 (by unfold len'; omega)
              rw [hv] at h
              obtain ⟨t', hL, ht'⟩ := s9_sound n x e _ t hx z3 h ht
              refine ⟨scopeTok true ((x.drop a.toNat).take (b.toNat - a.toNat)) ++ t', Lexes.cons hst hL, ?_⟩
              rw [ht', q0_eq, q0_eq]; simp (config := {decide := true}) [scopeTok, hne]
          · exact absurd (by simpa [bnew] using h.symm) ht
        · simp [s23, hk98] at h
          obtain ⟨wb1, wb2, wb3, wb4⟩ := word_end x p hx c r hdp
          rw [show s5 x p 98 = s1 (len' x) x p by simp [s5]] at h
          generalize hq : s1 (len' x) x p = q at *
          generalize ha : s13 (len' x) x q = a at h
          generalize hb : s1 (len' x) x a = b at h
          generalize he : s13 (len' x) x b = e at h
          split at h
          · rename_i h22
            obtain ⟨z1, z2, z3, z4⟩ := s22_sound x q a b e 98 1 hx wb2 ha.symm hb.symm he.symm (by decide) (by simpa using h22)
            rw [wb3] at z4
            rw [z4] at hst
            simp only [Option.map_some] at hst
            split at h
            · rename_i hab
              have hab' : a = b := by simpa using hab
              obtain ⟨t', hL, ht'⟩ := s9_sound n x e _ t hx z3 h ht
              refine ⟨scopeTok true ((x.drop a.toNat).take (b.toNat - a.toNat)) ++ t', Lexes.cons hst hL, ?_⟩
              rw [ht', q0_eq]; subst hab'; simp (config := {decide := true}) [scopeTok]
            · rename_i hab
              have hab' : a ≠ b := by simpa using hab
              have hlt : a.toNat < b.toNat := by
                have : a.toNat ≠ b.toNat := fun e0 => hab' (UInt64.toNat.inj e0)
                omega
              have hne : (x.drop a.toNat).take (b.toNat - a.toNat) ≠ [] := by
                intro e0; have := congrArg List.length e0; simp at this; omega
              have hv := s7_eq (len' x) x a b (q0 (q0 o 48) 14) hx z2 z1 (by unfold len'; omega)
              rw [hv] at h
              obtain ⟨t', hL, ht'⟩ := s9_sound n x e _ t hx z3 h ht
              refine ⟨scopeTok true ((x.drop a.toNat).take (b.toNat - a.toNat)) ++ t', Lexes.cons hst hL, ?_⟩
              rw [ht', q0_eq, q0_eq]; simp (config := {decide := true}) [scopeTok, hne]
          · exact absurd (by simpa [bnew] using h.symm) ht
        · simp [s23, hk97] at h
          obtain ⟨wb1, wb2, wb3, wb4⟩ := word_end x p hx c r hdp
          rw [show s5 x p 97 = s1 (len' x) x p by simp [s5]] at h
          generalize hq : s1 (len' x) x p = q at *
          generalize ha : s13 (len' x) x q = a at h
          generalize hb : s1 (len' x) x a = b at h
          generalize he : s13 (len' x) x b = e at h
          split at h
          · rename_i h22
            obtain ⟨z1, z2, z3, z4⟩ := s22_sound x q a b e 97 2 hx wb2 ha.symm hb.symm he.symm (by decide) (by simpa using h22)
            rw [wb3] at z4
            rw [z4] at hst
            simp only [Option.map_some] at hst
            split at h
            · rename_i hab
              have hab' : a = b := by simpa using hab
              obtain ⟨t', hL, ht'⟩ := s9_sound n x e _ t hx z3 h ht
              refine ⟨scopeTok false ((x.drop a.toNat).take (b.toNat - a.toNat)) ++ t', Lexes.cons hst hL, ?_⟩
              rw [ht', q0_eq]; subst hab'; simp (config := {decide := true}) [scopeTok]
            · rename_i hab
              have hab' : a ≠ b := by simpa using hab
              have hlt : a.toNat < b.toNat := by
                have : a.toNat ≠ b.toNat := fun e0 => hab' (UInt64.toNat.inj e0)
                omega
              have hne : (x.drop a.toNat).take (b.toNat - a.toNat) ≠ [] := by
                intro e0; have := congrArg List.length e0; simp at this; omega
              have hv := s7_eq (len' x) x a b (q0 (q0 o 49) 14) hx z2 z1 (by unfold len'; omega)
              rw [hv] at h
              obtain ⟨t', hL, ht'⟩ := s9_sound n x e _ t hx z3 h ht
              refine ⟨scopeTok false ((x.drop a.toNat).take (b.toNat - a.toNat)) ++ t', Lexes.cons hst hL, ?_⟩
              rw [ht', q0_eq, q0_eq]; simp (config := {decide := true}) [scopeTok, hne]
          · exact absurd (by simpa [bnew] using h.symm) ht
        · simp [s23, hk93] at h
          obtain ⟨wb1, wb2, wb3, wb4⟩ := word_end x p hx c r hdp
          rw [s5_93] at h
          split at h
          · rename_i hs17
            have hdn := s17_sound x _ 0 hx wb2 (by simpa using hs17)
            simp at hdn
            rw [wb3] at hdn
            obtain ⟨t', hL, ht'⟩ := s9_sound n x _ o t hx wb2 h ht
            rw [wb3] at hL
            exact ⟨[] ++ t', Lexes.cons (by rw [hst, if_pos hdn]) hL, by simpa using ht'⟩
          · exact absurd (by simpa [bnew] using h.symm) ht

/-- Lexer soundness: if `C.s10` returns a nonempty buffer, the input lexes to exactly that buffer
(`Lexes` = Nano/Lexer/Lex2Spec.lean; inputs under 2^32 bytes). -/
theorem s10_sound (x : List UInt8) (hx : x.length < 2 ^ 32) (t : Buf) (h : s10 x = t) (ht : t ≠ []) :
    Lexes x t := by
  obtain ⟨t', hL, e⟩ := s9_sound 16777216 x 0 bnew t hx (by simp) h ht
  simpa [bnew, e] using hL

/-- sanity (non-vacuity of the spec): `def x` lexes to `1, 14 (1,'x') 0`. -/
example : Lexes [100, 101, 102, 32, 120] [1, 14, 1, 120, 0] :=
  Lexes.cons (e := [1]) (r := [32, 120]) (by decide)
    (Lexes.cons (e := []) (r := [120]) (by decide)
      (Lexes.cons (e := [14, 1, 120, 0]) (r := []) (by decide) Lexes.nil))

end LexSpec
