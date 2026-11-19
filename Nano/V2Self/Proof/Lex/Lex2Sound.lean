import Nano.V2Self.C.Lex2
import Nano.V2Self.Proof.Lex.Lex2Spec
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

/-- s3 with its reads made parameters (definitionally the same body) -/
def s3' (d c c1 c2 c3 c4 c5 : UInt64) : UInt64 :=
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
  r19

theorem s3_eq_s3' (x : List UInt8) (p e : UInt64) :
    s3 x p e = s3' (e - p) (rd x p) (rd x (p + 1)) (rd x (p + 2)) (rd x (p + 3)) (rd x (p + 4)) (rd x (p + 5)) := rfl

theorem nest {α : Type} (p q : Prop) [Decidable p] [Decidable q] (x y : α) :
    (if p then (if q then x else y) else y) = (if p ∧ q then x else y) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

set_option maxHeartbeats 1000000 in
theorem s3'_eq (w : List UInt8) (c0 c1 c2 c3 c4 c5 : UInt64) (hl : w.length < 2 ^ 32)
    (h : ∀ j, j < 6 → j < w.length → [c0, c1, c2, c3, c4, c5].getD j 0 = (w.getD j 0).toUInt64) :
    s3' w.length.toUInt64 c0 c1 c2 c3 c4 c5 = (kwTable.lookup w).getD 14 := by
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, r⟩⟩⟩⟩⟩⟩⟩
  · simp (config := {zeta := false}) only [s3', nest]
    try simp [kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    simp at h0
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s3', nest]
    try simp [kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    simp at h0 h1
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s3', nest]
    try simp [kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    simp at h0 h1 h2
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s3', nest]
    try simp [kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    simp at h0 h1 h2 h3
    subst_vars
    clear h
    simp (config := {zeta := false}) only [s3', nest]
    try simp [kwTable, tu2, List.lookup]
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
    try simp [kwTable, tu2, List.lookup]
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
    try simp [kwTable, tu2, List.lookup]
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
    have hd : (a :: b :: c :: d :: e :: f :: g :: r).length = r.length + 7 := by simp
    obtain ⟨N, hN⟩ : ∃ N, N = r.length + 7 := ⟨_, rfl⟩
    rw [hd, ← hN]
    rw [hd] at hl
    have hl' : N < 2 ^ 32 := by omega
    have n2 : N.toUInt64 ≠ 2 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have n3 : N.toUInt64 ≠ 3 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have n4 : N.toUInt64 ≠ 4 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have n5 : N.toUInt64 ≠ 5 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have n6 : N.toUInt64 ≠ 6 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    simp [kwTable, List.lookup, n2, n3, n4, n5, n6]

theorem rd_seg (x : List UInt8) (p q : UInt64) (m j : Nat) (hj : j < m) (hq : q.toNat = p.toNat + j) :
    rd x q = (((x.drop p.toNat).take m).getD j 0).toUInt64 := by
  rw [rd_eq, hq]
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, hj, Nat.add_comm]

theorem s3_eq (x : List UInt8) (p e : UInt64) (hx : x.length < 2 ^ 32) (he : e.toNat ≤ x.length) (hp : p.toNat ≤ e.toNat) :
    s3 x p e = (kwTable.lookup ((x.drop p.toNat).take (e.toNat - p.toNat))).getD 14 := by
  rw [s3_eq_s3']
  have hw : ((x.drop p.toNat).take (e.toNat - p.toNat)).length = e.toNat - p.toNat := by simp; omega
  have hd : e - p = ((x.drop p.toNat).take (e.toNat - p.toNat)).length.toUInt64 := by
    apply UInt64.toNat.inj; rw [hw]; simp [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 hp)]
    omega
  rw [hd]
  apply s3'_eq _ _ _ _ _ _ _ (by rw [hw]; omega)
  intro j hj hjw
  rw [hw] at hjw
  have hrd : ∀ q : UInt64, q.toNat = p.toNat + j → rd x q = _ := fun q hq => rd_seg x p q _ j hjw hq
  obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  · simp; exact hrd p (by omega)
  · simp; exact hrd (p + 1) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 2) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 3) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 4) (by simp [UInt64.toNat_add]; omega)
  · simp; exact hrd (p + 5) (by simp [UInt64.toNat_add]; omega)

/-! ### the token kind (s4) -/

/-- s4 with its reads/inner calls made parameters (definitionally the same body) -/
def s4' (c d f A B : UInt64) : UInt64 :=
    if c == 32 then 90
    else if c == 10 then 90
    else if c == 40 then 6
    else if c == 41 then 7
    else if c == 43 then 10
    else if c == 45 then 11
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
      if c = 32 ∨ c = 10 then 90 else
      match opTable.find? (fun e => e.1.isPrefixOf [c, d, f]) with
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
  · subst h45; simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm]
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
  simp [s4', opTable, List.find?, List.isPrefixOf, tu2, bcomm, b32, b10, b40, b41, b43, b45, b42, b59, b44, b91, b93, b58, b61, b38, b124, b60, b62, b195, b226, h32, h10, h40, h41, h43, h45, h42, h59, h44, h91, h93, h58, h61, h38, h124, h60, h62, h195, h226]
  exact tailc c A B

/-! ### s4 = spec kind -/

def kind (l : List UInt8) : UInt64 :=
  match l with
  | [] => 91
  | c :: r =>
    if c = 32 ∨ c = 10 then 90 else
    match opTable.find? (fun e => e.1.isPrefixOf (c :: r)) with
    | some (_, t) => t
    | none =>
      if isD c then (if ((c :: r).takeWhile isW).all isD then 5 else 0)
      else if isW c then (kwTable.lookup ((c :: r).takeWhile isW)).getD 14 else 0

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

theorem kind_spec (c : UInt8) (r : List UInt8) :
    (kind (c :: r) = 90 ∧ step (c :: r) = some ([], r)) ∨
    (∃ e ∈ opTable, kind (c :: r) = e.2 ∧ step (c :: r) = some ([e.2], (c :: r).drop e.1.length) ∧
        e.1.isPrefixOf (c :: r) = true) ∨
    (kind (c :: r) = 5 ∧ ((c :: r).takeWhile isW).all isD = true ∧ step (c :: r) = some (5 :: le8 (numVal ((c :: r).takeWhile isW)), (c :: r).dropWhile isW)) ∨
    kind (c :: r) = 0 ∨
    (∃ e ∈ kwTable, kind (c :: r) = e.2 ∧ step (c :: r) = some ([e.2], (c :: r).dropWhile isW)) ∨
    (kind (c :: r) = 14 ∧ step (c :: r) = some (14 :: (((c :: r).takeWhile isW).flatMap fun b => [1, b.toUInt64]) ++ [0],
      (c :: r).dropWhile isW)) := by
  unfold kind step
  by_cases hws : c = 32 ∨ c = 10
  · have : (c == 32 || c == 10) = true := by simpa using hws
    simp [hws, this]
  · have : ¬ (c == 32 || c == 10) = true := by simpa using hws
    simp only [hws, this, if_false, Bool.false_eq_true]
    rcases hf : opTable.find? (fun e => e.1.isPrefixOf (c :: r)) with _ | ⟨s, t⟩
    · simp only [hf]
      by_cases hd : isD c = true
      · by_cases ha : ((c :: r).takeWhile isW).all isD = true
        · simp [hd, ha]
        · simp [hd, ha]
      · by_cases hw : isW c = true
        · simp only [hd, hw, if_true, if_false]
          rcases hl : kwTable.lookup ((c :: r).takeWhile isW) with _ | k
          · simp [hl]
          · obtain ⟨e, he, rfl⟩ := lookup_mem _ _ _ hl
            simp only [hl, Bool.false_eq_true, if_false, Option.getD_some]
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, rfl, rfl⟩))))
        · simp [hd, hw]
    · have hmem := List.mem_of_find?_eq_some hf
      have hpre := List.find?_some hf
      simp only [hf]
      right; left
      exact ⟨(s, t), hmem, rfl, rfl, by simpa using hpre⟩

theorem dw_eq (l : List UInt8) : l.dropWhile isW = l.drop (l.takeWhile isW).length := by
  have h := List.takeWhile_append_dropWhile (p := isW) (l := l)
  calc l.dropWhile isW = ((l.takeWhile isW) ++ (l.dropWhile isW)).drop (l.takeWhile isW).length := (List.drop_left' rfl).symm
    _ = _ := by rw [h]

theorem and255' : (∀ e ∈ opTable, e.2 &&& 255 = e.2) ∧ (∀ e ∈ kwTable, e.2 &&& 255 = e.2) := by decide

theorem drop_drop' (x : List UInt8) (a b : Nat) : (x.drop a).drop b = x.drop (a + b) := by
  simp [List.drop_drop]

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
  · rw [he, dw_eq, ← hdp, drop_drop']
  · rw [hdp, he, Nat.add_sub_cancel_left]; exact take_takeWhile _

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
        have hr : ∀ m, x.drop (p.toNat + m) = (c :: r).drop m := fun m => by rw [← hdp, drop_drop']
        rcases kind_spec c r with ⟨hk90, hst⟩ | ⟨e, he, hke, hst, hpre⟩ | ⟨hk5, hall, hst⟩ | hk0 | ⟨e, he, hke, hst⟩ | ⟨hk14, hst⟩
        · simp [hk90] at h
          have hp1 := inc_toNat (p := p) (n := x.length) hl hx
          obtain ⟨t', hL, ht'⟩ := s9_sound n x (p + 1) o t hx (by omega) h ht
          rw [hp1, hr 1] at hL
          exact ⟨[] ++ t', Lexes.cons hst (by simpa using hL), by simpa using ht'⟩
        · obtain ⟨h0, h5, h14, h90, h91, h256⟩ := op_props e he
          simp [hke, h0, h5, h14, h90, h91] at h
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
        · simp [hk5] at h
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
        · simp [hk0] at h; exact absurd h.symm ht
        · obtain ⟨h0, h5, h14, h90, h91, h256⟩ := kw_props e he
          simp [hke, h0, h5, h14, h90, h91] at h
          obtain ⟨wb1, wb2, wb3, wb4⟩ := word_end x p hx c r hdp
          rw [s5_word x p e.2 (Or.inr (Or.inr ⟨e, he, rfl⟩))] at h
          generalize hed : s1 (len' x) x p = ee at *
          obtain ⟨t', hL, ht'⟩ := s9_sound n x ee _ t hx wb2 h ht
          rw [wb3] at hL
          refine ⟨[e.2] ++ t', Lexes.cons hst hL, ?_⟩
          rw [ht', q0_eq, (and255'.2 e he)]; simp
        · simp [hk14] at h
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

/-- Lexer soundness: if `C.s10` returns a nonempty buffer, the input lexes to exactly that buffer
(`Lexes` = Nano/V2Self/Proof/Lex/Lex2Spec.lean; inputs under 2^32 bytes). -/
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
