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
  let r1 := if d == 4 && c == 101 && c1 == 108 && c2 == 115 && c3 == 101 then 34 else r0;
  let r2 := if d == 4 && c == 116 && c1 == 104 && c2 == 101 && c3 == 110 then 33 else r1;
  let r3 := if d == 2 && c == 105 && c1 == 102 then 32 else r2;
  let r4 := if d == 3 && c == 108 && c1 == 101 && c2 == 116 then 2 else r3;
  let r5 := if d == 3 && c == 100 && c1 == 101 && c2 == 102 then 1 else r4;
  let r6 := if d == 4 && c == 76 && c1 == 105 && c2 == 115 && c3 == 116 then 37 else r5;
  let r7 := if d == 3 && c == 66 && c1 == 117 && c2 == 102 then 36 else r6;
  let r8 := if d == 3 && c == 78 && c1 == 97 && c2 == 116 then 35 else r7;
  let r10 := if d == 5 && c == 85 && c1 == 73 && c2 == 110 && c3 == 116 && c4 == 56 then 38 else r8;
  let r11 := if d == 6 && c == 85 && c1 == 73 && c2 == 110 && c3 == 116 && c4 == 54 && c5 == 52 then 3 else r10;
  let r12 := if d == 2 && c == 114 && c1 == 100 then 40 else r11;
  let r13 := if d == 3 && c == 108 && c1 == 101 && c2 == 110 then 41 else r12;
  let r14 := if d == 4 && c == 108 && c1 == 101 && c2 == 110 && c3 == 39 then 39 else r13;
  let r15 := if d == 3 && c == 112 && c1 == 117 && c2 == 116 then 42 else r14;
  let r16 := if d == 4 && c == 98 && c1 == 110 && c2 == 101 && c3 == 119 then 43 else r15;
  let r17 := if d == 5 && c == 98 && c1 == 115 && c2 == 105 && c3 == 122 && c4 == 101 then 44 else r16;
  let r18 := if d == 4 && c == 98 && c1 == 103 && c2 == 101 && c3 == 116 then 45 else r17;
  let r19 := if d == 4 && c == 98 && c1 == 115 && c2 == 101 && c3 == 116 then 46 else r18;
  if d == 5 && c == 98 && c1 == 112 && c2 == 117 && c3 == 115 && c4 == 104 then 47 else r19

theorem s3_eq_s3' (x : List UInt8) (p e : UInt64) :
    s3 x p e = s3' (e - p) (rd x p) (rd x (p + 1)) (rd x (p + 2)) (rd x (p + 3)) (rd x (p + 4)) (rd x (p + 5)) := rfl

theorem s3'_eq (w : List UInt8) (c0 c1 c2 c3 c4 c5 : UInt64) (hl : w.length < 2 ^ 32)
    (h : ∀ j, j < 6 → j < w.length → [c0, c1, c2, c3, c4, c5].getD j 0 = (w.getD j 0).toUInt64) :
    s3' w.length.toUInt64 c0 c1 c2 c3 c4 c5 = (kwTable.lookup w).getD 14 := by
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, r⟩⟩⟩⟩⟩⟩⟩
  · try simp [s3', kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    simp at h0
    subst_vars
    try simp [s3', kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    simp at h0 h1
    subst_vars
    try simp [s3', kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    simp at h0 h1 h2
    subst_vars
    try simp [s3', kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    simp at h0 h1 h2 h3
    subst_vars
    try simp [s3', kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4
    subst_vars
    try simp [s3', kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    have h5 := h 5 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4 h5
    subst_vars
    try simp [s3', kwTable, tu2, List.lookup]
    try ((repeat' split) <;> simp_all)
  · have h0 := h 0 (by decide) (by simp)
    have h1 := h 1 (by decide) (by simp)
    have h2 := h 2 (by decide) (by simp)
    have h3 := h 3 (by decide) (by simp)
    have h4 := h 4 (by decide) (by simp)
    have h5 := h 5 (by decide) (by simp)
    simp at h0 h1 h2 h3 h4 h5
    subst_vars
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
    simp [s3', kwTable, List.lookup, n2, n3, n4, n5, n6]

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
    else if 48 ≤ c && c ≤ 57 then if A == 1 then 5 else 0
    else if s0 c == 1 then B
    else 0

theorem bcomm (a b : UInt8) : (a == b) = (b == a) := by
  cases h : a == b <;> cases h2 : b == a <;> simp_all (config := {decide := true}) [isD, isW]

theorem isD_iff (c : UInt8) : (48 ≤ c.toUInt64 ∧ c.toUInt64 ≤ 57) ↔ isD c = true := by
  rw [← isD_eq]; simp

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
  simp [s4', opTable, List.find?, List.isPrefixOf, tu2, isD_iff, s0_eq, bcomm, isD, isW, b32, b10, b40, b41, b43, b45, b42, b59, b44, b91, b93, b58, b61, b38, b124, b60, b62, b195, b226, h32, h10, h40, h41, h43, h45, h42, h59, h44, h91, h93, h58, h61, h38, h124, h60, h62, h195, h226]
