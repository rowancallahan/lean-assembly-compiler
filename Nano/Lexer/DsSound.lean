/- Nano/Lexer/DsSound: the match desugaring stage `C.t10` (Nano/Lexer/Dsg.lean) meets its specification
`DsSpec.ds` (Nano/Lexer/DsSpec.lean): `t10_sound : C.t10 t ≠ [] → DsSpec.ds t = some (C.t10 t)`. -/
import Nano.Lexer.Dsg
import Nano.Lexer.DsSpec
namespace DsSpec
open C

/-! ### buffers below 2^24 words -/

theorem bsize_toNat {t : Buf} (h : t.length < 16777216) : (bsize t).toNat = t.length := by
  simp [bsize]; omega

theorem lt_bsize {t : Buf} {p : UInt64} (h : t.length < 16777216) : p < bsize t ↔ p.toNat < t.length := by
  rw [UInt64.lt_iff_toNat_lt, bsize_toNat h]

theorem bget_eq (t : Buf) (p : UInt64) : bget t p = t.getD p.toNat 0 := rfl

theorem addU {p k : UInt64} (hp : p.toNat < 16777216) (hk : k.toNat < 16777216) : (p + k).toNat = p.toNat + k.toNat := by
  rw [UInt64.toNat_add]; omega

theorem add1 {p : UInt64} (hp : p.toNat < 16777216) : (p + 1).toNat = p.toNat + 1 := addU (k := 1) hp (by decide)
theorem add2 {p : UInt64} (hp : p.toNat < 16777216) : (p + 2).toNat = p.toNat + 2 := addU (k := 2) hp (by decide)
theorem add4 {p : UInt64} (hp : p.toNat < 16777216) : (p + 4).toNat = p.toNat + 4 := addU (k := 4) hp (by decide)
theorem add8 {p : UInt64} (hp : p.toNat < 16777216) : (p + 8).toNat = p.toNat + 8 := addU (k := 8) hp (by decide)
theorem add9 {p : UInt64} (hp : p.toNat < 16777216) : (p + 9).toNat = p.toNat + 9 := addU (k := 9) hp (by decide)
theorem add10 {p : UInt64} (hp : p.toNat < 16777216) : (p + 10).toNat = p.toNat + 10 := addU (k := 10) hp (by decide)
theorem add12 {p : UInt64} (hp : p.toNat < 16777216) : (p + 12).toNat = p.toNat + 12 := addU (k := 12) hp (by decide)

theorem drop_cons' {x : List UInt64} {n : Nat} (h : n < x.length) : x.drop n = x.getD n 0 :: x.drop (n + 1) := by
  rw [List.drop_eq_getElem_cons h]; simp [List.getD_eq_getElem?_getD, h]

theorem getD_none {x : List UInt64} {n : Nat} (h : x.length ≤ n) : x.getD n 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- the words `[i, e)` -/
def slice (t : Buf) (i e : Nat) : List UInt64 := (t.drop i).take (e - i)

theorem slice_app {t : Buf} {i e : Nat} (h1 : i ≤ e) (h2 : e ≤ t.length) : t.drop i = slice t i e ++ t.drop e := by
  unfold slice
  have : t.drop e = (t.drop i).drop (e - i) := by rw [List.drop_drop]; congr 1; omega
  rw [this, List.take_append_drop]

theorem slice_len {t : Buf} {i e : Nat} (h1 : i ≤ e) (h2 : e ≤ t.length) : (slice t i e).length = e - i := by
  unfold slice; simp; omega

/-! ### identifiers and tokens (t1, t0) -/

theorem t1_sound : ∀ (n : Nat) (t : Buf) (j : UInt64), t.length < 16777216 → j.toNat ≤ t.length → t1 n t j ≠ 0 →
    j.toNat < (t1 n t j).toNat ∧ (t1 n t j).toNat ≤ t.length ∧
    identTok (t.drop j.toNat) = some (slice t j.toNat (t1 n t j).toNat, t.drop (t1 n t j).toNat)
  | 0, t, j, _, _, h => by simp [t1] at h
  | n + 1, t, j, ht, hj, h => by
    have hlt : j < bsize t := by
      cases Decidable.em (j < bsize t) with
      | inl h' => exact h'
      | inr hc => simp only [t1, if_neg hc] at h; exact absurd rfl h
    have hl : j.toNat < t.length := (lt_bsize ht).1 hlt
    have hs : t1 (n + 1) t j = if bget t j == 0 then j + 1 else if bget t j == 1 then
        (if j + 1 < bsize t then t1 n t (j + 2) else 0) else 0 := by simp only [t1, if_pos hlt]
    rw [hs] at h ⊢
    rw [drop_cons' hl, bget_eq] at *
    by_cases h0 : t.getD j.toNat 0 = 0
    · simp only [h0, beq_self_eq_true, if_true]
      rw [add1 (by omega)]
      refine ⟨by omega, by omega, ?_⟩
      simp only [identTok, slice]
      rw [drop_cons' hl, h0]; simp
    · have h0' : (t.getD j.toNat 0 == 0) = false := by simpa using h0
      simp only [h0', Bool.false_eq_true, if_false] at h ⊢
      by_cases h1 : t.getD j.toNat 0 = 1
      · simp only [h1, beq_self_eq_true, if_true] at h ⊢
        by_cases hlt1 : j + 1 < bsize t
        · rw [if_pos hlt1] at h ⊢
          have hl1 : j.toNat + 1 < t.length := by rw [← add1 (by omega)]; exact (lt_bsize ht).1 hlt1
          have IH := t1_sound n t (j + 2) ht (by rw [add2 (by omega)]; omega) h
          rw [add2 (by omega)] at IH
          obtain ⟨a1, a2, a3⟩ := IH
          refine ⟨by omega, a2, ?_⟩
          rw [drop_cons' hl1]
          simp only [identTok]
          rw [show j.toNat + 1 + 1 = j.toNat + 2 by omega, a3]
          simp only [Option.map_some]
          congr 2
          unfold slice
          rw [drop_cons' hl, drop_cons' hl1, h1]
          rw [show (t1 n t (j + 2)).toNat - j.toNat = ((t1 n t (j + 2)).toNat - (j.toNat + 2)) + 1 + 1 by omega]
          simp [show j.toNat + 1 + 1 = j.toNat + 2 by omega]
        · rw [if_neg hlt1] at h; exact absurd rfl h
      · have h1' : (t.getD j.toNat 0 == 1) = false := by simpa using h1
        simp only [h1', Bool.false_eq_true, if_false] at h; exact absurd rfl h

theorem t0_sound (t : Buf) (i : UInt64) (ht : t.length < 16777216) (hi : i.toNat < t.length) (h : t0 t i ≠ 0) :
    i.toNat < (t0 t i).toNat ∧ (t0 t i).toNat ≤ t.length ∧
    splitTok (t.drop i.toNat) = some (slice t i.toNat (t0 t i).toNat, t.drop (t0 t i).toNat) := by
  have hd := drop_cons' hi
  unfold t0 at h ⊢
  rw [bget_eq] at h ⊢
  generalize hk : t.getD i.toNat 0 = k at hd h ⊢
  rw [hd]
  by_cases k5 : k = 5
  · subst k5
    simp only [beq_self_eq_true, if_true] at h ⊢
    by_cases h8 : i + 8 < bsize t
    · rw [if_pos h8]
      have h8' : i.toNat + 8 < t.length := by
        have := (lt_bsize ht).1 h8; rw [add8 (by omega)] at this; exact this
      have e9 : (i + 9).toNat = i.toNat + 9 := add9 (by omega)
      rw [e9]
      refine ⟨by omega, by omega, ?_⟩
      simp only [splitTok, if_true, List.length_drop]
      rw [if_pos (by omega)]
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · simp only [slice, show i.toNat + 9 - i.toNat = 8 + 1 by omega]
        rw [hd]; simp
      · rw [List.drop_drop]
    · rw [if_neg h8] at h; exact absurd rfl h
  · have k5' : (k == 5) = false := by simpa using k5
    simp only [k5', Bool.false_eq_true, if_false] at h ⊢
    by_cases k14 : k = 14
    · subst k14
      simp only [beq_self_eq_true, if_true] at h ⊢
      have hi1 := add1 (p := i) (by omega)
      obtain ⟨a1, a2, a3⟩ := t1_sound _ t (i + 1) ht (by omega) h
      rw [hi1] at a1 a3
      refine ⟨by omega, a2, ?_⟩
      simp only [splitTok, show ¬ ((14 : UInt64) = 5) by decide, if_false, if_true, a3, Option.map_some]
      congr 2
      simp only [slice]
      rw [hd, show (t1 16777216 t (i + 1)).toNat - i.toNat = ((t1 16777216 t (i + 1)).toNat - (i.toNat + 1)) + 1 by omega]
      simp
    · have k14' : (k == 14) = false := by simpa using k14
      simp only [k14', Bool.false_eq_true, if_false]
      rw [add1 (by omega)]
      refine ⟨by omega, by omega, ?_⟩
      simp only [splitTok, k5, k14, if_false]
      simp only [slice, show i.toNat + 1 - i.toNat = 1 by omega]
      rw [hd]; simp

/-! ### the word tests (t2 `match`, t3 `with`, t4 `_`) -/

/-- the `k` words from `i`, read one by one -/
theorem take_getD : ∀ (k : Nat) (t : Buf) (i : Nat), i + k ≤ t.length →
    (t.drop i).take k = (List.range k).map (fun j => t.getD (i + j) 0)
  | 0, t, i, _ => by simp
  | k + 1, t, i, h => by
    rw [drop_cons' (by omega), List.take_succ_cons, take_getD k t (i + 1) (by omega), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left; intro j _; simp [Function.comp, Nat.add_assoc, Nat.add_comm 1]

def ch12 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : UInt64) : UInt64 := if b0 == 14 then if b1 == 1 then if b2 == 109 then if b3 == 1 then if b4 == 97 then if b5 == 1 then if b6 == 116 then if b7 == 1 then if b8 == 99 then if b9 == 1 then if b10 == 104 then if b11 == 0 then 1 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0

theorem ch12_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : UInt64) : ch12 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 = if [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] = MATCH then 1 else 0 := by
  unfold ch12
  simp only [MATCH, List.cons.injEq, and_true]
  by_cases h0 : b0 = 14
  · subst h0
    by_cases h1 : b1 = 1
    · subst h1
      by_cases h2 : b2 = 109
      · subst h2
        by_cases h3 : b3 = 1
        · subst h3
          by_cases h4 : b4 = 97
          · subst h4
            by_cases h5 : b5 = 1
            · subst h5
              by_cases h6 : b6 = 116
              · subst h6
                by_cases h7 : b7 = 1
                · subst h7
                  by_cases h8 : b8 = 99
                  · subst h8
                    by_cases h9 : b9 = 1
                    · subst h9
                      by_cases h10 : b10 = 104
                      · subst h10
                        by_cases h11 : b11 = 0
                        · subst h11
                          simp
                        · simp [h11]
                      · simp [h10]
                    · simp [h9]
                  · simp [h8]
                · simp [h7]
              · simp [h6]
            · simp [h5]
          · simp [h4]
        · simp [h3]
      · simp [h2]
    · simp [h1]
  · simp [h0]
theorem t2_def (t : Buf) (i e : UInt64) : t2 t i e = if e == i + 12 then ch12 (bget t i) (bget t (i + 1)) (bget t (i + 2)) (bget t (i + 3)) (bget t (i + 4)) (bget t (i + 5)) (bget t (i + 6)) (bget t (i + 7)) (bget t (i + 8)) (bget t (i + 9)) (bget t (i + 10)) (bget t (i + 11)) else 0 := rfl

def ch10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : UInt64) : UInt64 := if b0 == 14 then if b1 == 1 then if b2 == 119 then if b3 == 1 then if b4 == 105 then if b5 == 1 then if b6 == 116 then if b7 == 1 then if b8 == 104 then if b9 == 0 then 1 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0

theorem ch10_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : UInt64) : ch10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = if [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] = WITH then 1 else 0 := by
  unfold ch10
  simp only [WITH, List.cons.injEq, and_true]
  by_cases h0 : b0 = 14
  · subst h0
    by_cases h1 : b1 = 1
    · subst h1
      by_cases h2 : b2 = 119
      · subst h2
        by_cases h3 : b3 = 1
        · subst h3
          by_cases h4 : b4 = 105
          · subst h4
            by_cases h5 : b5 = 1
            · subst h5
              by_cases h6 : b6 = 116
              · subst h6
                by_cases h7 : b7 = 1
                · subst h7
                  by_cases h8 : b8 = 104
                  · subst h8
                    by_cases h9 : b9 = 0
                    · subst h9
                      simp
                    · simp [h9]
                  · simp [h8]
                · simp [h7]
              · simp [h6]
            · simp [h5]
          · simp [h4]
        · simp [h3]
      · simp [h2]
    · simp [h1]
  · simp [h0]
theorem t3_def (t : Buf) (i e : UInt64) : t3 t i e = if e == i + 10 then ch10 (bget t i) (bget t (i + 1)) (bget t (i + 2)) (bget t (i + 3)) (bget t (i + 4)) (bget t (i + 5)) (bget t (i + 6)) (bget t (i + 7)) (bget t (i + 8)) (bget t (i + 9)) else 0 := rfl

def ch4 (b0 b1 b2 b3 : UInt64) : UInt64 := if b0 == 14 then if b1 == 1 then if b2 == 95 then if b3 == 0 then 1 else 0 else 0 else 0 else 0

theorem ch4_eq (b0 b1 b2 b3 : UInt64) : ch4 b0 b1 b2 b3 = if [b0, b1, b2, b3] = WILD then 1 else 0 := by
  unfold ch4
  simp only [WILD, List.cons.injEq, and_true]
  by_cases h0 : b0 = 14
  · subst h0
    by_cases h1 : b1 = 1
    · subst h1
      by_cases h2 : b2 = 95
      · subst h2
        by_cases h3 : b3 = 0
        · subst h3
          simp
        · simp [h3]
      · simp [h2]
    · simp [h1]
  · simp [h0]
theorem t4_def (t : Buf) (i e : UInt64) : t4 t i e = if e == i + 4 then ch4 (bget t i) (bget t (i + 1)) (bget t (i + 2)) (bget t (i + 3)) else 0 := rfl

theorem t2_eq (t : Buf) (i e : UInt64) (ht : t.length < 16777216) (hie : i.toNat < e.toNat) (he : e.toNat ≤ t.length) :
    t2 t i e = if slice t i.toNat e.toNat = MATCH then 1 else 0 := by
  rw [t2_def]
  by_cases h : e = i + 12
  · subst h
    have en : (i + 12).toNat = i.toNat + 12 := by rw [addU (k := 12) (by omega) (by decide)]; rfl
    simp only [beq_self_eq_true, if_true, ch12_eq]
    have r1 : bget t (i + 1) = t.getD (i.toNat + 1) 0 := by rw [bget_eq, addU (k := 1) (by omega) (by decide)]; rfl
    have r2 : bget t (i + 2) = t.getD (i.toNat + 2) 0 := by rw [bget_eq, addU (k := 2) (by omega) (by decide)]; rfl
    have r3 : bget t (i + 3) = t.getD (i.toNat + 3) 0 := by rw [bget_eq, addU (k := 3) (by omega) (by decide)]; rfl
    have r4 : bget t (i + 4) = t.getD (i.toNat + 4) 0 := by rw [bget_eq, addU (k := 4) (by omega) (by decide)]; rfl
    have r5 : bget t (i + 5) = t.getD (i.toNat + 5) 0 := by rw [bget_eq, addU (k := 5) (by omega) (by decide)]; rfl
    have r6 : bget t (i + 6) = t.getD (i.toNat + 6) 0 := by rw [bget_eq, addU (k := 6) (by omega) (by decide)]; rfl
    have r7 : bget t (i + 7) = t.getD (i.toNat + 7) 0 := by rw [bget_eq, addU (k := 7) (by omega) (by decide)]; rfl
    have r8 : bget t (i + 8) = t.getD (i.toNat + 8) 0 := by rw [bget_eq, addU (k := 8) (by omega) (by decide)]; rfl
    have r9 : bget t (i + 9) = t.getD (i.toNat + 9) 0 := by rw [bget_eq, addU (k := 9) (by omega) (by decide)]; rfl
    have r10 : bget t (i + 10) = t.getD (i.toNat + 10) 0 := by rw [bget_eq, addU (k := 10) (by omega) (by decide)]; rfl
    have r11 : bget t (i + 11) = t.getD (i.toNat + 11) 0 := by rw [bget_eq, addU (k := 11) (by omega) (by decide)]; rfl
    have hs : slice t i.toNat (i + 12).toNat = [t.getD i.toNat 0, t.getD (i.toNat + 1) 0, t.getD (i.toNat + 2) 0, t.getD (i.toNat + 3) 0, t.getD (i.toNat + 4) 0, t.getD (i.toNat + 5) 0, t.getD (i.toNat + 6) 0, t.getD (i.toNat + 7) 0, t.getD (i.toNat + 8) 0, t.getD (i.toNat + 9) 0, t.getD (i.toNat + 10) 0, t.getD (i.toNat + 11) 0] := by
      rw [en]; simp only [slice, show i.toNat + 12 - i.toNat = 12 by omega]
      rw [take_getD 12 t i.toNat (by rw [en] at he; exact he)]
      simp [List.range_succ]
    rw [hs, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, bget_eq]
  · have h' : (e == i + 12) = false := by simpa using h
    rw [if_neg (by simp [h'])]
    rw [if_neg]
    intro hs
    have := congrArg List.length hs
    rw [slice_len (by omega) he] at this
    simp [MATCH] at this
    apply h; apply UInt64.toNat_inj.1
    rw [addU (k := 12) (by omega) (by decide)]; simp; omega

theorem t3_eq (t : Buf) (i e : UInt64) (ht : t.length < 16777216) (hie : i.toNat < e.toNat) (he : e.toNat ≤ t.length) :
    t3 t i e = if slice t i.toNat e.toNat = WITH then 1 else 0 := by
  rw [t3_def]
  by_cases h : e = i + 10
  · subst h
    have en : (i + 10).toNat = i.toNat + 10 := by rw [addU (k := 10) (by omega) (by decide)]; rfl
    simp only [beq_self_eq_true, if_true, ch10_eq]
    have r1 : bget t (i + 1) = t.getD (i.toNat + 1) 0 := by rw [bget_eq, addU (k := 1) (by omega) (by decide)]; rfl
    have r2 : bget t (i + 2) = t.getD (i.toNat + 2) 0 := by rw [bget_eq, addU (k := 2) (by omega) (by decide)]; rfl
    have r3 : bget t (i + 3) = t.getD (i.toNat + 3) 0 := by rw [bget_eq, addU (k := 3) (by omega) (by decide)]; rfl
    have r4 : bget t (i + 4) = t.getD (i.toNat + 4) 0 := by rw [bget_eq, addU (k := 4) (by omega) (by decide)]; rfl
    have r5 : bget t (i + 5) = t.getD (i.toNat + 5) 0 := by rw [bget_eq, addU (k := 5) (by omega) (by decide)]; rfl
    have r6 : bget t (i + 6) = t.getD (i.toNat + 6) 0 := by rw [bget_eq, addU (k := 6) (by omega) (by decide)]; rfl
    have r7 : bget t (i + 7) = t.getD (i.toNat + 7) 0 := by rw [bget_eq, addU (k := 7) (by omega) (by decide)]; rfl
    have r8 : bget t (i + 8) = t.getD (i.toNat + 8) 0 := by rw [bget_eq, addU (k := 8) (by omega) (by decide)]; rfl
    have r9 : bget t (i + 9) = t.getD (i.toNat + 9) 0 := by rw [bget_eq, addU (k := 9) (by omega) (by decide)]; rfl
    have hs : slice t i.toNat (i + 10).toNat = [t.getD i.toNat 0, t.getD (i.toNat + 1) 0, t.getD (i.toNat + 2) 0, t.getD (i.toNat + 3) 0, t.getD (i.toNat + 4) 0, t.getD (i.toNat + 5) 0, t.getD (i.toNat + 6) 0, t.getD (i.toNat + 7) 0, t.getD (i.toNat + 8) 0, t.getD (i.toNat + 9) 0] := by
      rw [en]; simp only [slice, show i.toNat + 10 - i.toNat = 10 by omega]
      rw [take_getD 10 t i.toNat (by rw [en] at he; exact he)]
      simp [List.range_succ]
    rw [hs, r1, r2, r3, r4, r5, r6, r7, r8, r9, bget_eq]
  · have h' : (e == i + 10) = false := by simpa using h
    rw [if_neg (by simp [h'])]
    rw [if_neg]
    intro hs
    have := congrArg List.length hs
    rw [slice_len (by omega) he] at this
    simp [WITH] at this
    apply h; apply UInt64.toNat_inj.1
    rw [addU (k := 10) (by omega) (by decide)]; simp; omega

theorem t4_eq (t : Buf) (i e : UInt64) (ht : t.length < 16777216) (hie : i.toNat < e.toNat) (he : e.toNat ≤ t.length) :
    t4 t i e = if slice t i.toNat e.toNat = WILD then 1 else 0 := by
  rw [t4_def]
  by_cases h : e = i + 4
  · subst h
    have en : (i + 4).toNat = i.toNat + 4 := by rw [addU (k := 4) (by omega) (by decide)]; rfl
    simp only [beq_self_eq_true, if_true, ch4_eq]
    have r1 : bget t (i + 1) = t.getD (i.toNat + 1) 0 := by rw [bget_eq, addU (k := 1) (by omega) (by decide)]; rfl
    have r2 : bget t (i + 2) = t.getD (i.toNat + 2) 0 := by rw [bget_eq, addU (k := 2) (by omega) (by decide)]; rfl
    have r3 : bget t (i + 3) = t.getD (i.toNat + 3) 0 := by rw [bget_eq, addU (k := 3) (by omega) (by decide)]; rfl
    have hs : slice t i.toNat (i + 4).toNat = [t.getD i.toNat 0, t.getD (i.toNat + 1) 0, t.getD (i.toNat + 2) 0, t.getD (i.toNat + 3) 0] := by
      rw [en]; simp only [slice, show i.toNat + 4 - i.toNat = 4 by omega]
      rw [take_getD 4 t i.toNat (by rw [en] at he; exact he)]
      simp [List.range_succ]
    rw [hs, r1, r2, r3, bget_eq]
  · have h' : (e == i + 4) = false := by simpa using h
    rw [if_neg (by simp [h'])]
    rw [if_neg]
    intro hs
    have := congrArg List.length hs
    rw [slice_len (by omega) he] at this
    simp [WILD] at this
    apply h; apply UInt64.toNat_inj.1
    rw [addU (k := 4) (by omega) (by decide)]; simp; omega

end DsSpec

namespace DsSpec
open C

/-! ### emitting (t5, t6) and the packed arm result -/

theorem t5_eq (o : Buf) : t5 o = o ++ MU := by simp [t5, bpush, MU]

theorem t6_eq : ∀ (n : Nat) (t : Buf) (a b : UInt64) (o : Buf), t.length < 16777216 → b.toNat ≤ t.length →
    a.toNat ≤ b.toNat → b.toNat - a.toNat ≤ n → t6 n t a b o = o ++ slice t a.toNat b.toNat
  | 0, t, a, b, o, _, _, hab, hn => by
    have : b.toNat = a.toNat := by omega
    simp [t6, slice, this]
  | n + 1, t, a, b, o, ht, hb, hab, hn => by
    simp only [t6]
    by_cases hlt : a < b
    · have hl : a.toNat < b.toNat := UInt64.lt_iff_toNat_lt.1 hlt
      rw [if_pos hlt, t6_eq n t (a + 1) b _ ht hb (by rw [add1 (by omega)]; omega) (by rw [add1 (by omega)]; omega)]
      rw [add1 (by omega)]
      simp only [slice, bpush, bget_eq, List.append_assoc, List.singleton_append]
      congr 1
      have hd := drop_cons' (x := t) (n := a.toNat) (by omega)
      rw [show b.toNat - a.toNat = (b.toNat - (a.toNat + 1)) + 1 by omega, hd]
      simp
    · have : b.toNat = a.toNat := by have := UInt64.le_iff_toNat_le.1 (UInt64.not_lt.1 hlt); omega
      rw [if_neg hlt]; simp [slice, this]

theorem qdec (x c : UInt64) (hx : x.toNat < 16777216) (hc : c.toNat < 4) :
    (x * 4 + c) >>> 2 = x ∧ (x * 4 + c) &&& 3 = c := by
  have hm : (x * 4 + c).toNat = x.toNat * 4 + c.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  constructor
  · apply UInt64.toNat_inj.1
    rw [UInt64.toNat_shiftRight, hm]; simp [Nat.shiftRight_eq_div_pow]; omega
  · apply UInt64.toNat_inj.1
    rw [UInt64.toNat_and, hm]
    have : (3 : UInt64).toNat = 2 ^ 2 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]; omega

/-! ### the first word of a token -/

theorem slice_head (t : Buf) (i e : Nat) (h1 : i < e) (h2 : e ≤ t.length) :
    (slice t i e).head? = some (t.getD i 0) := by
  simp only [slice]; rw [drop_cons' (by omega), show e - i = (e - (i + 1)) + 1 by omega]; simp

theorem t0_one (t : Buf) (i : UInt64) (ht : t.length < 16777216) (hi : i.toNat < t.length)
    (h5 : bget t i ≠ 5) (h14 : bget t i ≠ 14) : (t0 t i).toNat = i.toNat + 1 ∧ slice t i.toNat (t0 t i).toNat = [bget t i] := by
  have e1 : t0 t i = i + 1 := by
    simp only [t0]; rw [if_neg (by simpa using h5), if_neg (by simpa using h14)]
  rw [e1, add1 (by omega)]
  refine ⟨rfl, ?_⟩
  simp only [slice, show i.toNat + 1 - i.toNat = 1 by omega]
  rw [drop_cons' hi]; simp [bget_eq]

/-- a token is a given one-word token exactly when its first word is that word (not 5, not 14) -/
theorem tok_single (t : Buf) (i : UInt64) (ht : t.length < 16777216) (hi : i.toNat < t.length) (hne : t0 t i ≠ 0)
    (x : UInt64) (hx5 : x ≠ 5) (hx14 : x ≠ 14) : slice t i.toNat (t0 t i).toNat = [x] ↔ bget t i = x := by
  obtain ⟨a1, a2, -⟩ := t0_sound t i ht hi hne
  constructor
  · intro h
    have := slice_head t i.toNat (t0 t i).toNat a1 a2
    rw [h] at this; simp at this; rw [bget_eq]; exact this.symm
  · intro h
    have h5 : bget t i ≠ 5 := by rw [h]; exact hx5
    have h14 : bget t i ≠ 14 := by rw [h]; exact hx14
    rw [(t0_one t i ht hi h5 h14).2, h]

end DsSpec

namespace DsSpec
open C

theorem bget_pos {t : Buf} {p v : UInt64} (h : bget t p = v) (hv : v ≠ 0) : p.toNat < t.length := by
  rw [bget_eq] at h
  by_cases hp : p.toNat < t.length
  · exact hp
  · rw [getD_none (by omega)] at h; exact absurd h.symm hv

theorem drop_bget {t : Buf} {p v : UInt64} (h : bget t p = v) (hv : v ≠ 0) : t.drop p.toNat = v :: t.drop (p.toNat + 1) := by
  rw [drop_cons' (bget_pos h hv), ← bget_eq, h]

theorem beq_t {a b : UInt64} : (a == b) = true ↔ a = b := by simp
theorem beq_f {a b : UInt64} : ¬ (a == b) = true ↔ a ≠ b := by simp

set_option maxHeartbeats 1000000 in
/-- the pair pattern `(x, y) =>` -/
theorem t8_sound (t : Buf) (j : UInt64) (o : Buf) (ht : t.length < 16777216) (hj : j.toNat < t.length)
    (hj6 : bget t j = 6) (q : UInt64) (o1 : Buf) (h : t8 t j o = (q, o1)) (hq : q ≠ 0) :
    ∃ x y pos, pat (t.drop j.toNat) = some (Pat.pair x y, t.drop pos) ∧
      o1 = o ++ ([2, 6] ++ x ++ [15] ++ y ++ [7, 9] ++ MU ++ [13]) ∧ j.toNat < pos ∧ pos ≤ t.length ∧
      q = pos.toUInt64 * 4 + 2 := by
  have hp : pat (t.drop j.toNat) = ((splitTok (t.drop (j.toNat + 1))).bind fun (x, r1) =>
        if x.head? = some 14 then
          match r1 with
          | 15 :: r2 => (splitTok r2).bind fun (y, r3) =>
              if y.head? = some 14 then (match r3 with | 7 :: 19 :: r4 => some (Pat.pair x y, r4) | _ => none) else none
          | _ => none
        else none) := by
    have hs : splitTok (t.drop j.toNat) = some ([6], t.drop (j.toNat + 1)) := by
      rw [drop_bget hj6 (by decide)]; simp [splitTok]
    unfold pat; rw [hs]; simp only [Option.bind_some]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos trivial]
    rfl
  rw [hp]
  unfold t8 at h
  simp only at h
  have c1 : bget t (j + 1) = 14 := by
    cases Decidable.em (bget t (j + 1) = 14) with
    | inl e' => exact e'
    | inr e' => rw [if_neg (by simpa using e')] at h; cases h; exact absurd rfl hq
  rw [if_pos (by simpa using c1)] at h
  have hj1 := add1 (p := j) (by omega)
  have l1 := bget_pos c1 (by decide); rw [hj1] at l1
  by_cases c2 : t0 t (j + 1) = 0
  · rw [if_pos (by simpa using c2)] at h; cases h; exact absurd rfl hq
  rw [if_neg (by simpa using c2)] at h
  obtain ⟨x1, x2, x3⟩ := t0_sound t (j + 1) ht (by omega) c2
  rw [hj1] at x1 x3
  generalize hX : t0 t (j + 1) = X at *
  have hxh : (slice t (j.toNat + 1) X.toNat).head? = some 14 := by
    rw [slice_head _ _ _ x1 x2, ← hj1, ← bget_eq, c1]
  have c3 : bget t X = 15 := by
    cases Decidable.em (bget t X = 15) with
    | inl e' => exact e'
    | inr e' => rw [if_neg (by simpa using e')] at h; cases h; exact absurd rfl hq
  rw [if_pos (by simpa using c3)] at h
  have d3 := drop_bget c3 (by decide)
  have hX1 := add1 (p := X) (by omega)
  have c4 : bget t (X + 1) = 14 := by
    cases Decidable.em (bget t (X + 1) = 14) with
    | inl e' => exact e'
    | inr e' => rw [if_neg (by simpa using e')] at h; cases h; exact absurd rfl hq
  rw [if_pos (by simpa using c4)] at h
  have l4 := bget_pos c4 (by decide); rw [hX1] at l4
  by_cases c5 : t0 t (X + 1) = 0
  · rw [if_pos (by simpa using c5)] at h; cases h; exact absurd rfl hq
  rw [if_neg (by simpa using c5)] at h
  obtain ⟨y1, y2, y3⟩ := t0_sound t (X + 1) ht (by omega) c5
  rw [hX1] at y1 y3
  generalize hY : t0 t (X + 1) = Y at *
  have hyh : (slice t (X.toNat + 1) Y.toNat).head? = some 14 := by
    rw [slice_head _ _ _ y1 y2, ← hX1, ← bget_eq, c4]
  have c6 : bget t Y = 7 := by
    cases Decidable.em (bget t Y = 7) with
    | inl e' => exact e'
    | inr e' => rw [if_neg (by simpa using e')] at h; cases h; exact absurd rfl hq
  rw [if_pos (by simpa using c6)] at h
  have d6 := drop_bget c6 (by decide)
  have hY1 := add1 (p := Y) (by omega)
  have c7 : bget t (Y + 1) = 19 := by
    cases Decidable.em (bget t (Y + 1) = 19) with
    | inl e' => exact e'
    | inr e' => rw [if_neg (by simpa using e')] at h; cases h; exact absurd rfl hq
  rw [if_pos (by simpa using c7)] at h
  have d7 := drop_bget c7 (by decide); rw [hY1] at d7
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨slice t (j.toNat + 1) X.toNat, slice t (X.toNat + 1) Y.toNat, Y.toNat + 2, ?_, ?_, by omega, ?_, ?_⟩
  · rw [x3]
    simp only [Option.bind_some, hxh, if_true]
    rw [d3]
    simp only
    rw [y3]
    simp only [Option.bind_some, hyh, if_true]
    rw [d6, d7]
    simp only [show Y.toNat + 1 + 1 = Y.toNat + 2 by omega]
  · rw [t5_eq, t6_eq _ t _ _ _ ht y2 (by omega) (by omega), t6_eq _ t _ _ _ ht x2 (by rw [hj1]; omega) (by rw [hj1]; omega)]
    rw [hj1, hX1]
    simp [bpush]
  · have : Y.toNat + 2 ≤ t.length := by have := bget_pos c7 (by decide); rw [hY1] at this; omega
    exact this
  · have hy2 := add2 (p := Y) (by omega)
    apply UInt64.toNat_inj.1
    rw [UInt64.toNat_add, UInt64.toNat_mul, hy2, UInt64.toNat_add, UInt64.toNat_mul]
    simp

end DsSpec

namespace DsSpec
open C

theorem qpack (pos : Nat) (c : UInt64) (hp : pos < 16777216) (hc : c.toNat < 4) :
    (pos.toUInt64 * 4 + c) >>> 2 = pos.toUInt64 ∧ (pos.toUInt64 * 4 + c) &&& 3 = c :=
  qdec _ c (by simp; omega) hc

theorem pos_pack (e : UInt64) (k : UInt64) (he : e.toNat + 1 < 16777216) (hk : k.toNat < 4) :
    (e + 1) * 4 + k = (e.toNat + 1).toUInt64 * 4 + k := by
  have : e + 1 = (e.toNat + 1).toUInt64 := by
    apply UInt64.toNat_inj.1; rw [add1 (by omega)]; first | omega | (simp; omega) | simp
  rw [this]

set_option maxHeartbeats 2000000 in
/-- one match arm: the pattern after `|` and its code -/
theorem t7_sound (t : Buf) (j f : UInt64) (o : Buf) (ht : t.length < 16777216) (hj : j.toNat ≤ t.length)
    (q : UInt64) (o1 : Buf) (h : t7 t j f o = (q, o1)) (hq : q ≠ 0) :
    ∃ p pos w c, pat (t.drop j.toNat) = some (p, t.drop pos) ∧ armCode (f == 1) p = some (w, c) ∧ o1 = o ++ w ∧
      j.toNat < pos ∧ pos ≤ t.length ∧ q = pos.toUInt64 * 4 + (cell c).toUInt64 := by
  unfold t7 at h
  simp only at h
  have c0 : j < bsize t := by
    cases Decidable.em (j < bsize t) with
    | inl e' => exact e'
    | inr e' => rw [if_neg e'] at h; cases h; exact absurd rfl hq
  rw [if_pos c0] at h
  have hjl : j.toNat < t.length := (lt_bsize ht).1 c0
  have c1 : t0 t j ≠ 0 := by
    intro e'; rw [if_pos (by simpa using e')] at h; cases h; exact absurd rfl hq
  rw [if_neg (by simpa using c1)] at h
  obtain ⟨e1, e2, e3⟩ := t0_sound t j ht hjl c1
  generalize hE : t0 t j = E at *
  have hhead := slice_head t j.toNat E.toNat e1 e2
  rw [← bget_eq] at hhead
  generalize hA : slice t j.toNat E.toNat = A at *
  unfold pat
  rw [e3]
  simp only [Option.bind_some]
  -- the prefix of a later arm
  have hP : (if f == 1 then o else bpush o 34) = o ++ (if (f == 1) = true then [] else [34]) := by
    split <;> simp [bpush]
  by_cases k5 : bget t j = 5
  · rw [if_pos (by simpa using k5)] at h
    rw [k5] at hhead
    rw [if_pos hhead]
    have c2 : bget t E = 19 := by
      cases Decidable.em (bget t E = 19) with
      | inl e' => exact e'
      | inr e' => rw [if_neg (by simpa using e')] at h; cases h; exact absurd rfl hq
    rw [if_pos (by simpa using c2)] at h
    rw [drop_bget c2 (by decide)]
    simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have l2 := bget_pos c2 (by decide)
    refine ⟨_, E.toNat + 1, _, false, rfl, rfl, ?_, by omega, by omega, ?_⟩
    · rw [t6_eq _ t _ _ _ ht e2 (by omega) (by omega), t5_eq, hP, hA]; simp [bpush]
    · rw [pos_pack E 1 (by omega) (by decide)]; rfl
  rw [if_neg (by simpa using k5)] at h
  have nh5 : ¬ A.head? = some 5 := by rw [hhead]; simpa using k5
  rw [if_neg nh5]
  rw [t4_eq t j E ht e1 e2, hA] at h
  by_cases kw : A = WILD
  · rw [if_pos kw] at h ⊢
    simp only [beq_self_eq_true, if_true] at h
    have c2 : bget t E = 19 := by
      cases Decidable.em (bget t E = 19) with
      | inl e' => exact e'
      | inr e' => rw [if_neg (by simpa using e')] at h; cases h; exact absurd rfl hq
    rw [if_pos (by simpa using c2)] at h
    rw [drop_bget c2 (by decide)]
    simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have l2 := bget_pos c2 (by decide)
    refine ⟨_, E.toNat + 1, _, true, rfl, rfl, ?_, by omega, by omega, ?_⟩
    · rw [hP]
    · rw [pos_pack E 2 (by omega) (by decide)]; rfl
  rw [if_neg kw] at h ⊢
  rw [if_neg (show ¬ ((0 : UInt64) == 1) = true by decide)] at h
  by_cases k14 : bget t j = 14
  · rw [if_pos (by simpa using k14)] at h
    rw [k14] at hhead
    rw [if_pos hhead]
    have c2 : bget t E = 19 := by
      cases Decidable.em (bget t E = 19) with
      | inl e' => exact e'
      | inr e' => rw [if_neg (by simpa using e')] at h; cases h; exact absurd rfl hq
    rw [if_pos (by simpa using c2)] at h
    rw [drop_bget c2 (by decide)]
    simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have l2 := bget_pos c2 (by decide)
    refine ⟨_, E.toNat + 1, _, true, rfl, rfl, ?_, by omega, by omega, ?_⟩
    · rw [t5_eq, t6_eq _ t _ _ _ ht e2 (by omega) (by omega), hP, hA]; simp [bpush]
    · rw [pos_pack E 2 (by omega) (by decide)]; rfl
  rw [if_neg (by simpa using k14)] at h
  have nh14 : ¬ A.head? = some 14 := by rw [hhead]; simpa using k14
  rw [if_neg nh14]
  by_cases k6 : bget t j = 6
  · rw [if_pos (by simpa using k6)] at h
    have hA6 : A = [6] := by
      rw [← hA, ← hE]; exact (tok_single t j ht hjl (by rw [hE]; exact c1) 6 (by decide) (by decide)).2 k6
    rw [if_pos hA6]
    have hE1 : E.toNat = j.toNat + 1 := by
      rw [← hE]; exact (t0_one t j ht hjl (by rw [k6]; decide) (by rw [k6]; decide)).1
    rw [hE1]
    by_cases f1 : f = 1
    · subst f1
      simp only [beq_self_eq_true, if_true] at h
      obtain ⟨x, y, pos, s1, s2, s3, s4, s5⟩ := t8_sound t j o ht hjl k6 q o1 h hq
      refine ⟨Pat.pair x y, pos, _, true, ?_, by simp [armCode], s2, by omega, s4, ?_⟩
      · rw [← s1]; unfold pat; rw [e3, ← hE1]; simp only [Option.bind_some]
        rw [if_neg nh5, if_neg kw, if_neg nh14, if_pos hA6]
      rw [s5]; rfl
    · rw [if_neg (by simpa using f1)] at h; cases h; exact absurd rfl hq
  · rw [if_neg (by simpa using k6)] at h; cases h; exact absurd rfl hq

end DsSpec

namespace DsSpec
open C

/-! ### the no-match shortcut (t11) -/

theorem identTok_app : ∀ (n : Nat) (l : List UInt64) {w r : List UInt64}, l.length ≤ n → identTok l = some (w, r) → l = w ++ r
  | 0, l, w, r, hl, h => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [identTok] at h
  | n + 1, l, w, r, hl, h => by
    unfold identTok at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
    · obtain ⟨⟨w', r'⟩, h1, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [List.length_cons] at hl
      have e := identTok_app n _ (by omega) h1
      rw [e]; rfl
    · cases h

theorem splitTok_app {l a r : List UInt64} (h : splitTok l = some (a, r)) : l = a ++ r := by
  match l, h with
  | k :: l', h =>
    simp only [splitTok] at h
    by_cases h5 : k = 5
    · rw [if_pos h5] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        subst h5; simp
      · cases h
    · rw [if_neg h5] at h
      by_cases h14 : k = 14
      · rw [if_pos h14] at h
        obtain ⟨⟨w, r'⟩, h1, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        subst h14; rw [identTok_app _ l' (Nat.le_refl _) h1]; rfl
      · rw [if_neg h14] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl

theorem t11_sound : ∀ (n f : Nat) (t : Buf) (i : UInt64), t.length < 16777216 → i.toNat ≤ t.length →
    t.length - i.toNat < f → t11 n t i = 1 → noMatch f (t.drop i.toNat) = true
  | 0, _, _, _, _, _, _, h => by simp [t11] at h
  | n + 1, f, t, i, ht, hi, hf, h => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [t11] at h
    by_cases hlt : i < bsize t
    · rw [if_pos hlt] at h
      have hl := (lt_bsize ht).1 hlt
      have c1 : t0 t i ≠ 0 := by intro e'; rw [if_pos (by simpa using e')] at h; cases h
      rw [if_neg (by simpa using c1)] at h
      obtain ⟨e1, e2, e3⟩ := t0_sound t i ht hl c1
      rw [t2_eq t i _ ht e1 e2] at h
      have nm : slice t i.toNat (t0 t i).toNat ≠ MATCH := by
        intro e'; rw [if_pos e'] at h; simp at h
      rw [if_neg nm] at h
      simp only [show ¬ ((0 : UInt64) == 1) = true by decide, if_false] at h
      have IH := t11_sound n f t (t0 t i) ht e2 (by omega) h
      rw [drop_cons' hl]
      rw [drop_cons' hl] at e3
      simp only [noMatch, e3, IH, Bool.and_true]
      simpa using nm
    · have : i.toNat = t.length := by have := (not_congr (lt_bsize ht)).1 hlt; omega
      rw [this]; simp [noMatch]

/-- on a text without `match`, a successful run of `go` (all cells 0) copies it -/
theorem go_noMatch : ∀ (f g : Nat) (ts : List UInt64) (cs : List Nat) (out : List UInt64), noMatch g ts = true →
    (∀ c ∈ cs, c = 0) → go f ts cs false = some out → out = ts
  | 0, _, _, _, _, _, _, h => by simp [go] at h
  | f + 1, g, [], cs, out, _, _, h => by
    simp only [go] at h; split at h
    · cases h; rfl
    · cases h
  | f + 1, 0, _ :: _, _, _, hn, _, _ => by simp [noMatch] at hn
  | f + 1, g + 1, x :: xs, cs, out, hn, hc, h => by
    simp only [noMatch] at hn
    split at hn
    · cases hn
    rename_i a r hs
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
    obtain ⟨hm, hr⟩ := hn
    have hts := splitTok_app hs
    have hh1 : cs.head? ≠ some 1 := by
      intro e'; have := hc 1 (List.mem_of_mem_head? e'); cases this
    have hh2 : cs.head? ≠ some 2 := by
      intro e'; have := hc 2 (List.mem_of_mem_head? e'); cases this
    simp only [go, hs, Option.bind_some, Bool.false_eq_true, if_false, hm] at h
    by_cases hw : a = WITH
    · rw [if_pos hw] at h; cases h
    rw [if_neg hw] at h
    by_cases h18 : a = [18]
    · rw [if_pos h18, if_neg hh1, if_neg hh2] at h
      obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [go_noMatch f g r cs o' hr hc h1, hts, h18]; rfl
    rw [if_neg h18] at h
    by_cases h6 : a = [6]
    · rw [if_pos h6] at h
      obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      have hc' : ∀ c ∈ (0 :: cs), c = 0 := by
        intro c hm'; rcases List.mem_cons.1 hm' with e' | e'
        · exact e'
        · exact hc c e'
      rw [go_noMatch f g r _ o' hr hc' h1, hts, h6]; rfl
    rw [if_neg h6] at h
    by_cases h7 : a = [7]
    · rw [if_pos h7] at h
      split at h
      · cases h
      obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      have hc' : ∀ c ∈ cs.tail, c = 0 := fun c hm' => hc c (List.mem_of_mem_tail hm')
      rw [go_noMatch f g r _ o' hr hc' h1, hts, h7]; rfl
    rw [if_neg h7] at h
    by_cases h1 : a = [1]
    · rw [if_pos h1] at h
      split at h
      · obtain ⟨o', h2, rfl⟩ := Option.map_eq_some_iff.1 h
        have hc' : ∀ c ∈ [0], c = 0 := by simp
        rw [go_noMatch f g r _ o' hr hc' h2, hts, h1]; rfl
      · cases h
    rw [if_neg h1] at h
    obtain ⟨o', h2, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [go_noMatch f g r cs o' hr hc h2, hts]

end DsSpec

namespace DsSpec
open C

/-! ### the match cells: `s[d - k]` is the cell of depth `d - k` = `cs[k]` -/

def Rep (s : Buf) (d : UInt64) (cs : List Nat) : Prop :=
  cs.length = d.toNat + 1 ∧ d.toNat < s.length ∧ ∀ k, k ≤ d.toNat → cs.getD k 0 = (s.getD (d.toNat - k) 0).toNat

theorem rep_head {s : Buf} {d : UInt64} {cs : List Nat} (h : Rep s d cs) : cs.head? = some (bget s d).toNat := by
  obtain ⟨h1, -, h3⟩ := h
  have := h3 0 (by omega)
  cases cs with
  | nil => simp at h1
  | cons c cs => simp at this ⊢; rw [this, bget_eq, List.getD_eq_getElem?_getD]

theorem rep_set {s : Buf} {d v : UInt64} {cs : List Nat} (h : Rep s d cs) : Rep (bset s d v) d (v.toNat :: cs.tail) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by cases cs <;> simp_all, by simp [bset]; omega, fun k hk => ?_⟩
  simp only [bset]
  cases k with
  | zero => simp [List.getElem?_set, h2]
  | succ k =>
    have := h3 (k + 1) hk
    cases cs with
    | nil => simp at h1
    | cons c cs =>
      simp only [List.getD_cons_succ, List.tail_cons] at this ⊢
      rw [this, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega)]

theorem rep_pop {s : Buf} {d : UInt64} {cs : List Nat} (h : Rep s d cs) (hd : d ≠ 0) :
    Rep (bset s d 0) (d - 1) cs.tail := by
  obtain ⟨h1, h2, h3⟩ := h
  have hd' : d.toNat ≠ 0 := fun e => hd (UInt64.toNat_inj.1 (by simpa using e))
  have hs : (d - 1).toNat = d.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le]; · simp
    · rw [UInt64.le_iff_toNat_le]; simp; omega
  unfold Rep; rw [hs]
  refine ⟨by cases cs <;> simp_all; omega, by simp [bset]; omega, fun k hk => ?_⟩
  have := h3 (k + 1) (by omega)
  cases cs with
  | nil => simp at h1
  | cons c cs =>
    simp only [List.getD_cons_succ, List.tail_cons] at this ⊢
    rw [this, show d.toNat - (k + 1) = d.toNat - 1 - k by omega]
    simp only [bset, List.getD_eq_getElem?_getD]
    rw [List.getElem?_set_ne (by omega)]

theorem rep_push {s : Buf} {d : UInt64} {cs : List Nat} (h : Rep s d cs) (hd : d.toNat + 1 < 16777216)
    (hs : s.length < 16777216) :
    Rep (if d + 1 < bsize s then bset s (d + 1) 0 else bpush s 0) (d + 1) (0 :: cs) := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := add1 (p := d) (by omega)
  have key : ∀ s' : Buf, s'.length > d.toNat + 1 → (∀ j, j ≤ d.toNat → s'.getD j 0 = s.getD j 0) →
      s'.getD (d.toNat + 1) 0 = 0 → Rep s' (d + 1) (0 :: cs) := by
    intro s' l1 l2 l3
    rw [Rep, e1]
    refine ⟨by simp; omega, l1, fun k hk => ?_⟩
    cases k with
    | zero => simp only [List.getD_cons_zero, Nat.sub_zero]; rw [l3]; rfl
    | succ k =>
      simp only [List.getD_cons_succ]
      rw [h3 k (by omega), show d.toNat + 1 - (k + 1) = d.toNat - k by omega, l2 _ (by omega)]
  split
  · rename_i hlt
    have hlt' : d.toNat + 1 < s.length := by rw [← e1]; exact (lt_bsize hs).1 hlt
    apply key
    · simp [bset]; omega
    · intro j hj; simp only [bset, List.getD_eq_getElem?_getD]; rw [List.getElem?_set_ne (by omega)]
    · simp only [bset, List.getD_eq_getElem?_getD, e1]; rw [List.getElem?_set_self (by omega)]; rfl
  · rename_i hlt
    have hle : s.length ≤ d.toNat + 1 := by
      have := (not_congr (lt_bsize (p := d + 1) hs)).1 hlt; rw [e1] at this; omega
    have hseq : s.length = d.toNat + 1 := by omega
    apply key
    · simp [bpush]; omega
    · intro j hj; simp only [bpush, List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left (by omega)]
    · simp only [bpush, List.getD_eq_getElem?_getD]; rw [List.getElem?_append_right (by omega)]; simp [hseq]

theorem rep_len1 {s : Buf} {d : UInt64} {cs : List Nat} (h : Rep s d cs) : cs.length = 1 ↔ d = 0 := by
  rw [h.1]; constructor
  · intro e; apply UInt64.toNat_inj.1; simp; omega
  · intro e; subst e; simp

theorem rep_zero {s : Buf} {cs : List Nat} (h : Rep s 0 cs) : Rep (bset s 0 0) 0 [0] := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp, by simp [bset] at h2 ⊢; omega, fun k hk => ?_⟩
  simp at hk; subst hk; simp [bset, List.getElem?_set, show 0 < s.length by simpa using h2]

end DsSpec

namespace DsSpec
open C

theorem bT {a b : UInt64} (h : a = b) : (a == b) = true := by simp [h]
theorem bF {a b : UInt64} (h : a ≠ b) : (a == b) = false := by simpa using h

theorem b01 : ((0 : UInt64) == 1) = false := by decide
theorem b11 : ((1 : UInt64) == 1) = true := by decide

theorem cell_lt (c : Bool) : (cell c).toUInt64.toNat = cell c ∧ (cell c).toUInt64.toNat < 4 := by
  cases c <;> simp [cell]

theorem cell_ne0 (c : Bool) : (cell c).toUInt64 ≠ 0 := by cases c <;> decide

/-- the C state after an arm: cell, position, output -/
theorem arm_step {t : Buf} {i d : UInt64} {s : Buf} {cs : List Nat} {q : UInt64} {pos : Nat} {cc : Bool}
    (ht : t.length < 16777216) (hd : d.toNat ≤ i.toNat) (hs : s.length ≤ i.toNat + 1) (hr : Rep s d cs)
    (hip : i.toNat < pos) (hpl : pos ≤ t.length) (hq : q = pos.toUInt64 * 4 + (cell cc).toUInt64) :
    (q >>> 2).toNat = pos ∧ d.toNat ≤ (q >>> 2).toNat ∧ (bset s d (q &&& 3)).length ≤ (q >>> 2).toNat + 1 ∧
      Rep (bset s d (q &&& 3)) d (cell cc :: cs.tail) := by
  obtain ⟨p1, p2⟩ := qpack pos (cell cc).toUInt64 (by omega) (cell_lt cc).2
  rw [hq, p1, p2]
  have hp : (pos.toUInt64).toNat = pos := by simp; omega
  refine ⟨hp, by omega, by simp [bset]; omega, ?_⟩
  have := rep_set (v := (cell cc).toUInt64) hr
  rwa [(cell_lt cc).1] at this

set_option maxHeartbeats 4000000 in
theorem t9_sound : ∀ (n : Nat) (t : Buf) (i d : UInt64) (s : Buf) (c : UInt64) (o : Buf) (cs : List Nat) (f : Nat),
    t.length < 16777216 → i.toNat ≤ t.length → d.toNat ≤ i.toNat → s.length ≤ i.toNat + 1 → Rep s d cs →
    (c = 0 ∨ c = 1) → t.length - i.toNat < f → t9 n t i d s c o ≠ [] →
    ∃ out, go f (t.drop i.toNat) cs (c == 1) = some out ∧ t9 n t i d s c o = o ++ out
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hne => by simp [t9, bnew] at hne
  | n + 1, t, i, d, s, c, o, cs, f, ht, hi, hd, hs, hr, hc, hf, hne => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    by_cases hlt : i < bsize t
    · have hl := (lt_bsize ht).1 hlt
      have hsz : s.length < 16777216 := by omega
      simp only [t9, if_pos hlt] at hne ⊢
      have c1 : t0 t i ≠ 0 := by
        intro e'; simp only [e', beq_self_eq_true, if_true, ite_true] at hne; exact hne rfl
      simp only [bF c1, Bool.false_eq_true, if_false, ite_false] at hne ⊢
      obtain ⟨e1, e2, e3⟩ := t0_sound t i ht hl c1
      have hhead := slice_head t i.toNat (t0 t i).toNat e1 e2
      rw [← bget_eq] at hhead
      have single : ∀ x : UInt64, x ≠ 5 → x ≠ 14 → (slice t i.toNat (t0 t i).toNat = [x] ↔ bget t i = x) :=
        fun x h5 h14 => tok_single t i ht hl c1 x h5 h14
      rw [t2_eq t i _ ht e1 e2, t3_eq t i _ ht e1 e2] at hne ⊢
      generalize hE : t0 t i = E at *
      generalize hA : slice t i.toNat E.toNat = A at *
      have e3' := e3
      rw [drop_cons' hl] at e3' ⊢
      simp only [go, e3', Option.bind_some]
      -- the copy step: continue at E with the token copied
      have copyIH : ∀ (c' : UInt64), (c' = 0 ∨ c' = 1) → t9 n t E d s c' (t6 16777216 t i E o) ≠ [] →
          ∃ out, go f (t.drop E.toNat) cs (c' == 1) = some out ∧ t9 n t E d s c' (t6 16777216 t i E o) = o ++ (A ++ out) := by
        intro c' hc' hn'
        obtain ⟨out, h1, h2⟩ := t9_sound n t E d s c' _ cs f ht e2 (by omega) (by omega) hr hc' (by omega) hn'
        refine ⟨out, h1, ?_⟩
        rw [h2, t6_eq _ t _ _ _ ht e2 (by omega) (by omega), hA]; simp
      rcases hc with rfl | rfl
      · -- outside a scrutinee
        simp only [show ((0 : UInt64) == 1) = false by decide, Bool.false_eq_true, if_false, ite_false] at hne ⊢
        by_cases hm : A = MATCH
        · simp only [hm, if_true, ite_true, show ((1 : UInt64) == 1) = true by decide] at hne ⊢
          have hh := rep_head hr
          by_cases h1 : bget s d = 1
          · simp only [bT h1, if_true, ite_true] at hne; exact absurd rfl hne
          simp only [bF h1, Bool.false_eq_true, if_false, ite_false] at hne ⊢
          rw [hh]
          have : ¬ (some (bget s d).toNat = some 1) := by
            intro e'; apply h1; apply UInt64.toNat_inj.1; simpa using e'
          rw [if_neg this]
          obtain ⟨out, g1, g2⟩ := t9_sound n t E d s 1 _ cs f ht e2 (by omega) (by omega) hr (Or.inr rfl) (by omega) hne
          refine ⟨_, by simp only [b01, b11] at g1; rw [g1]; rfl, ?_⟩
          rw [g2, t5_eq]; simp [bpush, MU]
        simp only [hm, if_false, ite_false, show ((0 : UInt64) == 1) = false by decide, Bool.false_eq_true] at hne ⊢
        by_cases hw : A = WITH
        · simp only [hw, if_true, ite_true, show ((1 : UInt64) == 1) = true by decide] at hne; exact absurd rfl hne
        simp only [hw, if_false, ite_false, show ((0 : UInt64) == 1) = false by decide, Bool.false_eq_true] at hne ⊢
        have hh := rep_head hr
        by_cases k18 : bget t i = 18
        · have hA18 : A = [18] := (single 18 (by decide) (by decide)).2 k18
          simp only [bT k18, if_true, ite_true, hA18] at hne ⊢
          rw [hh]
          by_cases h1 : bget s d = 1
          · have hs1 : some (bget s d).toNat = some 1 := by rw [h1]; rfl
            simp only [bT h1, if_true, ite_true, hs1] at hne ⊢
            generalize hT : t7 t E 0 o = T at hne
            obtain ⟨q, o1⟩ := T
            simp only at hne
            have hq : q ≠ 0 := by intro e'; simp [e', bnew] at hne
            simp only [bF hq, Bool.false_eq_true, if_false, ite_false] at hne ⊢
            obtain ⟨p, pos, w, cc, s1, s2, s3, s4, s5, s6⟩ := t7_sound t E 0 o ht e2 q o1 hT hq
            obtain ⟨a1, a2, a3, a4⟩ := arm_step ht (by omega) (by omega) hr (by omega) s5 s6
            rw [s1]
            simp only [Option.bind_some]
            rw [show ((0 : UInt64) == 1) = false by decide] at s2
            rw [s2]; simp only [Option.bind_some]
            obtain ⟨out, g1, g2⟩ := t9_sound n t (q >>> 2) d _ 0 o1 _ f ht (by omega) a2 a3 a4 (Or.inl rfl) (by omega) hne
            rw [a1] at g1
            refine ⟨_, by simp only [b01, b11] at g1; rw [g1]; rfl, ?_⟩
            rw [g2, s3]; simp
          have hs1 : ¬ some (bget s d).toNat = some 1 := by
            intro e'; apply h1; apply UInt64.toNat_inj.1; simpa using e'
          simp only [bF h1, Bool.false_eq_true, if_false, ite_false, hs1] at hne ⊢
          by_cases h2 : bget s d = 2
          · simp only [bT h2, if_true, ite_true] at hne; exact absurd rfl hne
          have hs2 : ¬ some (bget s d).toNat = some 2 := by
            intro e'; apply h2; apply UInt64.toNat_inj.1; simpa using e'
          simp only [bF h2, Bool.false_eq_true, if_false, ite_false, hs2] at hne ⊢
          obtain ⟨out, g1, g2⟩ := t9_sound n t E d s 0 _ cs f ht e2 (by omega) (by omega) hr (Or.inl rfl) (by omega) hne
          refine ⟨_, by simp only [b01, b11] at g1; rw [g1]; rfl, ?_⟩
          rw [g2]; simp [bpush]
        have nA18 : A ≠ [18] := fun e' => k18 ((single 18 (by decide) (by decide)).1 e')
        simp only [bF k18, Bool.false_eq_true, if_false, ite_false, nA18] at hne ⊢
        by_cases k6 : bget t i = 6
        · have hA6 : A = [6] := (single 6 (by decide) (by decide)).2 k6
          simp only [bT k6, if_true, ite_true, hA6] at hne ⊢
          have hE1 : E.toNat = i.toNat + 1 := by
            rw [← hE]; exact (t0_one t i ht hl (by rw [k6]; decide) (by rw [k6]; decide)).1
          have hd1 := add1 (p := d) (by omega)
          obtain ⟨out, g1, g2⟩ := t9_sound n t E (d + 1) _ 0 _ (0 :: cs) f ht e2 (by omega)
            (by split <;> simp [bset, bpush] <;> omega) (rep_push hr (by omega) hsz) (Or.inl rfl) (by omega) hne
          refine ⟨_, by simp only [b01, b11] at g1; rw [g1]; rfl, ?_⟩
          rw [g2]; simp [bpush]
        have nA6 : A ≠ [6] := fun e' => k6 ((single 6 (by decide) (by decide)).1 e')
        simp only [bF k6, Bool.false_eq_true, if_false, ite_false, nA6] at hne ⊢
        by_cases k7 : bget t i = 7
        · have hA7 : A = [7] := (single 7 (by decide) (by decide)).2 k7
          simp only [bT k7, if_true, ite_true, hA7] at hne ⊢
          rw [hh]
          by_cases h1 : bget s d = 1
          · simp only [bT h1, if_true, ite_true] at hne; exact absurd rfl hne
          simp only [bF h1, Bool.false_eq_true, if_false, ite_false] at hne ⊢
          by_cases h0 : d = 0
          · simp only [bT h0, if_true, ite_true] at hne; exact absurd rfl hne
          simp only [bF h0, Bool.false_eq_true, if_false, ite_false] at hne ⊢
          have hcond : ¬ (some (bget s d).toNat = some 1 ∨ cs.length ≤ 1) := by
            rintro (e' | e')
            · apply h1; apply UInt64.toNat_inj.1; simpa using e'
            · apply h0; apply UInt64.toNat_inj.1; have := hr.1; simp; omega
          rw [if_neg hcond]
          have hsub : (d - 1).toNat = d.toNat - 1 := by
            have hd' : d.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.1 (by simpa using e))
            rw [UInt64.toNat_sub_of_le]; · simp
            · rw [UInt64.le_iff_toNat_le]; simp; omega
          obtain ⟨out, g1, g2⟩ := t9_sound n t E (d - 1) _ 0 _ cs.tail f ht e2 (by omega) (by simp [bset]; omega)
            (rep_pop hr h0) (Or.inl rfl) (by omega) hne
          refine ⟨_, by simp only [b01, b11] at g1; rw [g1]; rfl, ?_⟩
          rw [g2]; simp [bpush]
        have nA7 : A ≠ [7] := fun e' => k7 ((single 7 (by decide) (by decide)).1 e')
        simp only [bF k7, Bool.false_eq_true, if_false, ite_false, nA7] at hne ⊢
        by_cases k1 : bget t i = 1
        · have hA1 : A = [1] := (single 1 (by decide) (by decide)).2 k1
          simp only [bT k1, if_true, ite_true, hA1] at hne ⊢
          by_cases h0 : d = 0
          · subst h0
            simp only [beq_self_eq_true, if_true, ite_true] at hne ⊢
            by_cases h1 : bget s 0 = 1
            · simp only [bT h1, if_true, ite_true] at hne; exact absurd rfl hne
            simp only [bF h1, Bool.false_eq_true, if_false, ite_false] at hne ⊢
            have hcond : cs.length = 1 ∧ cs.head? ≠ some 1 := by
              refine ⟨(rep_len1 hr).2 rfl, ?_⟩
              rw [rep_head hr]; intro e'; apply h1; apply UInt64.toNat_inj.1; simpa using e'
            rw [if_pos hcond]
            obtain ⟨out, g1, g2⟩ := t9_sound n t E 0 _ 0 _ [0] f ht e2 (by simp) (by simp [bset]; omega)
              (rep_zero hr) (Or.inl rfl) (by omega) hne
            refine ⟨_, by simp only [b01, b11] at g1; rw [g1]; rfl, ?_⟩
            rw [g2]; simp [bpush]
          · simp only [bF h0, Bool.false_eq_true, if_false, ite_false] at hne; exact absurd rfl hne
        have nA1 : A ≠ [1] := fun e' => k1 ((single 1 (by decide) (by decide)).1 e')
        simp only [bF k1, Bool.false_eq_true, if_false, ite_false, nA1] at hne ⊢
        obtain ⟨out, g1, g2⟩ := copyIH 0 (Or.inl rfl) hne
        exact ⟨_, by simp only [b01, b11] at g1; rw [g1]; rfl, g2⟩
      · -- inside a scrutinee
        simp only [show ((1 : UInt64) == 1) = true by decide, if_true, ite_true] at hne ⊢
        by_cases hw : A = WITH
        · simp only [hw, if_true, ite_true, show ((1 : UInt64) == 1) = true by decide] at hne ⊢
          by_cases h18 : bget t E = 18
          · simp only [bT h18, if_true, ite_true] at hne ⊢
            rw [drop_bget h18 (by decide)]
            simp only
            have hE1 := add1 (p := E) (by omega)
            generalize hT : t7 t (E + 1) 1 (bpush o 13) = T at hne
            obtain ⟨q, o1⟩ := T
            simp only at hne
            have hq : q ≠ 0 := by intro e'; simp [e', bnew] at hne
            simp only [bF hq, Bool.false_eq_true, if_false, ite_false] at hne ⊢
            have l18 := bget_pos h18 (by decide)
            obtain ⟨p, pos, w, cc, s1, s2, s3, s4, s5, s6⟩ := t7_sound t (E + 1) 1 _ ht (by omega) q o1 hT hq
            rw [hE1] at s1 s4
            obtain ⟨a1, a2, a3, a4⟩ := arm_step ht (by omega) (by omega) hr (by omega) s5 s6
            rw [s1]
            simp only [Option.bind_some]
            rw [show ((1 : UInt64) == 1) = true by decide] at s2
            rw [s2]; simp only [Option.bind_some]
            obtain ⟨out, g1, g2⟩ := t9_sound n t (q >>> 2) d _ 0 o1 _ f ht (by omega) a2 a3 a4 (Or.inl rfl) (by omega) hne
            rw [a1] at g1
            refine ⟨_, by simp only [b01, b11] at g1; rw [g1]; rfl, ?_⟩
            rw [g2, s3]; simp [bpush]
          · simp only [bF h18, Bool.false_eq_true, if_false, ite_false] at hne; exact absurd rfl hne
        simp only [hw, if_false, ite_false, show ((0 : UInt64) == 1) = false by decide, Bool.false_eq_true] at hne ⊢
        by_cases hm : A = MATCH
        · simp only [hm, if_true, ite_true, show ((1 : UInt64) == 1) = true by decide] at hne; exact absurd rfl hne
        simp only [hm, if_false, ite_false, show ((0 : UInt64) == 1) = false by decide, Bool.false_eq_true] at hne ⊢
        by_cases k18 : bget t i = 18
        · simp only [bT k18, if_true, ite_true] at hne; exact absurd rfl hne
        simp only [bF k18, Bool.false_eq_true, if_false, ite_false] at hne ⊢
        by_cases k19 : bget t i = 19
        · simp only [bT k19, if_true, ite_true] at hne; exact absurd rfl hne
        simp only [bF k19, Bool.false_eq_true, if_false, ite_false] at hne ⊢
        have nA18 : A ≠ [18] := fun e' => k18 ((single 18 (by decide) (by decide)).1 e')
        have nA19 : A ≠ [19] := fun e' => k19 ((single 19 (by decide) (by decide)).1 e')
        rw [if_neg (by simp [hm, nA18, nA19])]
        obtain ⟨out, g1, g2⟩ := copyIH 1 (Or.inr rfl) hne
        exact ⟨_, by simp only [b01, b11] at g1; rw [g1]; rfl, g2⟩
    · -- the end of the text
      have hiE : i.toNat = t.length := by have := (not_congr (lt_bsize ht)).1 hlt; omega
      simp only [t9, if_neg hlt] at hne ⊢
      rw [hiE, List.drop_length]
      simp only [go]
      rcases hc with rfl | rfl
      · simp only [show ((0 : UInt64) == 1) = false by decide, Bool.false_eq_true, if_false, ite_false] at hne ⊢
        by_cases h0 : d = 0
        · subst h0
          simp only [beq_self_eq_true, if_true, ite_true] at hne ⊢
          by_cases h1 : bget s 0 = 1
          · simp only [bT h1, if_true, ite_true] at hne; exact absurd rfl hne
          simp only [bF h1, Bool.false_eq_true, if_false, ite_false]
          have hcond : (!false) = true ∧ cs.length = 1 ∧ cs.head? ≠ some 1 := by
            refine ⟨rfl, (rep_len1 hr).2 rfl, ?_⟩
            rw [rep_head hr]; intro e'; apply h1; apply UInt64.toNat_inj.1; simpa using e'
          rw [if_pos hcond]; exact ⟨[], rfl, by simp⟩
        · simp only [bF h0, Bool.false_eq_true, if_false, ite_false] at hne; exact absurd rfl hne
      · simp only [show ((1 : UInt64) == 1) = true by decide, if_true, ite_true] at hne; exact absurd rfl hne

end DsSpec

namespace DsSpec
open C

/-! ### no redundant arm (`t12` sound for `dupOk`) -/

/-- the (match number, literal) pairs recorded in `u` (entries: number, 8 value words) -/
def seenOf : List UInt64 → List (Nat × List UInt64)
  | k :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: rest => (k.toNat, [5, w1, w2, w3, w4, w5, w6, w7, w8]) :: seenOf rest
  | _ => []

theorem seenOf_app : ∀ (u : List UInt64) (e : List UInt64), u.length % 9 = 0 → e.length = 9 →
    seenOf (u ++ e) = seenOf u ++ seenOf e
  | [], e, _, _ => by simp [seenOf]
  | k :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: rest, e, hu, he => by
    simp only [List.cons_append, seenOf]
    rw [seenOf_app rest e (by simp at hu; omega) he]
  | [_], _, hu, _ => by simp at hu
  | [_, _], _, hu, _ => by simp at hu
  | [_, _, _], _, hu, _ => by simp at hu
  | [_, _, _, _], _, hu, _ => by simp at hu
  | [_, _, _, _, _], _, hu, _ => by simp at hu
  | [_, _, _, _, _, _], _, hu, _ => by simp at hu
  | [_, _, _, _, _, _, _], _, hu, _ => by simp at hu
  | [_, _, _, _, _, _, _, _], _, hu, _ => by simp at hu

/-- the literal word at `j` -/
def litAt (t : Buf) (j : UInt64) : List UInt64 :=
  [5, bget t (j + 1), bget t (j + 2), bget t (j + 3), bget t (j + 4), bget t (j + 5), bget t (j + 6), bget t (j + 7), bget t (j + 8)]

theorem t15_eq (u : Buf) (id : UInt64) (t : Buf) (j : UInt64) :
    t15 u id t j = u ++ [id, bget t (j + 1), bget t (j + 2), bget t (j + 3), bget t (j + 4), bget t (j + 5), bget t (j + 6),
      bget t (j + 7), bget t (j + 8)] := by simp [t15, bpush]

theorem t15_seen (u : Buf) (id : UInt64) (t : Buf) (j : UInt64) (hu : u.length % 9 = 0) :
    seenOf (t15 u id t j) = seenOf u ++ [(id.toNat, litAt t j)] ∧ (t15 u id t j).length = u.length + 9 := by
  rw [t15_eq]; refine ⟨?_, by simp⟩
  rw [seenOf_app _ _ hu (by simp)]; simp [seenOf, litAt]

theorem t14_one (u : Buf) (k : UInt64) (t : Buf) (j : UInt64) (h : t14 u k t j ≠ 1) :
    [5, bget u (k + 1), bget u (k + 2), bget u (k + 3), bget u (k + 4), bget u (k + 5), bget u (k + 6), bget u (k + 7),
      bget u (k + 8)] ≠ litAt t j := by
  intro e; apply h
  simp only [litAt, List.cons.injEq] at e
  obtain ⟨-, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := e
  simp [t14, e1, e2, e3, e4, e5, e6, e7, e8]

/-- t13 (when it says "not found") scanned every entry from `k` on -/
theorem t13_sound : ∀ (n : Nat) (u : Buf) (k id : UInt64) (t : Buf) (j : UInt64), u.length < 16777216 →
    u.length % 9 = 0 → k.toNat % 9 = 0 → k.toNat ≤ u.length → t13 n u k id t j ≠ 1 →
    (id.toNat, litAt t j) ∉ seenOf (u.drop k.toNat)
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [t13] at h
  | n + 1, u, k, id, t, j, hu, h9, hk9, hk, h => by
    simp only [t13] at h
    by_cases hlt : k + 8 < bsize u
    · rw [if_pos hlt] at h
      have hl : k.toNat + 8 < u.length := by
        have := (lt_bsize hu).1 hlt; rw [addU (k := 8) (by omega) (by decide)] at this; exact this
      have hk1 : (k + 9).toNat = k.toNat + 9 := add9 (by omega)
      have IH := t13_sound n u (k + 9) id t j hu h9 (by rw [hk1]; omega) (by rw [hk1]; omega)
      rw [hk1] at IH
      have hd : u.drop k.toNat = bget u k :: bget u (k + 1) :: bget u (k + 2) :: bget u (k + 3) :: bget u (k + 4) ::
          bget u (k + 5) :: bget u (k + 6) :: bget u (k + 7) :: bget u (k + 8) :: u.drop (k.toNat + 9) := by
        simp only [bget_eq]
        rw [drop_cons' (by omega), drop_cons' (by omega), drop_cons' (by omega), drop_cons' (by omega), drop_cons' (by omega),
          drop_cons' (by omega), drop_cons' (by omega), drop_cons' (by omega), drop_cons' (by omega)]
        simp only [addU (k := 1) (p := k) (by omega) (by decide), addU (k := 2) (p := k) (by omega) (by decide),
          addU (k := 3) (p := k) (by omega) (by decide), addU (k := 4) (p := k) (by omega) (by decide),
          addU (k := 5) (p := k) (by omega) (by decide), addU (k := 6) (p := k) (by omega) (by decide),
          addU (k := 7) (p := k) (by omega) (by decide), addU (k := 8) (p := k) (by omega) (by decide)]
        simp
      rw [hd]; simp only [seenOf, List.mem_cons, not_or]
      by_cases hid : bget u k = id
      · rw [if_pos (bT hid)] at h
        by_cases h14 : t14 u k t j = 1
        · rw [if_pos (bT h14)] at h; exact absurd rfl h
        · rw [if_neg (by simpa using h14)] at h
          exact ⟨fun e => t14_one u k t j h14 (Prod.mk.inj e).2.symm, IH h⟩
      · rw [if_neg (by simpa using hid)] at h
        refine ⟨fun e => hid (UInt64.toNat_inj.1 (Prod.mk.inj e).1.symm), IH h⟩
    · have hl : ¬ (k.toNat + 8 < u.length) := fun h' =>
        hlt ((lt_bsize hu).2 (by rw [addU (k := 8) (by omega) (by decide)]; exact h'))
      have : k.toNat = u.length := by omega
      rw [this, List.drop_length]; simp [seenOf]

theorem splitTok_head {l a r : List UInt64} (h : splitTok l = some (a, r)) : a.head? = l.head? := by
  match l, h with
  | k :: l', h =>
    simp only [splitTok] at h
    by_cases h5 : k = 5
    · rw [if_pos h5] at h; split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [h5]
      · cases h
    · rw [if_neg h5] at h
      by_cases h14 : k = 14
      · rw [if_pos h14] at h
        obtain ⟨⟨w, r'⟩, -, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; simp [h14]
      · rw [if_neg h14] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp

theorem pat_lit_head {l r w : List UInt64} (h : pat l = some (.lit w, r)) : l.head? = some 5 := by
  unfold pat at h
  obtain ⟨⟨a, r'⟩, hs, h⟩ := Option.bind_eq_some_iff.1 h
  simp only at h
  rw [← splitTok_head hs]
  by_cases c5 : a.head? = some 5
  · exact c5
  rw [if_neg c5] at h
  split at h
  · split at h <;> cases h
  split at h
  · split at h <;> cases h
  split at h
  · cases h1 : (splitTok r') with
    | none => simp [h1] at h
    | some v =>
      obtain ⟨x, r1⟩ := v
      simp only [h1, Option.bind_some] at h
      split at h
      · split at h
        · obtain ⟨⟨y, r3⟩, -, h⟩ := Option.bind_eq_some_iff.1 h
          simp only at h; split at h
          · split at h <;> cases h
          · cases h
        · cases h
      · cases h
  · cases h

theorem lit_pat (t : Buf) (j : UInt64) (ht : t.length < 16777216) (h5 : bget t j = 5) (hl : j.toNat + 9 < t.length)
    (h19 : bget t (j + 9) = 19) : pat (t.drop j.toNat) = some (.lit (litAt t j), t.drop (j.toNat + 10)) := by
  have g : ∀ k : Nat, k ≤ 9 → bget t (j + UInt64.ofNat k) = t.getD (j.toNat + k) 0 := fun k hk => by
    rw [bget_eq]; congr 1; rw [UInt64.toNat_add]; simp; omega
  have hd : t.drop j.toNat = t.getD j.toNat 0 :: t.getD (j.toNat + 1) 0 :: t.getD (j.toNat + 2) 0 :: t.getD (j.toNat + 3) 0 ::
      t.getD (j.toNat + 4) 0 :: t.getD (j.toNat + 5) 0 :: t.getD (j.toNat + 6) 0 :: t.getD (j.toNat + 7) 0 ::
      t.getD (j.toNat + 8) 0 :: t.getD (j.toNat + 9) 0 :: t.drop (j.toNat + 10) := by
    rw [drop_cons' (by omega), drop_cons' (by omega), drop_cons' (by omega), drop_cons' (by omega), drop_cons' (by omega),
      drop_cons' (by omega), drop_cons' (by omega), drop_cons' (by omega), drop_cons' (by omega), drop_cons' (by omega)]
  have e0 : t.getD j.toNat 0 = 5 := by rw [← bget_eq]; exact h5
  have e9 : t.getD (j.toNat + 9) 0 = 19 := by rw [← g 9 (by omega)]; exact h19
  rw [hd, e0, e9]
  simp only [litAt, ← g 1 (by omega), ← g 2 (by omega), ← g 3 (by omega), ← g 4 (by omega), ← g 5 (by omega),
    ← g 6 (by omega), ← g 7 (by omega), ← g 8 (by omega)]
  simp [pat, splitTok]

theorem rep_dec {s : Buf} {d : UInt64} {cs : List Nat} (h : Rep s d cs) (hd : d ≠ 0) : Rep s (d - 1) cs.tail := by
  obtain ⟨h1, h2, h3⟩ := h
  have hd' : d.toNat ≠ 0 := fun e => hd (UInt64.toNat_inj.1 (by simpa using e))
  have hs : (d - 1).toNat = d.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le]; · simp
    · rw [UInt64.le_iff_toNat_le]; simp; omega
  unfold Rep; rw [hs]
  refine ⟨by cases cs <;> simp_all; omega, by omega, fun k hk => ?_⟩
  have := h3 (k + 1) (by omega)
  cases cs with
  | nil => simp at h1
  | cons c cs =>
    simp only [List.getD_cons_succ, List.tail_cons] at this ⊢
    rw [this, show d.toNat - (k + 1) = d.toNat - 1 - k by omega]

theorem rep_reset {s : Buf} {d : UInt64} {cs : List Nat} (h : Rep s d cs) : Rep (bset s 0 0) 0 [0] := by
  obtain ⟨-, h2, -⟩ := h
  refine ⟨by simp, by simp [bset]; omega, fun k hk => ?_⟩
  simp at hk; subst hk; simp [bset, List.getElem?_set, show 0 < s.length by omega]

theorem contains_mem (L : List (Nat × List UInt64)) (x : Nat × List UInt64) : L.contains x = true ↔ x ∈ L := by simp

theorem t12_01 : ∀ (n : Nat) (t : Buf) (i d : UInt64) (s u : Buf) (m c : UInt64),
    t12 n t i d s u m c = 0 ∨ t12 n t i d s u m c = 1
  | 0, _, _, _, _, _, _, _ => .inl rfl
  | n + 1, t, i, d, s, u, m, c => by
    simp only [t12]
    repeat' split
    all_goals first | exact .inl rfl | exact .inr rfl | exact t12_01 n _ _ _ _ _ _ _

/-- t12 (when it accepts) checks `dupOk` -/
theorem t12_sound : ∀ (n : Nat) (t : Buf) (i d : UInt64) (s u : Buf) (m c : UInt64) (ids : List Nat)
    (seen : List (Nat × List UInt64)) (f : Nat),
    t.length < 16777216 → i.toNat ≤ t.length → d.toNat ≤ i.toNat → s.length ≤ i.toNat + 1 → Rep s d ids →
    u.length % 9 = 0 → u.length ≤ i.toNat → (∀ x, x ∈ seen ↔ x ∈ seenOf u) → m.toNat ≤ i.toNat →
    (c = 0 ∨ c = 1) → t.length - i.toNat < f → t12 n t i d s u m c = 1 →
    dupOk f (t.drop i.toNat) ids seen m.toNat (c == 1) = true
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [t12] at h
  | n + 1, t, i, d, s, u, m, c, ids, seen, f, ht, hi, hd, hs, hr, hu9, hul, hseen, hm, hc, hf, h => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    by_cases hlt : i < bsize t
    · have hl := (lt_bsize ht).1 hlt
      have hsz : s.length < 16777216 := by omega
      simp only [t12, if_pos hlt] at h
      have c1 : t0 t i ≠ 0 := by
        intro e'; simp only [e', beq_self_eq_true, if_true, ite_true] at h; exact absurd h (by decide)
      simp only [bF c1, Bool.false_eq_true, if_false, ite_false] at h
      obtain ⟨e1, e2, e3⟩ := t0_sound t i ht hl c1
      have single : ∀ x : UInt64, x ≠ 5 → x ≠ 14 → (slice t i.toNat (t0 t i).toNat = [x] ↔ bget t i = x) :=
        fun x h5 h14 => tok_single t i ht hl c1 x h5 h14
      rw [t2_eq t i _ ht e1 e2, t3_eq t i _ ht e1 e2] at h
      generalize hE : t0 t i = E at *
      generalize hA : slice t i.toNat E.toNat = A at *
      have e3' := e3
      rw [drop_cons' hl] at e3' ⊢
      simp only [dupOk, e3']
      have IH := fun i' d' s' u' m' c' ids' seen' => t12_sound n t i' d' s' u' m' c' ids' seen' f ht
      rcases hc with rfl | rfl
      · -- outside a scrutinee
        simp only [show ((0 : UInt64) == 1) = false by decide, Bool.false_eq_true, if_false, ite_false] at h ⊢
        by_cases hmA : A = MATCH
        · simp only [hmA, if_true, ite_true, show ((1 : UInt64) == 1) = true by decide] at h ⊢
          have := IH E d s u m 1 ids seen e2 (by omega) (by omega) hr hu9 (by omega) hseen (by omega) (.inr rfl) (by omega) h
          simpa using this
        simp only [hmA, if_false, ite_false, show ((0 : UInt64) == 1) = false by decide, Bool.false_eq_true] at h ⊢
        by_cases k18 : bget t i = 18
        · have hA18 : A = [18] := (single 18 (by decide) (by decide)).2 k18
          simp only [bT k18, if_true, ite_true, hA18] at h ⊢
          rw [rep_head hr]
          simp only
          by_cases h0 : bget s d = 0
          · simp only [bT h0, if_true, ite_true] at h
            rw [h0]; simp only [UInt64.toNat_zero, if_true, ite_true]
            exact IH E d s u m 0 ids seen e2 (by omega) (by omega) hr hu9 (by omega) hseen (by omega) (.inl rfl) (by omega) h
          simp only [bF h0, Bool.false_eq_true, if_false, ite_false] at h
          have hk0 : (bget s d).toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.1 (by simpa using e))
          rw [if_neg hk0]
          have hE1 : E.toNat = i.toNat + 1 := by
            rw [← hE]; exact (t0_one t i ht hl (by rw [k18]; decide) (by rw [k18]; decide)).1
          by_cases h5 : bget t E = 5
          · simp only [bT h5, if_true, ite_true] at h
            by_cases hb9 : E + 9 < bsize t
            · simp only [hb9, if_true, ite_true] at h
              have hl9 : E.toNat + 9 < t.length := by
                have := (lt_bsize ht).1 hb9; rw [add9 (by omega)] at this; exact this
              by_cases h19 : bget t (E + 9) = 19
              · simp only [bT h19, if_true, ite_true] at h
                rw [lit_pat t E ht h5 hl9 h19]
                simp only
                by_cases h13 : t13 16777216 u 0 (bget s d) t E = 1
                · simp only [bT h13, if_true, ite_true] at h; exact absurd h (by decide)
                simp only [bF h13, Bool.false_eq_true, if_false, ite_false] at h
                have nm := t13_sound _ u 0 (bget s d) t E (by omega) hu9 (by simp) (by simp) h13
                simp only [UInt64.toNat_zero, List.drop_zero] at nm
                have nc : seen.contains ((bget s d).toNat, litAt t E) = false := by
                  cases e : seen.contains ((bget s d).toNat, litAt t E)
                  · rfl
                  · exact absurd ((hseen _).1 ((contains_mem _ _).1 e)) nm
                rw [nc]; simp only [Bool.false_eq_true, if_false, ite_false]
                obtain ⟨q1, q2⟩ := t15_seen u (bget s d) t E hu9
                have hE10 := add10 (p := E) (by omega)
                have := IH (E + 10) d s (t15 u (bget s d) t E) m 0 ids (((bget s d).toNat, litAt t E) :: seen)
                  (by rw [hE10]; omega) (by rw [hE10]; omega) (by rw [hE10]; omega) hr (by rw [q2]; omega) (by rw [q2, hE10]; omega)
                  (fun x => by rw [q1]; simp only [List.mem_cons, List.mem_append, List.mem_singleton, hseen x, List.not_mem_nil, or_false]; exact or_comm) (by rw [hE10]; omega) (.inl rfl) (by rw [hE10]; omega) h
                rw [hE10] at this; simpa using this
              · simp only [bF h19, Bool.false_eq_true, if_false, ite_false] at h; exact absurd h (by decide)
            · simp only [hb9, if_false, ite_false] at h; exact absurd h (by decide)
          · simp only [bF h5, Bool.false_eq_true, if_false, ite_false] at h
            generalize hT : t7 t E 0 bnew = T at h
            obtain ⟨q, o1⟩ := T
            simp only at h
            have hq : q ≠ 0 := by intro e'; simp [e'] at h
            simp only [bF hq, Bool.false_eq_true, if_false, ite_false] at h
            obtain ⟨p, pos, w, cc, s1, s2, s3, s4, s5, s6⟩ := t7_sound t E 0 bnew ht e2 q o1 hT hq
            obtain ⟨a1, a2, a3, a4⟩ := arm_step (cs := ids) ht (by omega) (by omega) hr (by omega) s5 s6
            have hq2 : q >>> 2 = pos.toUInt64 := by apply UInt64.toNat_inj.1; rw [a1]; simp; omega
            rw [s1]
            cases p with
            | lit w' =>
              exfalso
              have := pat_lit_head s1
              rw [List.head?_drop, List.getElem?_eq_getElem (by omega)] at this
              simp at this
              apply h5; rw [bget_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), this]; rfl
            | wild | var _ | pair _ _ =>
              simp only
              have := IH (q >>> 2) d (bset s d 0) u m 0 (0 :: ids.tail) seen (by omega) (by omega)
                (by rw [show (bset s d 0).length = s.length by simp [bset], a1]; omega) (by simpa using rep_set (v := 0) hr) hu9 (by omega) hseen (by omega) (.inl rfl) (by omega) h
              rw [a1] at this; simpa using this
        have nA18 : A ≠ [18] := fun e' => k18 ((single 18 (by decide) (by decide)).1 e')
        simp only [bF k18, Bool.false_eq_true, if_false, ite_false, nA18] at h ⊢
        by_cases k6 : bget t i = 6
        · have hA6 : A = [6] := (single 6 (by decide) (by decide)).2 k6
          simp only [bT k6, if_true, ite_true, hA6] at h ⊢
          have hE1 : E.toNat = i.toNat + 1 := by
            rw [← hE]; exact (t0_one t i ht hl (by rw [k6]; decide) (by rw [k6]; decide)).1
          have hd1 := add1 (p := d) (by omega)
          exact IH E (d + 1) _ u m 0 (0 :: ids) seen e2 (by omega) (by split <;> simp [bset, bpush] <;> omega)
            (rep_push hr (by omega) hsz) hu9 (by omega) hseen (by omega) (.inl rfl) (by omega) h
        have nA6 : A ≠ [6] := fun e' => k6 ((single 6 (by decide) (by decide)).1 e')
        simp only [bF k6, Bool.false_eq_true, if_false, ite_false, nA6] at h ⊢
        by_cases k7 : bget t i = 7
        · have hA7 : A = [7] := (single 7 (by decide) (by decide)).2 k7
          simp only [bT k7, if_true, ite_true, hA7] at h ⊢
          by_cases h0 : d = 0
          · simp only [bT h0, if_true, ite_true] at h; exact absurd h (by decide)
          simp only [bF h0, Bool.false_eq_true, if_false, ite_false] at h
          have hsub : (d - 1).toNat = d.toNat - 1 := by
            have hd' : d.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.1 (by simpa using e))
            rw [UInt64.toNat_sub_of_le]; · simp
            · rw [UInt64.le_iff_toNat_le]; simp; omega
          exact IH E (d - 1) s u m 0 ids.tail seen e2 (by omega) (by omega) (rep_dec hr h0) hu9 (by omega) hseen
            (by omega) (.inl rfl) (by omega) h
        have nA7 : A ≠ [7] := fun e' => k7 ((single 7 (by decide) (by decide)).1 e')
        simp only [bF k7, Bool.false_eq_true, if_false, ite_false, nA7] at h ⊢
        by_cases k1 : bget t i = 1
        · have hA1 : A = [1] := (single 1 (by decide) (by decide)).2 k1
          simp only [bT k1, if_true, ite_true, hA1] at h ⊢
          exact IH E 0 _ u m 0 [0] seen e2 (by simp) (by simp [bset]; omega) (rep_reset hr) hu9 (by omega) hseen
            (by omega) (.inl rfl) (by omega) h
        have nA1 : A ≠ [1] := fun e' => k1 ((single 1 (by decide) (by decide)).1 e')
        simp only [bF k1, Bool.false_eq_true, if_false, ite_false, nA1] at h ⊢
        exact IH E d s u m 0 ids seen e2 (by omega) (by omega) hr hu9 (by omega) hseen (by omega) (.inl rfl) (by omega) h
      · -- inside a scrutinee
        simp only [show ((1 : UInt64) == 1) = true by decide, if_true, ite_true] at h ⊢
        by_cases hw : A = WITH
        · simp only [hw, if_true, ite_true, show ((1 : UInt64) == 1) = true by decide] at h ⊢
          by_cases h18 : bget t E = 18
          · simp only [bT h18, if_true, ite_true] at h
            rw [drop_bget h18 (by decide)]
            simp only
            have hE1 := add1 (p := E) (by omega)
            have hm1 : (m + 1).toNat = m.toNat + 1 := add1 (by omega)
            have l18 := bget_pos h18 (by decide)
            by_cases h5 : bget t (E + 1) = 5
            · simp only [bT h5, if_true, ite_true] at h
              by_cases hb10 : E + 10 < bsize t
              · simp only [hb10, if_true, ite_true] at h
                have hl10 : (E + 1).toNat + 9 < t.length := by
                  have := (lt_bsize ht).1 hb10; rw [add10 (by omega)] at this; rw [hE1]; omega
                by_cases h19 : bget t (E + 10) = 19
                · simp only [bT h19, if_true, ite_true] at h
                  have h19' : bget t (E + 1 + 9) = 19 := by rw [UInt64.add_assoc]; exact h19
                  rw [← hE1, lit_pat t (E + 1) ht h5 hl10 h19']
                  simp only
                  obtain ⟨q1, q2⟩ := t15_seen u (m + 1) t (E + 1) hu9
                  have hE11 : (E + 11).toNat = E.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
                  have := IH (E + 11) d (bset s d (m + 1)) (t15 u (m + 1) t (E + 1)) (m + 1) 0
                    ((m + 1).toNat :: ids.tail) (((m + 1).toNat, litAt t (E + 1)) :: seen)
                    (by rw [hE11]; omega) (by rw [hE11]; omega) (by rw [show (bset s d (m + 1)).length = s.length by simp [bset], hE11]; omega) (rep_set hr)
                    (by rw [q2]; omega) (by rw [q2, hE11]; omega) (fun x => by rw [q1]; simp only [List.mem_cons, List.mem_append, List.mem_singleton, hseen x, List.not_mem_nil, or_false]; exact or_comm)
                    (by rw [hm1, hE11]; omega) (.inl rfl) (by rw [hE11]; omega) h
                  rw [hm1] at this
                  rw [hE11, show E.toNat + 11 = (E + 1).toNat + 10 by rw [hE1]] at this
                  simpa using this
                · simp only [bF h19, Bool.false_eq_true, if_false, ite_false] at h; exact absurd h (by decide)
              · simp only [hb10, if_false, ite_false] at h; exact absurd h (by decide)
            · simp only [bF h5, Bool.false_eq_true, if_false, ite_false] at h
              generalize hT : t7 t (E + 1) 1 bnew = T at h
              obtain ⟨q, o1⟩ := T
              simp only at h
              have hq : q ≠ 0 := by intro e'; simp [e'] at h
              simp only [bF hq, Bool.false_eq_true, if_false, ite_false] at h
              obtain ⟨p, pos, w, cc, s1, s2, s3, s4, s5, s6⟩ := t7_sound t (E + 1) 1 bnew ht (by omega) q o1 hT hq
              rw [hE1] at s1 s4
              obtain ⟨a1, a2, a3, a4⟩ := arm_step (cs := ids) ht (by omega) (by omega) hr (by omega) s5 s6
              rw [s1]
              cases p with
              | lit w' =>
                exfalso
                have := pat_lit_head s1
                rw [List.head?_drop, List.getElem?_eq_getElem (by omega)] at this
                simp at this
                apply h5; rw [bget_eq, hE1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), this]; rfl
              | wild | var _ | pair _ _ =>
                simp only
                have := IH (q >>> 2) d (bset s d 0) u (m + 1) 0 (0 :: ids.tail) seen (by omega) (by omega)
                  (by rw [show (bset s d 0).length = s.length by simp [bset], a1]; omega) (by simpa using rep_set (v := 0) hr) hu9 (by omega) hseen (by rw [hm1]; omega)
                  (.inl rfl) (by omega) h
                rw [a1, hm1] at this; simpa using this
          · simp only [bF h18, Bool.false_eq_true, if_false, ite_false] at h; exact absurd h (by decide)
        simp only [hw, if_false, ite_false, show ((0 : UInt64) == 1) = false by decide, Bool.false_eq_true] at h ⊢
        exact IH E d s u m 1 ids seen e2 (by omega) (by omega) hr hu9 (by omega) hseen (by omega) (.inr rfl) (by omega) h
    · have hiE : i.toNat = t.length := by have := (not_congr (lt_bsize ht)).1 hlt; omega
      rw [hiE, List.drop_length]; simp [dupOk]

end DsSpec

namespace DsSpec
open C

/-! ### the output is at most 3 words per input word -/

theorem splitTok_len {l a r : List UInt64} (h : splitTok l = some (a, r)) : 1 ≤ a.length := by
  match l, h with
  | k :: l', h =>
    simp only [splitTok] at h
    by_cases h5 : k = 5
    · rw [if_pos h5] at h; split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
      · cases h
    · rw [if_neg h5] at h
      by_cases h14 : k = 14
      · rw [if_pos h14] at h
        obtain ⟨⟨w, r'⟩, -, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; simp
      · rw [if_neg h14] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp

theorem pre_len (b : Bool) : (if b then ([] : List UInt64) else [34]).length ≤ 1 := by split <;> simp

theorem pat_len {r1 r2 w : List UInt64} {p : Pat} {b c : Bool} (hp : pat r1 = some (p, r2))
    (ha : armCode b p = some (w, c)) : w.length + 3 * r2.length ≤ 3 + 3 * r1.length := by
  unfold pat at hp
  obtain ⟨⟨a, r⟩, hs, hp⟩ := Option.bind_eq_some_iff.1 hp
  simp only at hp
  have e1 := splitTok_app hs
  have l1 := splitTok_len hs
  rw [e1]
  have hpre := pre_len b
  -- the three one-token patterns `a =>`
  have one : ∀ (r' : List UInt64), r = 19 :: r' → r2 = r' → w.length ≤ 8 + a.length →
      w.length + 3 * r2.length ≤ 3 + 3 * (a ++ r).length := by
    intro r' h1 h2 h3; subst h1; subst h2; simp; omega
  by_cases c5 : a.head? = some 5
  · rw [if_pos c5] at hp
    split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      simp only [armCode, Option.some.injEq, Prod.mk.injEq] at ha; obtain ⟨rfl, rfl⟩ := ha
      exact one _ rfl rfl (by simp [MU]; omega)
    · cases hp
  rw [if_neg c5] at hp
  by_cases cw : a = WILD
  · rw [if_pos cw] at hp
    split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      simp only [armCode, Option.some.injEq, Prod.mk.injEq] at ha; obtain ⟨rfl, rfl⟩ := ha
      exact one _ rfl rfl (by omega)
    · cases hp
  rw [if_neg cw] at hp
  by_cases c14 : a.head? = some 14
  · rw [if_pos c14] at hp
    split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      simp only [armCode, Option.some.injEq, Prod.mk.injEq] at ha; obtain ⟨rfl, rfl⟩ := ha
      exact one _ rfl rfl (by simp [MU]; omega)
    · cases hp
  rw [if_neg c14] at hp
  by_cases c6 : a = [6]
  · rw [if_pos c6] at hp
    subst c6
    obtain ⟨⟨x, r1'⟩, hx, hp⟩ := Option.bind_eq_some_iff.1 hp
    simp only at hp
    have ex := splitTok_app hx
    split at hp
    · split at hp
      · rename_i r2' _
        obtain ⟨⟨y, r3⟩, hy, hp⟩ := Option.bind_eq_some_iff.1 hp
        simp only at hp
        have ey := splitTok_app hy
        split at hp
        · split at hp
          · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
            rename_i r4 _ _
            cases b
            · simp [armCode] at ha
            · simp only [armCode, if_true, Option.some.injEq, Prod.mk.injEq] at ha; obtain ⟨rfl, rfl⟩ := ha
              subst ex; subst ey
              simp [MU]; omega
          · cases hp
        · cases hp
      · cases hp
    · cases hp
  · rw [if_neg c6] at hp; cases hp

/-- the code `go` emits is at most 3 words per input word -/
theorem go_len : ∀ (f : Nat) (ts : List UInt64) (cs : List Nat) (sc : Bool) (out : List UInt64),
    go f ts cs sc = some out → out.length ≤ 3 * ts.length
  | 0, _, _, _, _, h => by simp [go] at h
  | f + 1, [], cs, sc, out, h => by
    simp only [go] at h; split at h
    · cases h; simp
    · cases h
  | f + 1, x :: xs, cs, sc, out, h => by
    simp only [go] at h
    obtain ⟨⟨a, r⟩, hs, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    have e1 := splitTok_app hs
    have l1 := splitTok_len hs
    rw [e1]
    -- the copy / fixed-code steps
    have step : ∀ (pre : List UInt64) (cs' : List Nat) (sc' : Bool) (o' : List UInt64), go f r cs' sc' = some o' →
        pre.length ≤ 3 * a.length → (pre ++ o').length ≤ 3 * (a ++ r).length := by
      intro pre cs' sc' o' h1 h2
      have := go_len f r cs' sc' o' h1; simp; omega
    -- an arm after `| `
    have arm : ∀ (pre : List UInt64) (r1 : List UInt64) (p : Pat) (r2 w : List UInt64) (bb c' : Bool) (cs' : List Nat) (o' : List UInt64),
        r = r1 → pat r1 = some (p, r2) → armCode bb p = some (w, c') → go f r2 cs' false = some o' →
        pre.length + 3 ≤ 3 * a.length → (pre ++ w ++ o').length ≤ 3 * (a ++ r).length := by
      intro pre r1 p r2 w bb c' cs' o' hr h1 h2 h3 h4
      have := go_len f r2 cs' false o' h3
      have := pat_len h1 h2
      subst hr; simp; omega
    split at h
    · split at h
      · split at h
        · obtain ⟨⟨p, r2⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨⟨w, c'⟩, h2, h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨o', h3, rfl⟩ := Option.map_eq_some_iff.1 h
          have := go_len f r2 _ false o' h3
          have := pat_len h1 h2
          rw [‹a = WITH›]; simp [WITH]; omega
        · cases h
      · split at h
        · cases h
        · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
          exact step a cs true o' h1 (by omega)
    · split at h
      · split at h
        · cases h
        · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
          have := step ([2] ++ MU ++ [9]) cs true o' h1 (by rw [‹a = MATCH›]; simp [MU, MATCH])
          simpa using this
      · split at h
        · cases h
        · split at h
          · split at h
            · obtain ⟨⟨p, r2⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
              obtain ⟨⟨w, c'⟩, h2, h⟩ := Option.bind_eq_some_iff.1 h
              obtain ⟨o', h3, rfl⟩ := Option.map_eq_some_iff.1 h
              have := arm [] r p r2 w false c' _ o' rfl h1 h2 h3 (by rw [‹a = [18]›]; simp)
              simpa using this
            · split at h
              · cases h
              · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
                have := step [18] cs false o' h1 (by rw [‹a = [18]›]; simp)
                simpa using this
          · split at h
            · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
              have := step [6] _ false o' h1 (by rw [‹a = [6]›]; simp)
              simpa using this
            · split at h
              · split at h
                · cases h
                · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
                  have := step [7] _ false o' h1 (by rw [‹a = [7]›]; simp)
                  simpa using this
              · split at h
                · split at h
                  · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
                    have := step [1] _ false o' h1 (by rw [‹a = [1]›]; simp)
                    simpa using this
                  · cases h
                · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
                  exact step a cs false o' h1 (by omega)

end DsSpec

namespace DsSpec
open C

theorem rep0 : Rep (bpush bnew 0) 0 [0] := ⟨rfl, by simp [bpush, bnew], fun k hk => by simp at hk; subst hk; rfl⟩

/-- **the match desugaring is sound**: if `C.t10` accepts a token buffer (below 2^24 words), its output is the
specification's `ds` -/
theorem t10_sound (t : Buf) (ht : t.length < 16777216) (h : t10 t ≠ []) : ds t = some (t10 t) := by
  have hb : bsize t < 16777216 := by
    rw [UInt64.lt_iff_toNat_lt, bsize_toNat ht]; simpa using ht
  unfold t10 at h ⊢
  rw [if_pos hb] at h ⊢
  unfold ds
  rw [if_pos (by simpa using ht)]
  by_cases h11 : t11 16777216 t 0 = 1
  · rw [if_pos (bT h11)]
    have := t11_sound _ (t.length + 1) t 0 ht (by simp) (by simp) h11
    simp only [UInt64.toNat_zero, List.drop_zero] at this
    rw [if_pos this]
  simp only [bF h11, Bool.false_eq_true, if_false, ite_false] at h ⊢
  have h12 : t12 16777216 t 0 0 (bpush bnew 0) bnew 0 0 = 1 := by
    rcases t12_01 16777216 t 0 0 (bpush bnew 0) bnew 0 0 with e | e
    · rw [e] at h; simp [bnew] at h
    · exact e
  simp only [h12, show ((1 : UInt64) == 0) = false by decide, Bool.false_eq_true, if_false, ite_false] at h ⊢
  have hdup := t12_sound 16777216 t 0 0 (bpush bnew 0) bnew 0 0 [0] [] (t.length + 1) ht (by simp) (by simp)
    (by simp [bpush, bnew]) rep0 (by simp [bnew]) (by simp [bnew]) (fun x => by simp [seenOf, bnew]) (by simp) (.inl rfl)
    (by simp) h12
  simp only [UInt64.toNat_zero, List.drop_zero, b01] at hdup
  have hne : t9 16777216 t 0 0 (bpush bnew 0) 0 bnew ≠ [] := by
    intro e; rw [e] at h; simp [bsize, bnew] at h
  obtain ⟨out, g1, g2⟩ := t9_sound 16777216 t 0 0 (bpush bnew 0) 0 bnew [0] (t.length + 1) ht (by simp) (by simp)
    (by simp [bpush, bnew]) rep0 (Or.inl rfl) (by simp) hne
  simp only [UInt64.toNat_zero, List.drop_zero, b01] at g1
  rw [g2] at h ⊢
  simp only [bnew, List.nil_append] at h ⊢
  have hl := go_len _ _ _ _ _ g1
  have hO : bsize out < 16777216 := by
    cases Decidable.em (bsize out < 16777216) with
    | inl e => exact e
    | inr e => simp only [e, if_false, ite_false] at h; exact absurd rfl h
  have hO' : out.length < 16777216 := by
    rw [UInt64.lt_iff_toNat_lt] at hO; simp [bsize] at hO; omega
  simp only [hO, if_true, ite_true]
  by_cases hm : noMatch (t.length + 1) t = true
  · rw [if_pos hm, go_noMatch _ _ t [0] out hm (by simp) g1]
  · rw [if_neg hm, hdup]; simp only [Bool.not_true, Bool.false_eq_true, if_false, ite_false]; rw [g1]; simp [hO']

end DsSpec
