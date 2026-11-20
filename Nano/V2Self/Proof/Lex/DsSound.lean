/- Nano/V2Self/Proof/Lex/DsSound: the match desugaring stage `C.t10` (Nano/V2Self/C/Dsg.lean) meets its specification
`DsSpec.ds` (Nano/V2Self/Proof/Lex/DsSpec.lean): `t10_sound : C.t10 t ≠ [] → DsSpec.ds t = some (C.t10 t)`. -/
import Nano.V2Self.C.Dsg
import Nano.V2Self.Proof.Lex.DsSpec
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
