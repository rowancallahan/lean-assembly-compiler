/- Nano/V2Self/Proof/Own/OwnP6: the flag-region loop `o22` (c = 0 copy, 1 swap, 2 or, 3 zero) on lists, then on `RF`. -/
import Nano.V2Self.Proof.Own.OwnP5
namespace OwnP
open C OwnSpec

theorem o22_zero : ∀ (m : Nat) (f : Buf) (a b j n : Nat), a + n ≤ f.length → f.length < 2 ^ 62 → n - j ≤ m → j ≤ n →
    n < 2 ^ 40 →
    (o22 m f (u a) (u b) (u j) (u n) (u 3)).length = f.length ∧
    ∀ k, (o22 m f (u a) (u b) (u j) (u n) (u 3)).getD k 0 = if a + j ≤ k ∧ k < a + n then 0 else f.getD k 0 := by
  intro m; induction m with
  | zero => intro f a b j n _ _ hm _ _; rw [o22]; exact ⟨rfl, fun k => by rw [if_neg (by omega)]⟩
  | succ m ih =>
    intro f a b j n hl hl2 hm hjn hn
    rw [o22]
    by_cases hj : j < n
    · simp only [u_lt' (show j < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega), hj, if_true, u_add,
        show (u 1 : UInt64) = 1 from rfl]
      simp only [show (u 3 == 0) = false from rfl, show (u 3 == 1) = false from rfl, show (u 3 == 2) = false from rfl,
        show (u 3 == 3) = true from rfl, Bool.false_eq_true, if_false, if_true]
      rw [show (1 : UInt64) = u 1 from rfl, u_add]
      have s0 := o0_step (b := f) (j := a + j) (by omega) hl2 0
      have := ih (o0 f (u (a + j)) 0) a b (j + 1) n (by rw [s0.1]; omega) (by rw [s0.1]; omega) (by omega) (by omega) hn
      refine ⟨by rw [this.1, s0.1]; omega, fun k => ?_⟩
      rw [this.2, s0.2]
      by_cases hk : a + (j + 1) ≤ k ∧ k < a + n
      · rw [if_pos hk, if_pos (by omega)]
      · rw [if_neg hk]; by_cases hk2 : k = a + j
        · rw [if_pos hk2, if_pos (by omega)]
        · rw [if_neg hk2, if_neg (by omega)]
    · simp only [u_lt' (show j < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega), hj, if_false]
      exact ⟨trivial, fun k => by rw [if_neg (by omega)]⟩

theorem o22_copy : ∀ (m : Nat) (f : Buf) (a b j n : Nat), a + n ≤ b → b + j ≤ f.length → f.length < 2 ^ 62 → n - j ≤ m →
    j ≤ n → b + n < 2 ^ 62 →
    (o22 m f (u a) (u b) (u j) (u n) (u 0)).length = max f.length (b + n) ∧
    ∀ k, (o22 m f (u a) (u b) (u j) (u n) (u 0)).getD k 0 = if b + j ≤ k ∧ k < b + n then f.getD (a + (k - b)) 0 else f.getD k 0 := by
  intro m; induction m with
  | zero => intro f a b j n _ hl _ hm hjn _; rw [o22]; exact ⟨by omega, fun k => by rw [if_neg (by omega)]⟩
  | succ m ih =>
    intro f a b j n hab hl hl2 hm hjn hn
    rw [o22]
    by_cases hj : j < n
    · simp only [u_lt' (show j < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega), hj, if_true, u_add]
      simp only [show (u 0 == 0) = true from rfl, if_true]
      rw [show u j + 1 = u (j + 1) from u_add j 1, bget_u f (by omega)]
      have s0 := o0_step (b := f) (j := b + j) hl hl2 (f.getD (a + j) 0)
      have := ih (o0 f (u (b + j)) (f.getD (a + j) 0)) a b (j + 1) n hab (by rw [s0.1]; omega) (by rw [s0.1]; omega)
        (by omega) (by omega) hn
      refine ⟨by rw [this.1, s0.1]; omega, fun k => ?_⟩
      rw [this.2, s0.2, s0.2]
      repeat' split
      all_goals first | rfl | omega | (congr 1; omega)
    · simp only [u_lt' (show j < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega), hj, if_false]
      exact ⟨by omega, fun k => by rw [if_neg (by omega)]⟩

theorem o22_swap : ∀ (m : Nat) (f : Buf) (a b j n : Nat), a + n ≤ b → b + n ≤ f.length → f.length < 2 ^ 62 → n - j ≤ m →
    j ≤ n → b + n < 2 ^ 62 →
    (o22 m f (u a) (u b) (u j) (u n) (u 1)).length = f.length ∧
    ∀ k, (o22 m f (u a) (u b) (u j) (u n) (u 1)).getD k 0 =
      if a + j ≤ k ∧ k < a + n then f.getD (b + (k - a)) 0
      else if b + j ≤ k ∧ k < b + n then f.getD (a + (k - b)) 0 else f.getD k 0 := by
  intro m; induction m with
  | zero => intro f a b j n _ hl _ hm hjn _; rw [o22]; exact ⟨rfl, fun k => by rw [if_neg (by omega), if_neg (by omega)]⟩
  | succ m ih =>
    intro f a b j n hab hl hl2 hm hjn hn
    rw [o22]
    by_cases hj : j < n
    · simp only [u_lt' (show j < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega), hj, if_true, u_add]
      simp only [show (u 1 == 0) = false from rfl, show (u 1 == 1) = true from rfl, Bool.false_eq_true,
        if_false, if_true]
      rw [show u j + 1 = u (j + 1) from u_add j 1, bget_u f (by omega), bget_u f (by omega), bset_u _ (by omega),
        bset_u _ (by omega)]
      generalize hf1 : (f.set (a + j) (f.getD (b + j) 0)).set (b + j) (f.getD (a + j) 0) = f1
      have g1 : f1.length = f.length := by rw [← hf1]; simp
      have g2 : ∀ k, f1.getD k 0 = if k = b + j then f.getD (a + j) 0 else if k = a + j then f.getD (b + j) 0 else f.getD k 0 := by
        intro k; rw [← hf1, getD_set, getD_set]
        by_cases h1 : k = b + j
        · rw [if_pos ⟨h1.symm, by simp; omega⟩, if_pos h1]
        · rw [if_neg (fun h => h1 h.1.symm), if_neg h1]
          by_cases h2 : k = a + j
          · rw [if_pos ⟨h2.symm, by omega⟩, if_pos h2]
          · rw [if_neg (fun h => h2 h.1.symm), if_neg h2]
      have := ih f1 a b (j + 1) n hab (by omega) (by omega) (by omega) (by omega) hn
      refine ⟨by rw [this.1, g1], fun k => ?_⟩
      rw [this.2, g2, g2, g2]
      repeat' split
      all_goals first | rfl | omega | (congr 1; omega)
    · simp only [u_lt' (show j < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega), hj, if_false]
      exact ⟨trivial, fun k => by rw [if_neg (by omega), if_neg (by omega)]⟩

theorem o22_or : ∀ (m : Nat) (f : Buf) (a b j n : Nat), a + n ≤ b → b + n ≤ f.length → f.length < 2 ^ 62 → n - j ≤ m →
    j ≤ n → b + n < 2 ^ 62 →
    (o22 m f (u a) (u b) (u j) (u n) (u 2)).length = f.length ∧
    ∀ k, (o22 m f (u a) (u b) (u j) (u n) (u 2)).getD k 0 =
      if a + j ≤ k ∧ k < a + n then f.getD k 0 ||| f.getD (b + (k - a)) 0 else f.getD k 0 := by
  intro m; induction m with
  | zero => intro f a b j n _ hl _ hm hjn _; rw [o22]; exact ⟨rfl, fun k => by rw [if_neg (by omega)]⟩
  | succ m ih =>
    intro f a b j n hab hl hl2 hm hjn hn
    rw [o22]
    by_cases hj : j < n
    · simp only [u_lt' (show j < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega), hj, if_true, u_add]
      simp only [show (u 2 == 0) = false from rfl, show (u 2 == 1) = false from rfl,
        show (u 2 == 2) = true from rfl, Bool.false_eq_true, if_false, if_true]
      rw [show u j + 1 = u (j + 1) from u_add j 1, bget_u f (by omega), bget_u f (by omega), bset_u _ (by omega)]
      have := ih (f.set (a + j) (f.getD (a + j) 0 ||| f.getD (b + j) 0)) a b (j + 1) n hab (by simp; omega)
        (by simp; omega) (by omega) (by omega) hn
      refine ⟨by rw [this.1]; simp, fun k => ?_⟩
      rw [this.2]; simp only [getD_set]
      repeat' split
      all_goals first | rfl | omega | (congr 1 <;> omega) | (congr 2 <;> omega) | (simp_all; omega)
    · simp only [u_lt' (show j < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega), hj, if_false]
      exact ⟨trivial, fun k => by rw [if_neg (by omega)]⟩

/-- clear the dead flags (loop arms) -/
theorem rf_zero {W : WCx} {f : Buf} {A : AS} (hF : RF W f A) (hB : Bnd W A) :
    RF W (o22 16777216 f (u W.ns) (u W.ns) (u 0) (u W.ns) (u 3)) { A with F := List.replicate W.ns false } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hF
  have hns := hB.1
  have z := o22_zero 16777216 f W.ns W.ns 0 W.ns (by have := Nat.zero_le (W.ns * A.sn.length); omega) h4
    (by omega) (by omega) (by omega)
  refine ⟨by simp, h2, by rw [z.1]; exact h3, by rw [z.1]; exact h4, fun q hq => ?_, fun q hq => ?_, fun j hj q hq => ?_⟩
  · rw [z.2, if_neg (by omega)]; exact h5 q hq
  · rw [z.2, if_pos (by omega)]; simp [List.getD_eq_getElem?_getD, hq, b2n]; rfl
  · rw [z.2, if_neg (by have : 0 ≤ W.ns * j := Nat.zero_le _; omega)]; exact h7 j hj q hq

theorem mul_le' {ns j k : Nat} (h : j ≤ k) : ns * j ≤ ns * k := Nat.mul_le_mul_left ns h

/-- push a snapshot of the flags (IF: before the then-branch) -/
theorem rf_snap {W : WCx} {f : Buf} {A : AS} (hF : RF W f A) (hB : Bnd W A) :
    RF W (o22 16777216 f (u W.ns) (u (2 * W.ns + W.ns * A.sn.length)) (u 0) (u W.ns) (u 0)) { A with sn := A.sn ++ [A.F] } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hF
  have hns := hB.1; have hsn := hB.2.2.2.2.2.2.1
  have hb : W.ns * A.sn.length ≤ W.ns * 2 ^ 30 := mul_le' hsn
  have z : _ ∧ ∀ k, _ := o22_copy 16777216 f W.ns (2 * W.ns + W.ns * A.sn.length) 0 W.ns (by omega) (by omega) h4 (by omega) (by omega)
    (by omega)
  have hm : W.ns * (A.sn.length + 1) = W.ns * A.sn.length + W.ns := Nat.mul_succ _ _
  refine ⟨h1, ?_, ?_, ?_, fun q hq => ?_, fun q hq => ?_, fun j hj q hq => ?_⟩
  · intro l hl; rcases List.mem_append.mp hl with h | h
    · exact h2 l h
    · simp at h; rw [h]; exact h1
  · rw [z.1]; simp; omega
  · rw [z.1]; omega
  · rw [z.2, if_neg (by omega)]; exact h5 q hq
  · rw [z.2, if_neg (by omega)]; exact h6 q hq
  · simp only [List.length_append, List.length_singleton] at hj
    rw [z.2]
    by_cases hjl : j = A.sn.length
    · subst hjl
      rw [if_pos (by omega), show 2 * W.ns + W.ns * A.sn.length + q - (2 * W.ns + W.ns * A.sn.length) = q by omega, h6 q hq]
      simp [List.getD_eq_getElem?_getD]
    · have hj' : j < A.sn.length := by omega
      have : W.ns * j + W.ns ≤ W.ns * A.sn.length := by rw [← Nat.mul_succ]; exact mul_le' hj'
      rw [if_neg (by omega), h7 j hj' q hq]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj']

/-- swap the flags with the top snapshot (IF: between the branches) -/
theorem rf_swap {W : WCx} {f : Buf} {A : AS} (hF : RF W f A) (hB : Bnd W A) {sn0 : List (List Bool)} {S : List Bool}
    (hsn : A.sn = sn0 ++ [S]) :
    RF W (o22 16777216 f (u W.ns) (u (2 * W.ns + W.ns * sn0.length)) (u 0) (u W.ns) (u 1)) { A with F := S, sn := sn0 ++ [A.F] } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hF
  have hns := hB.1; have hsnb := hB.2.2.2.2.2.2.1
  rw [hsn] at h2 h3 h7 hsnb; simp only [List.length_append, List.length_singleton] at h3 h7 hsnb
  have hm : W.ns * (sn0.length + 1) = W.ns * sn0.length + W.ns := Nat.mul_succ _ _
  have hb : W.ns * sn0.length ≤ W.ns * 2 ^ 30 := mul_le' (by omega)
  have z : _ ∧ ∀ k, _ := o22_swap 16777216 f W.ns (2 * W.ns + W.ns * sn0.length) 0 W.ns (by omega) (by omega) h4 (by omega)
    (by omega) (by omega)
  have hS : S.length = W.ns := h2 S (by simp)
  unfold RF; dsimp only
  have gS : (sn0 ++ [S]).getD sn0.length [] = S := by simp [List.getD_eq_getElem?_getD]
  refine ⟨hS, ?_, ?_, ?_, fun q hq => ?_, fun q hq => ?_, fun j hj q hq => ?_⟩
  · intro l hl; rcases List.mem_append.mp hl with h | h
    · exact h2 l (by simp [h])
    · simp at h; rw [h]; exact h1
  · rw [z.1]; simp; omega
  · rw [z.1]; omega
  · rw [z.2, if_neg (by omega), if_neg (by omega)]; exact h5 q hq
  · rw [z.2, if_pos (by omega), show 2 * W.ns + W.ns * sn0.length + (W.ns + q - W.ns) = 2 * W.ns + W.ns * sn0.length + q by omega,
      h7 sn0.length (by omega) q hq, gS]
  · simp only [List.length_append, List.length_singleton] at hj
    rw [z.2]
    by_cases hjl : j = sn0.length
    · subst hjl
      rw [if_neg (by omega), if_pos (by omega), show W.ns + (2 * W.ns + W.ns * sn0.length + q - (2 * W.ns + W.ns * sn0.length)) =
        W.ns + q by omega, h6 q hq]
      simp [List.getD_eq_getElem?_getD]
    · have hj' : j < sn0.length := by omega
      have : W.ns * j + W.ns ≤ W.ns * sn0.length := by rw [← Nat.mul_succ]; exact mul_le' hj'
      rw [if_neg (by omega), if_neg (by omega), h7 j (by omega) q hq]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj']

theorem b2n_or (a b : Bool) : u (b2n a) ||| u (b2n b) = u (b2n (a || b)) := by cases a <;> cases b <;> decide

/-- or the top snapshot into the flags and drop it (IF: after the else-branch) -/
theorem rf_or {W : WCx} {f : Buf} {A : AS} (hF : RF W f A) (hB : Bnd W A) {sn0 : List (List Bool)} {S : List Bool}
    (hsn : A.sn = sn0 ++ [S]) :
    RF W (o22 16777216 f (u W.ns) (u (2 * W.ns + W.ns * sn0.length)) (u 0) (u W.ns) (u 2))
      { A with F := List.zipWith (· || ·) A.F S, sn := sn0 } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hF
  have hns := hB.1; have hsnb := hB.2.2.2.2.2.2.1
  rw [hsn] at h2 h3 h7 hsnb; simp only [List.length_append, List.length_singleton] at h3 h7 hsnb
  have hm : W.ns * (sn0.length + 1) = W.ns * sn0.length + W.ns := Nat.mul_succ _ _
  have hb : W.ns * sn0.length ≤ W.ns * 2 ^ 30 := mul_le' (by omega)
  have z : _ ∧ ∀ k, _ := o22_or 16777216 f W.ns (2 * W.ns + W.ns * sn0.length) 0 W.ns (by omega) (by omega) h4 (by omega)
    (by omega) (by omega)
  have hS : S.length = W.ns := h2 S (by simp)
  unfold RF; dsimp only
  refine ⟨by simp [h1, hS], fun l hl => h2 l (by simp [hl]), ?_, ?_, fun q hq => ?_, fun q hq => ?_, fun j hj q hq => ?_⟩
  · rw [z.1]; have : W.ns * sn0.length ≤ W.ns * sn0.length + W.ns := by omega
    omega
  · rw [z.1]; omega
  · rw [z.2, if_neg (by omega)]; exact h5 q hq
  · rw [z.2, if_pos (by omega), h6 q hq,
      show 2 * W.ns + W.ns * sn0.length + (W.ns + q - W.ns) = 2 * W.ns + W.ns * sn0.length + q by omega,
      h7 sn0.length (by omega) q hq, b2n_or]
    congr 2
    simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, show q < A.F.length by omega, show q < S.length by omega]
  · have : W.ns * j + W.ns ≤ W.ns * sn0.length := by rw [← Nat.mul_succ]; exact mul_le' hj
    rw [z.2, if_neg (by omega), h7 j (by omega) q hq]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

end OwnP
