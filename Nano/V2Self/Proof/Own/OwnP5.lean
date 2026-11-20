/- Nano/V2Self/Proof/Own/OwnP5: entry pushes: `o6` (one entry), `o27` (= `OwnSpec.locE`), `o20` (a callee's result kinds). -/
import Nano.V2Self.Proof.Own.OwnP4
namespace OwnP
open C OwnSpec

theorem rs_es {W : WCx} {s : Buf} {A : AS} (hS : RS W s A) (es' : List Nat) (hl : es'.length < 2 ^ 62) :
    RS W (bset s (u 7) (u es'.length)) { A with es := es' } :=
  rs_set hS (r := 7) (by omega) _ (by simp [regL]) rfl

theorem rv_push {v : Buf} {A : AS} (hV : RV v A) (e : Nat) (hl : A.es.length < 2 ^ 40) :
    RV (o0 v (u A.es.length) (u e)) { A with es := A.es ++ [e] } := by
  obtain ⟨h1, h2, h3⟩ := hV
  have := o0_step (b := v) (j := A.es.length) h1 h2 (u e)
  refine ⟨by simp; omega, by omega, fun j hj => ?_⟩
  rw [this.2]; simp only [List.length_append, List.length_singleton] at hj
  by_cases hje : j = A.es.length
  · subst hje; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg hje, h3 j (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show j < A.es.length by omega)]

theorem bnd_push {W : WCx} {A : AS} (hB : Bnd W A) {e : Nat} (he : e < 2 ^ 30) (hl : A.es.length < 2 ^ 24) :
    Bnd W { A with es := A.es ++ [e] } := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hB
  refine ⟨b1, b2, b3, b4, b5, b6, b7, by simp; omega, fun x hx => ?_, b10, b11⟩
  rcases List.mem_append.mp hx with h | h
  · exact b9 x h
  · simp at h; omega

/-- `o6`: push one entry (or an error at the 2^24 cap) -/
theorem o6_ok {W : WCx} {s v : Buf} {A : AS} (hS : RS W s A) (hV : RV v A) (hB : Bnd W A) {e : Nat} (he : e < 2 ^ 30) :
    (A.es.length < 2 ^ 24 ∧ o6 s v (u e) = (bset s (u 7) (u (A.es.length + 1)), o0 v (u A.es.length) (u e)) ∧
      RS W (bset s (u 7) (u (A.es.length + 1))) { A with es := A.es ++ [e] } ∧
      RV (o0 v (u A.es.length) (u e)) { A with es := A.es ++ [e] } ∧ Bnd W { A with es := A.es ++ [e] }) ∨
    bget (o6 s v (u e)).1 1 = 1 := by
  have h7 := (regs hS).2.2.2.2.2.2.1
  have hes := hB.2.2.2.2.2.2.2.1
  unfold o6; simp only [lit] at h7 ⊢; simp only [h7]
  by_cases hl : A.es.length < 2 ^ 24
  · left
    simp only [u_lt' (show A.es.length < 2 ^ 64 by omega) (show 16777216 < 2 ^ 64 by omega), show A.es.length < 16777216 by omega,
      if_true, u_add]
    refine ⟨trivial, trivial, ?_, rv_push hV e (by omega), bnd_push hB he hl⟩
    have := rs_es hS (A.es ++ [e]) (by simp; omega); simpa using this
  · right
    simp only [u_lt' (show A.es.length < 2 ^ 64 by omega) (show 16777216 < 2 ^ 64 by omega), show ¬ A.es.length < 16777216 by omega,
      if_false]
    exact err_o5 (by have := hS.1; omega)

theorem len_bset (s : Buf) (i v : UInt64) : (bset s i v).length = s.length := by simp [bset]

theorem err_bset {s : Buf} {i v : UInt64} (hi : i ≠ 1) (h : bget s 1 = 1) : bget (bset s i v) 1 = 1 := by
  simp only [bget, bset] at h ⊢; rw [getD_set]
  have : i.toNat ≠ 1 := fun e => hi (UInt64.toNat_inj.mp (by rw [e]; rfl))
  rw [if_neg (fun hc => this hc.1)]; exact h

/-- an error stays through `o6` -/
theorem o6_err {s v : Buf} {e : UInt64} (hl : 6 ≤ s.length) (h : bget s 1 = 1) :
    bget (o6 s v e).1 1 = 1 ∧ 6 ≤ (o6 s v e).1.length := by
  unfold o6; dsimp only; split
  · exact ⟨err_bset (by decide) h, by simp [len_bset]; omega⟩
  · exact ⟨err_o5 hl, by simp [o5, len_bset]; omega⟩

theorem o6_len {s v : Buf} {e : UInt64} : (o6 s v e).1.length = s.length := by
  unfold o6; dsimp only; split <;> simp [o5, len_bset]

theorem o27_err (f : Buf) (x w : UInt64) : ∀ (n : Nat) (s v : Buf) (j : UInt64), 6 ≤ s.length → bget s 1 = 1 →
    bget (o27 n s f v x j w).1 1 = 1 := by
  intro n; induction n with
  | zero => intro s v j hl _; simp only [o27]; exact err_o5 hl
  | succ n ih =>
    intro s v j hl h; rw [o27]; dsimp only; split
    · have := o6_err (v := v) (e := bget f (x + j) + 4 * (x + j + 1)) hl h
      revert this; generalize o6 s v (bget f (x + j) + 4 * (x + j + 1)) = z; obtain ⟨s1, v1⟩ := z
      intro ⟨h1, h2⟩; exact ih s1 v1 _ h2 h1
    · exact h

theorem locE_drop {K : List Nat} {x w j : Nat} (hj : j < w) :
    (locE K x w).drop j = (K.getD (x + j) 0 + 4 * (x + j + 1)) :: (locE K x w).drop (j + 1) := by
  have hl : j < (locE K x w).length := by simp [locE]; exact hj
  rw [drop_cons hl]; congr 1
  simp [locE, List.getD_eq_getElem?_getD, List.getElem?_range hj]

/-- `o27` pushes the entries of `LOCAL x w` from j (or an error) -/
theorem o27_ok {W : WCx} {f : Buf} {x w : Nat} (hxw : x + w ≤ W.ns) : ∀ (n : Nat) (A : AS) (s v : Buf) (j : Nat),
    RS W s A → RF W f A → RV v A → Bnd W A → j ≤ w →
    (∃ s' v', o27 n s f v (u x) (u j) (u w) = (s', v') ∧ RS W s' { A with es := A.es ++ (locE W.K x w).drop j } ∧
      RV v' { A with es := A.es ++ (locE W.K x w).drop j } ∧ Bnd W { A with es := A.es ++ (locE W.K x w).drop j }) ∨
    bget (o27 n s f v (u x) (u j) (u w)).1 1 = 1 := by
  intro n
  induction n with
  | zero => intro A s v j hS _ _ _ _; right; simp only [o27]; exact err_o5 (by have := hS.1; omega)
  | succ n ih =>
    intro A s v j hS hF hV hB hj
    have hns := hB.1
    have hnsK : W.ns = W.K.length := rfl
    rw [o27]; simp only [lit]
    by_cases hjw : j < w
    rotate_left
    · have : j = w := by omega
      subst this
      have hd : (locE W.K x j).drop j = [] := List.drop_of_length_le (by simp [locE])
      left; refine ⟨s, v, ?_, by simpa [hd] using hS, by simpa [hd] using hV, by simpa [hd] using hB⟩
      simp only [u_lt' (show j < 2 ^ 64 by omega) (show j < 2 ^ 64 by omega), Nat.lt_irrefl, if_false]
    simp only [u_lt' (show j < 2 ^ 64 by omega) (show w < 2 ^ 64 by omega), hjw, if_true, u_add, u_mul]
    rw [bget_u f (by omega), hF.2.2.2.2.1 (x + j) (by omega), u_add]
    have hk : W.K.getD (x + j) 0 ≤ 2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show x + j < W.K.length by omega)]
      exact hB.2.2.1 _ (List.getElem_mem _)
    generalize hE : W.K.getD (x + j) 0 + 4 * (x + j + 1) = e
    have he : e < 2 ^ 30 := by omega
    rcases o6_ok hS hV hB he with ⟨hl, ho6, hS1, hV1, hB1⟩ | herr
    · rw [ho6]; simp only
      have hF1 : RF W f { A with es := A.es ++ [e] } := hF
      rcases ih { A with es := A.es ++ [e] } _ _ (j + 1) hS1 hF1 hV1 hB1 (by omega) with ⟨s', v', h1, h2, h3, h4⟩ | h
      · have key : A.es ++ (locE W.K x w).drop j = (A.es ++ [e]) ++ (locE W.K x w).drop (j + 1) := by
          rw [locE_drop hjw, hE]; simp
        left; refine ⟨s', v', h1, ?_, ?_, ?_⟩ <;> rw [key] <;> assumption
      · right; exact h
    · right
      have hl6 : 6 ≤ (o6 s v (u e)).1.length := by rw [o6_len]; have := hS.1; omega
      revert herr hl6; generalize o6 s v (u e) = z; obtain ⟨s1, v1⟩ := z; intro herr hl6
      exact o27_err f _ _ n s1 v1 _ hl6 herr

theorem o20_err (t : Buf) (a n0 : UInt64) : ∀ (n : Nat) (s v : Buf) (j : UInt64), 6 ≤ s.length → bget s 1 = 1 →
    bget (o20 n s v t a j n0).1 1 = 1 := by
  intro n; induction n with
  | zero => intro s v j hl _; simp only [o20]; exact err_o5 hl
  | succ n ih =>
    intro s v j hl h; rw [o20]; dsimp only; split
    · have := o6_err (v := v) (e := bget t (a + j)) hl h
      revert this; generalize o6 s v (bget t (a + j)) = z; obtain ⟨s1, v1⟩ := z
      intro ⟨h1, h2⟩; exact ih s1 v1 _ h2 h1
    · exact h

/-- `o20` pushes `L.drop j` read from `t` at `a` (or an error) -/
theorem o20_ok {W : WCx} {a : Nat} {L : List Nat} (hL : ∀ j < L.length, W.t.getD (a + j) 0 = u (L.getD j 0))
    (hLv : ∀ k ∈ L, k ≤ 1) (ha : a + L.length < 2 ^ 40) : ∀ (n : Nat) (A : AS) (s v : Buf) (j : Nat),
    RS W s A → RV v A → Bnd W A → j ≤ L.length →
    (∃ s' v', o20 n s v W.t (u a) (u j) (u L.length) = (s', v') ∧ RS W s' { A with es := A.es ++ L.drop j } ∧
      RV v' { A with es := A.es ++ L.drop j } ∧ Bnd W { A with es := A.es ++ L.drop j }) ∨
    bget (o20 n s v W.t (u a) (u j) (u L.length)).1 1 = 1 := by
  intro n
  induction n with
  | zero => intro A s v j hS _ _ _; right; simp only [o20]; exact err_o5 (by have := hS.1; omega)
  | succ n ih =>
    intro A s v j hS hV hB hj
    rw [o20]; simp only [lit]
    by_cases hjw : j < L.length
    rotate_left
    · have : j = L.length := by omega
      subst this
      have hd : L.drop L.length = [] := List.drop_length
      left; refine ⟨s, v, ?_, by simpa [hd] using hS, by simpa [hd] using hV, by simpa [hd] using hB⟩
      simp only [u_lt' (show L.length < 2 ^ 64 by omega) (show L.length < 2 ^ 64 by omega), Nat.lt_irrefl, if_false]
    simp only [u_lt' (show j < 2 ^ 64 by omega) (show L.length < 2 ^ 64 by omega), hjw, if_true, u_add]
    rw [bget_u _ (by omega), hL j hjw]
    have hk : L.getD j 0 ≤ 1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjw]; exact hLv _ (List.getElem_mem _)
    generalize hE : L.getD j 0 = e at hk
    rcases o6_ok hS hV hB (e := e) (by omega) with ⟨hl, ho6, hS1, hV1, hB1⟩ | herr
    · rw [ho6]; simp only
      rcases ih { A with es := A.es ++ [e] } _ _ (j + 1) hS1 hV1 hB1 (by omega) with ⟨s', v', h1, h2, h3, h4⟩ | h
      · have key : A.es ++ L.drop j = (A.es ++ [e]) ++ L.drop (j + 1) := by
          rw [drop_cons hjw, hE]; simp
        left; refine ⟨s', v', h1, ?_, ?_, ?_⟩ <;> rw [key] <;> assumption
      · right; exact h
    · right
      have hl6 : 6 ≤ (o6 s v (u e)).1.length := by rw [o6_len]; have := hS.1; omega
      revert herr hl6; generalize o6 s v (u e) = z; obtain ⟨s1, v1⟩ := z; intro herr hl6
      exact o20_err _ _ _ n s1 v1 _ hl6 herr

end OwnP
