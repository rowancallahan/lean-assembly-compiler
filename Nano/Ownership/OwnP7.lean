/- Nano/Ownership/OwnP7: branch join (`o25`, `o28` = `OwnSpec.join`) and the `let` check (`o26`). -/
import Nano.Ownership.OwnP6
namespace OwnP
open C OwnSpec

def mx (x y : UInt64) : UInt64 := if x < y then y else x

theorem mx_u {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : mx (u a) (u b) = u (max a b) := by
  unfold mx; simp only [u_lt' ha hb]
  by_cases h : a < b
  · rw [if_pos h, Nat.max_eq_right (by omega)]
  · rw [if_neg h, Nat.max_eq_left (by omega)]

/-- `o25` on lists -/
theorem o25_spec : ∀ (m : Nat) (v : Buf) (a b j w : Nat), a + w ≤ b → b + w ≤ v.length → v.length < 2 ^ 62 → w - j ≤ m →
    j ≤ w →
    (o25 m v (u a) (u b) (u j) (u w)).length = v.length ∧
    ∀ k, (o25 m v (u a) (u b) (u j) (u w)).getD k 0 =
      if a + j ≤ k ∧ k < a + w then mx (v.getD k 0) (v.getD (b + (k - a)) 0) else v.getD k 0 := by
  intro m; induction m with
  | zero => intro v a b j w _ _ _ hm hj; rw [o25]; exact ⟨rfl, fun k => by rw [if_neg (by omega)]⟩
  | succ m ih =>
    intro v a b j w hab hl hl2 hm hj
    rw [o25]
    by_cases hjw : j < w
    · simp only [u_lt' (show j < 2 ^ 64 by omega) (show w < 2 ^ 64 by omega), hjw, if_true, u_add]
      rw [show u j + 1 = u (j + 1) from u_add j 1, bget_u v (by omega), bget_u v (by omega)]
      have key : ∀ v' : Buf, v'.length = v.length → (∀ k, v'.getD k 0 = if k = a + j then mx (v.getD (a + j) 0) (v.getD (b + j) 0)
          else v.getD k 0) →
          (o25 m v' (u a) (u b) (u (j + 1)) (u w)).length = v.length ∧
          ∀ k, (o25 m v' (u a) (u b) (u (j + 1)) (u w)).getD k 0 =
            if a + j ≤ k ∧ k < a + w then mx (v.getD k 0) (v.getD (b + (k - a)) 0) else v.getD k 0 := by
        intro v' hl' hg
        have := ih v' a b (j + 1) w hab (by omega) (by omega) (by omega) (by omega)
        refine ⟨by rw [this.1, hl'], fun k => ?_⟩
        simp only [this.2, hg]
        repeat' split
        all_goals first | rfl | omega | (subst_vars; simp [Nat.add_sub_cancel_left])
      by_cases hxy : v.getD (a + j) 0 < v.getD (b + j) 0
      · simp only [hxy, if_true]
        rw [bset_u v (by omega)]
        refine key _ (by simp) (fun k => ?_)
        rw [getD_set]
        by_cases hk : k = a + j
        · subst hk; simp only [show a + j < v.length by omega, and_self, if_true, mx, hxy]
        · simp [Ne.symm hk, hk]
      · simp only [hxy, if_false]
        refine key _ rfl (fun k => ?_)
        by_cases hk : k = a + j
        · subst hk; simp only [if_true, mx, hxy, if_false]
        · simp [hk]
    · simp only [u_lt' (show j < 2 ^ 64 by omega) (show w < 2 ^ 64 by omega), hjw, if_false]
      exact ⟨trivial, fun k => by rw [if_neg (by omega)]⟩

theorem bnd_es {W : WCx} {A : AS} (hB : Bnd W A) (es' : List Nat) (hl : es'.length ≤ 2 ^ 24) (he : ∀ e ∈ es', e < 2 ^ 30) :
    Bnd W { A with es := es' } := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hB
  exact ⟨b1, b2, b3, b4, b5, b6, b7, hl, he, b10, b11⟩

theorem getD_app3 (pre t e : List Nat) (j : Nat) :
    (pre ++ t ++ e).getD j 0 = if j < pre.length then pre.getD j 0 else if j < pre.length + t.length then t.getD (j - pre.length) 0
      else e.getD (j - pre.length - t.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append]
  by_cases h1 : j < pre.length
  · simp [h1]
  · by_cases h2 : j < pre.length + t.length
    · simp [h1, show j - pre.length < t.length by omega, h2]
    · simp [h1, h2, show ¬ j - pre.length < t.length by omega]

/-- `o28` = `join` of the entries `t` (from a) and `e` (from m), result from a; or an error -/
theorem o28_ok {W : WCx} {s v : Buf} {A : AS} (hS : RS W s A) (hV : RV v A) (hB : Bnd W A) {pre t e : List Nat}
    (hes : A.es = pre ++ t ++ e) :
    (∃ k s' v', join t e = some k ∧ o28 s v (u pre.length) (u (pre.length + t.length)) (u A.es.length) = (s', v') ∧
      RS W s' { A with es := pre ++ k } ∧ RV v' { A with es := pre ++ k } ∧ Bnd W { A with es := pre ++ k }) ∨
    bget (o28 s v (u pre.length) (u (pre.length + t.length)) (u A.es.length)).1 1 = 1 := by
  have hl := hS.1
  have hesl := hB.2.2.2.2.2.2.2.1
  have hlen : A.es.length = pre.length + t.length + e.length := by rw [hes]; simp; omega
  have h8 := (regs hS).2.2.2.2.2.2.2.1
  unfold o28; simp only [lit] at h8 ⊢
  rw [u_beq (by omega) (by omega)]
  by_cases ht : t = []
  · subst ht; left
    refine ⟨e, s, v, by simp [join], by simp, ?_⟩
    have : pre ++ e = A.es := by rw [hes]; simp
    rw [this]; exact ⟨hS, hV, hB⟩
  have ht0 : t.length ≠ 0 := fun h => ht (List.eq_nil_of_length_eq_zero h)
  simp only [show ¬ (pre.length + t.length = pre.length) by omega, decide_false, Bool.false_eq_true, if_false]
  rw [u_beq (by omega) (by omega)]
  by_cases he : e = []
  · subst he; left
    refine ⟨t, s, v, by simp [join, ht], by simp [hlen], ?_⟩
    have : pre ++ t = A.es := by rw [hes]; simp
    rw [this]; exact ⟨hS, hV, hB⟩
  have he0 : e.length ≠ 0 := fun h => he (List.eq_nil_of_length_eq_zero h)
  simp only [show ¬ (A.es.length = pre.length + t.length) by omega, decide_false, Bool.false_eq_true, if_false]
  rw [u_sub' (by omega) (by omega), u_sub' (by omega) (by omega), u_beq (by omega) (by omega)]
  by_cases hte : pre.length + t.length - pre.length = A.es.length - (pre.length + t.length)
  · simp only [hte, decide_true, if_true]
    left
    have htl : t.length = e.length := by omega
    refine ⟨List.zipWith max t e, _, _, by simp [join, ht, he, htl], rfl, ?_, ?_, ?_⟩
    · have := rs_es hS (pre ++ List.zipWith max t e) (by simp; omega)
      have hz : (pre ++ List.zipWith max t e).length = pre.length + t.length := by simp [htl]
      rw [← hz]; exact this
    · obtain ⟨h1, h2, h3⟩ := hV
      have z := o25_spec 16777216 v pre.length (pre.length + t.length) 0 (A.es.length - (pre.length + t.length))
        (by omega) (by omega) h2 (by omega) (by omega)
      refine ⟨by simp; omega, by rw [z.1]; exact h2, fun j hj => ?_⟩
      simp only [List.length_append, List.length_zipWith] at hj
      dsimp only
      rw [z.2]
      by_cases hj1 : j < pre.length
      · rw [if_neg (by omega), h3 j (by omega), hes, getD_app3]
        simp [hj1, List.getD_eq_getElem?_getD, List.getElem?_append_left hj1]
      · rw [if_pos (by omega), h3 j (by omega), h3 _ (by omega), hes, getD_app3, getD_app3,
          if_neg hj1, if_pos (by omega), if_neg (by omega), if_neg (by omega)]
        have ht1 : (t.getD (j - pre.length) 0) < 2 ^ 30 := by
          have := es_lt hB (q := j); rw [hes, getD_app3, if_neg hj1, if_pos (by omega)] at this; exact this
        have he1 : (e.getD (pre.length + t.length + (j - pre.length) - pre.length - t.length) 0) < 2 ^ 30 := by
          have := es_lt hB (q := pre.length + t.length + (j - pre.length))
          rw [hes, getD_app3, if_neg (by omega), if_neg (by omega)] at this; exact this
        rw [mx_u (by omega) (by omega)]
        congr 1
        simp only [List.getD_eq_getElem?_getD]
        rw [show pre.length + t.length + (j - pre.length) - pre.length - t.length = j - pre.length by omega,
          List.getElem?_append_right (by omega), List.getElem?_zipWith,
          List.getElem?_eq_getElem (show j - pre.length < t.length by omega),
          List.getElem?_eq_getElem (show j - pre.length < e.length by omega)]
        simp
    · apply bnd_es hB _ (by simp; omega)
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hB.2.2.2.2.2.2.2.2.1 x (by rw [hes]; simp [h])
      · rcases List.mem_iff_getElem.mp h with ⟨i, hi, rfl⟩
        simp only [List.getElem_zipWith]
        simp only [List.length_zipWith] at hi
        have a1 := hB.2.2.2.2.2.2.2.2.1 (t[i]'(by omega)) (by rw [hes]; simp)
        have a2 := hB.2.2.2.2.2.2.2.2.1 (e[i]'(by omega)) (by rw [hes]; simp)
        omega
  · simp only [hte, decide_false, Bool.false_eq_true, if_false, h8, show (u 0 == u 0) = true from rfl, if_true]
    right; exact err_bset (by decide) (by rw [← lit 1]; exact err_set1 (by omega))

theorem notDeadR_iff (F : List Bool) (x : Nat) : ∀ w, notDeadR F x w = true ↔ ∀ i < w, dead F (x + i) = false
  | 0 => by simp [notDeadR]
  | w + 1 => by
    rw [notDeadR, Bool.and_eq_true, notDeadR_iff F x w]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hiw : i = w
      · subst hiw; simpa using h1
      · exact h2 i (by omega)
    · intro h; exact ⟨by simpa using h w (by omega), fun i hi => h i (by omega)⟩

/-- `o26` (mode 0): the `let` value's entries `kv` (from a) equal `K[x ..]` and the slots are live; or an error -/
theorem o26_ok {W : WCx} {s f v : Buf} {A : AS} (hS : RS W s A) (hF : RF W f A) (hV : RV v A) (hB : Bnd W A)
    {pre kv : List Nat} (hes : A.es = pre ++ kv) {x : Nat} (hx : x + kv.length ≤ W.ns) :
    ∀ (n j : Nat), j ≤ kv.length →
    (o26 n s f v (u x) (u j) (u kv.length) (u pre.length) = (s, f) ∧
      ∀ i, j ≤ i → i < kv.length → kv.getD i 0 = W.K.getD (x + i) 0 ∧ dead A.F (x + i) = false) ∨
    bget (o26 n s f v (u x) (u j) (u kv.length) (u pre.length)).1 1 = 1 := by
  have hl := hS.1
  have hns := hB.1
  have hesl := hB.2.2.2.2.2.2.2.1
  have h8 := (regs hS).2.2.2.2.2.2.2.1
  have hlen : A.es.length = pre.length + kv.length := by rw [hes]; simp
  have hnsK : W.ns = W.K.length := rfl
  intro n
  induction n with
  | zero => intro j hj; right; rw [o26]; exact err_o5 (by omega)
  | succ n ih =>
    intro j hj
    rw [o26]; simp only [lit] at h8 ⊢
    by_cases hjw : j < kv.length
    · simp only [u_lt' (show j < 2 ^ 64 by omega) (show kv.length < 2 ^ 64 by omega), hjw, if_true, u_add, h8,
        show (u 0 == u 0) = true from rfl]
      have hq : pre.length + j < A.es.length := by omega
      rw [es_get hV hq (by omega), bget_u f (by omega), hF.2.2.2.2.1 (x + j) (by omega)]
      have he := es_lt hB (q := pre.length + j)
      have hk : W.K.getD (x + j) 0 ≤ 2 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show x + j < W.K.length by omega)]
        exact hB.2.2.1 _ (List.getElem_mem _)
      have hkv : A.es.getD (pre.length + j) 0 = kv.getD j 0 := by
        rw [hes]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
      rw [u_beq (by omega) (by omega)]
      by_cases heq : A.es.getD (pre.length + j) 0 = W.K.getD (x + j) 0
      · simp only [heq, decide_true, if_true]
        rw [o7_dead hS hF hB (by omega)]
        by_cases hd : dead A.F (x + j) = true
        · simp only [hd, Bool.not_true, Bool.false_eq_true, if_false]; right; rw [← lit 1]; exact err_set1 (by omega)
        · simp only [hd, Bool.not_false, if_true]
          rcases ih (j + 1) (by omega) with ⟨h1, h2⟩ | h
          · left; refine ⟨h1, fun i hi1 hi2 => ?_⟩
            by_cases hij : i = j
            · subst hij; exact ⟨hkv ▸ heq, by simpa using hd⟩
            · exact h2 i (by omega) hi2
          · right; exact h
      · simp only [heq, decide_false, Bool.false_eq_true, if_false]; right; rw [← lit 1]; exact err_set1 (by omega)
    · have : j = kv.length := by omega
      subst this
      left; simp only [u_lt' (show kv.length < 2 ^ 64 by omega) (show kv.length < 2 ^ 64 by omega), Nat.lt_irrefl, if_false]
      exact ⟨trivial, fun i h1 h2 => absurd h2 (by omega)⟩

end OwnP
