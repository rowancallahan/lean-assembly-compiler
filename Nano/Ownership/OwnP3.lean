/- Nano/Ownership/OwnP3: the inner loops of the walk in mode 0, each = an `OwnSpec` function or an error. -/
import Nano.Ownership.OwnP2
namespace OwnP
open C OwnSpec

theorem es_get {v : Buf} {A : AS} (hV : RV v A) {q : Nat} (hq : q < A.es.length) (hq' : q < 2 ^ 64) :
    bget v (u q) = u (A.es.getD q 0) := by rw [bget_u v hq']; exact hV.2.2 q hq

theorem es_lt {W : WCx} {A : AS} (hB : Bnd W A) {q : Nat} : A.es.getD q 0 < 2 ^ 30 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : A.es[q]? with
  | none => simp
  | some e => simp; exact hB.2.2.2.2.2.2.2.2.1 e (List.mem_of_getElem? h)

theorem drop_cons {l : List Nat} {q : Nat} (h : q < l.length) : l.drop q = l.getD q 0 :: l.drop (q + 1) := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem dest_le {W : WCx} {A : AS} (hT : RT W) (hB : Bnd W A) {r : Fr} (hr : r.ok W) (o : Nat) :
    dest (dsOf W r) o ≤ 4 := by
  unfold dest dsOf
  have gl : ∀ (l : List Nat), (∀ k ∈ l, k ≤ 4) → l.getD o 4 ≤ 4 := by
    intro l hl; rw [List.getD_eq_getElem?_getD]; cases h : l[o]? with
    | none => simp
    | some e => simpa using hl e (List.mem_of_getElem? h)
  by_cases h0 : r.d = 0
  · simp [h0]
  by_cases h1 : r.d = 1
  · simp only [h0, h1, if_false, if_true]; exact gl _ (by simp)
  by_cases h2 : r.d = 2
  · simp only [h0, h1, h2, if_false, if_true]
    exact gl _ (by intro k hk; unfold dsP at hk; split at hk <;> simp at hk <;> omega)
  by_cases h3 : r.d = 3
  · simp only [h0, h1, h2, h3, if_false, if_true]
    obtain ⟨-, -, -, -, -, -, -, -, -, hk, -⟩ := hT.2.2.2 r.a (hr.2.2 h3)
    exact gl _ (fun k h => by have := hk k h; omega)
  · simp only [h0, h1, h2, h3, if_false]
    exact gl _ (by
      intro k hk; unfold stD at hk; rw [List.mem_map] at hk; obtain ⟨a, ha, rfl⟩ := hk
      have := hB.2.2.1 a (List.mem_of_mem_drop (List.mem_of_mem_take ha))
      split <;> omega)

/-- `o14` = `okAll` on the entries from q, or an error -/
theorem o14_ok {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hr : r.ok W) : ∀ (n q : Nat), r.vb ≤ q → q ≤ A.es.length →
    (o14 n s f v W.t (u q) (u A.es.length) = (s, f) ∧ okAll (dsOf W r) A.F (q - r.vb) (A.es.drop q) = true) ∨
    bget (o14 n s f v W.t (u q) (u A.es.length)).1 1 = 1 := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  have hl := hS.1
  intro n
  induction n with
  | zero => intro q _ _; right; simp only [o14]; exact err_o5 (by omega)
  | succ n ih =>
    intro q hq1 hq2
    have hes := hB.2.2.2.2.2.2.2.1
    have h4 := o1_eq hS hΦ hB.2.2.2.2.2.1 (k := 4) (by omega)
    have h8 := (regs hS).2.2.2.2.2.2.2.1
    simp only [Fr.fld] at h4
    have hsm := hB.2.2.2.2.2.2.2.2.2.1 r (by rw [hΦ]; simp)
    have hvb := hsm 4 (by omega); simp only [Fr.fld] at hvb
    rw [o14]; simp only [lit] at h8 ⊢
    by_cases hqb : q < A.es.length
    · simp only [u_lt' (show q < 2 ^ 64 by omega) (show A.es.length < 2 ^ 64 by omega), hqb, if_true]
      simp only [h4, h8, u_sub' hq1 (by omega), es_get hV hqb (by omega), o9_eq hS hF hT hB hΦ hr (o := q - r.vb) (by omega),
        beq_self_eq_true, if_true]
      have hd : dest (dsOf W r) (q - r.vb) < 2 ^ 30 := by have := dest_le hT hB hr (q - r.vb); omega
      rw [o12_eq hS hF hB (es_lt hB) hd, drop_cons hqb]
      simp only [okAll]
      by_cases hok : ok1 A.F (A.es.getD q 0) (dest (dsOf W r) (q - r.vb)) = true
      · simp only [hok, if_true, Bool.true_and, u_add]
        rcases ih (q + 1) (by omega) (by omega) with h | h
        · left; rw [h.1]; refine ⟨rfl, ?_⟩; rw [show q - r.vb + 1 = q + 1 - r.vb by omega]; exact h.2
        · right; exact h
      · simp only [hok, Bool.false_eq_true, if_false]; right
        rw [show (u 0 == u 1) = false by decide]; simp only [Bool.false_eq_true, if_false]
        rw [← lit 1]; exact err_set1 (by omega)
    · have : q = A.es.length := by omega
      subst this
      left; simp only [u_lt' (show A.es.length < 2 ^ 64 by omega) (show A.es.length < 2 ^ 64 by omega), Nat.lt_irrefl,
        if_false, List.drop_length, okAll, and_self]

/-! ## state updates used by the loops -/
theorem rs_congr {W : WCx} {s : Buf} {A A' : AS} (h : RS W s A) (hi : A'.i = A.i) (hΦ : A'.Φ = A.Φ)
    (he : A'.es.length = A.es.length) (hsn : A'.sn.length = A.sn.length) (hph : A'.ph = A.ph) : RS W s A' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have : regL W A' = regL W A := by simp [regL, hi, hΦ, he, hsn, hph]
  exact ⟨by rw [hΦ]; exact h1, h2, by rw [this]; exact h3, by rw [hΦ]; exact h4⟩

theorem rv_set {v : Buf} {A : AS} (hV : RV v A) {q : Nat} (hq : q < A.es.length) {w : Nat} :
    RV (bset v (u q) (u w)) { A with es := A.es.set q w } := by
  obtain ⟨h1, h2, h3⟩ := hV
  rw [bset_u v (by omega)]
  refine ⟨by simp; omega, by simp; omega, fun j hj => ?_⟩
  simp only [List.length_set] at hj
  rw [getD_set]
  by_cases hjq : q = j
  · subst hjq; simp only [show q < v.length by omega, and_self, if_true, List.getD_eq_getElem?_getD]
    rw [List.getElem?_set_self hq]; rfl
  · simp only [hjq, false_and, if_false]; rw [h3 j hj]
    simp [List.getD_eq_getElem?_getD, List.getElem?_set, hjq]

theorem rf_dead {W : WCx} {f : Buf} {A : AS} (hF : RF W f A) (hns : W.ns < 2 ^ 20) {x : Nat} (hx : x < W.ns) :
    RF W (bset f (u (W.ns + x)) (u 1)) { A with F := A.F.set x true } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hF
  rw [bset_u f (by omega)]
  refine ⟨by simp [h1], h2, by simp; exact h3, by simp; exact h4, fun q hq => ?_, fun q hq => ?_, fun j hj q hq => ?_⟩
  · rw [getD_set, if_neg (by omega)]; exact h5 q hq
  · rw [getD_set]
    by_cases hqx : x = q
    · subst hqx; simp [show W.ns + x < f.length by omega, List.getD_eq_getElem?_getD, show x < A.F.length by omega, b2n]
    · rw [if_neg (by omega), h6 q hq]; simp [List.getD_eq_getElem?_getD, List.getElem?_set, hqx]
  · rw [getD_set, if_neg (by omega)]; exact h7 j hj q hq

theorem set_drop (l : List Nat) (q w : Nat) : (l.set q w).drop (q + 1) = l.drop (q + 1) := by
  apply List.ext_getElem?; intro j; simp [List.getElem?_set]; omega

theorem set_take {l : List Nat} {q : Nat} (h : q < l.length) (w : Nat) : (l.set q w).take (q + 1) = l.take q ++ [w] := by
  rw [List.take_add_one, List.getElem?_set_self (by simpa using h), List.take_set_of_le (by omega)]; rfl

theorem take_succ' {l : List Nat} {q : Nat} (h : q < l.length) : l.take (q + 1) = l.take q ++ [l.getD q 0] := by
  rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem bnd_es_set {W : WCx} {A : AS} (hB : Bnd W A) {q w : Nat} (hw : w < 2 ^ 30) :
    Bnd W { A with es := A.es.set q w } := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hB
  refine ⟨b1, b2, b3, b4, b5, b6, b7, by simpa using b8, fun e he => ?_, b10, b11⟩
  rcases List.mem_or_eq_of_mem_set he with h | h
  · exact b9 e h
  · omega

/-- `o15` = `tr` on the entries from q (in place), or an error -/
theorem o15_ok {W : WCx} {s : Buf} : ∀ (n : Nat) (A : AS) (f v : Buf) (q : Nat), RS W s A → RF W f A → RV v A →
    Bnd W A → q ≤ A.es.length →
    (∃ F' ks f' v', tr A.F (A.es.drop q) = some (F', ks) ∧ o15 n s f v (u q) (u A.es.length) = (s, (f', v')) ∧
      RF W f' { A with F := F' } ∧ RV v' { A with es := A.es.take q ++ ks }) ∨
    bget (o15 n s f v (u q) (u A.es.length)).1 1 = 1 := by
  intro n
  induction n with
  | zero => intro A f v q hS _ _ _ _; right; simp only [o15]; exact err_o5 (by have := hS.1; omega)
  | succ n ih =>
    intro A f v q hS hF hV hB hq
    have hl := hS.1
    have hes := hB.2.2.2.2.2.2.2.1
    have hns := hB.1
    have h8 := (regs hS).2.2.2.2.2.2.2.1
    have h6 := (regs hS).2.2.2.2.2.1
    have h2 := (regs hS).2.2.1
    rw [o15]; simp only [lit] at h8 h6 h2 ⊢
    by_cases hqb : q < A.es.length
    rotate_left
    · have : q = A.es.length := by omega
      subst this
      left; refine ⟨A.F, [], f, v, by simp [tr], ?_, by exact hF, by simpa using hV⟩
      simp only [u_lt' (show A.es.length < 2 ^ 64 by omega) (show A.es.length < 2 ^ 64 by omega), Nat.lt_irrefl, if_false]
    simp only [u_lt' (show q < 2 ^ 64 by omega) (show A.es.length < 2 ^ 64 by omega), hqb, if_true]
    have he := es_lt hB (q := q)
    generalize hE : A.es.getD q 0 = e at he
    simp only [es_get hV hqb (by omega), hE, h8, h6, h2]
    simp (disch := omega) only [u_lt', u_and3, u_shr2, u_beq, u_add]
    rw [drop_cons hqb, hE]
    by_cases e4 : e < 4
    · simp only [e4, if_true, tr, decide_true]
      by_cases e2 : e < 2
      · simp only [e2, if_true, show e ≤ 1 by omega]
        rcases ih A f v (q + 1) hS hF hV hB (by omega) with ⟨F', ks, f', v', h1, h2', h3, h4⟩ | h
        · left; refine ⟨F', e :: ks, f', v', by simp [h1], h2', h3, ?_⟩
          rw [take_succ' hqb, hE] at h4; simpa using h4
        · right; exact h
      · simp only [e2, if_false, show ¬ e ≤ 1 by omega]; right; rw [← lit 1]; exact err_set1 (by omega)
    simp only [e4, if_false]
    simp (disch := omega) only [u_sub', u_add]
    have hq64 : q < 2 ^ 64 := by omega
    by_cases k0 : e % 4 = 0
    · simp only [k0, decide_true, if_true, show ¬ (4 > e) by omega]
      have := ih { A with es := A.es.set q 0 } f (bset v (u q) (u 0)) (q + 1)
        (rs_congr hS rfl rfl (by simp) rfl rfl) hF (rv_set hV hqb) (bnd_es_set hB (by omega)) (by simp; omega)
      simp only [List.length_set, set_drop] at this
      rcases this with ⟨F', ks, f', v', h1, h2', h3, h4⟩ | h
      · left; refine ⟨F', 0 :: ks, f', v', by simp [tr, e4, k0, h1], h2', h3, ?_⟩
        rw [set_take hqb] at h4; simpa using h4
      · right; exact h
    by_cases k1 : e % 4 = 1
    · simp only [k0, k1, decide_true, decide_false, Bool.false_eq_true, if_true, if_false]
      have hx : e / 4 - 1 < 2 ^ 40 := by omega
      rw [o7_dead hS hF hB hx]
      by_cases hd : dead A.F (e / 4 - 1) = true
      · simp only [hd, Bool.not_true, Bool.false_eq_true, if_false]
        right; rw [if_neg (by decide)]; rw [← lit 1]; exact err_set1 (by omega)
      · simp only [hd, Bool.not_false, if_true]
        have hxn : e / 4 - 1 < W.ns := by
          rcases Nat.lt_or_ge (e / 4 - 1) W.ns with hc | hc
          · exact hc
          · exfalso; apply hd; unfold dead; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hF.1]; omega)]; rfl
        have := ih { A with F := A.F.set (e / 4 - 1) true, es := A.es.set q 1 } (bset f (u (W.ns + (e / 4 - 1))) (u 1))
          (bset v (u q) (u 1)) (q + 1) (rs_congr hS rfl rfl (by simp) rfl rfl) (rf_dead hF hns hxn) (rv_set hV hqb)
          (bnd_es_set hB (by omega)) (by simp; omega)
        simp only [List.length_set, set_drop] at this
        rcases this with ⟨F', ks, f', v', h1, h2', h3, h4⟩ | h
        · left; refine ⟨F', 1 :: ks, f', v', ?_, h2', h3, ?_⟩
          · simp [tr, e4, k0, k1, consume1, show dead A.F (e / 4 - 1) = false by simpa using hd, h1]
          · rw [set_take hqb] at h4; simp at h4; exact h4
        · right; exact h
    · simp only [k0, k1, decide_false, Bool.false_eq_true, if_false]
      right; rw [if_pos (by decide)]; rw [← lit 1]; exact err_set1 (by omega)

end OwnP
