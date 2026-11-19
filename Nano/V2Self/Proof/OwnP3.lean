/- Nano/V2Self/Proof/OwnP3: the inner loops of the walk in mode 0, each = an `OwnSpec` function or an error. -/
import Nano.V2Self.Proof.OwnP2
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
