/- Nano/V2Self/Proof/OwnP4: the end-of-list passes `o17` (= `OwnSpec.finC`), `o18` (= `finB`), `o19` (= `strip`). -/
import Nano.V2Self.Proof.OwnP3
namespace OwnP
open C OwnSpec

theorem own_iff (e : Nat) : own e = (decide (4 ≤ e) && decide (e % 4 = 1)) := by
  unfold own; by_cases h : 4 ≤ e <;> by_cases h2 : e % 4 = 1 <;> simp [h, h2]

/-- `o17` = `finC`, or an error -/
theorem o17_ok {W : WCx} {s v : Buf} {Φ0 : List Fr} {r : Fr} (hr : r.ok W) : ∀ (n : Nat) (A : AS) (f : Buf) (q : Nat),
    A.Φ = Φ0 ++ [r] → RS W s A → RF W f A → RV v A → RT W → Bnd W A → r.vb ≤ q → q ≤ A.es.length →
    (∃ F' f', finC (dsOf W r) A.F (q - r.vb) (A.es.drop q) = some F' ∧
      o17 n s f v W.t (u q) (u A.es.length) = (s, f') ∧ RF W f' { A with F := F' }) ∨
    bget (o17 n s f v W.t (u q) (u A.es.length)).1 1 = 1 := by
  intro n
  induction n with
  | zero => intro A f q _ hS _ _ _ _ _ _; right; simp only [o17]; exact err_o5 (by have := hS.1; omega)
  | succ n ih =>
    intro A f q hΦ hS hF hV hT hB hq1 hq
    have hl := hS.1
    have hes := hB.2.2.2.2.2.2.2.1
    have hns := hB.1
    have h6 := (regs hS).2.2.2.2.2.1
    have h4 := o1_eq hS hΦ hB.2.2.2.2.2.1 (k := 4) (by omega)
    simp only [Fr.fld] at h4
    have hsm := hB.2.2.2.2.2.2.2.2.2.1 r (by rw [hΦ]; simp)
    have hvb := hsm 4 (by omega); simp only [Fr.fld] at hvb
    rw [o17]; simp only [lit] at h6 h4 ⊢
    by_cases hqb : q < A.es.length
    rotate_left
    · have : q = A.es.length := by omega
      subst this
      left; refine ⟨A.F, f, by simp [finC], ?_, by exact hF⟩
      simp only [u_lt' (show A.es.length < 2 ^ 64 by omega) (show A.es.length < 2 ^ 64 by omega), Nat.lt_irrefl, if_false]
    simp only [u_lt' (show q < 2 ^ 64 by omega) (show A.es.length < 2 ^ 64 by omega), hqb, if_true]
    have he := es_lt hB (q := q)
    generalize hE : A.es.getD q 0 = e at he
    simp only [es_get hV hqb (by omega), hE, h6, h4, u_sub' hq1 (by omega),
      o9_eq hS hF hT hB hΦ hr (o := q - r.vb) (by omega)]
    have hd := dest_le hT hB hr (q - r.vb)
    simp (disch := omega) only [u_lt', u_and3, u_shr2, u_beq, u_add]
    rw [drop_cons hqb, hE]
    have hrest : ∀ F', finC (dsOf W r) F' (q - r.vb + 1) (A.es.drop (q + 1)) =
        finC (dsOf W r) F' (q + 1 - r.vb) (A.es.drop (q + 1)) := fun F' => by rw [show q - r.vb + 1 = q + 1 - r.vb by omega]
    have skip : ¬ (own e && dest (dsOf W r) (q - r.vb) == 1) = true →
        ((∃ F' f', finC (dsOf W r) A.F (q - r.vb) (e :: A.es.drop (q + 1)) = some F' ∧
          o17 n s f v W.t (u (q + 1)) (u A.es.length) = (s, f') ∧ RF W f' { A with F := F' }) ∨
        bget (o17 n s f v W.t (u (q + 1)) (u A.es.length)).1 1 = 1) := by
      intro hn
      rcases ih A f (q + 1) hΦ hS hF hV hT hB (by omega) (by omega) with ⟨F', f', h1, h2, h3⟩ | h
      · left; refine ⟨F', f', ?_, h2, h3⟩; simp only [finC, hn, if_false, Bool.false_eq_true]; rw [hrest]; exact h1
      · right; exact h
    by_cases e4 : e < 4
    · simp only [e4, if_true]; exact skip (by simp [own_iff]; omega)
    simp only [e4, if_false]
    simp (disch := omega) only [u_sub']
    by_cases k1 : e % 4 = 1
    rotate_left
    · simp only [k1, decide_false, Bool.false_eq_true, if_false]; exact skip (by simp [own_iff, k1])
    simp only [k1, decide_true, if_true]
    by_cases d1 : dest (dsOf W r) (q - r.vb) = 1
    rotate_left
    · simp only [d1, decide_false, Bool.false_eq_true, if_false]; exact skip (by simp [own_iff, d1])
    simp only [d1, decide_true, if_true]
    rw [o7_dead hS hF hB (by omega)]
    by_cases hd' : dead A.F (e / 4 - 1) = true
    · simp only [hd', Bool.not_true, Bool.false_eq_true, if_false]; right; rw [← lit 1]; exact err_set1 (by omega)
    simp only [hd', Bool.not_false, if_true, u_add]
    have hxn : e / 4 - 1 < W.ns := by
      rcases Nat.lt_or_ge (e / 4 - 1) W.ns with hc | hc
      · exact hc
      · exfalso; apply hd'; unfold dead; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hF.1]; omega)]; rfl
    have := ih { A with F := A.F.set (e / 4 - 1) true } (bset f (u (W.ns + (e / 4 - 1))) (u 1)) (q + 1) hΦ
      (rs_congr hS rfl rfl rfl rfl rfl) (rf_dead hF hns hxn) hV hT hB (by omega) (by dsimp only; omega)
    dsimp only at this
    rcases this with ⟨F', f', h1, h2, h3⟩ | h
    · left; refine ⟨F', f', ?_, h2, h3⟩
      simp only [finC, own_iff, d1, k1, show 4 ≤ e by omega, decide_true, Bool.and_true, beq_self_eq_true, if_true,
        consume1, show dead A.F (e / 4 - 1) = false by simpa using hd', Bool.false_eq_true, if_false, Option.bind_some]
      rw [hrest]; exact h1
    · right; exact h

/-- `o18` = `finB`, or an error -/
theorem o18_ok {W : WCx} {s f v : Buf} {A : AS} {Φ0 : List Fr} {r : Fr} (hr : r.ok W) (hΦ : A.Φ = Φ0 ++ [r])
    (hS : RS W s A) (hF : RF W f A) (hV : RV v A) (hT : RT W) (hB : Bnd W A) : ∀ (n q : Nat), r.vb ≤ q → q ≤ A.es.length →
    (o18 n s f v W.t (u q) (u A.es.length) = s ∧ finB (dsOf W r) A.F (q - r.vb) (A.es.drop q) = true) ∨
    bget (o18 n s f v W.t (u q) (u A.es.length)) 1 = 1 := by
  have hl := hS.1
  have hes := hB.2.2.2.2.2.2.2.1
  have hns := hB.1
  have h4 := o1_eq hS hΦ hB.2.2.2.2.2.1 (k := 4) (by omega)
  simp only [Fr.fld] at h4
  have hsm := hB.2.2.2.2.2.2.2.2.2.1 r (by rw [hΦ]; simp)
  have hvb := hsm 4 (by omega); simp only [Fr.fld] at hvb
  intro n
  induction n with
  | zero => intro q _ _; right; simp only [o18]; exact err_o5 (by omega)
  | succ n ih =>
    intro q hq1 hq
    rw [o18]; simp only [lit] at h4 ⊢
    by_cases hqb : q < A.es.length
    rotate_left
    · have : q = A.es.length := by omega
      subst this
      left; refine ⟨?_, by simp [finB]⟩
      simp only [u_lt' (show A.es.length < 2 ^ 64 by omega) (show A.es.length < 2 ^ 64 by omega), Nat.lt_irrefl, if_false]
    simp only [u_lt' (show q < 2 ^ 64 by omega) (show A.es.length < 2 ^ 64 by omega), hqb, if_true]
    have he := es_lt hB (q := q)
    generalize hE : A.es.getD q 0 = e at he
    simp only [es_get hV hqb (by omega), hE, h4, u_sub' hq1 (by omega), o9_eq hS hF hT hB hΦ hr (o := q - r.vb) (by omega)]
    have hd := dest_le hT hB hr (q - r.vb)
    simp (disch := omega) only [u_lt', u_and3, u_shr2, u_beq, u_add]
    rw [drop_cons hqb, hE]
    have hrest : finB (dsOf W r) A.F (q - r.vb + 1) (A.es.drop (q + 1)) =
        finB (dsOf W r) A.F (q + 1 - r.vb) (A.es.drop (q + 1)) := by rw [show q - r.vb + 1 = q + 1 - r.vb by omega]
    have skip : (!(own e && dest (dsOf W r) (q - r.vb) == 2) || !dead A.F (e / 4 - 1)) = true →
        ((o18 n s f v W.t (u (q + 1)) (u A.es.length) = s ∧ finB (dsOf W r) A.F (q - r.vb) (e :: A.es.drop (q + 1)) = true) ∨
        bget (o18 n s f v W.t (u (q + 1)) (u A.es.length)) 1 = 1) := by
      intro hn
      rcases ih (q + 1) (by omega) (by omega) with ⟨h1, h2⟩ | h
      · left; refine ⟨h1, ?_⟩; simp only [finB, hn, Bool.true_and]; rw [hrest]; exact h2
      · right; exact h
    by_cases e4 : e < 4
    · simp only [e4, if_true]; exact skip (by simp [own_iff]; omega)
    simp only [e4, if_false]
    simp (disch := omega) only [u_sub']
    by_cases k1 : e % 4 = 1
    rotate_left
    · simp only [k1, decide_false, Bool.false_eq_true, if_false]; exact skip (by simp [own_iff, k1])
    simp only [k1, decide_true, if_true]
    by_cases d2 : dest (dsOf W r) (q - r.vb) = 2
    rotate_left
    · simp only [d2, decide_false, Bool.false_eq_true, if_false]; exact skip (by simp [own_iff, d2])
    simp only [d2, decide_true, if_true]
    rw [o7_dead hS hF hB (by omega)]
    by_cases hd' : dead A.F (e / 4 - 1) = true
    · simp only [hd', Bool.not_true, Bool.false_eq_true, if_false]; right; rw [← lit 1]; exact err_set1 (by omega)
    · simp only [hd', Bool.not_false, if_true]; exact skip (by simp [hd'])

/-- `o19` = `strip` from q (in place) -/
theorem o19_ok {W : WCx} : ∀ (n : Nat) (A : AS) (v : Buf) (q : Nat), RV v A → Bnd W A → q ≤ A.es.length →
    A.es.length - q ≤ n → RV (o19 n v (u q) (u A.es.length)) { A with es := A.es.take q ++ strip (A.es.drop q) } := by
  intro n
  induction n with
  | zero =>
    intro A v q hV _ hq hn
    have : q = A.es.length := by omega
    subst this; simp only [o19, List.drop_length, List.take_length, strip, List.map_nil, List.append_nil]; exact hV
  | succ n ih =>
    intro A v q hV hB hq hn
    have hes := hB.2.2.2.2.2.2.2.1
    rw [o19]; simp only [lit]
    by_cases hqb : q < A.es.length
    rotate_left
    · have : q = A.es.length := by omega
      subst this
      simp only [u_lt' (show A.es.length < 2 ^ 64 by omega) (show A.es.length < 2 ^ 64 by omega), Nat.lt_irrefl, if_false,
        List.drop_length, List.take_length, strip, List.map_nil, List.append_nil]; exact hV
    simp only [u_lt' (show q < 2 ^ 64 by omega) (show A.es.length < 2 ^ 64 by omega), hqb, if_true]
    have he := es_lt hB (q := q)
    have hst : strip (A.es.drop q) = (if A.es.getD q 0 < 4 then A.es.getD q 0 else min (A.es.getD q 0 % 4) 1) ::
        strip (A.es.drop (q + 1)) := by rw [drop_cons hqb]; rfl
    generalize hE : A.es.getD q 0 = e at he hst
    simp only [es_get hV hqb (by omega), hE, u_add]
    simp (disch := omega) only [u_lt', u_and3, u_beq]
    by_cases e4 : e < 4
    · simp only [e4, if_true]
      have := ih A v (q + 1) hV hB (by omega) (by omega)
      rw [take_succ' hqb, hE, List.append_assoc] at this
      rw [hst]; simp only [e4, if_true]; exact this
    simp only [e4, if_false]
    have key : ∀ w, w = min (e % 4) 1 → RV (o19 n (bset v (u q) (u w)) (u (q + 1)) (u A.es.length))
        { A with es := A.es.take q ++ strip (A.es.drop q) } := by
      intro w hw
      have := ih { A with es := A.es.set q w } (bset v (u q) (u w)) (q + 1) (rv_set hV hqb) (bnd_es_set hB (by omega))
        (by simp; omega) (by simp; omega)
      simp only [List.length_set, set_drop, set_take hqb, List.append_assoc] at this
      rw [hst]; simp only [e4, if_false, ← hw]; exact this
    by_cases k0 : e % 4 = 0
    · simp only [k0, decide_true, if_true]; exact key 0 (by simp [k0])
    · simp only [k0, decide_false, Bool.false_eq_true, if_false]; exact key 1 (by omega)

theorem o11_eq {p : Nat} (hp : p < 10) : o11 (u p) = u (dsP p).length := by
  unfold o11; simp only [lit]
  have e : ∀ k : Nat, k < 10 → (u p == u k) = decide (p = k) := fun k hk => u_beq (by omega) (by omega)
  simp only [e 2 (by omega), e 4 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega)]
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9) with
    h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp [dsP]

theorem len_set1 (s : Buf) : (bset s 1 1).length = s.length := by simp [bset]

/-- an error stays an error through `o18` -/
theorem o18_err (f v t : Buf) : ∀ (n : Nat) (s : Buf) (q b : UInt64), 6 ≤ s.length → bget s 1 = 1 →
    bget (o18 n s f v t q b) 1 = 1 := by
  intro n; induction n with
  | zero => intro s q b hl _; simp only [o18]; exact err_o5 hl
  | succ n ih =>
    intro s q b hl he
    rw [o18]; split
    · dsimp only; split
      · exact ih _ _ _ hl he
      · split
        · split
          · split
            · exact ih _ _ _ hl he
            · exact err_set1 (by omega)
          · exact ih _ _ _ hl he
        · exact ih _ _ _ hl he
    · exact he

theorem o17_len (v t : Buf) : ∀ (n : Nat) (s f : Buf) (q b : UInt64), (o17 n s f v t q b).1.length = s.length := by
  intro n; induction n with
  | zero => intro s f q b; simp [o17, o5, bset]
  | succ n ih =>
    intro s f q b
    rw [o17]; split
    · dsimp only; split
      · exact ih _ _ _ _
      · split
        · split
          · split
            · exact ih _ _ _ _
            · simp [bset]
          · exact ih _ _ _ _
        · exact ih _ _ _ _
    · rfl

/-- `o29` = `fin` (without the strip), or an error -/
theorem o29_ok {W : WCx} {s f v : Buf} {A : AS} {Φ0 : List Fr} {r : Fr} (hr : r.ok W) (hΦ : A.Φ = Φ0 ++ [r])
    (hS : RS W s A) (hF : RF W f A) (hV : RV v A) (hT : RT W) (hB : Bnd W A) (hvb : r.vb ≤ A.es.length) :
    (∃ F2 f', fin (dsOf W r) A.F (A.es.drop r.vb) = some (F2, strip (A.es.drop r.vb)) ∧ o29 s f v W.t = (s, f') ∧
      RF W f' { A with F := F2 }) ∨ bget (o29 s f v W.t).1 1 = 1 := by
  have hl := hS.1
  have hes := hB.2.2.2.2.2.2.2.1
  have hb := hB.2.2.2.2.2.1
  have h3 := o1_eq hS hΦ hb (k := 3) (by omega)
  have h4 := o1_eq hS hΦ hb (k := 4) (by omega)
  have h6 := o1_eq hS hΦ hb (k := 6) (by omega)
  have h7 := (regs hS).2.2.2.2.2.2.1
  have h8 := (regs hS).2.2.2.2.2.2.2.1
  have h2 := (regs hS).2.2.1
  simp only [Fr.fld] at h3 h4 h6
  have hsm := hB.2.2.2.2.2.2.2.2.2.1 r (by rw [hΦ]; simp)
  have hd := hsm 3 (by omega); have ha6 := hsm 6 (by omega); simp only [Fr.fld] at hd ha6
  -- the two passes
  have pass : (∃ F2 f', finC (dsOf W r) A.F 0 (A.es.drop r.vb) = some F2 ∧ finB (dsOf W r) F2 0 (A.es.drop r.vb) = true ∧
      (let (s1, f1) := o17 16777216 s f v W.t (u r.vb) (u A.es.length); (o18 16777216 s1 f1 v W.t (u r.vb) (u A.es.length), f1))
        = (s, f') ∧ RF W f' { A with F := F2 }) ∨
      bget (let (s1, f1) := o17 16777216 s f v W.t (u r.vb) (u A.es.length);
        (o18 16777216 s1 f1 v W.t (u r.vb) (u A.es.length), f1)).1 1 = 1 := by
    rcases o17_ok hr 16777216 A f r.vb hΦ hS hF hV hT hB (Nat.le_refl _) hvb with ⟨F2, f1, h1, h2', h3'⟩ | h
    · rw [h2']; simp only [Nat.sub_self] at h1
      have hS1 : RS W s { A with F := F2 } := rs_congr hS rfl rfl rfl rfl rfl
      rcases o18_ok (A := { A with F := F2 }) hr hΦ hS1 h3' hV hT hB 16777216 r.vb (Nat.le_refl _) hvb with ⟨h4', h5⟩ | h
      · left; exact ⟨F2, f1, h1, by simpa using h5, by simp only [h4'], h3'⟩
      · right; simpa using h
    · right
      have hlz := o17_len v W.t 16777216 s f (u r.vb) (u A.es.length)
      revert h hlz; generalize o17 16777216 s f v W.t (u r.vb) (u A.es.length) = z; intro h hlz
      obtain ⟨s1, f1⟩ := z
      exact o18_err f1 v W.t _ s1 _ _ (by simp at hlz; omega) h
  have finEq : ∀ F2, finC (dsOf W r) A.F 0 (A.es.drop r.vb) = some F2 → finB (dsOf W r) F2 0 (A.es.drop r.vb) = true →
      (∀ l, dsOf W r = some l → (A.es.drop r.vb).length = l.length) →
      fin (dsOf W r) A.F (A.es.drop r.vb) = some (F2, strip (A.es.drop r.vb)) := by
    intro F2 h1 h2 h3; unfold fin
    revert h1 h2 h3; cases dsOf W r with
    | none => intro h1 h2 _; simp [h1, h2]
    | some l => intro h1 h2 h3; simp [h1, h2, h3 l rfl]
  have usePass : (∀ l, dsOf W r = some l → (A.es.drop r.vb).length = l.length) →
      ((∃ F2 f', fin (dsOf W r) A.F (A.es.drop r.vb) = some (F2, strip (A.es.drop r.vb)) ∧
        (let (s1, f1) := o17 16777216 s f v W.t (u r.vb) (u A.es.length);
          (o18 16777216 s1 f1 v W.t (u r.vb) (u A.es.length), f1)) = (s, f') ∧ RF W f' { A with F := F2 }) ∨
       bget (let (s1, f1) := o17 16777216 s f v W.t (u r.vb) (u A.es.length);
          (o18 16777216 s1 f1 v W.t (u r.vb) (u A.es.length), f1)).1 1 = 1) := by
    intro hc
    rcases pass with ⟨F2, f', h1, h2, h3, h4⟩ | h
    · left; exact ⟨F2, f', finEq F2 h1 h2 hc, h3, h4⟩
    · right; exact h
  unfold o29; simp only [lit] at h7 h8 h2 ⊢
  simp only [h3, h4, h6, h7, h8, h2, beq_self_eq_true, if_true]
  have e : ∀ k : Nat, k < 10 → (u r.d == u k) = decide (r.d = k) := fun k hk => u_beq (by omega) (by omega)
  simp only [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), u_sub' hvb (by omega)]
  have hlen : (A.es.drop r.vb).length = A.es.length - r.vb := List.length_drop
  by_cases d0 : r.d = 0
  · simp only [d0, decide_true, if_true]; exact usePass (by simp [dsOf, d0])
  simp only [d0, decide_false, Bool.false_eq_true, if_false]
  -- the expected count `w` = the destination list's length, as a word
  have hw : ∃ l, dsOf W r = some l ∧ l.length < 2 ^ 20 ∧
      ((if r.d = 1 then u 2 else if r.d = 2 then o11 (u r.a) else if r.d = 3 then bget W.t (bget W.t (u r.a))
        else u W.npw - u 1) = u l.length ∨ W.npw = 0 ∧ r.d = 4 ∧ l = []) := by
    by_cases d1 : r.d = 1
    · exact ⟨[0, 0], by simp [dsOf, d1], by simp, .inl (by simp [d1])⟩
    by_cases d2 : r.d = 2
    · exact ⟨dsP r.a, by simp [dsOf, d0, d1, d2], by unfold dsP; split <;> simp,
        .inl (by simp [d1, d2]; exact o11_eq (hr.2.1 d2))⟩
    by_cases d3 : r.d = 3
    · obtain ⟨a, ha, hl', hp20, -, hnp, -⟩ := hT.2.2.2 r.a (hr.2.2 d3)
      refine ⟨W.ps.getD r.a [], by simp [dsOf, d0, d1, d2, d3], hp20, .inl ?_⟩
      simp only [d1, d2, d3, if_false, if_true]
      have ht := hT.2.2.1
      rw [bget_u _ (by omega), ha, bget_u _ (by omega), hnp]
      all_goals first | rfl | omega
    · have d4 : r.d = 4 := by have := hr.1; omega
      have hnpw := hB.2.1; have hns := hB.1; have hnsK : W.ns = W.K.length := rfl
      refine ⟨stD W.K W.npw, by simp [dsOf, d0, d1, d2, d3], by simp [stD]; omega, ?_⟩
      simp only [d1, d2, d3, if_false]
      by_cases hn0 : W.npw = 0
      · right; exact ⟨hn0, d4, by simp [stD, hn0]⟩
      · left; rw [u_sub' (by omega) (by omega)]; simp [stD]; congr 1; omega
  obtain ⟨l, hl', hl20, hw⟩ := hw
  generalize hW : (if r.d = 1 then u 2 else if r.d = 2 then o11 (u r.a) else if r.d = 3 then bget W.t (bget W.t (u r.a))
        else u W.npw - u 1) = w at hw
  have hWgoal : (if (decide (r.d = 1)) = true then u 2 else if (decide (r.d = 2)) = true then o11 (u r.a)
      else if (decide (r.d = 3)) = true then bget W.t (bget W.t (u r.a)) else u W.npw - u 1) = w := by
    rw [← hW]; simp only [decide_eq_true_eq]
  rw [hWgoal]
  rcases hw with hw | ⟨hn0, d4, hl0⟩
  · subst hw
    rw [u_beq (by omega) (by omega)]
    by_cases hc : A.es.length - r.vb = l.length
    · simp only [hc, decide_true, if_true]; exact usePass (by intro l' h'; rw [hl'] at h'; cases h'; rw [hlen, hc])
    · simp only [hc, decide_false, Bool.false_eq_true, if_false]; right; rw [← lit 1]; exact err_set1 (by omega)
  · have : w = u (2 ^ 64 - 1) := by rw [← hW]; simp [d4, hn0]; decide
    subst this
    rw [u_beq (by omega) (by omega), if_neg (by simp; omega)]; right; rw [← lit 1]; exact err_set1 (by omega)

end OwnP
