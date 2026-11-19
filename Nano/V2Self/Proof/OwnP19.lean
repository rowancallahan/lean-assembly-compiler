/- Nano/V2Self/Proof/OwnP19: LET frame steps (after the value: transfer + slot check; after the body: transfer) and the
LOOP arm steps (transfer, join). -/
import Nano.V2Self.Proof.OwnP18
namespace OwnP
open C OwnSpec ParSpec

/-- LET (or LOOP arm 2 / IF analogue) after the body: transfer its entries, done := c + 1, phase 2 -/
theorem ph1_let_body {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 1) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hg : r.g = 5) (hc : r.c = 1) {pre eb : List Nat} (hes : A.es = pre ++ eb)
    (hpre : pre.length = r.vc) :
    Reach W (s, f, v) (fun σ => ∃ F' kb, tr A.F eb = some (F', kb) ∧
      St W σ.1 σ.2.1 σ.2.2 { A with F := F', es := pre ++ kb, Φ := Φ0 ++ [Fr.set r 2 2], ph := 2 }) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨f0, -, f2, -, -, f5, -, -, hsm⟩ := frame_facts hS hB hΦ
  have hesl : A.es.length = pre.length + eb.length := by rw [hes]; simp
  have hesb := hB.2.2.2.2.2.2.2.1
  apply reach_one hS
  rw [stp_eq, o30_ph1 hS hp]
  unfold o32
  have r7 := (regs hS).2.2.2.2.2.2.1
  simp only [lit] at r7 ⊢
  simp only [nfr_ne hS hB hΦ, Bool.false_eq_true, if_false, f0, f2, f5, r7, hg, hc,
    show (u 5 == u 4) = false from rfl, show (u 5 == u 5) = true from rfl, if_true, show (u 1 == u 0) = false from rfl]
  rcases o15_ok 16777216 A f v r.vc hS hF hV hB (by omega) with ⟨F', kb, f', v', htr, ho15, hF1, hV1⟩ | herr
  · rw [ho15]; simp only
    have hdrop : A.es.drop r.vc = eb := by rw [hes, ← hpre]; simp
    have htake : A.es.take r.vc = pre := by rw [hes, ← hpre]; simp
    rw [hdrop] at htr; rw [htake] at hV1
    obtain ⟨hkl, hkv⟩ := tr_len' _ _ _ _ htr
    left; refine ⟨F', kb, htr, ?_⟩
    have hS0 : RS W s { A with F := F', es := pre ++ kb } := rs_congr hS rfl rfl (by simp [hesl, hkl]) rfl rfl
    have hS1 : RS W (bset s (u 11) (u 2)) { A with F := F', es := pre ++ kb, ph := 2 } :=
      rs_set hS0 (r := 11) (by omega) _ (by simp [regL]) rfl
    have hS2 := o2_eq hS1 (Φ0 := Φ0) (r := r) hΦ hB.2.2.2.2.2.1 (k := 2) (by omega) 2
    have hsm2 := small_set hsm (k := 2) (by omega) (show 2 < 2 ^ 60 by omega)
    refine ⟨hS2, hF1, hV1, hT, ?_⟩
    refine bnd_gen hB rfl ?_ hB.2.2.2.2.2.2.1 ?_ ?_ ?_ (show 2 < 3 by omega)
    · have := hB.2.2.2.2.2.1; rw [hΦ] at this; simp at this; simp; omega
    · simp; omega
    · intro e he; simp at he; rcases he with he | he
      · exact hB.2.2.2.2.2.2.2.2.1 e (by rw [hes]; simp [he])
      · have := hkv e he; omega
    · intro x hx; rcases List.mem_append.mp hx with h | h
      · exact hB.2.2.2.2.2.2.2.2.2.1 x (by rw [hΦ]; simp [h])
      · simp at h; subst h; exact hsm2
  · right
    revert herr; generalize o15 16777216 s f v (u r.vc) (u A.es.length) = z; obtain ⟨s1, f1, v1⟩ := z; intro herr
    simp only at herr ⊢
    exact o2_err (err_bset (by decide) herr) (by omega) (by omega) _

theorem err_o5' {s : Buf} (h : bget s 1 = 1) : bget (o5 s) 1 = 1 := err_bset (by decide) (err_set1' h)

theorem o26_err (v : Buf) (x w a : UInt64) : ∀ (n : Nat) (s f : Buf) (j : UInt64), bget s 1 = 1 →
    bget (o26 n s f v x j w a).1 1 = 1 := by
  intro n; induction n with
  | zero => intro s f j h; simp only [o26]; exact err_o5' h
  | succ n ih =>
    intro s f j h; rw [o26]; dsimp only
    split
    · split
      · split
        · split
          · exact ih _ _ _ h
          · exact err_set1' h
        · exact err_set1' h
      · exact ih _ _ _ h
    · exact h

theorem take_drop_eq {K kv : List Nat} {s0 w0 : Nat} (hl : kv.length = w0) (hsw : s0 + w0 ≤ K.length)
    (h : ∀ i, i < w0 → kv.getD i 0 = K.getD (s0 + i) 0) : kv = (K.drop s0).take w0 := by
  apply List.ext_getElem?; intro i
  by_cases hi : i < w0
  · have := h i hi
    simp only [List.getD_eq_getElem?_getD] at this
    rw [List.getElem?_eq_getElem (by omega)] at this ⊢
    rw [List.getElem?_take, if_pos hi, List.getElem?_drop, List.getElem?_eq_getElem (by omega)] at *
    simp at this ⊢; exact this
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- LET after its value: transfer, the slots `[s0, s0 + w0)` take the value (kinds = K, slots live), values popped -/
theorem ph1_let_val {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 1) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hg : r.g = 5) (hc : r.c = 0) {pre ev : List Nat} (hes : A.es = pre ++ ev)
    (hpre : pre.length = r.vc) (hs0 : r.a < 2 ^ 20) (hw0 : r.b < 2 ^ 20) :
    Reach W (s, f, v) (fun σ => ∃ F2 kv, tr A.F ev = some (F2, kv) ∧ W.npw ≤ r.a ∧ r.a + r.b ≤ W.K.length ∧
      kv = (W.K.drop r.a).take r.b ∧ notDeadR F2 r.a r.b = true ∧
      St W σ.1 σ.2.1 σ.2.2 { A with F := F2, es := pre, Φ := Φ0 ++ [Fr.set r 2 1], ph := 2 }) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨f0, -, f2, -, -, f5, f6, f7, hsm⟩ := frame_facts hS hB hΦ
  have hesl : A.es.length = pre.length + ev.length := by rw [hes]; simp
  have hesb := hB.2.2.2.2.2.2.2.1
  have hns := hB.1
  have hnsK : W.ns = W.K.length := rfl
  apply reach_one hS
  rw [stp_eq, o30_ph1 hS hp]
  unfold o32
  have r7 := (regs hS).2.2.2.2.2.2.1
  have r6 := (regs hS).2.2.2.2.2.1
  have r2 := (regs hS).2.2.1
  have r8 := (regs hS).2.2.2.2.2.2.2.1
  simp only [lit] at r7 r6 r2 r8 ⊢
  simp only [nfr_ne hS hB hΦ, Bool.false_eq_true, if_false, f0, f2, f5, f6, f7, r7, r6, r2, r8, hg, hc,
    show (u 5 == u 4) = false from rfl, show (u 5 == u 5) = true from rfl, if_true, show (u 0 == u 0) = true from rfl,
    show (u 0 == u 1) = false from rfl]
  rcases o15_ok 16777216 A f v r.vc hS hF hV hB (by omega) with ⟨F2, kv, f', v', htr, ho15, hF1, hV1⟩ | herr
  · rw [ho15]; simp only
    have hdrop : A.es.drop r.vc = ev := by rw [hes, ← hpre]; simp
    have htake : A.es.take r.vc = pre := by rw [hes, ← hpre]; simp
    rw [hdrop] at htr; rw [htake] at hV1
    obtain ⟨hkl, hkv⟩ := tr_len' _ _ _ _ htr
    have hnpw := hB.2.1
    simp only [u_lt' (show r.a < 2 ^ 64 by omega) (show W.npw < 2 ^ 64 by omega), u_add,
      u_lt' (show W.ns < 2 ^ 64 by omega) (show r.a + r.b < 2 ^ 64 by omega), u_sub' (show r.vc ≤ A.es.length by omega)
      (show A.es.length < 2 ^ 64 by omega), u_beq (show A.es.length - r.vc < 2 ^ 64 by omega) (show r.b < 2 ^ 64 by omega), r8]
    have e0 : bget (bset s (u 1) (u 1)) 1 = 1 := err_set1 (by have := hS.1; omega)
    have errk : ∀ x y z : UInt64, bget (o2 (bset (bset (bset s (u 1) (u 1)) (u 7) x) (u 11) y) (u 2) z) 1 = 1 := by
      intro x y z
      have e1 : bget (bset (bset (bset s (u 1) (u 1)) (u 7) x) (u 11) y) 1 = 1 :=
        err_bset (by decide) (err_bset (by decide) e0)
      exact o2_err e1 (k := 2) (by omega) (by omega) z
    by_cases c1 : r.a < W.npw
    · simp only [c1, if_true, show ((u 0 : UInt64) == u 1) = false from rfl, Bool.false_eq_true, if_false,
        show (u 0 == u 0) = true from rfl]
      right; exact errk _ _ _
    by_cases c2 : W.ns < r.a + r.b
    · simp only [c1, c2, if_true, if_false, show ((u 0 : UInt64) == u 1) = false from rfl, Bool.false_eq_true,
        show (u 0 == u 0) = true from rfl]
      right; exact errk _ _ _
    by_cases c3 : A.es.length - r.vc = r.b
    rotate_left
    · simp only [c1, c2, c3, decide_false, if_false, Bool.false_eq_true, show ((u 0 : UInt64) == u 1) = false from rfl,
        show (u 0 == u 0) = true from rfl, if_true]
      right; exact errk _ _ _
    simp only [c1, c2, c3, decide_true, if_false, if_true, show ((u 1 : UInt64) == u 1) = true from rfl]
    have hkb : kv.length = r.b := by omega
    have hS0 : RS W s { A with F := F2, es := pre ++ kv } := rs_congr hS rfl rfl (by simp [hesl, hkl]) rfl rfl
    have hB0 : Bnd W { A with F := F2, es := pre ++ kv } := by
      refine bnd_gen hB rfl hB.2.2.2.2.2.1 hB.2.2.2.2.2.2.1 (by simp; omega) ?_ hB.2.2.2.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.2.2.2.2
      intro e he; simp at he; rcases he with he | he
      · exact hB.2.2.2.2.2.2.2.2.1 e (by rw [hes]; simp [he])
      · have := hkv e he; omega
    have h26 := o26_ok hS0 hF1 hV1 hB0 (pre := pre) (kv := kv) rfl (x := r.a) (by omega) 16777216 0 (by omega)
    rw [← hkb, ← hpre]
    rcases h26 with ⟨h1, h2⟩ | herr
    · rw [h1]; left
      refine ⟨F2, kv, htr, by omega, by omega, take_drop_eq rfl (by omega) (fun i hi => (h2 i (by omega) (by omega)).1),
        (notDeadR_iff F2 r.a kv.length).mpr (fun i hi => (h2 i (by omega) (by omega)).2), ?_⟩
      have hS1 : RS W (bset s (u 7) (u pre.length)) { A with F := F2, es := pre } := by
        have := rs_es hS pre (by omega); exact rs_congr this rfl rfl rfl rfl rfl
      have hS2 : RS W (bset (bset s (u 7) (u pre.length)) (u 11) (u 2)) { A with F := F2, es := pre, ph := 2 } :=
        rs_set hS1 (r := 11) (by omega) _ (by simp [regL]) rfl
      have hS3 := o2_eq hS2 (Φ0 := Φ0) (r := r) hΦ hB.2.2.2.2.2.1 (k := 2) (by omega) 1
      have hsm2 := small_set hsm (k := 2) (by omega) (show 1 < 2 ^ 60 by omega)
      refine ⟨hS3, hF1, rv_prefix (A := { A with F := F2, es := pre ++ kv }) hV1 rfl, hT, ?_⟩
      refine bnd_gen hB rfl ?_ hB.2.2.2.2.2.2.1 ?_ ?_ ?_ (show 2 < 3 by omega)
      · have := hB.2.2.2.2.2.1; rw [hΦ] at this; simp at this; simp; omega
      · simp; omega
      · intro e he; exact hB.2.2.2.2.2.2.2.2.1 e (by rw [hes]; simp [he])
      · intro x hx; rcases List.mem_append.mp hx with h | h
        · exact hB.2.2.2.2.2.2.2.2.2.1 x (by rw [hΦ]; simp [h])
        · simp at h; subst h; exact hsm2
    · right
      revert herr; generalize o26 16777216 s f' v' (u r.a) (u 0) (u kv.length) (u pre.length) = z; obtain ⟨s2, f2⟩ := z
      intro herr; simp only at herr ⊢
      exact o2_err (err_bset (by decide) (err_bset (by decide) herr)) (by omega) (by omega) _
  · right
    revert herr; generalize o15 16777216 s f v (u r.vc) (u A.es.length) = z; obtain ⟨s1, f1, v1⟩ := z; intro herr
    simp only at herr ⊢
    repeat' split
    all_goals (refine o2_err ?_ (k := 2) (by omega) (by omega) _
               refine err_bset (by decide) ?_; refine err_bset (by decide) ?_
               first | exact o26_err _ _ _ _ _ _ _ _ herr | exact err_set1' herr | exact herr)

end OwnP
