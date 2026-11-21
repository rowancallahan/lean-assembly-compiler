/- Nano/V2Self/Proof/Own/OwnP12: finish of PAIR (strip), CALL (callee result kinds), PRIM (`rk`), CONTINUE (nothing). -/
import Nano.V2Self.Proof.Own.OwnP11
namespace OwnP
open C OwnSpec ParSpec

theorem err_pop {s : Buf} (h : bget s 1 = 1) (a b : UInt64) : bget (bset (bset s (u 4) a) (u 11) b) 1 = 1 :=
  err_bset (by decide) (err_bset (by decide) h)

theorem fin_pair {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 2) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hr : r.ok W) (hg : r.g = 6) (hc : r.c = r.n) {pre acc : List Nat}
    (hes : A.es = pre ++ acc) (hpre : pre.length = r.vb) :
    Reach W (s, f, v) (fun σ => ∃ F2, fin (dsOf W r) A.F acc = some (F2, strip acc) ∧ Fin W A Φ0 pre F2 (strip acc) σ) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨f0, -, -, -, f4, -, -, -, hsm⟩ := frame_facts hS hB hΦ
  have hesl : A.es.length = pre.length + acc.length := by rw [hes]; simp
  have hesb := hB.2.2.2.2.2.2.2.1
  have hdrop : A.es.drop r.vb = acc := by rw [hes, ← hpre]; simp
  apply reach_one hS
  rw [stp_eq, o30_ph2 hS hp]
  unfold o33; generalize hN : 16777216 = N; revert N; apply id; intro N hN
  have r4 := (regs hS).2.2.2.1
  have r7 := (regs hS).2.2.2.2.2.2.1
  have r8 := (regs hS).2.2.2.2.2.2.2.1
  simp only [lit] at r4 r7 r8 ⊢
  simp only [ph2_done_pre hS hB hΦ hc, if_false, f0, hg, r4, r7]
  rw [show (u 6 == u 3) = false from rfl, if_neg (by decide), show (u 6 == u 6) = true from rfl, if_pos rfl]
  rcases o29_ok hr hΦ hS hF hV hT hB (by omega) with ⟨F2, f', hfin, ho29, hF2⟩ | herr
  · rw [ho29]; simp only [r8, f4, show (u 0 == u 0) = true from rfl, if_true]
    left
    refine ⟨F2, by rw [hdrop] at hfin; exact hfin, ?_⟩
    have hst := o19_ok (W := W) N A v r.vb hV hB (by omega) (by omega)
    have htk : A.es.take r.vb ++ strip (A.es.drop r.vb) = pre ++ strip acc := by rw [hdrop, hes, ← hpre]; simp
    rw [htk] at hst
    have hlen : (pre ++ strip acc).length = A.es.length := by simp [strip, hesl]
    have hS1 : RS W s { A with F := F2, es := pre ++ strip acc } := rs_congr hS rfl rfl hlen rfl rfl
    have hB1 : Bnd W { A with F := F2, es := pre ++ strip acc } := by
      apply bnd_es hB _ (by omega)
      intro e he; rcases List.mem_append.mp he with h | h
      · exact hB.2.2.2.2.2.2.2.2.1 e (by rw [hes]; simp [h])
      · simp [strip] at h; obtain ⟨a, -, rfl⟩ := h; split <;> omega
    exact ⟨rs_pop hS1 hB1 (r := r) hΦ, hF2, hst, hT, bnd_pop hB1 hΦ⟩
  · right; exact err_pop herr _ _

theorem fin_cont {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 2) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hr : r.ok W) (hg : r.g = 11) (hc : r.c = r.n) {pre acc : List Nat}
    (hes : A.es = pre ++ acc) (hpre : pre.length = r.vb) :
    Reach W (s, f, v) (fun σ => ∃ F2, fin (dsOf W r) A.F acc = some (F2, strip acc) ∧ Fin W A Φ0 pre F2 [] σ) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨f0, -, -, -, f4, -, -, -, hsm⟩ := frame_facts hS hB hΦ
  have hesl : A.es.length = pre.length + acc.length := by rw [hes]; simp
  have hesb := hB.2.2.2.2.2.2.2.1
  have hdrop : A.es.drop r.vb = acc := by rw [hes, ← hpre]; simp
  apply reach_one hS
  rw [stp_eq, o30_ph2 hS hp]
  unfold o33; generalize hN : 16777216 = N; revert N; apply id; intro N hN
  have r4 := (regs hS).2.2.2.1
  simp only [lit] at r4 ⊢
  simp only [ph2_done_pre hS hB hΦ hc, if_false, f0, hg, r4]
  rw [show (u 11 == u 3) = false from rfl, if_neg (by decide), show (u 11 == u 6) = false from rfl, if_neg (by decide),
    show (u 11 == u 8) = false from rfl, if_neg (by decide), show (u 11 == u 9) = false from rfl, if_neg (by decide),
    show (u 11 == u 11) = true from rfl, if_pos rfl]
  rcases o29_ok hr hΦ hS hF hV hT hB (by omega) with ⟨F2, f', hfin, ho29, hF2⟩ | herr
  · rw [ho29]; simp only [f4]
    left
    refine ⟨F2, by rw [hdrop] at hfin; exact hfin, ?_⟩
    have hS1 : RS W (bset s (u 7) (u pre.length)) { A with F := F2, es := pre } := by
      have := rs_es hS pre (by omega); exact rs_congr this rfl rfl rfl rfl rfl
    have hV1 := rv_prefix (A := { A with F := F2 }) hV hes
    have hB1 := bnd_prefix (A := { A with F := F2 }) hB hes
    rw [← hpre]
    have hS2 := rs_pop hS1 hB1 (r := r) hΦ
    unfold Fin; simp only [List.append_nil]
    exact ⟨hS2, hF2, hV1, hT, bnd_pop hB1 hΦ⟩
  · right; exact err_pop (err_bset (by decide) herr) _ _

theorem rk_eq {p : Nat} (hp : p < 10) : (if (u p == u 4) = true then u 1 else if (u p == u 5) = true then u 1
    else if (u p == u 8) = true then u 1 else if (u p == u 9) = true then u 1 else u 0) = u (rk p) := by
  simp only [u_beq (show p < 2 ^ 64 by omega) (show 4 < 2 ^ 64 by omega), u_beq (show p < 2 ^ 64 by omega) (show 5 < 2 ^ 64 by omega),
    u_beq (show p < 2 ^ 64 by omega) (show 8 < 2 ^ 64 by omega), u_beq (show p < 2 ^ 64 by omega) (show 9 < 2 ^ 64 by omega), rk]
  by_cases h4 : p = 4 <;> by_cases h5 : p = 5 <;> by_cases h8 : p = 8 <;> by_cases h9 : p = 9 <;> simp [h4, h5, h8, h9] <;> omega

theorem fin_prim {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 2) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hr : r.ok W) (hg : r.g = 9) (ha : r.a < 10) (hc : r.c = r.n) {pre acc : List Nat}
    (hes : A.es = pre ++ acc) (hpre : pre.length = r.vb) :
    Reach W (s, f, v) (fun σ => ∃ F2, fin (dsOf W r) A.F acc = some (F2, strip acc) ∧ Fin W A Φ0 pre F2 [rk r.a] σ) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨f0, -, -, -, f4, -, f6, -, hsm⟩ := frame_facts hS hB hΦ
  have hesl : A.es.length = pre.length + acc.length := by rw [hes]; simp
  have hesb := hB.2.2.2.2.2.2.2.1
  have hdrop : A.es.drop r.vb = acc := by rw [hes, ← hpre]; simp
  apply reach_one hS
  rw [stp_eq, o30_ph2 hS hp]
  unfold o33; generalize hN : 16777216 = N; revert N; apply id; intro N hN
  have r4 := (regs hS).2.2.2.1
  simp only [lit] at r4 ⊢
  simp only [ph2_done_pre hS hB hΦ hc, if_false, f0, hg, r4]
  rw [show (u 9 == u 3) = false from rfl, if_neg (by decide), show (u 9 == u 6) = false from rfl, if_neg (by decide),
    show (u 9 == u 8) = false from rfl, if_neg (by decide), show (u 9 == u 9) = true from rfl, if_pos rfl]
  rcases o29_ok hr hΦ hS hF hV hT hB (by omega) with ⟨F2, f', hfin, ho29, hF2⟩ | herr
  · rw [ho29]; simp only [f4, f6, rk_eq ha]
    have hS1 : RS W (bset s (u 7) (u pre.length)) { A with F := F2, es := pre } := by
      have := rs_es hS pre (by omega); exact rs_congr this rfl rfl rfl rfl rfl
    have hV1 := rv_prefix (A := { A with F := F2 }) hV hes
    have hB1 := bnd_prefix (A := { A with F := F2 }) hB hes
    rw [← hpre]
    rcases o6_ok hS1 hV1 hB1 (e := rk r.a) (by unfold rk; split <;> omega) with ⟨-, ho6, hS2, hV2, hB2⟩ | herr
    · rw [ho6]; left
      exact ⟨F2, by rw [hdrop] at hfin; exact hfin, rs_pop hS2 hB2 hΦ, hF2, hV2, hT, bnd_pop hB2 hΦ⟩
    · right; exact err_pop herr _ _
  · right
    have hl6 : 6 ≤ (bset (o29 s f v W.t).1 (u 7) (o1 (o29 s f v W.t).1 (u 4))).length := by
      rw [len_bset, o29_len]; have := hS.1; omega
    have he1 : bget (bset (o29 s f v W.t).1 (u 7) (o1 (o29 s f v W.t).1 (u 4))) 1 = 1 := err_bset (by decide) herr
    exact err_pop (o6_err (v := v) (e := _) hl6 he1).1 _ _

theorem fin_call {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 2) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hr : r.ok W) (hg : r.g = 8) (hd : r.d = 3) (hc : r.c = r.n) {pre acc : List Nat}
    (hes : A.es = pre ++ acc) (hpre : pre.length = r.vb) :
    Reach W (s, f, v) (fun σ => ∃ F2, fin (dsOf W r) A.F acc = some (F2, strip acc) ∧
      Fin W A Φ0 pre F2 (W.rs.getD r.a []) σ) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨f0, -, -, -, f4, -, f6, -, hsm⟩ := frame_facts hS hB hΦ
  have hesl : A.es.length = pre.length + acc.length := by rw [hes]; simp
  have hesb := hB.2.2.2.2.2.2.2.1
  have hdrop : A.es.drop r.vb = acc := by rw [hes, ← hpre]; simp
  have hc' := hr.2.2 hd
  obtain ⟨off, hoff, hlen, hp20, hr20, hnp, hnr, -, hR, -, hRv⟩ := hT.2.2.2 r.a hc'
  have ht := hT.2.2.1
  apply reach_one hS
  rw [stp_eq, o30_ph2 hS hp]
  unfold o33; generalize hN : 16777216 = N; revert N; apply id; intro N hN
  have r4 := (regs hS).2.2.2.1
  simp only [lit] at r4 ⊢
  simp only [ph2_done_pre hS hB hΦ hc, if_false, f0, hg, r4]
  rw [show (u 8 == u 3) = false from rfl, if_neg (by decide), show (u 8 == u 6) = false from rfl, if_neg (by decide),
    show (u 8 == u 8) = true from rfl, if_pos rfl]
  rcases o29_ok hr hΦ hS hF hV hT hB (by omega) with ⟨F2, f', hfin, ho29, hF2⟩ | herr
  · rw [ho29]; simp only [f4, f6]
    have hra : r.a < 4096 := by have := hT.2.1; omega
    rw [bget_u _ (show r.a < 2 ^ 64 by omega), hoff]
    simp only [u_add, u_mul]
    rw [bget_u _ (show off < 2 ^ 64 by omega), hnp, bget_u _ (show off + 1 < 2 ^ 64 by omega), hnr]
    simp only [u_add, u_mul]
    have hS1 : RS W (bset s (u 7) (u pre.length)) { A with F := F2, es := pre } := by
      have := rs_es hS pre (by omega); exact rs_congr this rfl rfl rfl rfl rfl
    have hV1 := rv_prefix (A := { A with F := F2 }) hV hes
    have hB1 := bnd_prefix (A := { A with F := F2 }) hB hes
    rw [← hpre]
    rcases o20_ok (W := W) (a := off + 2 + 2 * (W.ps.getD r.a []).length) (L := W.rs.getD r.a []) hR hRv (by omega)
      N { A with F := F2, es := pre } _ v 0 hS1 hV1 hB1 (by omega) with ⟨s', v', h1, h2, h3, h4⟩ | herr
    · rw [h1]; left
      refine ⟨F2, by rw [hdrop] at hfin; exact hfin, ?_⟩
      unfold Fin; simp only [List.drop_zero] at h2 h3 h4
      exact ⟨rs_pop h2 h4 hΦ, hF2, h3, hT, bnd_pop h4 hΦ⟩
    · right; exact err_pop herr _ _
  · right
    have hl6 : 6 ≤ (bset (o29 s f v W.t).1 (u 7) (o1 (o29 s f v W.t).1 (u 4))).length := by
      rw [len_bset, o29_len]; have := hS.1; omega
    have he1 : bget (bset (o29 s f v W.t).1 (u 7) (o1 (o29 s f v W.t).1 (u 4))) 1 = 1 := err_bset (by decide) herr
    exact err_pop (o20_err _ _ _ N _ _ _ hl6 he1) _ _

end OwnP
