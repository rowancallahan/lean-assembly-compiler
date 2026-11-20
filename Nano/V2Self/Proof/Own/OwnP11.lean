/- Nano/V2Self/Proof/Own/OwnP11: frame pop and the finish of an argument-list frame (BIN 3, PAIR 6, CALL 8, PRIM 9,
CONTINUE 11): `fin`, then the node's result entries, pop, phase 1. -/
import Nano.V2Self.Proof.Own.OwnP10
namespace OwnP
open C OwnSpec ParSpec

theorem rs_pop {W : WCx} {s : Buf} {A : AS} (h : RS W s A) (hB : Bnd W A) {Φ0 : List Fr} {r : Fr} (hΦ : A.Φ = Φ0 ++ [r]) :
    RS W (bset (bset s (u 4) (u A.Φ.length - u 1)) (u 11) (u 1)) { A with Φ := Φ0, ph := 1 } := by
  have hb := hB.2.2.2.2.2.1
  have hl : A.Φ.length = Φ0.length + 1 := by rw [hΦ]; simp
  rw [hl, u_sub' (by omega) (by omega), show Φ0.length + 1 - 1 = Φ0.length by omega]
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hS1 : RS W (bset s (u 4) (u Φ0.length)) { A with Φ := Φ0 } := by
    rw [bset_u s (by omega)]
    refine ⟨by simp; omega, by simp; omega, fun k x hk => ?_, fun j hj k hk => ?_⟩
    · rw [getD_set]
      have hk16 : k < 16 := by have := (List.getElem?_eq_some_iff.mp hk).1; simpa [regL_len] using this
      by_cases k4 : k = 4
      · subst k4; simp [regL] at hk; simp [show 4 < s.length by omega, hk]
      · rw [if_neg (by omega)]; apply h3 k x
        have : regL W { A with Φ := Φ0 } = (regL W A).set 4 (some (u Φ0.length)) := by simp [regL, hl]
        rw [this, List.getElem?_set, if_neg (Ne.symm k4)] at hk; exact hk
    · simp only at hj; rw [getD_set, if_neg (by omega), h4 j (by omega) k hk, hΦ]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  exact rs_set hS1 (r := 11) (by omega) _ (by simp [regL]) rfl

theorem rv_prefix {v : Buf} {A : AS} (hV : RV v A) {pre acc : List Nat} (hes : A.es = pre ++ acc) :
    RV v { A with es := pre } := by
  obtain ⟨h1, h2, h3⟩ := hV
  have hl : A.es.length = pre.length + acc.length := by rw [hes]; simp
  refine ⟨by simp; omega, h2, fun j hj => ?_⟩
  simp only at hj
  rw [h3 j (by omega), hes]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem bnd_prefix {W : WCx} {A : AS} (hB : Bnd W A) {pre acc : List Nat} (hes : A.es = pre ++ acc) :
    Bnd W { A with es := pre } := by
  apply bnd_es hB pre (by have := hB.2.2.2.2.2.2.2.1; rw [hes] at this; simp at this; omega)
  intro e he; exact hB.2.2.2.2.2.2.2.2.1 e (by rw [hes]; simp [he])

/-- the end of a frame: the values `pre` below, F2, entries `pre ++ res`, popped, phase 1 -/
def Fin (W : WCx) (A : AS) (Φ0 : List Fr) (pre : List Nat) (F2 : List Bool) (res : List Nat) (σ : SB) : Prop :=
  St W σ.1 σ.2.1 σ.2.2 { A with F := F2, es := pre ++ res, Φ := Φ0, ph := 1 }

theorem o18_len (f v t : Buf) : ∀ (n : Nat) (s : Buf) (q b : UInt64), (o18 n s f v t q b).length = s.length := by
  intro n; induction n with
  | zero => intro s q b; simp [o18, o5, bset]
  | succ n ih =>
    intro s q b; rw [o18]; split
    · dsimp only; split
      · exact ih _ _ _
      · split
        · split
          · split
            · exact ih _ _ _
            · simp [bset]
          · exact ih _ _ _
        · exact ih _ _ _
    · rfl

theorem o29_len (s f v t : Buf) : (o29 s f v t).1.length = s.length := by
  unfold o29; generalize hN : 16777216 = N; revert N; apply id; intro N hN; dsimp only
  repeat' split
  all_goals simp [o18_len, o17_len, bset]

/-- phase 2 with all children done: o33 = its finish branch (common facts) -/
theorem ph2_done_pre {W : WCx} {s : Buf} {A : AS} (hS : RS W s A) (hB : Bnd W A) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hc : r.c = r.n) : (o1 s (u 2) < o1 s (u 1)) = False := by
  obtain ⟨-, f1, f2, -, -, -, -, -, hsm⟩ := frame_facts hS hB hΦ
  have g1 := hsm 1 (by omega); have g2 := hsm 2 (by omega); simp only [Fr.fld] at g1 g2
  rw [f1, f2, u_lt' (by omega) (by omega)]; simp [hc]

theorem bnd_pop {W : WCx} {A : AS} (hB : Bnd W A) {Φ0 : List Fr} {r : Fr} (hΦ : A.Φ = Φ0 ++ [r]) :
    Bnd W { A with Φ := Φ0, ph := 1 } := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hB
  refine ⟨b1, b2, b3, b4, b5, ?_, b7, b8, b9, fun x hx => b10 x (by rw [hΦ]; simp [hx]), ?_⟩
  · show Φ0.length ≤ _; rw [hΦ] at b6; simp at b6; omega
  · show 1 < 3; omega

theorem fin_bin {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 2) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hr : r.ok W) (hg : r.g = 3) (hc : r.c = r.n) {pre acc : List Nat}
    (hes : A.es = pre ++ acc) (hpre : pre.length = r.vb) :
    Reach W (s, f, v) (fun σ => ∃ F2, fin (dsOf W r) A.F acc = some (F2, strip acc) ∧ Fin W A Φ0 pre F2 [0] σ) := by
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
  rw [show (u 3 == u 3) = true from rfl, if_pos rfl]
  rcases o29_ok hr hΦ hS hF hV hT hB (by omega) with ⟨F2, f', hfin, ho29, hF2⟩ | herr
  · rw [ho29]; simp only
    rw [f4]
    have hS1 : RS W (bset s (u 7) (u pre.length)) { A with F := F2, es := pre } := by
      have := rs_es hS pre (by omega); exact rs_congr this rfl rfl rfl rfl rfl
    have hV1 := rv_prefix (A := { A with F := F2 }) hV hes
    have hB1 := bnd_prefix (A := { A with F := F2 }) hB hes
    rw [← hpre]
    rcases o6_ok hS1 hV1 hB1 (e := 0) (by omega) with ⟨-, ho6, hS2, hV2, hB2⟩ | herr
    · rw [ho6]; left
      refine ⟨F2, by rw [hdrop] at hfin; exact hfin, ?_⟩
      have hS3 := rs_pop hS2 hB2 (Φ0 := Φ0) (r := r) hΦ
      exact ⟨hS3, hF2, hV2, hT, bnd_pop hB2 hΦ⟩
    · right; exact err_bset (by decide) (err_bset (by decide) herr)
  · right
    have hl6 : 6 ≤ (bset (o29 s f v W.t).1 (u 7) (o1 (o29 s f v W.t).1 (u 4))).length := by
      rw [len_bset, o29_len]; have := hS.1; omega
    have he1 : bget (bset (o29 s f v W.t).1 (u 7) (o1 (o29 s f v W.t).1 (u 4))) 1 = 1 := err_bset (by decide) herr
    exact err_bset (by decide) (err_bset (by decide) (o6_err (v := v) (e := u 0) hl6 he1).1)

end OwnP
