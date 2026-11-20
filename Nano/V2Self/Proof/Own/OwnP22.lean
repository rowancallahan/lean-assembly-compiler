/- Nano/V2Self/Proof/Own/OwnP22: the root LOOP frame (tag 10): each arm starts from fresh flags; after the zero arm its
entries are transferred; after the step arm its entries are transferred and joined with the zero arm's. -/
import Nano.V2Self.Proof.Own.OwnP21
namespace OwnP
open C OwnSpec ParSpec

theorem ph2_loop {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 2) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hg : r.g = 10) (hc : r.c < r.n) :
    Reach W (s, f, v) (fun σ => St W σ.1 σ.2.1 σ.2.2
      { A with F := List.replicate W.ns false, Φ := Φ0 ++ [r.set 5 A.es.length], ph := 0 }) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨f0, f1, f2, -, -, -, -, -, hsm⟩ := frame_facts hS hB hΦ
  have hesl := hB.2.2.2.2.2.2.2.1
  apply reach_one hS
  rw [stp_eq, o30_ph2 hS hp]
  unfold o33; generalize hN : 16777216 = N; revert N; apply id; intro N hN
  have r7 := (regs hS).2.2.2.2.2.2.1
  have r6 := (regs hS).2.2.2.2.2.1
  simp only [lit] at r7 r6 ⊢
  have g1 := hsm 1 (by omega); have g2 := hsm 2 (by omega)
  simp only [Fr.fld] at g1 g2
  simp only [f0, f1, f2, r7, r6, u_lt' (show r.c < 2 ^ 64 by omega) (show r.n < 2 ^ 64 by omega), hc, if_true, hg,
    show (u 10 == u 4) = false from rfl, show (u 10 == u 10) = true from rfl, Bool.false_eq_true, if_false]
  have hS1 := rs_set hS (A' := { A with F := List.replicate W.ns false, ph := 0 }) (r := 11) (by omega) (u 0)
    (by simp [regL]) rfl
  have hS2 := o2_eq hS1 (Φ0 := Φ0) (r := r) hΦ hB.2.2.2.2.2.1 (k := 5) (by omega) A.es.length
  left
  exact ⟨hS2, (by rw [← hN]; exact rf_zero hF hB), hV, hT, bnd_frame (A := { A with F := List.replicate W.ns false }) hB hΦ
    (small_set hsm (by omega) (by omega)) (by omega)⟩

/-- after the zero arm: transfer, a := entries end, done := 1 -/
theorem ph1_loop_z {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 1) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hg : r.g = 10) (hc : r.c = 0) {pre ez : List Nat} (hes : A.es = pre ++ ez)
    (hpre : pre.length = r.vc) :
    Reach W (s, f, v) (fun σ => ∃ Fz kz, tr A.F ez = some (Fz, kz) ∧
      St W σ.1 σ.2.1 σ.2.2 { A with F := Fz, es := pre ++ kz, Φ := Φ0 ++ [Fr.set (Fr.set r 6 A.es.length) 2 1], ph := 2 }) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨f0, -, f2, -, -, f5, -, -, hsm⟩ := frame_facts hS hB hΦ
  have hesl : A.es.length = pre.length + ez.length := by rw [hes]; simp
  have hesb := hB.2.2.2.2.2.2.2.1
  apply reach_one hS
  rw [stp_eq, o30_ph1 hS hp]
  unfold o32; generalize hN : 16777216 = N; revert N; apply id; intro N hN
  have r7 := (regs hS).2.2.2.2.2.2.1
  simp only [lit] at r7 ⊢
  simp only [nfr_ne hS hB hΦ, Bool.false_eq_true, if_false, f0, f2, f5, r7, hg, hc,
    show (u 10 == u 4) = false from rfl, show (u 10 == u 5) = false from rfl, show (u 10 == u 10) = true from rfl,
    if_true, show (u 0 == u 0) = true from rfl]
  rcases o15_ok N A f v r.vc hS hF hV hB (by omega) with ⟨Fz, kz, f', v', htr, ho15, hF1, hV1⟩ | herr
  · rw [ho15]; simp only
    have hdrop : A.es.drop r.vc = ez := by rw [hes, ← hpre]; simp
    have htake : A.es.take r.vc = pre := by rw [hes, ← hpre]; simp
    rw [hdrop] at htr; rw [htake] at hV1
    obtain ⟨hkl, hkv⟩ := tr_len' _ _ _ _ htr
    left; refine ⟨Fz, kz, htr, ?_⟩
    have hb30 := hB.2.2.2.2.2.1
    have hS0 : RS W s { A with F := Fz, es := pre ++ kz } := rs_congr hS rfl rfl (by simp [hesl, hkl]) rfl rfl
    have hS1 : RS W (bset s (u 11) (u 2)) { A with F := Fz, es := pre ++ kz, ph := 2 } :=
      rs_set hS0 (r := 11) (by omega) _ (by simp [regL]) rfl
    have hS2 := o2_eq hS1 (Φ0 := Φ0) (r := r) hΦ hb30 (k := 6) (by omega) A.es.length
    have hS3 := o2_eq hS2 (Φ0 := Φ0) (r := r.set 6 A.es.length) rfl (by simpa [hΦ] using hb30) (k := 2) (by omega) 1
    have hsm6 := small_set hsm (k := 6) (by omega) (show A.es.length < 2 ^ 60 by omega)
    have hsm2 := small_set hsm6 (k := 2) (by omega) (show 1 < 2 ^ 60 by omega)
    refine ⟨hS3, hF1, hV1, hT, ?_⟩
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
    revert herr; generalize o15 N s f v (u r.vc) (u A.es.length) = z; obtain ⟨s1, f1, v1⟩ := z; intro herr
    simp only at herr ⊢
    exact o2_err (o2_err (err_bset (by decide) herr) (by omega) (by omega) _) (by omega) (by omega) _

/-- after the step arm: transfer, join with the zero arm's entries, done := 2 -/
theorem ph1_loop_s {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 1) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hg : r.g = 10) (hc : r.c = 1) {pre kz es : List Nat} (hes : A.es = pre ++ kz ++ es)
    (hvb : pre.length = r.vb) (ha : pre.length + kz.length = r.a) (hvc : pre.length + kz.length = r.vc) :
    Reach W (s, f, v) (fun σ => ∃ Fs ks k, tr A.F es = some (Fs, ks) ∧ join kz ks = some k ∧
      St W σ.1 σ.2.1 σ.2.2 { A with F := Fs, es := pre ++ k, Φ := Φ0 ++ [Fr.set r 2 2], ph := 2 }) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨f0, -, f2, -, f4, f5, f6, -, hsm⟩ := frame_facts hS hB hΦ
  have hesl : A.es.length = pre.length + kz.length + es.length := by rw [hes]; simp; omega
  have hesb := hB.2.2.2.2.2.2.2.1
  apply reach_one hS
  rw [stp_eq, o30_ph1 hS hp]
  unfold o32; generalize hN : 16777216 = N; revert N; apply id; intro N hN
  have r7 := (regs hS).2.2.2.2.2.2.1
  simp only [lit] at r7 ⊢
  simp only [nfr_ne hS hB hΦ, Bool.false_eq_true, if_false, f0, f2, f5, r7, hg, hc,
    show (u 10 == u 4) = false from rfl, show (u 10 == u 5) = false from rfl, show (u 10 == u 10) = true from rfl,
    if_true, show (u 1 == u 0) = false from rfl]
  rcases o15_ok N A f v r.vc hS hF hV hB (by omega) with ⟨Fs, ks, f', v', htr, ho15, hF1, hV1⟩ | herr
  · rw [ho15]; simp only [f4, f6]
    have hdrop : A.es.drop r.vc = es := by rw [hes, ← hvc, ← List.length_append, List.drop_left]
    have htake : A.es.take r.vc = pre ++ kz := by rw [hes, ← hvc, ← List.length_append, List.take_left]
    rw [hdrop] at htr; rw [htake] at hV1
    obtain ⟨hkl, hkv⟩ := tr_len' _ _ _ _ htr
    have hS0 : RS W s { A with F := Fs, es := pre ++ kz ++ ks } := rs_congr hS rfl rfl (by simp [hesl, hkl]; omega) rfl rfl
    have hB1 : Bnd W { A with F := Fs, es := pre ++ kz ++ ks } := by
      refine bnd_gen hB rfl hB.2.2.2.2.2.1 hB.2.2.2.2.2.2.1 ?_ ?_ hB.2.2.2.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.2.2.2.2
      · simp; omega
      · intro e he; simp at he; rcases he with he | he | he
        · exact hB.2.2.2.2.2.2.2.2.1 e (by rw [hes]; simp [he])
        · exact hB.2.2.2.2.2.2.2.2.1 e (by rw [hes]; simp [he])
        · have := hkv e he; omega
    have hV1' : RV v' { A with F := Fs, es := pre ++ kz ++ ks } := hV1
    have hlen : A.es.length = ({ A with F := Fs, es := pre ++ kz ++ ks } : AS).es.length := by
      simp [hesl, hkl]; omega
    simp only [← ha, ← hvb]
    rw [hlen]
    rcases o28_ok hS0 hV1' hB1 (pre := pre) (t := kz) (e := ks) rfl with ⟨k, s', v'', hj, ho28, hS2, hV2, hB2⟩ | herr
    · rw [ho28]; left; refine ⟨Fs, ks, k, htr, hj, ?_⟩
      have hS3 := rs_set hS2 (A' := { A with F := Fs, es := pre ++ k, ph := 2 }) (r := 11) (by omega) (u 2)
        (by simp [regL]) rfl
      have hS4 := o2_eq hS3 (Φ0 := Φ0) (r := r) hΦ hB.2.2.2.2.2.1 (k := 2) (by omega) 2
      have hsm2 := small_set hsm (k := 2) (by omega) (show 2 < 2 ^ 60 by omega)
      refine ⟨hS4, hF1, hV2, hT, ?_⟩
      refine bnd_gen hB2 rfl ?_ hB2.2.2.2.2.2.2.1 hB2.2.2.2.2.2.2.2.1 hB2.2.2.2.2.2.2.2.2.1 ?_ (show 2 < 3 by omega)
      · have := hB.2.2.2.2.2.1; rw [hΦ] at this; simp at this; simp; omega
      · intro x hx; rcases List.mem_append.mp hx with h | h
        · exact hB.2.2.2.2.2.2.2.2.2.1 x (by rw [hΦ]; simp [h])
        · simp at h; subst h; exact hsm2
    · right; exact o2_err (err_bset (by decide) herr) (by omega) (by omega) _
  · right
    revert herr; generalize o15 N s f v (u r.vc) (u A.es.length) = z; obtain ⟨s1, f1, v1⟩ := z; intro herr
    simp only at herr ⊢
    exact o2_err (err_bset (by decide) (o28_err herr)) (by omega) (by omega) _

end OwnP
