/- Nano/V2Self/Proof/OwnP17: IF after its else-branch (transfer, or the flags with the snapshot, join the values). -/
import Nano.V2Self.Proof.OwnP16
namespace OwnP
open C OwnSpec ParSpec

theorem err_set1' {s : Buf} (h : bget s 1 = 1) : bget (bset s 1 1) 1 = 1 := by
  simp only [bget, bset] at h ⊢; rw [show (1 : UInt64).toNat = 1 from rfl] at h ⊢; rw [getD_set]; split <;> simp_all

theorem o28_err {s v : Buf} {a m b : UInt64} (h : bget s 1 = 1) : bget (o28 s v a m b).1 1 = 1 := by
  unfold o28
  split
  · exact h
  · split
    · exact h
    · split
      · exact err_bset (by decide) h
      · split
        · exact err_bset (by decide) (err_set1' h)
        · exact err_bset (by decide) h

theorem ph1_if_else {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 1) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hg : r.g = 4) (hc : r.c = 3) {sn0 : List (List Bool)} {S : List Bool}
    (hsn : A.sn = sn0 ++ [S]) (hb : r.b = sn0.length) {pre kt ee : List Nat} (hes : A.es = pre ++ kt ++ ee)
    (hvb : pre.length = r.vb) (ha : pre.length + kt.length = r.a) (hvc : pre.length + kt.length = r.vc) :
    Reach W (s, f, v) (fun σ => ∃ Fe ke k, tr A.F ee = some (Fe, ke) ∧ join kt ke = some k ∧
      St W σ.1 σ.2.1 σ.2.2 { A with F := List.zipWith (· || ·) Fe S, es := pre ++ k, sn := sn0, Φ := Φ0 ++ [Fr.set r 2 4], ph := 2 }) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨f0, -, f2, -, f4, f5, f6, f7, hsm⟩ := frame_facts hS hB hΦ
  have hesl : A.es.length = pre.length + kt.length + ee.length := by rw [hes]; simp; omega
  have hesb := hB.2.2.2.2.2.2.2.1
  have hns := hB.1
  apply reach_one hS
  rw [stp_eq, o30_ph1 hS hp]
  unfold o32
  have r7 := (regs hS).2.2.2.2.2.2.1
  have r6 := (regs hS).2.2.2.2.2.1
  simp only [lit] at r7 r6 ⊢
  simp only [nfr_ne hS hB hΦ, Bool.false_eq_true, if_false, f0, f2, f5, r7, r6, hg, hc,
    show (u 4 == u 4) = true from rfl, if_true, show (u 3 < u 2) = False from by rw [u_lt' (by omega) (by omega)]; simp,
    if_false, show (u 3 == u 2) = false from rfl]
  rcases o15_ok 16777216 A f v r.vc hS hF hV hB (by omega) with ⟨Fe, ke, f', v', htr, ho15, hF1, hV1⟩ | herr
  · rw [ho15]; simp only [f4, f6, f7, hb]
    have hdrop : A.es.drop r.vc = ee := by rw [hes, ← hvc, ← List.length_append, List.drop_left]
    have htake : A.es.take r.vc = pre ++ kt := by rw [hes, ← hvc, ← List.length_append, List.take_left]
    rw [hdrop] at htr; rw [htake] at hV1
    obtain ⟨hkl, hkv⟩ := tr_len' _ _ _ _ htr
    have hS0 : RS W s { A with F := Fe, es := pre ++ kt ++ ke } := rs_congr hS rfl rfl (by simp [hesl, hkl]; omega) rfl rfl
    have hS1 : RS W (bset s (u 10) (u sn0.length)) { A with F := Fe, es := pre ++ kt ++ ke, sn := sn0 } :=
      rs_set hS0 (r := 10) (by omega) _ (by simp [regL]) rfl
    have hB1 : Bnd W { A with F := Fe, es := pre ++ kt ++ ke, sn := sn0 } := by
      refine bnd_gen hB rfl hB.2.2.2.2.2.1 ?_ ?_ ?_ hB.2.2.2.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.2.2.2.2
      · have := hB.2.2.2.2.2.2.1; rw [hsn] at this; simp at this; simp; omega
      · simp; omega
      · intro e he; simp at he; rcases he with he | he | he
        · exact hB.2.2.2.2.2.2.2.2.1 e (by rw [hes]; simp [he])
        · exact hB.2.2.2.2.2.2.2.2.1 e (by rw [hes]; simp [he])
        · have := hkv e he; omega
    have hV1' : RV v' { A with F := Fe, es := pre ++ kt ++ ke, sn := sn0 } := hV1
    have hlen : A.es.length = ({ A with F := Fe, es := pre ++ kt ++ ke, sn := sn0 } : AS).es.length := by
      simp [hesl, hkl]; omega
    simp only [u_mul, u_add, ← ha, ← hvb, ← hvc]
    rw [hlen]
    rcases o28_ok hS1 hV1' hB1 (pre := pre) (t := kt) (e := ke) rfl with ⟨k, s', v'', hj, ho28, hS2, hV2, hB2⟩ | herr
    · rw [ho28]; left; refine ⟨Fe, ke, k, htr, hj, ?_⟩
      have hS3 := rs_set hS2 (A' := { A with F := Fe, es := pre ++ k, sn := sn0, ph := 2 }) (r := 11) (by omega) (u 2)
        (by simp [regL]) rfl
      have hS4 := o2_eq hS3 (Φ0 := Φ0) (r := r) hΦ hB.2.2.2.2.2.1 (k := 2) (by omega) 4
      have hF2 := rf_or (A := { A with F := Fe }) hF1 hB hsn
      have hsm2 := small_set hsm (k := 2) (by omega) (show 4 < 2 ^ 60 by omega)
      refine ⟨hS4, hF2, hV2, hT, ?_⟩
      refine bnd_gen hB2 rfl ?_ hB2.2.2.2.2.2.2.1 hB2.2.2.2.2.2.2.2.1 hB2.2.2.2.2.2.2.2.2.1 ?_ (show 2 < 3 by omega)
      · have := hB.2.2.2.2.2.1; rw [hΦ] at this; simp at this; simp; omega
      · intro x hx; rcases List.mem_append.mp hx with h | h
        · exact hB.2.2.2.2.2.2.2.2.2.1 x (by rw [hΦ]; simp [h])
        · simp at h; subst h; exact hsm2
    · right; exact o2_err (err_bset (by decide) herr) (by omega) (by omega) _
  · right
    revert herr; generalize o15 16777216 s f v (u r.vc) (u A.es.length) = z; obtain ⟨s1, f1, v1⟩ := z; intro herr
    simp only at herr ⊢
    exact o2_err (err_bset (by decide) (o28_err (err_bset (by decide) herr))) (by omega) (by omega) _

end OwnP
