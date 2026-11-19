/- Nano/V2Self/Proof/OwnP16: the IF / LET / LOOP frame steps that are not argument-list steps: plain finish (pop),
IF condition end + flag snapshot, IF after the then-branch (transfer, swap), after the else-branch (transfer, or, join). -/
import Nano.V2Self.Proof.OwnP15
namespace OwnP
open C OwnSpec ParSpec

/-- finish of IF / LET / LOOP: pop, phase 1 -/
theorem ph2_pop {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 2) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hg : r.g = 4 ∨ r.g = 5 ∨ r.g = 10) (hc : r.c = r.n) :
    Reach W (s, f, v) (fun σ => St W σ.1 σ.2.1 σ.2.2 { A with Φ := Φ0, ph := 1 }) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨f0, -, -, -, -, -, -, -, hsm⟩ := frame_facts hS hB hΦ
  have g0 := hsm 0 (by omega); simp only [Fr.fld] at g0
  apply reach_one hS
  rw [stp_eq, o30_ph2 hS hp]
  unfold o33
  have r4 := (regs hS).2.2.2.1
  simp only [lit] at r4 ⊢
  simp only [ph2_done_pre hS hB hΦ hc, if_false, f0, r4]
  have e : ∀ k : Nat, k < 20 → (u r.g == u k) = decide (r.g = k) := fun k hk => u_beq (by omega) (by omega)
  simp only [e 3 (by omega), e 6 (by omega), e 8 (by omega), e 9 (by omega), e 11 (by omega)]
  have : ¬ r.g = 3 ∧ ¬ r.g = 6 ∧ ¬ r.g = 8 ∧ ¬ r.g = 9 ∧ ¬ r.g = 11 := by omega
  simp only [this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2, decide_false, Bool.false_eq_true, if_false]
  left
  exact ⟨rs_pop hS hB hΦ, hF, hV, hT, bnd_pop hB hΦ⟩

theorem bnd_gen {W : WCx} {A A' : AS} (hB : Bnd W A) (hi : A'.i = A.i) (hΦ : A'.Φ.length ≤ 2 ^ 30)
    (hsn : A'.sn.length ≤ 2 ^ 30) (hes : A'.es.length ≤ 2 ^ 24) (he : ∀ e ∈ A'.es, e < 2 ^ 30) (hr : ∀ r ∈ A'.Φ, r.small)
    (hph : A'.ph < 3) : Bnd W A' := by
  obtain ⟨b1, b2, b3, b4, b5, -⟩ := hB
  exact ⟨b1, b2, b3, b4, by rw [hi]; exact b5, hΦ, hsn, hes, he, hr, hph⟩

/-- IF after its condition operands: `fin [0, 0]`, pop the operand entries, snapshot the flags, then-branch next -/
theorem ph2_if_cond {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 2) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hr : r.ok W) (hg : r.g = 4) (hd : r.d = 1) (hc : r.c = 2) (hn : r.n = 4) {pre acc : List Nat}
    (hes : A.es = pre ++ acc) (hpre : pre.length = r.vb) :
    Reach W (s, f, v) (fun σ => ∃ F2, fin (some [0, 0]) A.F acc = some (F2, strip acc) ∧
      St W σ.1 σ.2.1 σ.2.2 { A with F := F2, es := pre, sn := A.sn ++ [F2], Φ := Φ0 ++ [Fr.set (Fr.set r 5 r.vb) 7 A.sn.length], ph := 0 }) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨f0, f1, f2, -, f4, -, -, -, hsm⟩ := frame_facts hS hB hΦ
  have hesl : A.es.length = pre.length + acc.length := by rw [hes]; simp
  have hesb := hB.2.2.2.2.2.2.2.1
  have hsnb := hB.2.2.2.2.2.2.1
  have hns := hB.1
  have hdrop : A.es.drop r.vb = acc := by rw [hes, ← hpre]; simp
  have hds : dsOf W r = some [0, 0] := by simp [dsOf, hd]
  apply reach_one hS
  rw [stp_eq, o30_ph2 hS hp]
  unfold o33
  have r4 := (regs hS).2.2.2.1
  have r6 := (regs hS).2.2.2.2.2.1
  simp only [lit] at r4 r6 ⊢
  simp only [f0, f1, f2, hg, hc, hn, r6, show (u 2 < u 4) = True from by rw [u_lt' (by omega) (by omega)]; simp, if_true,
    show (u 4 == u 4) = true from rfl, show (u 2 == u 2) = true from rfl]
  rcases o29_ok hr hΦ hS hF hV hT hB (by omega) with ⟨F2, f', hfin, ho29, hF2⟩ | herr
  · rw [ho29]; simp only [f4]
    have r10 := (regs hS).2.2.2.2.2.2.2.2.1
    simp only [lit] at r10; rw [r10]
    by_cases hj : A.sn.length < 2 ^ 30
    · simp only [u_lt' (show A.sn.length < 2 ^ 64 by omega) (show 1073741824 < 2 ^ 64 by omega),
        show A.sn.length < 1073741824 by omega, if_true, u_mul, u_add]
      left
      refine ⟨F2, by rw [hds, hdrop] at hfin; exact hfin, ?_⟩
      have hS1 : RS W (bset s (u 7) (u r.vb)) { A with F := F2, es := pre } := by
        have := rs_es hS pre (by omega); rw [hpre] at this; exact rs_congr this rfl rfl rfl rfl rfl
      have hS2 : RS W (bset (bset s (u 7) (u r.vb)) (u 10) (u (A.sn.length + 1)))
          { A with F := F2, es := pre, sn := A.sn ++ [F2] } :=
        rs_set hS1 (r := 10) (by omega) _ (by simp [regL, hpre]) rfl
      have hS3 : RS W (bset (bset (bset s (u 7) (u r.vb)) (u 10) (u (A.sn.length + 1))) (u 11) (u 0))
          { A with F := F2, es := pre, sn := A.sn ++ [F2], ph := 0 } :=
        rs_set hS2 (r := 11) (by omega) _ (by simp [regL, hpre]) rfl
      have hb30 : ({ A with F := F2, es := pre, sn := A.sn ++ [F2], ph := 0 } : AS).Φ.length ≤ 2 ^ 30 := hB.2.2.2.2.2.1
      have hS4 := o2_eq hS3 (Φ0 := Φ0) (r := r) hΦ hb30 (k := 5) (by omega) r.vb
      have hS5 := o2_eq hS4 (Φ0 := Φ0) (r := r.set 5 r.vb) rfl (by simpa [hΦ] using hb30) (k := 7) (by omega) A.sn.length
      have hF3 := rf_snap (A := { A with F := F2 }) hF2 hB
      have hsm5 := small_set hsm (k := 5) (by omega) (show r.vb < 2 ^ 60 by have := hsm 4 (by omega); simpa [Fr.fld] using this)
      have hsm7 := small_set hsm5 (k := 7) (by omega) (show A.sn.length < 2 ^ 60 by omega)
      refine ⟨hS5, hF3, rv_prefix (A := { A with F := F2 }) hV hes, hT, ?_⟩
      have hΦl : A.Φ.length = Φ0.length + 1 := by rw [hΦ]; simp
      have hb6 := hB.2.2.2.2.2.1
      have hesl2 := hB.2.2.2.2.2.2.2.1
      refine bnd_gen hB rfl ?_ ?_ ?_ ?_ ?_ ?_
      · simp; omega
      · simp; omega
      · simp; omega
      · intro e he; exact hB.2.2.2.2.2.2.2.2.1 e (by rw [hes]; simp [he])
      · intro x hx; rcases List.mem_append.mp hx with h | h
        · exact hB.2.2.2.2.2.2.2.2.2.1 x (by rw [hΦ]; simp [h])
        · simp at h; subst h; exact hsm7
      · show 0 < 3; omega
    · simp only [u_lt' (show A.sn.length < 2 ^ 64 by omega) (show 1073741824 < 2 ^ 64 by omega),
        show ¬ A.sn.length < 1073741824 by omega, if_false]
      right; exact err_o5 (by have := hS.1; omega)
  · right
    have hl := o29_len s f v W.t
    generalize o29 s f v W.t = z at herr hl
    obtain ⟨s1, f1⟩ := z
    simp only at herr hl ⊢
    split
    · exact o2_err (o2_err (err_bset (by decide) (err_bset (by decide) (err_bset (by decide) herr))) (by omega) (by omega) _)
        (by omega) (by omega) _
    · exact err_o5 (by have := hS.1; omega)

end OwnP
