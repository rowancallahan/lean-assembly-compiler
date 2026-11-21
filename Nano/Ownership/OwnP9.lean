/- Nano/Ownership/OwnP9: frame steps — phase 2 "start the next child" and phase 1 "an argument completed". -/
import Nano.Ownership.OwnP8
namespace OwnP
open C OwnSpec ParSpec

theorem frame_facts {W : WCx} {s : Buf} {A : AS} (h : RS W s A) (hB : Bnd W A) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) :
    o1 s (u 0) = u r.g ∧ o1 s (u 1) = u r.n ∧ o1 s (u 2) = u r.c ∧ o1 s (u 3) = u r.d ∧ o1 s (u 4) = u r.vb ∧
    o1 s (u 5) = u r.vc ∧ o1 s (u 6) = u r.a ∧ o1 s (u 7) = u r.b ∧ r.small := by
  have hb := hB.2.2.2.2.2.1
  exact ⟨o1_eq h hΦ hb (by omega), o1_eq h hΦ hb (by omega), o1_eq h hΦ hb (by omega), o1_eq h hΦ hb (by omega),
    o1_eq h hΦ hb (by omega), o1_eq h hΦ hb (by omega), o1_eq h hΦ hb (by omega), o1_eq h hΦ hb (by omega),
    hB.2.2.2.2.2.2.2.2.2.1 r (by rw [hΦ]; simp)⟩

theorem bnd_frame {W : WCx} {A : AS} (hB : Bnd W A) {Φ0 : List Fr} {r r' : Fr} (hΦ : A.Φ = Φ0 ++ [r]) (hr : r'.small)
    {ph : Nat} (hp : ph < 3) : Bnd W { A with Φ := Φ0 ++ [r'], ph := ph } := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hB
  refine ⟨b1, b2, b3, b4, b5, by simpa [hΦ] using b6, b7, b8, b9, fun x hx => ?_, hp⟩
  rcases List.mem_append.mp hx with h | h
  · exact b10 x (by rw [hΦ]; simp [h])
  · simp at h; subst h; exact hr

theorem small_set {r : Fr} (hr : r.small) {k x : Nat} (hk : k < 8) (hx : x < 2 ^ 60) : (r.set k x).small := by
  intro j hj; rw [Fr.fld_set _ hk]; split
  · exact hx
  · exact hr j hj

/-- phase 2, the next child of a frame other than IF-at-its-branches and LOOP: phase 0, current base := top -/
theorem ph2_next {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 2) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hc : r.c < r.n) (hg : r.g ≠ 10) (hg4 : r.g = 4 → r.c ≠ 2) :
    Reach W (s, f, v) (fun σ => St W σ.1 σ.2.1 σ.2.2 { A with Φ := Φ0 ++ [r.set 5 A.es.length], ph := 0 }) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨f0, f1, f2, -, -, -, -, -, hsm⟩ := frame_facts hS hB hΦ
  have hesl := hB.2.2.2.2.2.2.2.1
  apply reach_one hS
  rw [stp_eq, o30_ph2 hS hp]
  unfold o33; generalize hN : 16777216 = N; revert N; apply id; intro N hN
  have r7 := (regs hS).2.2.2.2.2.2.1
  simp only [lit] at r7 ⊢
  have g0 := hsm 0 (by omega); have g1 := hsm 1 (by omega); have g2 := hsm 2 (by omega)
  simp only [Fr.fld] at g0 g1 g2
  simp only [f0, f1, f2, r7, u_lt' (show r.c < 2 ^ 64 by omega) (show r.n < 2 ^ 64 by omega), hc, if_true]
  have e : ∀ k : Nat, k < 20 → (u r.g == u k) = decide (r.g = k) := fun k hk => u_beq (by omega) (by omega)
  have ec : (u r.c == u 2) = decide (r.c = 2) := u_beq (by omega) (by omega)
  simp only [e 4 (by omega), e 10 (by omega), ec, hg, decide_false, Bool.false_eq_true, if_false]
  have hS1 := rs_set hS (A' := { A with ph := 0 }) (r := 11) (by omega) (u 0) (by simp [regL]) rfl
  have hS2 := o2_eq hS1 (Φ0 := Φ0) (r := r) hΦ hB.2.2.2.2.2.1 (k := 5) (by omega) A.es.length
  have fin : St W (o2 (bset s (u 11) (u 0)) (u 5) (u A.es.length)) f v { A with Φ := Φ0 ++ [r.set 5 A.es.length], ph := 0 } :=
    ⟨hS2, hF, hV, hT, bnd_frame hB hΦ (small_set hsm (by omega) (by omega)) (by omega)⟩
  by_cases h4 : r.g = 4
  · simp only [h4, decide_true, if_true, hg4 h4]; left; exact fin
  · simp only [h4, decide_false, Bool.false_eq_true, if_false]; left; exact fin

theorem nfr_ne {W : WCx} {s : Buf} {A : AS} (h : RS W s A) (hB : Bnd W A) {Φ0 : List Fr} {r : Fr} (hΦ : A.Φ = Φ0 ++ [r]) :
    (bget s (u 4) == u 0) = false := by
  have r4 := (regs h).2.2.2.1; simp only [lit] at r4; rw [r4]
  have hb := hB.2.2.2.2.2.1
  rw [u_beq (by omega) (by omega)]; simp [hΦ]

theorem idx_ne1 (y : UInt64) (k : Nat) (hk : k < 8) (hk1 : k ≠ 1) : (16 : UInt64) + 8 * y + u k ≠ 1 := by
  intro h
  have := congrArg (fun z : UInt64 => z.toNat % 8) h
  simp only [UInt64.toNat_add, UInt64.toNat_mul, u_toNat (show k < 2 ^ 64 by omega)] at this
  simp at this
  omega

theorem o2_err {s : Buf} (h : bget s 1 = 1) {k : Nat} (hk : k < 8) (hk1 : k ≠ 1) (x : UInt64) : bget (o2 s (u k) x) 1 = 1 :=
  err_bset (idx_ne1 _ k hk hk1) h

/-- phase 1 after an argument (list frames, and IF operands): `okAll`, done := c + 1, phase 2 -/
theorem ph1_arg {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 1) {Φ0 : List Fr} {r : Fr}
    (hΦ : A.Φ = Φ0 ++ [r]) (hr : r.ok W) (hg5 : r.g ≠ 5) (hg10 : r.g ≠ 10) (hg4 : r.g = 4 → r.c < 2)
    (hvb : r.vb ≤ r.vc) (hvc : r.vc ≤ A.es.length) (hcn : r.c + 1 < 2 ^ 60) :
    Reach W (s, f, v) (fun σ => okAll (dsOf W r) A.F (r.vc - r.vb) (A.es.drop r.vc) = true ∧
      St W σ.1 σ.2.1 σ.2.2 { A with Φ := Φ0 ++ [r.set 2 (r.c + 1)], ph := 2 }) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨f0, f1, f2, -, -, f5, -, -, hsm⟩ := frame_facts hS hB hΦ
  apply reach_one hS
  rw [stp_eq, o30_ph1 hS hp]
  unfold o32; generalize hN : 16777216 = N; revert N; apply id; intro N hN
  have r7 := (regs hS).2.2.2.2.2.2.1
  simp only [lit] at r7 ⊢
  have g0 := hsm 0 (by omega); have g2 := hsm 2 (by omega)
  simp only [Fr.fld] at g0 g2
  simp only [nfr_ne hS hB hΦ, Bool.false_eq_true, if_false, f0, f2, f5, r7]
  have e : ∀ k : Nat, k < 20 → (u r.g == u k) = decide (r.g = k) := fun k hk => u_beq (by omega) (by omega)
  simp only [e 4 (by omega), e 5 (by omega), e 10 (by omega), hg5, hg10, decide_false, Bool.false_eq_true, if_false]
  have key : (∃ z, o14 N s f v W.t (u r.vc) (u A.es.length) = z ∧
      ((z = (s, f) ∧ okAll (dsOf W r) A.F (r.vc - r.vb) (A.es.drop r.vc) = true) ∨ bget z.1 1 = 1)) :=
    ⟨_, rfl, o14_ok ⟨hS, hF, hV, hT, hB⟩ hΦ hr N r.vc hvb hvc⟩
  obtain ⟨z, hz, hz2⟩ := key
  have hbr : ∀ X Y : Buf × (Buf × Buf), (if decide (r.g = 4) = true then (if u r.c < u 2 then X else Y) else X) = X := by
    intro X Y
    by_cases h4 : r.g = 4
    · simp only [h4, decide_true, if_true, u_lt' (show r.c < 2 ^ 64 by omega) (show 2 < 2 ^ 64 by omega), hg4 h4]
    · simp only [h4, decide_false, Bool.false_eq_true, if_false]
  rw [hbr]
  rw [hz]
  rcases hz2 with ⟨rfl, hok⟩ | he
  · left; refine ⟨hok, ?_⟩
    have hS1 := rs_set hS (A' := { A with ph := 2 }) (r := 11) (by omega) (u 2) (by simp [regL]) rfl
    have hS2 := o2_eq hS1 (Φ0 := Φ0) (r := r) hΦ hB.2.2.2.2.2.1 (k := 2) (by omega) (r.c + 1)
    rw [u_add]
    exact ⟨hS2, hF, hV, hT, bnd_frame hB hΦ (small_set hsm (by omega) hcn) (by omega)⟩
  · right; obtain ⟨s1, f1⟩ := z
    exact o2_err (err_bset (by decide) he) (by omega) (by omega) _

end OwnP
