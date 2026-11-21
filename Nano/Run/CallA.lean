/- A-variants of the prologue / call lemmas with the REAL position-indexed capacity jumps (Gen emits three different jal offsets
to the stub word `tgt`): `proA`, `pro_runA`, `call_liveA`.  The statements of Call.lean are unchanged. -/
import Nano.Run.Expr
namespace CallProbe

def proA (tgt q r : Nat) : List J :=
  pushA tgt q 1 ++ (pushA tgt (q + 4) 8 ++ [.addi 8 31 0, .addi 31 31 (-8 * (r : Int)), .bgeu 31 30 2, .jal 0 ((tgt : Int) - ((q : Int) + 11))])

theorem pro_runA {C : List J} {f r tgt : Nat} {s : St} (hC : At C f (proA tgt f r)) (hlt : (s.x 31).toNat < 2 ^ 63)
    (hh : (s.x 30).toNat + 16 + 8 * r ≤ (s.x 31).toNat) :
    ∃ s1, run C 9 (f, s) = some (f + 12, s1) ∧
      (s1.x 31).toNat = (s.x 31).toNat - 16 - 8 * r ∧ (s1.x 8).toNat = (s.x 31).toNat - 16 ∧
      (∀ i, i ≠ 31 → i ≠ 8 → s1.x i = s.x i) ∧
      s1.m = upd (upd s.m ((s.x 31).toNat - 8) (s.x 1)) ((s.x 31).toNat - 16) (s.x 8) := by
  have A1 : At C f (push 1 ((tgt : Int) - ((f : Int) + 2))) := hC.left
  have R1 : At C (f + 4) (push 8 ((tgt : Int) - (((f + 4 : Nat) : Int) + 2)) ++
      [.addi 8 31 0, .addi 31 31 (-8 * (r : Int)), .bgeu 31 30 2, .jal 0 ((tgt : Int) - ((f : Int) + 11))]) := by
    simpa [proA, pushA, push] using hC.right
  have A2 : At C (f + 4) (push 8 ((tgt : Int) - (((f + 4 : Nat) : Int) + 2))) := R1.left
  have A3 : At C (f + 8) [.addi 8 31 0, .addi 31 31 (-8 * (r : Int)), .bgeu 31 30 2, .jal 0 ((tgt : Int) - ((f : Int) + 11))] := by
    simpa [push] using R1.right
  have r1 := push_run (s := s) A1 (by decide) (by decide) (by omega)
  have lt : (s.x 31).toNat < 2 ^ 64 := (s.x 31).toNat_lt
  have t8 : (UInt64.ofNat ((s.x 31).toNat - 8)).toNat = (s.x 31).toNat - 8 := by simp; omega
  have t16 : (UInt64.ofNat ((s.x 31).toNat - 8 - 8)).toNat = (s.x 31).toNat - 16 := by simp; omega
  have r2 := push_run (s := ⟨upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8)), upd s.m ((s.x 31).toNat - 8) (s.x 1), s.b, s.wk⟩) A2 (by decide) (by decide)
    (by simp [upd, t8]; omega)
  simp only [upd_same, upd_other _ _ (show (30:Nat) ≠ 31 by decide), upd_other _ _ (show (8:Nat) ≠ 31 by decide), t8] at r2
  have r12 := run_add (l := 3) r1
  rw [r2] at r12
  have b0 := A3.at 0 (by simp); have b1 := A3.at 1 (by simp); have b2 := A3.at 2 (by simp)
  simp at b0 b1 b2
  have t16r : (UInt64.ofNat ((s.x 31).toNat - 16 - 8 * r)).toNat = (s.x 31).toNat - 16 - 8 * r := by simp; omega
  have t16' : (UInt64.ofNat ((s.x 31).toNat - 16)).toNat = (s.x 31).toNat - 16 := by simp; omega
  have e16 : (s.x 31).toNat - 8 - 8 = (s.x 31).toNat - 16 := by omega
  rw [e16] at r12
  refine ⟨⟨upd (upd (upd (upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8))) 31 (UInt64.ofNat ((s.x 31).toNat - 16)))
      8 (UInt64.ofNat ((s.x 31).toNat - 16))) 31 (UInt64.ofNat ((s.x 31).toNat - 16 - 8 * r)),
    upd (upd s.m ((s.x 31).toNat - 8) (s.x 1)) ((s.x 31).toNat - 16) (s.x 8), s.b, s.wk⟩, ?_, ?_, ?_, ?_, rfl⟩
  · rw [show 9 = (3 + 3) + 3 by rfl, run_add r12]
    have ea1 : ea (UInt64.ofNat ((s.x 31).toNat - 16)) 0 = (s.x 31).toNat - 16 := by simp [ea, t16']
    have ea2 : ea (UInt64.ofNat ((s.x 31).toNat - 16)) (-8 * (r : Int)) = (s.x 31).toNat - 16 - 8 * r := by
      simp only [ea, t16']; omega
    have c : (s.x 30).toNat ≤ (s.x 31).toNat - 16 - 8 * r := by omega
    simp [run, step, b0, b1, b2, wr, upd_same, upd_other _ _ (show (31:Nat) ≠ 8 by decide), ea1, ea2,
      upd_other _ _ (show (30:Nat) ≠ 31 by decide), upd_other _ _ (show (30:Nat) ≠ 8 by decide), t16r, c,
      show ((f : Int) + 8 + 2 + 2).toNat = f + 12 by omega]
    omega
  · simp [upd_same, t16r]
  · simp [upd_same, upd_other _ _ (show (8:Nat) ≠ 31 by decide), t16']
  · intro i h1 h2; simp [upd, h1, h2]


theorem call_liveA {C : List J} {c f e p q r tgt : Nat} {off : Int} (Bd : St → St → Prop)
    (hj : C[c]? = some (.jal 1 off)) (hf : ((c : Int) + off).toNat = f)
    (hP : At C f (proA tgt f r)) (hE : At C e (epi p q)) (s : St)
    (hT : (s.x 31).toNat + 8 * p < 2 ^ 62) (hc : s.b + s.w * (c + 1) < 2 ^ 64)
    (hh : (s.x 30).toNat + 16 + 8 * r ≤ (s.x 31).toNat)
    (hB : ∀ s1, (s1.x 31).toNat = (s.x 31).toNat - 16 - 8 * r → (s1.x 8).toNat = (s.x 31).toNat - 16 →
      s1.x 30 = s.x 30 → ∃ s2, Bd s1 s2 ∧ Star C (f + 12, s1) (e, s2) ∧ s2.x 8 = s1.x 8 ∧
        (s2.x 31).toNat + 8 * q = (s.x 31).toNat - 16 - 8 * r ∧
        ∀ a, ((s.x 31).toNat - 16 ≤ a ∧ a < (s.x 31).toNat) ∨ (s.x 31).toNat + 8 * p ≤ a → s2.m a = s1.m a) :
    ∃ s1 s2 s3, Bd s1 s2 ∧ Star C (c, s) (c + 1, s3) ∧
      (s3.x 31).toNat = (s.x 31).toNat + 8 * p - 8 * q ∧ s3.x 8 = s.x 8 ∧
      (∀ a, (s.x 31).toNat + 8 * p ≤ a → s3.m a = s.m a) ∧
      ∀ i, i < q → s3.m ((s.x 31).toNat + 8 * p - 8 * (i + 1)) = s2.m ((s2.x 31).toNat + 8 * (q - 1 - i)) := by
  -- the call
  let sj := wr s 1 (UInt64.ofNat (s.b + s.w * (c + 1)))
  have sj1 : step C (c, s) = some (f, sj) := by rw [s_jal hj, hf]
  have sjx : ∀ i, i ≠ 1 → sj.x i = s.x i := by intro i hi; simp [sj, wr, upd, hi]
  have sjm : sj.m = s.m := by simp [sj, wr]
  have sjr : sj.x 1 = UInt64.ofNat (s.b + s.w * (c + 1)) := by simp [sj, wr, upd]
  have sjb : sj.b = s.b := wr_b _ _ _
  have j31 := sjx 31 (by decide); have j30 := sjx 30 (by decide); have j8 := sjx 8 (by decide)
  -- the prologue
  obtain ⟨s1, hr1, h31, h8, hx1, hm1⟩ := pro_runA (s := sj) hP (by rw [j31]; omega) (by rw [j31, j30]; exact hh)
  rw [j31] at h31 h8 hm1
  -- the body
  obtain ⟨s2, hb, hst, k8, k31, kmem⟩ := hB s1 h31 h8 (by rw [hx1 30 (by decide) (by decide), j30])
  -- the epilogue
  have kD : (s2.x 31).toNat + 8 * q ≤ (s2.x 8).toNat + 8 * p + 16 := by rw [k8, h8]; omega
  have kl : (s2.x 8).toNat + 8 * p + 16 < 2 ^ 63 := by rw [k8, h8]; omega
  obtain ⟨s3, hr3, g3b, g31, g8, gx, gm⟩ := epi_run s2 hE kD kl
  have b2 : s2.b = s.b := by
    exact hst.b.trans ((run_star hr1).b.trans sjb)
  have S8 : (s2.x 8).toNat = (s.x 31).toNat - 16 := by rw [k8, h8]
  have ra : s2.m ((s2.x 8).toNat + 8) = UInt64.ofNat (s.b + s.w * (c + 1)) := by
    rw [S8, kmem _ (Or.inl ⟨by omega, by omega⟩), hm1, upd_other _ _ (by omega),
      show (s.x 31).toNat - 16 + 8 = (s.x 31).toNat - 8 by omega, upd_same, sjr]
  have w2 : s2.w = s.w := St.w_eq (hst.w.trans ((run_star hr1).w.trans (wr_w _ _ _)))
  have pc3 : ((s2.m ((s2.x 8).toNat + 8)).toNat - s2.b) / s2.w = c + 1 := by
    have tn : (UInt64.ofNat (s.b + s.w * (c + 1))).toNat = s.b + s.w * (c + 1) := by simp; omega
    rw [ra, b2, w2, tn, link_div]
  rw [pc3] at hr3
  refine ⟨s1, s2, s3, hb, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Star.one sj1).trans ((run_star hr1).trans (hst.trans (run_star hr3)))
  · rw [g31, S8]; omega
  · rw [g8, S8, kmem _ (Or.inl ⟨Nat.le_refl _, by omega⟩), hm1, upd_same, j8]
  · intro a ha
    rw [gm, S8, Mc_above _ _ _ q (by omega) q (Nat.le_refl _) a (by omega), kmem _ (Or.inr ha), hm1,
      upd_other _ _ (by omega), upd_other _ _ (by omega), sjm]
  · intro i hi
    rw [gm, S8, show (s.x 31).toNat + 8 * p - 8 * (i + 1) = (s.x 31).toNat - 16 + 8 * p + 16 - 8 * (i + 1) by omega,
      Mc_dest _ _ _ q (by omega) q (Nat.le_refl _) i hi]

end CallProbe
