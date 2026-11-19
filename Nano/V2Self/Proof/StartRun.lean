/- Machine bridge (Opus box E): the start code on the J machine.  `start_setup`: from word 0 (the jump to the start
code) to main's entry: heap base t5 = a2 + 16, expression stack t6 = sp rounded down to 8, ra / s0 saved at a2 / a2 + 8,
input registers t3 / t4, `jal ra main`. -/
import Nano.V2Self.Proof.StartCode
namespace Templates
open CallProbe

theorem At.get {C : List J} {h : Nat} {l : List J} (hC : At C h l) (j : Nat) (hj : j < l.length) :
    C[h + j]? = l[j]? := hC j hj

/-- the state at main's entry -/
structure Entry (s0 s1 : St) (S : Nat) : Prop where
  x0 : s1.x 0 = 0
  x1 : s1.x 1 = UInt64.ofNat (s0.b + 4 * (S + 12))
  x8 : s1.x 8 = s0.x 8
  x12 : s1.x 12 = s0.x 12
  x13 : s1.x 13 = s0.x 13
  x28 : s1.x 28 = s0.x 10
  x29 : s1.x 29 = s0.x 11
  x30 : s1.x 30 = UInt64.ofNat ((s0.x 12).toNat + 16)
  x31 : s1.x 31 = (s0.x 2 >>> 3) <<< 3
  m : s1.m = upd (upd s0.m (s0.x 12).toNat (s0.x 1)) ((s0.x 12).toNat + 8) (s0.x 8)
  b : s1.b = s0.b

theorem start_setup {C : List J} {S w : Nat} (h0 : At C 0 (stubJ S)) (hS : At C S (startJ S w)) (s0 : St)
    (z0 : s0.x 0 = 0) (ha2 : (s0.x 12).toNat + 16 < 2 ^ 64)
    (hroom : (s0.x 12).toNat + 16 ≤ ((s0.x 2 >>> 3) <<< 3).toNat) :
    ∃ s1, Star C (0, s0) (w, s1) ∧ Entry s0 s1 S := by
  have c := fun j (hj : j < 32) => At.get hS j (by rw [startJ_len]; exact hj)
  have j0 : C[0]? = some (.jal 0 (S : Int)) := by simpa [stubJ] using At.get h0 0 (by simp [stubJ])
  simp only [startJ] at c
  have c0 := c 0 (by omega); have c1 := c 1 (by omega); have c2 := c 2 (by omega); have c3 := c 3 (by omega)
  have c7 := c 7 (by omega); have c8 := c 8 (by omega); have c9 := c 9 (by omega); have c10 := c 10 (by omega)
  have c11 := c 11 (by omega)
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at c0 c1 c2 c3 c7 c8 c9 c10 c11
  have lt12 := (s0.x 12).toNat_lt
  have e16 : ea (s0.x 12) 16 = (s0.x 12).toNat + 16 := by simp [ea]; omega
  have e0 : ∀ v : UInt64, ea v 0 = v.toNat := by intro v; simp [ea]
  have e8 : ea (s0.x 12) 8 = (s0.x 12).toNat + 8 := by simp [ea]; omega
  have hd : ∀ {a b c}, step C a = some b → Star C b c → Star C a c := fun h1 h2 => (Star.one h1).trans h2
  have sj : step C (0, s0) = some (S, s0) := by simp [step, j0, CallProbe.wr]
  have jw : ∀ {s : St}, step C (S + 11, s) = some (w, CallProbe.wr s 1 (UInt64.ofNat (s.b + 4 * (S + 11 + 1)))) := by
    intro s; rw [s_jal (by simpa using c11)]; congr; omega
  have bg : ∀ {s : St}, (s.x 30).toNat ≤ (s.x 31).toNat → step C (S + 3, s) = some (S + 7, s) := by
    intro s h; rw [s_bgeu_t (by simpa using c3) h]; congr 2
  refine ⟨_, hd sj (hd (s_addi (by simpa using c0)) (hd (by simp [step, c1]; rfl) (hd (s_slli (by simpa using c2))
    (hd (bg ?_) (hd (s_sd (by simpa using c7)) (hd (s_sd (by simpa using c8))
    (hd (s_addi (by simpa using c9)) (hd (s_addi (by simpa using c10)) (Star.one jw))))))))), ?_⟩
  · simp [CallProbe.wr, CallProbe.upd, e16, UInt64.toNat_ofNat] at hroom ⊢; omega
  · have u30 : UInt64.ofNat (ea (s0.x 12) 16) = UInt64.ofNat ((s0.x 12).toNat + 16) := by rw [e16]
    constructor <;> simp [CallProbe.wr, CallProbe.upd, e0, e8, z0]
    · rw [UInt64.add_assoc]; rfl
    · rw [e16]; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add]

/-- the copy loop of the start code (words S+21 .. S+27) -/
def loopJ : List J := [.beq 7 0 7, .ld 15 6 0, .sb 15 14 0, .addi 6 6 8, .addi 14 14 1, .addi 7 7 (-1), .jal 0 (-6)]

/-- the loop copies the low bytes of r words (stride 8 from t1) to r bytes at a4; `K` = cells that must survive
(the source words among them); registers other than t1 t2 a4 a5 are kept -/
theorem copy_loop {C : List J} {L : Nat} (hL : At C L loopJ) (K : Nat → Prop) :
    ∀ (r : Nat) (s : St), s.x 0 = 0 → s.x 7 = UInt64.ofNat r → r < 2 ^ 64 →
    (s.x 6).toNat + 8 * r < 2 ^ 64 → (s.x 14).toNat + r < 2 ^ 64 →
    (∀ i, i < r → ¬ K ((s.x 14).toNat + i - ((s.x 14).toNat + i) % 8)) → (∀ i, i < r → K ((s.x 6).toNat + 8 * i)) →
    ∃ s', Star C (L, s) (L + 7, s') ∧ s'.b = s.b ∧ (∀ c, K c → s'.m c = s.m c) ∧
      (∀ i, i < r → lbm s'.m ((s.x 14).toNat + i) = s.m ((s.x 6).toNat + 8 * i) &&& 255) ∧
      (∀ a, ¬ ((s.x 14).toNat ≤ a ∧ a < (s.x 14).toNat + r) → lbm s'.m a = lbm s.m a) ∧
      (∀ k, k ≠ 6 → k ≠ 7 → k ≠ 14 → k ≠ 15 → s'.x k = s.x k) := by
  have c := fun j (hj : j < 7) => At.get hL j (by simp [loopJ]; exact hj)
  simp only [loopJ] at c
  have c0 := c 0 (by omega); have c1 := c 1 (by omega); have c2 := c 2 (by omega); have c3 := c 3 (by omega)
  have c4 := c 4 (by omega); have c5 := c 5 (by omega); have c6 := c 6 (by omega)
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at c0 c1 c2 c3 c4 c5 c6
  have hd : ∀ {a b c}, step C a = some b → Star C b c → Star C a c := fun h1 h2 => (Star.one h1).trans h2
  have sJ : ∀ {s : St}, step C (L + 6, s) = some (L, s) := by
    intro s; rw [s_jal c6]; simp [CallProbe.wr]; omega
  intro r
  induction r with
  | zero =>
    intro s z0 h7 _ _ _ _ _
    refine ⟨s, Star.one ?_, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl,
      fun _ _ _ _ _ => rfl⟩
    have : s.x 7 = s.x 0 := by rw [h7, z0]; rfl
    simp [step, c0, this]; omega
  | succ r ih =>
    intro s z0 h7 hr h6 h14 hK hR
    let p := (s.x 6).toNat
    let q := (s.x 14).toNat
    let s5 : St := ⟨upd (upd (upd (upd s.x 15 (s.m p)) 6 (s.x 6 + 8)) 14 (s.x 14 + 1)) 7
      (UInt64.ofNat r), sbm s.m q (s.m p), s.b⟩
    have ne : s.x 7 ≠ s.x 0 := by
      rw [h7, z0]; intro h; have := congrArg UInt64.toNat h; simp at this; omega
    obtain ⟨sX, hX, eX⟩ : ∃ sX, Star C (L, s) (L, sX) ∧ sX = s5 := by
      refine ⟨_, hd (by simp [step, c0, ne]; rfl) (hd (s_ld c1) (hd (by simp [step, c2]; rfl) (hd (s_addi c3)
        (hd (s_addi c4) (hd (s_addi c5) (Star.one sJ)))))), ?_⟩
      have e0 : ∀ v : UInt64, ea v 0 = v.toNat := by intro v; simp [ea]
      have e8 : ∀ v : UInt64, ea v 8 = v.toNat + 8 := by intro v; simp [ea]; omega
      have e1 : ∀ v : UInt64, ea v 1 = v.toNat + 1 := by intro v; simp [ea]
      have em : ea (UInt64.ofNat r + 1) (-1) = r := by
        have : (UInt64.ofNat r + 1).toNat = r + 1 := by simp [UInt64.toNat_add, UInt64.toNat_ofNat]; omega
        simp [ea, this]; omega
      simp [CallProbe.wr, s5, e0, e8, e1, em, h7, upd_same, upd_other, p, q]
      done
    subst eX
    have t6 : (s5.x 6).toNat = p + 8 := by simp [s5, upd_same, upd_other, UInt64.toNat_add, p]; omega
    have t14 : (s5.x 14).toNat = q + 1 := by simp [s5, upd_same, upd_other, UInt64.toNat_add, q]; omega
    obtain ⟨s', hs, hb, hKm, hby, hout, hx⟩ := ih s5 (by simp [s5, upd_other, z0]) (by simp [s5, upd_same])
      (by omega) (by rw [t6]; omega) (by rw [t14]; omega)
      (fun i hi => by rw [t14]; have := hK (i + 1) (by omega); rwa [show q + 1 + i = (s.x 14).toNat + (i + 1) by omega])
      (fun i hi => by rw [t6]; have := hR (i + 1) (by omega); rwa [show p + 8 + 8 * i = (s.x 6).toNat + 8 * (i + 1) by omega])
    have hK0 := hK 0 (by omega); simp only [Nat.add_zero] at hK0
    refine ⟨s', hX.trans hs, hb, fun c hc => ?_, fun i hi => ?_, fun a ha => ?_, fun k k6 k7 k14 k15 => ?_⟩
    · rw [hKm c hc]; exact sbm_other _ _ _ _ (fun h => hK0 (h ▸ hc))
    · rcases i with _ | i
      · show lbm s'.m (q + 0) = s.m (p + 8 * 0) &&& 255
        rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero, hout q (by rw [t14]; omega)]; exact lbm_sbm_same _ _ _
      · have e := hby i (by omega); rw [t14, t6] at e
        show lbm s'.m (q + (i + 1)) = s.m (p + 8 * (i + 1)) &&& 255
        rw [show q + (i + 1) = q + 1 + i by omega, e]
        show sbm s.m q (s.m p) _ &&& 255 = _
        rw [sbm_other _ _ _ _ (fun h => hK0 (h ▸ ?_))]
        · congr 2; omega
        · have := hR (i + 1) (by omega); rwa [show p + 8 + 8 * i = (s.x 6).toNat + 8 * (i + 1) by omega]
    · rw [hout a (by rw [t14]; omega)]
      exact lbm_sbm_other _ _ _ _ (by omega)
    · rw [hx k k6 k7 k14 k15]; simp [s5, upd_other, k6, k7, k14, k15]

end Templates
