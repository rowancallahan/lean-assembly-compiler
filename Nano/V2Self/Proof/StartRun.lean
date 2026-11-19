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

theorem At.dt {C : List J} {p : Nat} {l : List J} (h : At C p l) (k n : Nat) (hk : k + n ≤ l.length) :
    At C (p + k) ((l.drop k).take n) := by
  intro i hi
  simp only [List.length_take, List.length_drop] at hi
  rw [Nat.add_assoc, h (k + i) (by omega)]
  simp [List.getElem?_take, show i < n by omega]

theorem Star.pc {C : List J} {a : Nat × St} {p p' : Nat} {t : St} (h : Star C a (p, t)) (e : p = p') :
    Star C a (p', t) := e ▸ h

theorem Star.pc_step {C : List J} {a : Nat × St} {p p' : Nat} {t : St} (h : step C a = some (p, t)) (e : p = p') :
    step C a = some (p', t) := e ▸ h

/-- the cells the tail reads after main: ra / s0 save slots and the result buffer's byte words -/
def KeepT (A2 P N : Nat) (c : Nat) : Prop := c = A2 ∨ c = A2 + 8 ∨ ∃ j, j < N ∧ c = P + 16 + 8 * j

/-- after main returns at S+12 (result buffer address on t6's top): copy the buffer bytes to a3, a0 := 0
(or 1 when the buffer is empty), a1 := length, restore ra / s0 from a2, return -/
theorem start_tail {C : List J} {S w : Nat} (hS : At C S (startJ S w)) (s2 : St) (z0 : s2.x 0 = 0)
    (hA : (s2.x 12).toNat + 8 < 2 ^ 64)
    (hP : (s2.m (s2.x 31).toNat).toNat + 16 + 8 * (s2.m (s2.m (s2.x 31).toNat).toNat).toNat < 2 ^ 64)
    (hQ : (s2.x 13).toNat + (s2.m (s2.m (s2.x 31).toNat).toNat).toNat < 2 ^ 64)
    (hdis : ∀ i, i < (s2.m (s2.m (s2.x 31).toNat).toNat).toNat →
      ¬ KeepT (s2.x 12).toNat (s2.m (s2.x 31).toNat).toNat (s2.m (s2.m (s2.x 31).toNat).toNat).toNat
        ((s2.x 13).toNat + i - ((s2.x 13).toNat + i) % 8)) :
    ∃ s3, Star C (S + 12, s2) (((s2.m (s2.x 12).toNat).toNat - s2.b) / 4, s3) ∧ s3.b = s2.b ∧
      s3.x 1 = s2.m (s2.x 12).toNat ∧ s3.x 8 = s2.m ((s2.x 12).toNat + 8) ∧ s3.x 2 = s2.x 2 ∧
      s3.x 10 = (if s2.m (s2.m (s2.x 31).toNat).toNat = 0 then 1 else 0) ∧
      s3.x 11 = s2.m (s2.m (s2.x 31).toNat).toNat ∧
      (∀ i, i < (s2.m (s2.m (s2.x 31).toNat).toNat).toNat →
        lbm s3.m ((s2.x 13).toNat + i) = s2.m ((s2.m (s2.x 31).toNat).toNat + 16 + 8 * i) &&& 255) := by
  have c12 : C[S + 12]? = some (.ld 5 31 0) := (At.get hS 12 (by rw [startJ_len]; decide)).trans rfl
  have c13 : C[S + 13]? = some (.ld 7 5 0) := (At.get hS 13 (by rw [startJ_len]; decide)).trans rfl
  have c14 : C[S + 14]? = some (.bne 7 0 4) := (At.get hS 14 (by rw [startJ_len]; decide)).trans rfl
  have c15 : C[S + 15]? = some (.addi 10 0 1) := (At.get hS 15 (by rw [startJ_len]; decide)).trans rfl
  have c16 : C[S + 16]? = some (.addi 11 0 0) := (At.get hS 16 (by rw [startJ_len]; decide)).trans rfl
  have c17 : C[S + 17]? = some (.jal 0 12) := (At.get hS 17 (by rw [startJ_len]; decide)).trans rfl
  have c18 : C[S + 18]? = some (.addi 11 7 0) := (At.get hS 18 (by rw [startJ_len]; decide)).trans rfl
  have c19 : C[S + 19]? = some (.addi 6 5 16) := (At.get hS 19 (by rw [startJ_len]; decide)).trans rfl
  have c20 : C[S + 20]? = some (.addi 14 13 0) := (At.get hS 20 (by rw [startJ_len]; decide)).trans rfl
  have c28 : C[S + 28]? = some (.addi 10 0 0) := (At.get hS 28 (by rw [startJ_len]; decide)).trans rfl
  have c29 : C[S + 29]? = some (.ld 1 12 0) := (At.get hS 29 (by rw [startJ_len]; decide)).trans rfl
  have c30 : C[S + 30]? = some (.ld 8 12 8) := (At.get hS 30 (by rw [startJ_len]; decide)).trans rfl
  have c31 : C[S + 31]? = some (.jalr 0 1) := (At.get hS 31 (by rw [startJ_len]; decide)).trans rfl
  have hL : At C (S + 21) loopJ := At.dt hS 21 7 (by rw [startJ_len]; decide)
  have hd : ∀ {a b c}, step C a = some b → Star C b c → Star C a c := fun h1 h2 => (Star.one h1).trans h2
  have e0 : ∀ v : UInt64, ea v 0 = v.toNat := by intro v; simp [ea]
  have e8 : ∀ v : UInt64, ea v 8 = v.toNat + 8 := by intro v; simp [ea]; omega
  have e16 : ∀ v : UInt64, ea v 16 = v.toNat + 16 := by intro v; simp [ea]; omega
  generalize hPd : s2.m (s2.x 31).toNat = P at *
  generalize hNd : s2.m P.toNat = N at *
  -- the common exit: S+29 .. S+31
  have ex : ∀ s : St, s.b = s2.b → s.x 0 = 0 → s.x 12 = s2.x 12 → s.m (s2.x 12).toNat = s2.m (s2.x 12).toNat →
      s.m ((s2.x 12).toNat + 8) = s2.m ((s2.x 12).toNat + 8) →
      ∃ s3, Star C (S + 29, s) (((s2.m (s2.x 12).toNat).toNat - s2.b) / 4, s3) ∧ s3.b = s2.b ∧
        s3.x 1 = s2.m (s2.x 12).toNat ∧ s3.x 8 = s2.m ((s2.x 12).toNat + 8) ∧ s3.m = s.m ∧
        ∀ k, k ≠ 1 → k ≠ 8 → s3.x k = s.x k := by
    intro s hb _ h12 m0 m8
    refine ⟨_, Star.pc (hd (s_ld c29) (hd (s_ld (by simpa using c30)) (Star.one (s_jalr (by simpa using c31))))) ?_,
      ?_⟩
    · simp [CallProbe.wr, upd_same, upd_other, e0, e8, h12, m0, hb]
    · simp [CallProbe.wr, upd_same, upd_other, e0, e8, h12, m0, m8, hb]
      intro k k1 k8; simp [upd, k1, k8]
  let sa : St := ⟨upd (upd s2.x 5 P) 7 N, s2.m, s2.b⟩
  obtain ⟨sX, hX, eX⟩ : ∃ sX, Star C (S + 12, s2) (S + 14, sX) ∧ sX = sa :=
    ⟨_, hd (s_ld c12) (Star.one (s_ld (by simpa using c13))), by simp [CallProbe.wr, sa, e0, hPd, upd_same, hNd]⟩
  subst eX
  by_cases hN : N = 0
  · let sb : St := ⟨upd (upd sa.x 10 1) 11 0, s2.m, s2.b⟩
    have bn : step C (S + 14, sa) = some (S + 15, sa) := by simp [step, c14, sa, upd_same, upd_other, z0, hN]
    obtain ⟨sY, hY, eY⟩ : ∃ sY, Star C (S + 14, sa) (S + 29, sY) ∧ sY = sb := by
      refine ⟨_, hd bn (hd (s_addi (by simpa using c15))
        (hd (s_addi (by simpa using c16)) (Star.one (Star.pc_step (s_jal (by simpa using c17)) ?_)))), ?_⟩
      · omega
      · simp [CallProbe.wr, sb, sa, e0, z0, upd_other, ea]
    subst eY
    obtain ⟨s3, h3, b3, x1, x8, -, xk⟩ := ex sb rfl (by simp [sb, sa, upd, z0]) (by simp [sb, sa, upd]) rfl rfl
    refine ⟨s3, hX.trans (hY.trans h3), b3, x1, x8, ?_, ?_, ?_, fun i hi => ?_⟩
    · rw [xk 2 (by omega) (by omega)]; simp [sb, sa, upd]
    · rw [xk 10 (by omega) (by omega), if_pos hN]; simp [sb, sa, upd]
    · rw [xk 11 (by omega) (by omega), hN]; simp [sb, sa, upd]
    · subst hN; simp at hi
  · let sc : St := ⟨upd (upd (upd sa.x 11 N) 6 (P + 16)) 14 (s2.x 13), s2.m, s2.b⟩
    have bn : step C (S + 14, sa) = some (S + 18, sa) := by
      simp [step, c14, sa, upd_same, upd_other, z0, hN]; omega
    obtain ⟨sY, hY, eY⟩ : ∃ sY, Star C (S + 14, sa) (S + 21, sY) ∧ sY = sc := by
      refine ⟨_, hd bn (hd (s_addi c18) (hd (s_addi (by simpa using c19)) (Star.one (s_addi (by simpa using c20))))),
        ?_⟩
      simp [CallProbe.wr, sc, sa, e0, e16, upd_same, upd_other]
      done
    subst eY
    have t6 : (sc.x 6).toNat = P.toNat + 16 := by simp [sc, upd, UInt64.toNat_add]; omega
    have t14 : (sc.x 14).toNat = (s2.x 13).toNat := by simp [sc, upd]
    obtain ⟨sd, hD, bd, md, byd, -, xd⟩ := copy_loop hL (KeepT (s2.x 12).toNat P.toNat N.toNat) N.toNat sc
      (by simp [sc, sa, upd, z0]) (by simp [sc, sa, upd]) N.toNat_lt (by rw [t6]; omega) (by rw [t14]; omega)
      (fun i hi => by rw [t14]; exact hdis i hi) (fun i _ => by rw [t6]; exact Or.inr (Or.inr ⟨i, by omega, rfl⟩))
    have a28 := s_addi (s := sd) c28
    have x12 : sd.x 12 = s2.x 12 := by rw [xd 12 (by omega) (by omega) (by omega) (by omega)]; simp [sc, sa, upd]
    obtain ⟨s3, h3, b3, x1, x8, m3, xk⟩ := ex (CallProbe.wr sd 10 (UInt64.ofNat (ea (sd.x 0) 0)))
      (by simp [CallProbe.wr, bd, sc]) (by simp [CallProbe.wr, upd]; rw [xd 0 (by omega) (by omega) (by omega) (by omega)]; simp [sc, sa, upd, z0]) (by simp [CallProbe.wr, upd, x12])
      (by simp [CallProbe.wr]; rw [md _ (Or.inl rfl)])
      (by simp [CallProbe.wr]; rw [md _ (Or.inr (Or.inl rfl))])
    refine ⟨s3, hX.trans (hY.trans (hD.trans (hd a28 h3))), b3, x1, x8, ?_, ?_, ?_, fun i hi => ?_⟩
    · rw [xk 2 (by omega) (by omega)]; simp [CallProbe.wr, upd]; rw [xd 2 (by omega) (by omega) (by omega) (by omega)]; simp [sc, sa, upd]
    · have x0 : sd.x 0 = 0 := by rw [xd 0 (by omega) (by omega) (by omega) (by omega)]; simp [sc, sa, upd, z0]
      rw [xk 10 (by omega) (by omega), if_neg hN]; simp [CallProbe.wr, upd, ea, x0]
    · rw [xk 11 (by omega) (by omega)]; simp [CallProbe.wr, upd]; rw [xd 11 (by omega) (by omega) (by omega) (by omega)]; simp [sc, sa, upd]
    · rw [m3]; simp only [CallProbe.wr, if_neg (show (10 : Nat) ≠ 0 by omega)]
      have := byd i hi; rw [t14, t6] at this; exact this

end Templates
