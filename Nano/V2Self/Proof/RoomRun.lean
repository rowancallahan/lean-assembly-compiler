/- Opus box E: the out-of-memory exit (`room`) of the leaf templates as SAFE runs: the checked push finds no room
(t6 − 8 < t5) and jumps to the OOM stub (word 1). -/
import Nano.V2Self.Proof.CapNode
import Nano.V2Self.Proof.EVSLeaf
namespace Templates
open CallProbe SimW SafeRun

theorem push_oom_srun {K : LayW} {C : List J} {pc tgt : Nat} {r : Nat} {s : St}
    (hC : At C pc (push r ((tgt : Int) - ((pc : Int) + 2)))) (h16 : 16 ≤ (s.x 31).toNat)
    (hh : (s.x 31).toNat < (s.x 30).toNat + 8) (ht : tgt < C.length) (hC18 : C.length < 2 ^ 18)
    (hpc : pc + 3 < C.length) :
    SStar K C (pc, s) (tgt, ⟨upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8)), s.m, s.b⟩) := by
  have r := push_oom (s := s) hC (by omega) hh
  rw [show ((pc : Int) + 2 + ((tgt : Int) - ((pc : Int) + 2))).toNat = tgt by omega] at r
  refine sstar_of_run r ?_
  intro j hj c hc
  have h0 := hC.at 0 (by simp [push]); have h1 := hC.at 1 (by simp [push]); have h2 := hC.at 2 (by simp [push])
  simp only [push, Nat.add_zero] at h0 h1 h2
  simp at h0 h1 h2
  have lt : (s.x 31).toNat < 2 ^ 64 := (s.x 31).toNat_lt
  have e : ea (s.x 31) (-8) = (s.x 31).toNat - 8 := by simp [ea]; omega
  have t6' : (UInt64.ofNat ((s.x 31).toNat - 8)).toNat = (s.x 31).toNat - 8 := by simp [UInt64.toNat_ofNat]; omega
  have c2 : ¬ (s.x 30).toNat ≤ (s.x 31).toNat - 8 := by omega
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · simp [CallProbe.run] at hc; subst hc; simp [Safe, h0]; omega
  · simp [CallProbe.run, CallProbe.step, h0] at hc; subst hc; simp [Safe, h1]
  · simp [CallProbe.run, CallProbe.step, h0, h1, CallProbe.wr, e, upd_same, upd_other _ _ (show (30:Nat) ≠ 31 by decide), t6', c2] at hc
    subst hc
    simp [Safe, h2]; omega

/-- a one-word leaf whose template is a checked push: at no room it reaches the OOM stub (word 1) -/
theorem leafRoom {KL : LayW} {C : List J} {pc p nl hb E0 : Nat} {Inv G : St → Prop} {R : Nat → Prop}
    {V : Env → UInt64} (hI : InvOKH hb p Inv) (hG : ∀ s, Inv s → G s)
    (hst : ∀ env env', (∀ k, R k → env k = env' k) → V env = V env')
    (hgo : ∀ (s : St) (env : Env), s.x 0 = 0 → Frame p nl s env → FrameOK p nl s → Lay KL hb E0 p s →
      hb ≤ (s.x 30).toNat → (s.x 30).toNat ≤ (s.x 31).toNat →
      16 ≤ (s.x 31).toNat → (s.x 31).toNat < (s.x 30).toNat + 8 →
      ∃ s', SStarX KL C (pc, s) (1, s') ∧ s'.m = s.m ∧ s'.x 8 = s.x 8 ∧ s'.x 28 = s.x 28 ∧ s'.x 29 = s.x 29 ∧
        s'.b = s.b ∧ s'.x 0 = 0) :
    CapW .room 1 KL C pc p nl Inv G hb E0 R (leafF V) where
  stable := fun env env' sp H h => by simp only [leafF]; rw [hst env env' h]
  cap := fun s env H I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [leafF] at hS
    split at hS
    · simp at hS
    rename_i hc
    have top0 : (s.x 30).toNat = H.top := R0.2.2.2.2.1
    obtain ⟨s', r, hm, e8, e28, e29, eb, z'⟩ := hgo s env z0 F0 O0 L0 (by have := R0.2.1; omega)
      (by have := R0.2.2.1; omega) (hrel_sp R0) (by omega)
    exact ⟨s', r, hG _ (hI s s' I0 e8 e28 e29 eb (fun a _ => by rw [hm])), z'⟩

theorem constRoom {KL : LayW} {C : List J} {pc p nl hb E0 : Nat} {Inv G : St → Prop} {R : Nat → Prop} {v : UInt64}
    (hI : InvOKH hb p Inv) (hG : ∀ s, Inv s → G s) (hC : At C pc (constT 1 pc v)) (h1 : 1 < C.length)
    (hC18 : C.length < 2 ^ 18) (hl : pc + (liT 5 v).length + 3 < C.length) :
    CapW .room 1 KL C pc p nl Inv G hb E0 R (leafF (fun _ => v)) :=
  leafRoom hI hG (fun _ _ _ => rfl) (fun s _ hx0 _ _ _ _ _ h16 hh => by
    obtain ⟨s1, hr1, hx1, hm1, hb1⟩ := li_srun (K := KL) (d := 5) s (by decide) (by decide) hx0 hC.left
    have hP : At C (pc + (liT 5 v).length) (push 5 ((1 : Int) - ((pc + (liT 5 v).length : Nat) + 2))) := by
      simpa [constT, pushA] using hC.right
    have e31 : s1.x 31 = s.x 31 := by rw [hx1]; exact upd_other _ _ (by decide)
    have e30 : s1.x 30 = s.x 30 := by rw [hx1]; exact upd_other _ _ (by decide)
    have r2 := push_oom_srun (K := KL) (s := s1) hP (by rw [e31]; exact h16) (by rw [e31, e30]; exact hh) h1 hC18 hl
    refine ⟨_, SStarX.of (hr1.trans r2), hm1, ?_, ?_, ?_, hb1, ?_⟩ <;> simp only [upd_ne, hx1] <;> simp [upd, hx0])

theorem lenRoom {KL : LayW} {C : List J} {pc p nl hb E0 : Nat} {Inv G : St → Prop} {R : Nat → Prop} {c29 : UInt64}
    (hI : InvOKH hb p Inv) (hG : ∀ s, Inv s → G s) (hC : At C pc (lenT 1 pc)) (h1 : 1 < C.length)
    (hC18 : C.length < 2 ^ 18) (hl : pc + 3 < C.length) :
    CapW .room 1 KL C pc p nl Inv G hb E0 R (leafF (fun _ => c29)) :=
  leafRoom hI hG (fun _ _ _ => rfl) (fun s _ hx0 _ _ _ _ _ h16 hh => by
    have r := push_oom_srun (K := KL) (s := s) (by simpa [lenT, pushA] using hC) h16 hh h1 hC18 hl
    refine ⟨_, SStarX.of r, rfl, ?_, ?_, ?_, rfl, ?_⟩ <;> simp [upd, hx0])


theorem slot_wok' {KL : LayW} {hb E0 p nl k : Nat} {s : St} (L : Lay KL hb E0 p s) (O : FrameOK p nl s)
    (h30 : hb ≤ (s.x 30).toNat) (h31 : (s.x 30).toNat ≤ (s.x 31).toNat) (hk : k < nl) :
    wok KL (CallProbe.slotAddr p k (s.x 8).toNat) := by
  have := L.top; have := L.a8; obtain ⟨o1, o2, o3⟩ := O
  unfold CallProbe.slotAddr
  split <;> exact L.wok (by omega) (by omega) (by omega)

theorem local1Room {KL : LayW} {C : List J} {pc p nl hb E0 k : Nat} {Inv G : St → Prop}
    (hI : InvOKH hb p Inv) (hG : ∀ s, Inv s → G s) (hp : p < 2 ^ 20) (hnl : nl < 251) (hk : k < nl)
    (hC : At C pc (localT 1 p k pc 1)) (h1 : 1 < C.length) (hC18 : C.length < 2 ^ 18) (hl : pc + 4 < C.length) :
    CapW .room 1 KL C pc p nl Inv G hb E0 (fun j => j = k) (leafF (fun env => env k)) :=
  leafRoom hI hG (fun env env' h => h k rfl) (fun s env hx0 _ hO L0 h30 h31 h16 hh => by
    have hsw := slot_wok' (k := k) L0 hO h30 h31 hk
    obtain ⟨o1, o2, o3⟩ := hO
    have hkp : k < p ∨ 8 * (k - p + 1) ≤ (s.x 8).toNat := by omega
    have hA : At C pc ([.ld 5 8 (offOf p k)] ++ pushA 1 (pc + 1) 5 ++ localT 1 p (k + 1) (pc + 5) 0) := hC
    have l0 := hA.left.left.at 0 (by simp); simp at l0
    have hP : At C (pc + 1) (push 5 ((1 : Int) - ((pc + 1 : Nat) + 2))) := by simpa [pushA] using hA.left.right
    have ea0 : ea (s.x 8) (offOf p k) = CallProbe.slotAddr p k (s.x 8).toNat := ea_slot p k _ (by omega) hp hkp _ rfl
    let s1 : St := ⟨upd s.x 5 (s.m (CallProbe.slotAddr p k (s.x 8).toNat)), s.m, s.b⟩
    have st1 : CallProbe.step C (pc, s) = some (pc + 1, s1) := by simp [CallProbe.step, l0, CallProbe.wr, ea0, s1]
    have sf1 : Safe KL C (pc, s) := by
      simp only [Safe, l0]; refine ⟨by decide, by decide, ?_, ?_, ?_, by rw [ea0]; exact hsw⟩ <;> unfold offOf <;>
        split <;> omega
    have x31 : s1.x 31 = s.x 31 := by simp [s1, upd_ne]
    have x30 : s1.x 30 = s.x 30 := by simp [s1, upd_ne]
    have r2 := push_oom_srun (K := KL) (s := s1) hP (by rw [x31]; exact h16) (by rw [x31, x30]; exact hh) h1 hC18 hl
    refine ⟨_, SStarX.of (.head sf1 st1 r2), rfl, ?_, ?_, ?_, rfl, ?_⟩ <;> simp [s1, upd, hx0])


theorem localRoom {KL : LayW} {C : List J} {p nl hb E0 : Nat} {Inv G : St → Prop}
    (hI : InvOKH hb p Inv) (hG : ∀ s, Inv s → G s) (hp : p < 2 ^ 20) (hnl : nl < 251) (h1 : 1 < C.length)
    (hC18 : C.length < 2 ^ 18) :
    ∀ w k pc, k + w ≤ nl → At C pc (localT 1 p k pc w) → pc + 5 * w ≤ C.length →
      CapW .room 1 KL C pc p nl Inv G hb E0 (fun j => k ≤ j ∧ j < k + w) (localF k w)
  | 0, k, pc, _, _, _ => noCap (fun _ _ _ => by simp [localF, nilF]) (fun _ _ _ _ _ => rfl)
  | w + 1, k, pc, hk, hC, hl => by
    rw [localT_succ] at hC
    have hs1 := local1XS (KL := KL) (nl := nl) (k := k) (W := fun _ => False) (E0 := E0) hI hp hnl (by omega) hC.left
    rw [← oW_leaf] at hs1
    have c1 := local1Room (KL := KL) (E0 := E0) hI hG hp hnl (by omega) hC.left h1 hC18 (by omega)
    have c2 := localRoom (KL := KL) (E0 := E0) hI hG hp hnl h1 hC18 w (k + 1) (pc + 5) (by omega) (by simpa using hC.right) (by omega)
    exact (pairCap hs1 c1 c2 (fun _ _ h => h)).mono (fun j q => by rcases q with e | ⟨e1, e2⟩ <;> constructor <;> omega)


theorem run_add' {C : List J} {k l : Nat} {a b c : Nat × St} (h1 : CallProbe.run C k a = some b)
    (h2 : CallProbe.run C l b = some c) : CallProbe.run C (k + l) a = some c := by rw [run_add h1]; exact h2

/-- BNEW at the OOM exit: the heap check fails (jal to `tgt`) or the result push finds no room (header written) -/
theorem bnew_oom_srun {L : LayW} {C : List J} {pc tgt κ : Nat} (s : St) (hC : At C pc (bnewT tgt pc κ)) (hx0 : s.x 0 = 0)
    (hκ : κ < 2 ^ 40) (hsp : (s.x 31).toNat < 2 ^ 62) (h16 : 16 ≤ (s.x 31).toNat) (h31 : (s.x 30).toNat ≤ (s.x 31).toNat)
    (hroom : (s.x 31).toNat < (s.x 30).toNat + 8 * (κ + 2) + 8)
    (w0 : (s.x 30).toNat + 8 * (κ + 2) ≤ (s.x 31).toNat → wok L (s.x 30).toNat ∧ wok L ((s.x 30).toNat + 8))
    (ht : tgt < C.length) (hC18 : C.length < 2 ^ 18) (hl : pc + (bnewT tgt pc κ).length ≤ C.length) :
    ∃ s', SStar L C (pc, s) (tgt, s') ∧ s'.x 8 = s.x 8 ∧ s'.x 0 = 0 ∧ s'.x 28 = s.x 28 ∧ s'.x 29 = s.x 29 ∧
      s'.b = s.b ∧ (∀ a, a ≠ (s.x 30).toNat → a ≠ (s.x 30).toNat + 8 → s'.m a = s.m a) ∧
      (s'.m = s.m ∨ (s.x 30).toNat + 16 ≤ (s.x 31).toNat) := by
  have lt31 := (s.x 31).toNat_lt
  have lt30 := (s.x 30).toNat_lt
  have hC' : At C pc ([.addi 5 30 0] ++ (liT 6 (UInt64.ofNat ((κ + 2) * 8)) ++ ([.alu 1 6 6 30, .bgeu 31 6 2,
      .jal 0 ((tgt : Int) - ((pc + 1 + (liT 6 (UInt64.ofNat ((κ + 2) * 8))).length + 2 : Nat) : Int))] ++
      (liT 7 (UInt64.ofNat κ) ++ ([.sd 0 5 0, .sd 7 5 8, .addi 30 6 0] ++
      pushA tgt (pc + 1 + (liT 6 (UInt64.ofNat ((κ + 2) * 8))).length + 3 + (liT 7 (UInt64.ofNat κ)).length + 3) 5))))) := hC
  generalize hW : UInt64.ofNat ((κ + 2) * 8) = W at *
  generalize hK : UInt64.ofNat κ = K at *
  have hWn : W.toNat = (κ + 2) * 8 := by rw [← hW]; simp only [UInt64.toNat_ofNat']; omega
  have hKn : K.toNat = κ := by rw [← hK]; simp only [UInt64.toNat_ofNat']; omega
  have p1 := hC'.left
  have R1 : At C (pc + 1) (liT 6 W ++ ([.alu 1 6 6 30, .bgeu 31 6 2,
      .jal 0 ((tgt : Int) - ((pc + 1 + (liT 6 W).length + 2 : Nat) : Int))] ++
      (liT 7 K ++ ([.sd 0 5 0, .sd 7 5 8, .addi 30 6 0] ++ pushA tgt (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3) 5)))) := by
    simpa using hC'.right
  have p2 := R1.left
  have R2 : At C (pc + 1 + (liT 6 W).length) ([.alu 1 6 6 30, .bgeu 31 6 2,
      .jal 0 ((tgt : Int) - ((pc + 1 + (liT 6 W).length + 2 : Nat) : Int))] ++
      (liT 7 K ++ ([.sd 0 5 0, .sd 7 5 8, .addi 30 6 0] ++ pushA tgt (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3) 5))) := R1.right
  have p3 := R2.left
  have R3 : At C (pc + 1 + (liT 6 W).length + 3) (liT 7 K ++ ([.sd 0 5 0, .sd 7 5 8, .addi 30 6 0] ++
      pushA tgt (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3) 5)) := by simpa using R2.right
  have p4 := R3.left
  have R4 : At C (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length) ([.sd 0 5 0, .sd 7 5 8, .addi 30 6 0] ++
      pushA tgt (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3) 5) := R3.right
  have p5 := R4.left
  have p6 : At C (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3)
      (pushA tgt (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3) 5) := by simpa using R4.right
  have e30 : UInt64.ofNat (s.x 30).toNat = s.x 30 := by simp
  -- 1: t0 := t5
  have h1 := p1.at 0 (by simp); simp at h1
  let s1 : St := ⟨upd s.x 5 (s.x 30), s.m, s.b⟩
  have r1 : CallProbe.run C 1 (pc, s) = some (pc + 1, s1) := by
    simp [CallProbe.run, CallProbe.step, h1, CallProbe.wr, ea, e30, s1]
  have z1 : s1.x 0 = 0 := by simp [s1, upd_ne, hx0]
  -- 2: li t1 W
  obtain ⟨s2, r2, hx2, hm2, hb2⟩ := li_run (d := 6) s1 (by decide) z1 p2
  have a30 : s2.x 30 = s.x 30 := by rw [hx2]; simp [s1, upd_ne]
  have a31 : s2.x 31 = s.x 31 := by rw [hx2]; simp [s1, upd_ne]
  have a6 : s2.x 6 = W := by rw [hx2]; simp [upd_same]
  have a5 : s2.x 5 = s.x 30 := by rw [hx2]; simp [s1, upd_ne, upd_same]
  have a0 : s2.x 0 = 0 := by rw [hx2]; simp [s1, upd_ne, hx0]
  have mm2 : s2.m = s.m := hm2
  -- 3: t1 := t1 + t5
  have h3 := p3.at 0 (by simp); simp at h3
  let s3 : St := ⟨upd s2.x 6 (W + s.x 30), s2.m, s2.b⟩
  have r3 : CallProbe.run C 1 (pc + 1 + (liT 6 W).length, s2) = some (pc + 1 + (liT 6 W).length + 1, s3) := by
    simp [CallProbe.run, CallProbe.step, h3, CallProbe.wr, aluf, a6, a30, s3]
  have q1 : SR L C 1 (pc, s) := SR.one (by simp [Safe, h1]; have := (s.x 30).toNat_lt; omega)
  have q2 := li_sr (K := L) (d := 6) (v := W) s1 (by decide) (by decide) z1 p2
  have q3 : SR L C 1 (pc + 1 + (liT 6 W).length, s2) := SR.one (by simp [Safe, h3])
  have h4 := p3.at 1 (by simp); simp at h4
  have h5j := p3.at 2 (by simp); simp at h5j
  have hsum : (W + s.x 30).toNat = (κ + 2) * 8 + (s.x 30).toNat := by
    rw [UInt64.toNat_add, hWn]; simp; omega
  have q4 : SR L C 1 (pc + 1 + (liT 6 W).length + 1, s3) := SR.one (by simp [Safe, h4])
  have hlen : (bnewT tgt pc κ).length = 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3 + 4 := by
    rw [← hW, ← hK]; simp [bnewT, pushA, push]; omega
  by_cases hfit : (s.x 30).toNat + 8 * (κ + 2) ≤ (s.x 31).toNat
  · -- the heap fits, the result push does not
    have r4 : CallProbe.step C (pc + 1 + (liT 6 W).length + 1, s3) = some (pc + 1 + (liT 6 W).length + 3, s3) := by
      have : (s3.x 6).toNat ≤ (s3.x 31).toNat := by
        simp [s3, upd_same, upd_ne, a31, hsum]; omega
      rw [s_bgeu_t h4 (by simpa using this)]
      first | rfl | (congr 1; congr 1; omega) | (congr 1; omega)
    have z3 : s3.x 0 = 0 := by simp [s3, upd_ne, a0]
    obtain ⟨s5, r5, hx5, hm5, hb5⟩ := li_run (d := 7) s3 (by decide) z3 p4
    have b30 : s5.x 30 = s.x 30 := by rw [hx5]; simp [s3, upd_ne, a30]
    have b31 : s5.x 31 = s.x 31 := by rw [hx5]; simp [s3, upd_ne, a31]
    have b6 : s5.x 6 = W + s.x 30 := by rw [hx5]; simp [s3, upd_ne, upd_same]
    have b5 : s5.x 5 = s.x 30 := by rw [hx5]; simp [s3, upd_ne, a5]
    have b7 : s5.x 7 = K := by rw [hx5]; simp [upd_same]
    have b0 : s5.x 0 = 0 := by rw [hx5]; simp [s3, upd_ne, a0]
    have mm5 : s5.m = s.m := by rw [hm5]; exact mm2
    have h6 := p5.at 0 (by simp); have h7 := p5.at 1 (by simp); have h8 := p5.at 2 (by simp)
    simp at h6 h7 h8
    have eT0 : ea (s5.x 5) 0 = (s.x 30).toNat := by simp [ea, b5]
    have eT8 : ea (s5.x 5) 8 = (s.x 30).toNat + 8 := by simp [ea, b5]; omega
    let s8 : St := ⟨upd s5.x 30 (W + s.x 30), upd (upd s5.m (s.x 30).toNat 0) ((s.x 30).toNat + 8) K, s5.b⟩
    have ea0 : ∀ b : UInt64, ea b 0 = b.toNat := fun b => by simp [ea]
    have e6 : UInt64.ofNat (ea (W + s.x 30) 0) = W + s.x 30 := by rw [ea0]; exact UInt64.ofNat_toNat
    have r678 : CallProbe.run C 3 (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length, s5) =
        some (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3, s8) := by
      simp [CallProbe.run, CallProbe.step, h6, h7, h8, CallProbe.wr, eT0, eT8, b0, b7, e6, b6, s8]
    have y30 : s8.x 30 = W + s.x 30 := by simp [s8, upd_same]
    have y31 : s8.x 31 = s.x 31 := by simp [s8, upd_ne, b31]
    have hh8 : (s8.x 31).toNat < (s8.x 30).toNat + 8 := by rw [y30, y31, hsum]; omega
    have r4' : CallProbe.run C 1 (pc + 1 + (liT 6 W).length + 1, s3) = some (pc + 1 + (liT 6 W).length + 3, s3) := by simp [CallProbe.run, r4]
    have q5 := li_sr (K := L) (d := 7) (v := K) s3 (by decide) (by decide) z3 p4
    obtain ⟨ww0, ww1⟩ := w0 hfit
    have q6 : SR L C 3 (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length, s5) := by
      intro j hj c hc
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · simp [CallProbe.run] at hc; subst hc; simp only [Safe, h6, eT0]; exact ⟨by decide, by decide, by decide, by decide, by omega, ww0⟩
      · simp [CallProbe.run, CallProbe.step, h6, eT0] at hc; subst hc; simp only [Safe, h7, eT8]; exact ⟨by decide, by decide, by decide, by decide, by omega, ww1⟩
      · simp [CallProbe.run, CallProbe.step, h6, h7, eT0, eT8] at hc; subst hc
        simp only [Safe, h8, b6]
        refine ⟨by decide, by decide, by decide, by decide, by omega, ?_⟩
        rw [hsum]; omega
    have pre : SStar L C (pc, s) (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3, s8) :=
      sstar_of_run (run_add' r1 (run_add' r2 (run_add' r3 (run_add' r4' (run_add' r5 r678)))))
        (q1.add r1 (q2.add r2 (q3.add r3 (q4.add r4' (q5.add r5 (q6))))))
    have p6' : At C (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3)
        (push 5 ((tgt : Int) - (((pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3 : Nat) : Int) + 2))) := by
      simpa [pushA] using p6
    have r9 := push_oom_srun (K := L) (s := s8) p6' (by rw [y31]; omega) hh8 ht hC18 (by omega)
    refine ⟨_, pre.trans r9, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr (by omega)⟩
    · simp [s8, upd_ne, hx5, s3, hx2, s1]
    · simp [s8, upd_ne, b0]
    · simp [s8, upd_ne, hx5, s3, hx2, s1]
    · simp [s8, upd_ne, hx5, s3, hx2, s1]
    · simp [s8, hb5, s3, hb2, s1]
    · intro a h1' h2'; simp [s8, upd, h1', h2', mm5]
  · -- the heap does not fit: bgeu falls through to the jal
    have r4 : CallProbe.step C (pc + 1 + (liT 6 W).length + 1, s3) = some (pc + 1 + (liT 6 W).length + 2, s3) := by
      have : ¬ (s3.x 6).toNat ≤ (s3.x 31).toNat := by
        simp [s3, upd_same, upd_ne, a31, hsum]; omega
      rw [s_bgeu_f h4 (by simpa using this)]
    have r5 : CallProbe.step C (pc + 1 + (liT 6 W).length + 2, s3) = some (tgt, s3) := by
      rw [s_jal h5j]; simp [CallProbe.wr]; omega
    have sf5 : Safe L C (pc + 1 + (liT 6 W).length + 2, s3) := by simp [Safe, h5j]; omega
    have pre : SStar L C (pc, s) (pc + 1 + (liT 6 W).length + 1, s3) :=
      sstar_of_run (run_add' r1 (run_add' r2 r3)) (q1.add r1 (q2.add r2 (q3)))
    refine ⟨s3, pre.trans (.head (by simp [Safe, h4]) r4 (.head sf5 r5 (.refl _))), ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inl (by simp [s3, mm2])⟩
    · simp [s3, upd_ne, hx2, s1]
    · simp [s3, upd_ne, a0]
    · simp [s3, upd_ne, hx2, s1]
    · simp [s3, upd_ne, hx2, s1]
    · simp [s3, hb2, s1]
    · intro a _ _; simp [s3, mm2]


theorem bnewRoom {KL : LayW} {C : List J} {pc κ p nl hb E0 : Nat} {Inv G : St → Prop} {R : Nat → Prop}
    (hI : InvOKH hb p Inv) (hG : ∀ s, Inv s → G s) (hC : At C pc (bnewT 1 pc κ)) (hκ : κ < 2 ^ 40)
    (he : E0 < 2 ^ 62) (h1 : 1 < C.length) (hC18 : C.length < 2 ^ 18) (hl : pc + (bnewT 1 pc κ).length ≤ C.length) :
    CapW .room 1 KL C pc p nl Inv G hb E0 R (oneF (bnewF κ)) where
  stable := fun _ _ _ _ _ => rfl
  cap := fun s env H I0 z0 F0 O0 R0 L0 A0 hS => by
    have h2 := map_cap hS
    simp only [bnewF] at h2
    cases e : bnewS κ env (s.x 31).toNat H with
    | some _ => rw [e] at h2; simp [ofO] at h2
    | none =>
      simp only [bnewS] at e
      split at e
      · simp at e
      rename_i hc
      have top0 : (s.x 30).toNat = H.top := R0.2.2.2.2.1
      have hb30 : hb ≤ (s.x 30).toNat := by have := R0.2.1; omega
      have h31 : (s.x 30).toNat ≤ (s.x 31).toNat := by have := R0.2.2.1; omega
      have hsp : (s.x 31).toNat < 2 ^ 62 := by have := L0.top; obtain ⟨o1, o2, o3⟩ := O0; omega
      have hal := R0.2.2.2.1
      obtain ⟨s', r, e8, z', e28, e29, eb, hm, hm'⟩ := bnew_oom_srun (L := KL) s hC z0 hκ hsp (hrel_sp R0) h31
        (by omega) (fun hfit => ⟨L0.wok hb30 (by have := L0.top; obtain ⟨o1, o2, o3⟩ := O0; omega) (by omega),
          L0.wok (by omega) (by have := L0.top; obtain ⟨o1, o2, o3⟩ := O0; omega) (by omega)⟩) h1 hC18 hl
      refine ⟨s', SStarX.of r, hG _ (hI s s' I0 e8 e28 e29 eb (fun a ha => ?_)), z'⟩
      rcases hm' with hm' | hm'
      · rw [hm']
      · apply hm a <;> intro e <;> apply ha <;> obtain ⟨o1, o2, o3⟩ := O0 <;> omega

end Templates
