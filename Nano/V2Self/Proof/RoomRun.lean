/- Opus box E: the out-of-memory exit (`room`) of the leaf templates as SAFE runs: the checked push finds no room
(t6 − 8 < t5) and jumps to the OOM stub (word 1). -/
import Nano.V2Self.Proof.CapNode
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
    (hgo : ∀ (s : St), s.x 0 = 0 → 16 ≤ (s.x 31).toNat → (s.x 31).toNat < (s.x 30).toNat + 8 →
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
    obtain ⟨s', r, hm, e8, e28, e29, eb, z'⟩ := hgo s z0 (hrel_sp R0) (by omega)
    exact ⟨s', r, hG _ (hI s s' I0 e8 e28 e29 eb (fun a _ => by rw [hm])), z'⟩

theorem constRoom {KL : LayW} {C : List J} {pc p nl hb E0 : Nat} {Inv G : St → Prop} {R : Nat → Prop} {v : UInt64}
    (hI : InvOKH hb p Inv) (hG : ∀ s, Inv s → G s) (hC : At C pc (constT 1 pc v)) (h1 : 1 < C.length)
    (hC18 : C.length < 2 ^ 18) (hl : pc + (liT 5 v).length + 3 < C.length) :
    CapW .room 1 KL C pc p nl Inv G hb E0 R (leafF (fun _ => v)) :=
  leafRoom hI hG (fun _ _ _ => rfl) (fun s hx0 h16 hh => by
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
  leafRoom hI hG (fun _ _ _ => rfl) (fun s hx0 h16 hh => by
    have r := push_oom_srun (K := KL) (s := s) (by simpa [lenT, pushA] using hC) h16 hh h1 hC18 hl
    refine ⟨_, SStarX.of r, rfl, ?_, ?_, ?_, rfl, ?_⟩ <;> simp [upd, hx0])

end Templates
