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

end Templates
