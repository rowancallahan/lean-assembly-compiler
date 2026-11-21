/- Safe retrofit (EVS) P1: leaves as `EVHwS` (Opus box E).  Same proofs as EVXP with SafeX runs; the pushed cell
t6 − 8 is a work cell by `Lay.wok` (hb ≤ H.top ≤ t6 − 8, t6 ≤ s0 ≤ frame top ≤ E0, aligned). -/
import Nano.Run.EVSDefs
namespace Templates
open CallProbe SimW SafeRun

/-- the cell below t6 is a work cell when there is room -/
theorem push_wok {KL : LayW} {hb E0 p nl : Nat} {s : St} {H : Hp} (L : Lay KL hb E0 p s) (O : FrameOK p nl s)
    (R : HRel hb s H) (room : H.top + 8 ≤ (s.x 31).toNat) : wok KL ((s.x 31).toNat - 8) := by
  have := R.2.1; have := L.top; have := L.a31; obtain ⟨o1, o2, o3⟩ := O
  exact L.wok (by omega) (by omega) (by omega)

theorem leafX {KL : LayW} {C : List J} {pc len p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop}
    {V : Env → UInt64}
    (hI : InvOKH hb p Inv) (hst : ∀ env env', (∀ k, R k → env k = env' k) → V env = V env')
    (hgo : ∀ (s : St) (env : Env), Inv s → s.x 0 = 0 → Frame p nl s env → FrameOK p nl s →
      (s.x 30).toNat + 8 ≤ (s.x 31).toNat → wok KL ((s.x 31).toNat - 8) → Lay KL hb E0 p s →
      hb ≤ (s.x 30).toNat →
      ∃ s', SStarX KL C (pc, s) (pc + len, s') ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 ∧
        s'.m = upd s.m ((s.x 31).toNat - 8) (V env) ∧ s'.x 8 = s.x 8 ∧ s'.x 28 = s.x 28 ∧ s'.x 29 = s.x 29 ∧
        s'.x 30 = s.x 30 ∧ s'.x 0 = s.x 0) :
    EVHwS KL C pc len p nl Inv hb E0 R W 1 (leafS V) where
  stable := fun env env' sp H h => by simp only [leafS]; rw [hst env env' h]
  run := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [leafS] at hS
    split at hS
    rotate_left; · simp at hS
    rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hS; obtain ⟨rfl, rfl⟩ := hS
    have top0 : (s.x 30).toNat = H.top := R0.2.2.2.2.1
    obtain ⟨s', r, p31, hm, e8, e28, e29, e30, e0⟩ :=
      hgo s env I0 z0 F0 O0 (by omega) (push_wok L0 O0 R0 hc) L0 (by have := R0.2.1; omega)
    obtain ⟨o1, o2, o3⟩ := O0
    have hne : ∀ k, k < nl → slotAddr p (s.x 8).toNat k ≠ (s.x 31).toNat - 8 := fun k hk => by
      have := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk; omega
    refine ⟨s', env, r, ?_, by rw [e0, z0], by rw [p31], rfl, ?_, e8, ?_, fun _ _ => rfl, ?_, A0, ?_⟩
    · apply hI s s' I0 e8 e28 e29 r.star.b r.star.w
      intro a ha; rw [hm]; apply upd_other; intro e; apply ha; rw [e]
      exact ⟨by have := R0.2.1; omega, by omega⟩
    · intro i hi; have : i = 0 := by omega
      subst this; rw [hm]; simp [upd_same]
    · intro k hk; show s'.m (slotAddr p (s'.x 8).toNat k) = env k
      rw [e8, hm, upd_other _ _ (hne k hk)]; exact F0 k hk
    · exact HRel_stack R0 e30 (by rw [p31]; omega) (fun a _ h2 => by rw [hm]; apply upd_other; omega)
    · intro a ha _; rw [hm]; apply upd_other; omega

/-- CONST v -/
theorem constX {KL : LayW} {C : List J} {pc p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop} {v : UInt64}
    (hI : InvOKH hb p Inv) (hC : At C pc (constT 1 pc v)) :
    EVHwS KL C pc ((liT 5 v).length + 4) p nl Inv hb E0 R W 1 (leafS (fun _ => v)) :=
  leafX hI (fun _ _ _ => rfl) (fun s env _ hx0 _ _ room hw _ _ => by
    obtain ⟨s', hr, hx, hm, hb⟩ := const_srun (K := KL) s hx0 hC room hw
    have lt64 := (s.x 31).toNat_lt
    refine ⟨s', hr, ?_, hm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx]; simp only [upd_same]; simp only [UInt64.toNat_ofNat']; omega
    all_goals rw [hx]; simp [upd_ne])

/-- ISIZE / LEN -/
theorem lenX {KL : LayW} {C : List J} {pc p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop} {c29 : UInt64}
    (hI : InvOKH hb p Inv) (hInv : ∀ s, Inv s → s.x 29 = c29) (hC : At C pc (lenT 1 pc)) :
    EVHwS KL C pc 4 p nl Inv hb E0 R W 1 (leafS (fun _ => c29)) :=
  leafX hI (fun _ _ _ => rfl) (fun s env I0 hx0 _ _ room hw _ _ => by
    have lt64 := (s.x 31).toNat_lt
    have hr := len_srun (K := KL) s hC room hw
    refine ⟨_, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [upd_same, UInt64.toNat_ofNat']; omega
    · simp [hInv s I0]
    all_goals simp [upd_ne])

/-- a frame slot is a work cell -/
theorem slot_wok {KL : LayW} {hb E0 p nl k : Nat} {s : St} (L : Lay KL hb E0 p s) (O : FrameOK p nl s)
    (h30 : hb ≤ (s.x 30).toNat) (room : (s.x 30).toNat + 8 ≤ (s.x 31).toNat) (hk : k < nl) :
    wok KL (CallProbe.slotAddr p k (s.x 8).toNat) := by
  have := L.top; have := L.a8; obtain ⟨o1, o2, o3⟩ := O
  unfold CallProbe.slotAddr
  split <;> exact L.wok (by omega) (by omega) (by omega)

/-- LOCAL k, width 1 -/
theorem local1X {KL : LayW} {C : List J} {pc p nl hb E0 k : Nat} {Inv : St → Prop} {W : Nat → Prop}
    (hI : InvOKH hb p Inv) (hp : p < 2 ^ 20) (hnl : nl < 251) (hk : k < nl) (hC : At C pc (localT 1 p k pc 1)) :
    EVHwS KL C pc 5 p nl Inv hb E0 (fun j => j = k) W 1 (leafS (fun env => env k)) :=
  leafX hI (fun env env' h => h k rfl) (fun s env _ hx0 hF hO room hpw L0 h30 => by
    have hsw := slot_wok (k := k) L0 hO h30 room hk
    obtain ⟨o1, o2, o3⟩ := hO
    have hv : CallProbe.slotAddr p k (s.x 8).toNat = slotAddr p (s.x 8).toNat k := slotAddr_eq (by omega) o2 hk
    have hkp : k < p ∨ 8 * (k - p + 1) ≤ (s.x 8).toNat := by omega
    obtain ⟨s', hr, hx, hm⟩ := local1_run s hC (by omega) hp hkp room
    have ss : SStarX KL C (pc, s) (pc + 5, s') := (local_srun 1 k pc s hC (by omega) hp
      (fun i hi => by
        have : i = 0 := by omega
        subst this; refine ⟨hkp, ?_⟩; simp only [Nat.add_zero]; rw [hv]
        exact slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk)
      (by omega)
      (fun i hi => by
        have : i = 0 := by omega
        subst this; simp only [Nat.add_zero, Nat.zero_add, Nat.mul_one]
        refine ⟨hsw, hpw, ?_, ?_⟩ <;> unfold offOf <;> split <;> omega)
      _ hr)
    have lt64 := (s.x 31).toNat_lt
    rw [hv] at hx hm
    refine ⟨s', ss, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx]; simp only [upd_same]; simp only [UInt64.toNat_ofNat']; omega
    · rw [hm, hF k hk]
    all_goals rw [hx]; simp [upd_ne])

end Templates