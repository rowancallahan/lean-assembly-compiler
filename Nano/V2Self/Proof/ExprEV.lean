/- The expression leaves as instances of Opus's environment contract `Templates.EV` (Proof/Templates.lean), so that IF/LET/BIN
compose over them.  `leaf_EV` turns "one push, memory changes only at t6−8" into an EV; `const_EV`, `local_EV`, `len_EV` are the leaves. -/
import Nano.V2Self.Proof.Templates
import Nano.V2Self.Proof.Expr
namespace Templates
open CallProbe

/-- a leaf that pushes `V env` at t6 − 8, touching only registers 5, 6, 7, 14, 31 and that one cell -/
theorem leaf_EV {C : List J} {pc len n p nl : Nat} {Inv : St → Prop} {R W : Nat → Prop} {V : (Nat → UInt64) → UInt64}
    (hI : InvOK p Inv) (hn : 1 ≤ n) (hst : ∀ env env', (∀ k, R k → env k = env' k) → V env = V env')
    (hgo : ∀ (s : St) (env : Nat → UInt64), Inv s → s.x 0 = 0 → Frame p nl s env → FrameOK p nl s →
      (s.x 30).toNat + 8 ≤ (s.x 31).toNat →
      ∃ s', Star C (pc, s) (pc + len, s') ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 ∧
        s'.m = upd s.m ((s.x 31).toNat - 8) (V env) ∧ s'.x 8 = s.x 8 ∧ s'.x 28 = s.x 28 ∧ s'.x 29 = s.x 29 ∧
        s'.x 30 = s.x 30 ∧ s'.x 0 = s.x 0) :
    EV C pc len n p nl Inv R W V where
  stable := hst
  run := fun s env hI0 hx0 hF hO room => by
    obtain ⟨s', r, p31, hm, e8, e28, e29, e30, e0⟩ := hgo s env hI0 hx0 hF hO (by omega)
    obtain ⟨o1, o2, o3⟩ := hO
    have hne : ∀ k, k < nl → slotAddr p (s.x 8).toNat k ≠ (s.x 31).toNat - 8 := fun k hk => by
      have := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk; omega
    refine ⟨s', env, r, ?_, by rw [e0, hx0], p31, by rw [hm]; exact upd_same _ _ _, e8, e30, ?_, fun _ _ => rfl, ?_⟩
    · apply hI s s' hI0 e8 e28 e29 e30
      intro a ha; rw [hm]; apply upd_other; intro e; apply ha; rw [e]
      exact ⟨by omega, by omega⟩
    · intro k hk; show s'.m (slotAddr p (s'.x 8).toNat k) = env k
      rw [e8, hm, upd_other _ _ (hne k hk)]; exact hF k hk
    · intro a ha _; rw [hm]; apply upd_other; omega

/-- CONST v -/
theorem const_EV {C : List J} {pc tgt n p nl : Nat} {Inv : St → Prop} {R W : Nat → Prop} {v : UInt64}
    (hI : InvOK p Inv) (hn : 1 ≤ n) (hC : At C pc (constT tgt pc v)) :
    EV C pc ((liT 5 v).length + 4) n p nl Inv R W (fun _ => v) :=
  leaf_EV hI hn (fun _ _ _ => rfl) (fun s env _ hx0 _ _ room => by
    obtain ⟨s', hr, hx, hm⟩ := const_run s hx0 hC room
    have lt64 := (s.x 31).toNat_lt
    refine ⟨s', run_star hr, ?_, hm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx]; simp only [upd_same]; simp only [UInt64.toNat_ofNat']; omega
    · rw [hx]; simp [upd_ne]
    · rw [hx]; simp [upd_ne]
    · rw [hx]; simp [upd_ne]
    · rw [hx]; simp [upd_ne]
    · rw [hx]; simp [upd_ne])

/-- the two slot-address definitions agree on a valid frame -/
theorem slotAddr_eq {p nl S0 k : Nat} (h : 8 * (nl - p) ≤ S0) (hp : p ≤ nl) (hk : k < nl) :
    CallProbe.slotAddr p k S0 = slotAddr p S0 k := by
  unfold CallProbe.slotAddr slotAddr slotOff; split <;> omega

theorem offOf_eq (p k : Nat) : CallProbe.offOf p k = slotOff p k := by
  unfold CallProbe.offOf slotOff; split <;> rfl

/-- LOCAL of width 1: `ld t0, off(s0)`, then the checked push -/
theorem local1_run {C : List J} {pc tgt p k : Nat} (s : St) (hC : At C pc (localT tgt p k pc 1)) (hs0 : (s.x 8).toNat < 2 ^ 62)
    (hp : p < 2 ^ 20) (hk : k < p ∨ 8 * (k - p + 1) ≤ (s.x 8).toNat) (hh : (s.x 30).toNat + 8 ≤ (s.x 31).toNat) :
    ∃ s', run C 4 (pc, s) = some (pc + 5, s') ∧
      s'.x = upd (upd s.x 5 (s.m (CallProbe.slotAddr p k (s.x 8).toNat))) 31 (UInt64.ofNat ((s.x 31).toNat - 8)) ∧
      s'.m = upd s.m ((s.x 31).toNat - 8) (s.m (CallProbe.slotAddr p k (s.x 8).toNat)) := by
  have hA : At C pc ([.ld 5 8 (offOf p k)] ++ pushA tgt (pc + 1) 5 ++ localT tgt p (k + 1) (pc + 5) 0) := hC
  have hL : At C pc [.ld 5 8 (offOf p k)] := hA.left.left
  have hP : At C (pc + 1) (pushA tgt (pc + 1) 5) := by simpa using hA.left.right
  have l0 := hL.at 0 (by simp); simp at l0
  have ea0 : ea (s.x 8) (offOf p k) = CallProbe.slotAddr p k (s.x 8).toNat := ea_slot p k _ hs0 hp hk _ rfl
  let v := s.m (CallProbe.slotAddr p k (s.x 8).toNat)
  let s1 : St := ⟨upd s.x 5 v, s.m, s.b⟩
  have r1 : run C 1 (pc, s) = some (pc + 1, s1) := by simp [run, step, l0, wr, ea0, v, s1]
  have x31 : s1.x 31 = s.x 31 := by simp [s1, upd_ne]
  have x30 : s1.x 30 = s.x 30 := by simp [s1, upd_ne]
  have hh1 : (s1.x 30).toNat + 8 ≤ (s1.x 31).toNat := by rw [x31, x30]; exact hh
  have r2 := push_run (s := s1) (by simpa [pushA] using hP) (by decide) (by decide) hh1
  refine ⟨⟨upd (upd s.x 5 v) 31 (UInt64.ofNat ((s.x 31).toNat - 8)), upd s.m ((s.x 31).toNat - 8) v, s.b⟩, ?_, rfl, rfl⟩
  rw [show 4 = 1 + 3 from rfl, run_add r1, r2]
  have e5 : s1.x 5 = v := by simp [s1, upd_same]
  rw [e5, x31]

/-- LOCAL k (width 1) -/
theorem local_EV {C : List J} {pc tgt n p nl k : Nat} {Inv : St → Prop} {W : Nat → Prop}
    (hI : InvOK p Inv) (hn : 1 ≤ n) (hp : p < 2 ^ 20) (hk : k < nl) (hC : At C pc (localT tgt p k pc 1)) :
    EV C pc 5 n p nl Inv (fun j => j = k) W (fun env => env k) :=
  leaf_EV hI hn (fun env env' h => h k rfl) (fun s env _ hx0 hF hO room => by
    obtain ⟨o1, o2, o3⟩ := hO
    have hv : CallProbe.slotAddr p k (s.x 8).toNat = slotAddr p (s.x 8).toNat k := slotAddr_eq (by omega) o2 hk
    have hkp : k < p ∨ 8 * (k - p + 1) ≤ (s.x 8).toNat := by omega
    obtain ⟨s', hr, hx, hm⟩ := local1_run s hC (by omega) hp hkp room
    have lt64 := (s.x 31).toNat_lt
    rw [hv] at hx hm
    refine ⟨s', run_star hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx]; simp only [upd_same]; simp only [UInt64.toNat_ofNat']; omega
    · rw [hm, hF k hk]
    · rw [hx]; simp [upd_ne]
    · rw [hx]; simp [upd_ne]
    · rw [hx]; simp [upd_ne]
    · rw [hx]; simp [upd_ne]
    · rw [hx]; simp [upd_ne])

/-- BIN: A; B; the 5-instruction binary step (`binT op`) -/
theorem bin_EV {C : List J} {pc la lb nA nB N p nl op : Nat} {Inv : St → Prop} {RA WA RB WB : Nat → Prop}
    {VA VB : (Nat → UInt64) → UInt64} (hI : InvOK p Inv)
    (hA : EV C pc la nA p nl Inv RA WA VA) (hB : EV C (pc + la) lb nB p nl Inv RB WB VB)
    (hBin : At C (pc + la + lb) (binT op)) (hsc : ∀ k, RB k → ¬ WA k) (hnB : 1 ≤ nB) (h1 : nA ≤ N) (h2 : nB + 1 ≤ N) :
    EV C pc (la + lb + 5) N p nl Inv (fun k => RA k ∨ RB k) (fun k => WA k ∨ WB k)
      (fun env => aluf op (VA env) (VB env)) where
  stable := fun env env' h => by
    rw [hA.stable env env' (fun k hk => h k (Or.inl hk)), hB.stable env env' (fun k hk => h k (Or.inr hk))]
  run := fun s env hI0 hx0 hF hO room => by
    obtain ⟨s1, env1, r1, I1, z1, p1, v1, e81, e301, F1, ag1, m1⟩ := hA.run s env hI0 hx0 hF hO (by omega)
    obtain ⟨o1, o2, o3⟩ := hO
    have lt64 := (s.x 31).toNat_lt
    have hO1 : FrameOK p nl s1 := ⟨by rw [p1, e81]; omega, o2, by rw [e81]; omega⟩
    obtain ⟨s2, env2, r2, I2, z2, p2, v2, e82, e302, F2, ag2, m2⟩ :=
      hB.run s1 env1 I1 z1 F1 hO1 (by rw [e301, p1]; omega)
    have hne : ∀ k, k < nl → slotAddr p (s.x 8).toNat k ≠ (s.x 31).toNat - 8 := fun k hk => by
      have := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk; omega
    have vB : s2.m ((s.x 31).toNat - 8 - 8) = VB env := by
      rw [p1] at p2 v2; rw [v2]
      exact hB.stable env1 env (fun k hk => ag1 k (hsc k hk))
    have vA : s2.m ((s.x 31).toNat - 8) = VA env := by
      rw [m2 _ (by omega) (fun k hk _ => by rw [e81]; exact (hne k hk).symm)]; exact v1
    -- the binary step
    have hl : (s2.x 31).toNat + 16 < 2 ^ 63 := by rw [p2, p1]; omega
    have rB := bin_run s2 (by simpa using hBin) hl
    have e2' : (s2.x 31).toNat + 8 = (s.x 31).toNat - 8 := by rw [p2, p1]; omega
    have e2'' : (s2.x 31).toNat = (s.x 31).toNat - 8 - 8 := by rw [p2, p1]
    rw [e2', e2'', vA, vB] at rB
    have key : ∃ s3 : St, run C 5 (pc + la + lb, s2) = some (pc + la + lb + 5, s3) ∧
        (s3.x 31).toNat = (s.x 31).toNat - 8 ∧ s3.m = upd s2.m ((s.x 31).toNat - 8) (aluf op (VA env) (VB env)) ∧
        (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 31 → s3.x r = s2.x r) := by
      refine ⟨_, rB, ?_, rfl, ?_⟩
      · simp only [upd_ne _ _ (show (31:Nat) ≠ 5 by decide), upd_same, UInt64.toNat_ofNat']; omega
      · intro r h5 h6 h31; simp [upd_ne, h5, h6, h31]
    obtain ⟨s3, rr, q31, qm, qx⟩ := key
    have q8 : s3.x 8 = s.x 8 := by rw [qx 8 (by decide) (by decide) (by decide), e82, e81]
    have q30 : s3.x 30 = s.x 30 := by rw [qx 30 (by decide) (by decide) (by decide), e302, e301]
    have q28 : s3.x 28 = s2.x 28 := qx 28 (by decide) (by decide) (by decide)
    have q29 : s3.x 29 = s2.x 29 := qx 29 (by decide) (by decide) (by decide)
    have z3 : s3.x 0 = 0 := by rw [qx 0 (by decide) (by decide) (by decide), z2]
    have I3 : Inv s3 := by
      apply hI s2 s3 I2 (by rw [q8, e82, e81]) q28 q29 (by rw [q30, e302, e301])
      intro a ha; rw [qm]; apply upd_other; intro e; apply ha; rw [e]
      exact ⟨by rw [e302, e301]; omega, by rw [e82, e81]; omega⟩
    have F3 : Frame p nl s3 env2 := by
      intro k hk
      show s3.m (slotAddr p (s3.x 8).toNat k) = env2 k
      rw [q8, qm, upd_other _ _ (hne k hk)]
      have := F2 k hk; rw [e82, e81] at this; exact this
    refine ⟨s3, env2, ?_, I3, z3, q31, ?_, q8, q30, F3, ?_, ?_⟩
    · have : pc + la + lb + 5 = pc + (la + lb + 5) := by omega
      rw [← this]; exact (r1.trans r2).trans (run_star rr)
    · rw [qm, upd_same]
    · intro k hk
      rw [not_or] at hk
      rw [ag2 k hk.2, ag1 k hk.1]
    · intro a ha hW
      rw [qm, upd_other _ _ (by omega)]
      rw [m2 a (by omega) (fun k hk wk => by rw [e81]; exact hW k hk (Or.inr wk))]
      exact m1 a ha (fun k hk wk => hW k hk (Or.inl wk))

end Templates
