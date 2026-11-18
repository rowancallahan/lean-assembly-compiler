/- Codegen templates beyond the expression leaves (Astra-11, Opus box): IF (value mode).  Fragments are specified by
the value contract `PV`: with n words of stack room the code at [pc, pc+len) pushes ONE word `V s`, keeps s0 (x8),
t5 (x30) and every cell at or above the old t6; `V` only depends on s0 and the cells at or above t6 (`stable`).
The IF layout is Gen's (g36 visit + g37 items 3/4/5): A; B; pop2 (ld t1,0(t6); ld t0,8(t6); t6 += 16);
beq/bltu t0,t1,+8; jal ELSE; T; jal END; ELSE: E; END. -/
import Nano.V2Self.Proof.Call

namespace Templates
open CallProbe

structure PV (C : List J) (pc len n : Nat) (V : St → UInt64) : Prop where
  run : ∀ s : St, (s.x 30).toNat + 8 * n ≤ (s.x 31).toNat → (s.x 31).toNat < 2 ^ 62 →
    ∃ s', Star C (pc, s) (pc + len, s') ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 ∧
      s'.m ((s.x 31).toNat - 8) = V s ∧ s'.x 8 = s.x 8 ∧ s'.x 30 = s.x 30 ∧
      ∀ a, (s.x 31).toNat ≤ a → s'.m a = s.m a
  stable : ∀ s s' : St, s'.x 8 = s.x 8 → (∀ a, (s.x 31).toNat ≤ a → s'.m a = s.m a) → V s' = V s

theorem At.sub {C pos l} (h : At C pos l) {i} (hi : i < l.length) {x} (hx : l[i]? = some x) : C[pos + i]? = some x := by
  rw [h.at i hi, hx]

theorem ofNat_toNat_small (v : Nat) (h : v < 2 ^ 64) : (UInt64.ofNat v).toNat = v := by simp; omega

/-- the IF head after both operands: pop2, `beq t0, t1, +2`, `jal 0 (lt+2)` -/
def ifHead (lt : Nat) : List J := [.ld 6 31 0, .ld 5 31 8, .addi 31 31 16, .beq 5 6 2, .jal 0 ((lt : Int) + 2)]

/-- **IF (==), value mode**: A; B; head; T; jal END; E pushes `if VA = VB then VT else VE` -/
theorem if_eq {C : List J} {pc la lb lt le nA nB nT nE N : Nat} {VA VB VT VE : St → UInt64}
    (hA : PV C pc la nA VA) (hB : PV C (pc + la) lb nB VB)
    (hH : At C (pc + la + lb) (ifHead lt)) (hT : PV C (pc + la + lb + 5) lt nT VT)
    (hJ : C[pc + la + lb + 5 + lt]? = some (.jal 0 ((le : Int) + 1)))
    (hE : PV C (pc + la + lb + 6 + lt) le nE VE)
    (h1 : nA ≤ N) (h2 : nB + 1 ≤ N) (h3 : nT ≤ N) (h4 : nE ≤ N) (h5 : 2 ≤ N) :
    PV C pc (la + lb + 6 + lt + le) N (fun s => if VA s = VB s then VT s else VE s) where
  stable := fun s s' e8 em => by
    rw [hA.stable s s' e8 em, hB.stable s s' e8 em, hT.stable s s' e8 em, hE.stable s s' e8 em]
  run := fun s room lim => by
    -- A
    obtain ⟨s1, r1, p1, v1, e81, e301, m1⟩ := hA.run s (by omega) lim
    -- B
    obtain ⟨s2, r2, p2, v2, e82, e302, m2⟩ := hB.run s1 (by rw [e301, p1]; omega) (by rw [p1]; omega)
    have sp := (s.x 31).toNat
    rw [p1] at p2 v2 m2
    -- the head: two loads and the pop
    have c0 := hH.at 0 (by simp [ifHead]); have c1 := hH.at 1 (by simp [ifHead])
    have c2 := hH.at 2 (by simp [ifHead]); have c3 := hH.at 3 (by simp [ifHead]); have c4 := hH.at 4 (by simp [ifHead])
    simp [ifHead] at c0 c1 c2 c3 c4
    have va : s2.m ((s.x 31).toNat - 8) = VA s := by rw [m2 _ (by omega), v1]
    have vb : s2.m ((s.x 31).toNat - 8 - 8) = VB s := by
      rw [v2, hB.stable s s1 e81 (fun a ha => m1 a ha)]
    have ea0 : ea (s2.x 31) 0 = (s.x 31).toNat - 8 - 8 := by simp [ea, p2]
    have ea8 : ea (s2.x 31) 8 = (s.x 31).toNat - 8 := by simp [ea, p2]; omega
    have ea16 : ea (s2.x 31) 16 = (s.x 31).toNat := by simp [ea, p2]; omega
    let s3 : St := ⟨upd (upd (upd s2.x 6 (VB s)) 5 (VA s)) 31 (UInt64.ofNat (s.x 31).toNat), s2.m, s2.b⟩
    have r3 : run C 3 (pc + la + lb, s2) = some (pc + la + lb + 3, s3) := by
      simp [run, step, c0, c1, c2, wr, ea0, ea8, va, vb, upd_other _ _ (show (31:Nat) ≠ 6 by decide),
        upd_other _ _ (show (31:Nat) ≠ 5 by decide), ea16, s3]
    have lt64 : (s.x 31).toNat < 2 ^ 64 := (s.x 31).toNat_lt
    have x31 : (s3.x 31).toNat = (s.x 31).toNat := by simp [s3, upd]
    have x30 : s3.x 30 = s.x 30 := by simp [s3, upd, e302, e301]
    have x8 : s3.x 8 = s.x 8 := by simp [s3, upd, e82, e81]
    have x5 : s3.x 5 = VA s := by simp [s3, upd]
    have x6 : s3.x 6 = VB s := by simp [s3, upd]
    have mm : ∀ a, (s.x 31).toNat ≤ a → s3.m a = s.m a := by
      intro a ha; simp only [s3]; rw [m2 a (by omega), m1 a ha]
    have st3 : Star C (pc, s) (pc + la + lb + 3, s3) :=
      (r1.trans r2).trans (run_star r3)
    by_cases hc : VA s = VB s
    · -- then
      have sb : step C (pc + la + lb + 3, s3) = some (pc + la + lb + 5, s3) := by
        simp [step, c3, x5, x6, hc]; omega
      obtain ⟨s4, r4, p4, v4, e84, e304, m4⟩ := hT.run s3 (by rw [x30, x31]; omega) (by rw [x31]; exact lim)
      have sj : step C (pc + la + lb + 5 + lt, s4) =
          some (pc + (la + lb + 6 + lt + le), wr s4 0 (UInt64.ofNat (s4.b + 4 * (pc + la + lb + 5 + lt + 1)))) := by
        simp [step, hJ]; omega
      refine ⟨wr s4 0 (UInt64.ofNat (s4.b + 4 * (pc + la + lb + 5 + lt + 1))), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (st3.tail sb |>.trans r4).tail sj
      · simp [wr]; rw [p4, x31]
      · simp [wr]; rw [x31] at v4; rw [v4, hT.stable s s3 x8 mm, if_pos hc]
      · simp [wr]; rw [e84, x8]
      · simp [wr]; rw [e304, x30]
      · intro a ha; simp [wr]; rw [m4 a (by rw [x31]; exact ha), mm a ha]
    · -- else
      have sb : step C (pc + la + lb + 3, s3) = some (pc + la + lb + 4, s3) := by
        simp [step, c3, x5, x6, hc]
      have sj0 : step C (pc + la + lb + 4, s3) =
          some (pc + la + lb + 6 + lt, wr s3 0 (UInt64.ofNat (s3.b + 4 * (pc + la + lb + 4 + 1)))) := by
        simp [step, c4]; omega
      have w3 : wr s3 0 (UInt64.ofNat (s3.b + 4 * (pc + la + lb + 4 + 1))) = s3 := by simp [wr]
      rw [w3] at sj0
      obtain ⟨s5, r5, p5, v5, e85, e305, m5⟩ := hE.run s3 (by rw [x30, x31]; omega) (by rw [x31]; exact lim)
      refine ⟨s5, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have : pc + la + lb + 6 + lt + le = pc + (la + lb + 6 + lt + le) := by omega
        rw [← this]; exact ((st3.tail sb).tail sj0).trans r5
      · rw [p5, x31]
      · rw [x31] at v5; rw [v5, hE.stable s s3 x8 mm, if_neg hc]
      · rw [e85, x8]
      · rw [e305, x30]
      · intro a ha; rw [m5 a (by rw [x31]; exact ha), mm a ha]

/-- the IF head after both operands: pop2, `beq t0, t1, +2`, `jal 0 (lt+2)` -/
def ifHeadLt (lt : Nat) : List J := [.ld 6 31 0, .ld 5 31 8, .addi 31 31 16, .bltu 5 6 2, .jal 0 ((lt : Int) + 2)]

/-- **IF (<, unsigned), value mode**: A; B; head; T; jal END; E pushes `if VA = VB then VT else VE` -/
theorem if_lt {C : List J} {pc la lb lt le nA nB nT nE N : Nat} {VA VB VT VE : St → UInt64}
    (hA : PV C pc la nA VA) (hB : PV C (pc + la) lb nB VB)
    (hH : At C (pc + la + lb) (ifHeadLt lt)) (hT : PV C (pc + la + lb + 5) lt nT VT)
    (hJ : C[pc + la + lb + 5 + lt]? = some (.jal 0 ((le : Int) + 1)))
    (hE : PV C (pc + la + lb + 6 + lt) le nE VE)
    (h1 : nA ≤ N) (h2 : nB + 1 ≤ N) (h3 : nT ≤ N) (h4 : nE ≤ N) (h5 : 2 ≤ N) :
    PV C pc (la + lb + 6 + lt + le) N (fun s => if (VA s).toNat < (VB s).toNat then VT s else VE s) where
  stable := fun s s' e8 em => by
    rw [hA.stable s s' e8 em, hB.stable s s' e8 em, hT.stable s s' e8 em, hE.stable s s' e8 em]
  run := fun s room lim => by
    -- A
    obtain ⟨s1, r1, p1, v1, e81, e301, m1⟩ := hA.run s (by omega) lim
    -- B
    obtain ⟨s2, r2, p2, v2, e82, e302, m2⟩ := hB.run s1 (by rw [e301, p1]; omega) (by rw [p1]; omega)
    have sp := (s.x 31).toNat
    rw [p1] at p2 v2 m2
    -- the head: two loads and the pop
    have c0 := hH.at 0 (by simp [ifHeadLt]); have c1 := hH.at 1 (by simp [ifHeadLt])
    have c2 := hH.at 2 (by simp [ifHeadLt]); have c3 := hH.at 3 (by simp [ifHeadLt]); have c4 := hH.at 4 (by simp [ifHeadLt])
    simp [ifHeadLt] at c0 c1 c2 c3 c4
    have va : s2.m ((s.x 31).toNat - 8) = VA s := by rw [m2 _ (by omega), v1]
    have vb : s2.m ((s.x 31).toNat - 8 - 8) = VB s := by
      rw [v2, hB.stable s s1 e81 (fun a ha => m1 a ha)]
    have ea0 : ea (s2.x 31) 0 = (s.x 31).toNat - 8 - 8 := by simp [ea, p2]
    have ea8 : ea (s2.x 31) 8 = (s.x 31).toNat - 8 := by simp [ea, p2]; omega
    have ea16 : ea (s2.x 31) 16 = (s.x 31).toNat := by simp [ea, p2]; omega
    let s3 : St := ⟨upd (upd (upd s2.x 6 (VB s)) 5 (VA s)) 31 (UInt64.ofNat (s.x 31).toNat), s2.m, s2.b⟩
    have r3 : run C 3 (pc + la + lb, s2) = some (pc + la + lb + 3, s3) := by
      simp [run, step, c0, c1, c2, wr, ea0, ea8, va, vb, upd_other _ _ (show (31:Nat) ≠ 6 by decide),
        upd_other _ _ (show (31:Nat) ≠ 5 by decide), ea16, s3]
    have lt64 : (s.x 31).toNat < 2 ^ 64 := (s.x 31).toNat_lt
    have x31 : (s3.x 31).toNat = (s.x 31).toNat := by simp [s3, upd]
    have x30 : s3.x 30 = s.x 30 := by simp [s3, upd, e302, e301]
    have x8 : s3.x 8 = s.x 8 := by simp [s3, upd, e82, e81]
    have x5 : s3.x 5 = VA s := by simp [s3, upd]
    have x6 : s3.x 6 = VB s := by simp [s3, upd]
    have mm : ∀ a, (s.x 31).toNat ≤ a → s3.m a = s.m a := by
      intro a ha; simp only [s3]; rw [m2 a (by omega), m1 a ha]
    have st3 : Star C (pc, s) (pc + la + lb + 3, s3) :=
      (r1.trans r2).trans (run_star r3)
    by_cases hc : (VA s).toNat < (VB s).toNat
    · -- then
      have sb : step C (pc + la + lb + 3, s3) = some (pc + la + lb + 5, s3) := by
        simp [step, c3, x5, x6, hc]; omega
      obtain ⟨s4, r4, p4, v4, e84, e304, m4⟩ := hT.run s3 (by rw [x30, x31]; omega) (by rw [x31]; exact lim)
      have sj : step C (pc + la + lb + 5 + lt, s4) =
          some (pc + (la + lb + 6 + lt + le), wr s4 0 (UInt64.ofNat (s4.b + 4 * (pc + la + lb + 5 + lt + 1)))) := by
        simp [step, hJ]; omega
      refine ⟨wr s4 0 (UInt64.ofNat (s4.b + 4 * (pc + la + lb + 5 + lt + 1))), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (st3.tail sb |>.trans r4).tail sj
      · simp [wr]; rw [p4, x31]
      · simp [wr]; rw [x31] at v4; rw [v4, hT.stable s s3 x8 mm, if_pos hc]
      · simp [wr]; rw [e84, x8]
      · simp [wr]; rw [e304, x30]
      · intro a ha; simp [wr]; rw [m4 a (by rw [x31]; exact ha), mm a ha]
    · -- else
      have sb : step C (pc + la + lb + 3, s3) = some (pc + la + lb + 4, s3) := by
        simp [step, c3, x5, x6, hc]
      have sj0 : step C (pc + la + lb + 4, s3) =
          some (pc + la + lb + 6 + lt, wr s3 0 (UInt64.ofNat (s3.b + 4 * (pc + la + lb + 4 + 1)))) := by
        simp [step, c4]; omega
      have w3 : wr s3 0 (UInt64.ofNat (s3.b + 4 * (pc + la + lb + 4 + 1))) = s3 := by simp [wr]
      rw [w3] at sj0
      obtain ⟨s5, r5, p5, v5, e85, e305, m5⟩ := hE.run s3 (by rw [x30, x31]; omega) (by rw [x31]; exact lim)
      refine ⟨s5, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have : pc + la + lb + 6 + lt + le = pc + (la + lb + 6 + lt + le) := by omega
        rw [← this]; exact ((st3.tail sb).tail sj0).trans r5
      · rw [p5, x31]
      · rw [x31] at v5; rw [v5, hE.stable s s3 x8 mm, if_neg hc]
      · rw [e85, x8]
      · rw [e305, x30]
      · intro a ha; rw [m5 a (by rw [x31]; exact ha), mm a ha]

end Templates
