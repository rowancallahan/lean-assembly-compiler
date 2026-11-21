/- Codegen templates beyond the expression leaves (Astra-11, Opus box): IF (value mode).  Fragments are specified by
the value contract `PV`: with n words of stack room the code at [pc, pc+len) pushes ONE word `V s`, keeps s0 (x8),
t5 (x30) and every cell at or above the old t6; `V` only depends on s0 and the cells at or above t6 (`stable`).
The IF layout is Gen's (g36 visit + g37 items 3/4/5): A; B; pop2 (ld t1,0(t6); ld t0,8(t6); t6 += 16);
beq/bltu t0,t1,+8; jal ELSE; T; jal END; ELSE: E; END. -/
import Nano.Run.Call

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
    let s3 : St := ⟨upd (upd (upd s2.x 6 (VB s)) 5 (VA s)) 31 (UInt64.ofNat (s.x 31).toNat), s2.m, s2.b, s2.wk⟩
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
          some (pc + (la + lb + 6 + lt + le), wr s4 0 (UInt64.ofNat (s4.b + s4.w * (pc + la + lb + 5 + lt + 1)))) := by
        simp [step, hJ]; omega
      refine ⟨wr s4 0 (UInt64.ofNat (s4.b + s4.w * (pc + la + lb + 5 + lt + 1))), ?_, ?_, ?_, ?_, ?_, ?_⟩
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
          some (pc + la + lb + 6 + lt, wr s3 0 (UInt64.ofNat (s3.b + s3.w * (pc + la + lb + 4 + 1)))) := by
        simp [step, c4]; omega
      have w3 : wr s3 0 (UInt64.ofNat (s3.b + s3.w * (pc + la + lb + 4 + 1))) = s3 := by simp [wr]
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
    let s3 : St := ⟨upd (upd (upd s2.x 6 (VB s)) 5 (VA s)) 31 (UInt64.ofNat (s.x 31).toNat), s2.m, s2.b, s2.wk⟩
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
          some (pc + (la + lb + 6 + lt + le), wr s4 0 (UInt64.ofNat (s4.b + s4.w * (pc + la + lb + 5 + lt + 1)))) := by
        simp [step, hJ]; omega
      refine ⟨wr s4 0 (UInt64.ofNat (s4.b + s4.w * (pc + la + lb + 5 + lt + 1))), ?_, ?_, ?_, ?_, ?_, ?_⟩
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
          some (pc + la + lb + 6 + lt, wr s3 0 (UInt64.ofNat (s3.b + s3.w * (pc + la + lb + 4 + 1)))) := by
        simp [step, c4]; omega
      have w3 : wr s3 0 (UInt64.ofNat (s3.b + s3.w * (pc + la + lb + 4 + 1))) = s3 := by simp [wr]
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

/-! ## frames and the environment contract (for LET) -/

/-- slot k of a def with p parameter words: params above s0 (`s0 + 16 + 8(p−1−k)`), locals below (`s0 − 8(k−p+1)`) -/
def slotOff (p k : Nat) : Int := if k < p then 8 * ((p - 1 - k : Nat) : Int) + 16 else -(8 * ((k - p + 1 : Nat) : Int))
def slotAddr (p S0 k : Nat) : Nat := ((S0 : Int) + slotOff p k).toNat

/-- the frame holds `env` in its `nl` slots -/
def Frame (p nl : Nat) (s : St) (env : Nat → UInt64) : Prop :=
  ∀ k, k < nl → s.m (slotAddr p (s.x 8).toNat k) = env k

/-- the frame sits between t6 and the caller's stack: locals above t6, s0 large enough -/
def FrameOK (p nl : Nat) (s : St) : Prop :=
  (s.x 31).toNat + 8 * (nl - p) ≤ (s.x 8).toNat ∧ p ≤ nl ∧ (s.x 8).toNat + 8 * p + 16 < 2 ^ 62

theorem slotAddr_ge {p nl S0 T k} (h : T + 8 * (nl - p) ≤ S0) (hp : p ≤ nl) (hk : k < nl) : T ≤ slotAddr p S0 k := by
  unfold slotAddr slotOff; split <;> omega

theorem slotAddr_inj {p nl S0 k k'} (h : 8 * (nl - p) ≤ S0) (hk : k < nl) (hk' : k' < nl)
    (e : slotAddr p S0 k = slotAddr p S0 k') : k = k' := by
  unfold slotAddr slotOff at e; split at e <;> split at e <;> omega

theorem slotAddr_lt {p nl S0 k} (h : 8 * (nl - p) ≤ S0) (hk : k < nl) : slotAddr p S0 k < S0 + 8 * p + 16 := by
  unfold slotAddr slotOff; split <;> omega

/-- the ENVIRONMENT contract: the fragment pushes `V env`, where `V` reads only the slots in `R`; it may write the frame
slots in `W` (its own lets) and nothing else at or above t6; s0 and t5 are kept; x0 = 0 and the invariant `Inv` (the
input / heap / input-register facts a leaf's value depends on) are kept -/
structure EV (C : List J) (pc len n p nl : Nat) (Inv : St → Prop) (R W : Nat → Prop) (V : (Nat → UInt64) → UInt64) : Prop where
  run : ∀ (s : St) (env : Nat → UInt64), Inv s → s.x 0 = 0 → Frame p nl s env → FrameOK p nl s →
    (s.x 30).toNat + 8 * n ≤ (s.x 31).toNat →
    ∃ s' env', Star C (pc, s) (pc + len, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 ∧
      s'.m ((s.x 31).toNat - 8) = V env ∧ s'.x 8 = s.x 8 ∧ s'.x 30 = s.x 30 ∧
      Frame p nl s' env' ∧ (∀ k, ¬ W k → env' k = env k) ∧
      ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → W k → a ≠ slotAddr p (s.x 8).toNat k) → s'.m a = s.m a
  stable : ∀ env env', (∀ k, R k → env k = env' k) → V env = V env'

/-- pop the top word into slot k (`g26`, w = 1) -/
def popSlot (p k : Nat) : List J := [.ld 5 31 0, .addi 31 31 8, .sd 5 8 (slotOff p k)]

/-- `Inv` reads only s0, x28, x29, t5 and memory outside the stack/frame block [t5, frame top) -/
def InvOK (p : Nat) (Inv : St → Prop) : Prop :=
  ∀ s s' : St, Inv s → s'.x 8 = s.x 8 → s'.x 28 = s.x 28 → s'.x 29 = s.x 29 → s'.x 30 = s.x 30 →
    (∀ a, ¬ ((s.x 30).toNat ≤ a ∧ a < (s.x 8).toNat + 8 * p + 16) → s'.m a = s.m a) → Inv s'

/-- **LET** (width 1): value; pop into slot k0; body.  Scoping: the body reads none of the value's own lets. -/
theorem let1 {C : List J} {pc lv lb n p nl k0 : Nat} {Inv : St → Prop} {Rv Wv Rb Wb : Nat → Prop}
    {Vv Vb : (Nat → UInt64) → UInt64} (hI : InvOK p Inv)
    (hv : EV C pc lv n p nl Inv Rv Wv Vv) (hS : At C (pc + lv) (popSlot p k0)) (hb : EV C (pc + lv + 3) lb n p nl Inv Rb Wb Vb)
    (hk0 : k0 < nl) (hsc : ∀ k, Rb k → k ≠ k0 → ¬ Wv k) (hn : 1 ≤ n) :
    EV C pc (lv + 3 + lb) n p nl Inv (fun k => Rv k ∨ (Rb k ∧ k ≠ k0)) (fun k => Wv k ∨ k = k0 ∨ Wb k)
      (fun env => Vb (upd env k0 (Vv env))) where
  stable := fun env env' h => by
    have e1 : Vv env = Vv env' := hv.stable env env' (fun k hk => h k (Or.inl hk))
    apply hb.stable; intro k hk
    by_cases hk' : k = k0
    · subst hk'; simp [upd, e1]
    · simp [upd, hk']; exact h k (Or.inr ⟨hk, hk'⟩)
  run := fun s env hI0 hx0 hF hO room => by
    obtain ⟨s1, env1, r1, I1, z1, p1, v1, e81, e301, F1, ag1, m1⟩ := hv.run s env hI0 hx0 hF hO room
    obtain ⟨o1, o2, o3⟩ := hO
    have lt64 := (s.x 31).toNat_lt
    -- pop into the slot
    have c0 := hS.at 0 (by simp [popSlot]); have c1 := hS.at 1 (by simp [popSlot]); have c2 := hS.at 2 (by simp [popSlot])
    simp [popSlot] at c0 c1 c2
    have ea0 : ea (s1.x 31) 0 = (s.x 31).toNat - 8 := by simp [ea, p1]
    have ea8 : ea (s1.x 31) 8 = (s.x 31).toNat := by simp [ea, p1]; omega
    have eaK : ea (s1.x 8) (slotOff p k0) = slotAddr p (s.x 8).toNat k0 := by simp [ea, slotAddr, e81]
    let s2 : St := ⟨upd (upd s1.x 5 (Vv env)) 31 (UInt64.ofNat (s.x 31).toNat),
      upd s1.m (slotAddr p (s.x 8).toNat k0) (Vv env), s1.b, s1.wk⟩
    have r2 : run C 3 (pc + lv, s1) = some (pc + lv + 3, s2) := by
      simp [run, step, c0, c1, c2, wr, ea0, v1, ea8, upd_other _ _ (show (31:Nat) ≠ 5 by decide),
        upd_other _ _ (show (8:Nat) ≠ 31 by decide), upd_other _ _ (show (8:Nat) ≠ 5 by decide), eaK, s2,
        upd_other _ _ (show (5:Nat) ≠ 31 by decide), upd_same]
    have x31 : (s2.x 31).toNat = (s.x 31).toNat := by simp [s2, upd]
    have x8 : s2.x 8 = s.x 8 := by simp [s2, upd, e81]
    have x30 : s2.x 30 = s.x 30 := by simp [s2, upd, e301]
    let env2 := upd env1 k0 (Vv env)
    have F2 : Frame p nl s2 env2 := by
      intro k hk
      show s2.m (slotAddr p (s2.x 8).toNat k) = env2 k
      rw [x8]
      show upd s1.m (slotAddr p (s.x 8).toNat k0) (Vv env) (slotAddr p (s.x 8).toNat k) = upd env1 k0 (Vv env) k
      by_cases e : k = k0
      · subst e; simp [upd]
      · have ne : slotAddr p (s.x 8).toNat k ≠ slotAddr p (s.x 8).toNat k0 :=
          fun h => e (slotAddr_inj (by omega) hk hk0 h)
        rw [upd_other _ _ ne, upd_other _ _ e, ← e81]; exact F1 k hk
    have I2 : Inv s2 := by
      apply hI s1 s2 I1 (by simp [s2, upd]) (by simp [s2, upd]) (by simp [s2, upd]) (by simp [s2, upd])
      intro a ha
      simp only [s2]; rw [upd_other]
      intro e; apply ha; rw [e, e301, e81]
      exact ⟨by have := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk0; omega, slotAddr_lt (by omega) hk0⟩
    have z2 : s2.x 0 = 0 := by simp [s2, upd, z1]
    obtain ⟨s3, env3, r3, I3, z3, p3, v3, e83, e303, F3, ag3, m3⟩ :=
      hb.run s2 env2 I2 z2 F2 ⟨by rw [x31, x8]; omega, o2, by rw [x8]; omega⟩ (by rw [x30, x31]; exact room)
    refine ⟨s3, env3, ?_, I3, z3, ?_, ?_, ?_, ?_, F3, ?_, ?_⟩
    · have : pc + lv + 3 + lb = pc + (lv + 3 + lb) := by omega
      rw [← this]; exact (r1.trans (run_star r2)).trans r3
    · rw [p3, x31]
    · rw [x31] at v3; rw [v3]
      apply hb.stable; intro k hk
      by_cases e : k = k0
      · subst e; simp [upd, env2]
      · simp only [env2, upd, e, if_false]; exact ag1 k (hsc k hk e)
    · rw [e83, x8]
    · rw [e303, x30]
    · intro k hk
      simp only [not_or] at hk
      rw [ag3 k hk.2.2]; simp only [env2, upd, hk.2.1, if_false]; exact ag1 k hk.1
    · intro a ha hW
      rw [m3 a (by rw [x31]; exact ha) (fun k hk wk => by rw [x8]; exact hW k hk (Or.inr (Or.inr wk)))]
      simp only [s2]; rw [upd_other _ _ (hW k0 hk0 (Or.inr (Or.inl rfl)))]
      exact m1 a ha (fun k hk wk => hW k hk (Or.inl wk))

/-- **IF (==) under EV**: A; B; head; T; jal END; E.  Scoping: B reads none of A's lets; T and E read none of A's or B's. -/
theorem ifE_eq {C : List J} {pc la lb lt le n p nl : Nat} {Inv : St → Prop} {RA WA RB WB RT WT RE WE : Nat → Prop}
    {VA VB VT VE : (Nat → UInt64) → UInt64} (hI : InvOK p Inv)
    (hA : EV C pc la n p nl Inv RA WA VA) (hB : EV C (pc + la) lb n p nl Inv RB WB VB)
    (hH : At C (pc + la + lb) (ifHead lt)) (hT : EV C (pc + la + lb + 5) lt n p nl Inv RT WT VT)
    (hJ : C[pc + la + lb + 5 + lt]? = some (.jal 0 ((le : Int) + 1)))
    (hE : EV C (pc + la + lb + 6 + lt) le n p nl Inv RE WE VE)
    (sB : ∀ k, RB k → ¬ WA k) (sT : ∀ k, RT k → ¬ WA k ∧ ¬ WB k) (sE : ∀ k, RE k → ¬ WA k ∧ ¬ WB k) (hn : 1 ≤ n) :
    EV C pc (la + lb + 6 + lt + le) (n + 1) p nl Inv (fun k => RA k ∨ RB k ∨ RT k ∨ RE k) (fun k => WA k ∨ WB k ∨ WT k ∨ WE k)
      (fun env => if VA env = VB env then VT env else VE env) where
  stable := fun env env' h => by
    rw [hA.stable env env' (fun k hk => h k (Or.inl hk)), hB.stable env env' (fun k hk => h k (Or.inr (Or.inl hk))),
      hT.stable env env' (fun k hk => h k (Or.inr (Or.inr (Or.inl hk)))),
      hE.stable env env' (fun k hk => h k (Or.inr (Or.inr (Or.inr hk))))]
  run := fun s env I0 z0 F0 O0 room => by
    obtain ⟨o1, o2, o3⟩ := O0
    obtain ⟨s1, env1, r1, I1, z1, p1, v1, e81, e301, F1, ag1, m1⟩ := hA.run s env I0 z0 F0 ⟨o1, o2, o3⟩ (by omega)
    obtain ⟨s2, env2, r2, I2, z2, p2, v2, e82, e302, F2, ag2, m2⟩ := hB.run s1 env1 I1 z1 F1
      ⟨by rw [p1, e81]; omega, o2, by rw [e81]; omega⟩ (by rw [e301, p1]; omega)
    rw [p1] at p2 v2 m2
    rw [e81] at m2
    have c0 := hH.at 0 (by simp [ifHead]); have c1 := hH.at 1 (by simp [ifHead])
    have c2 := hH.at 2 (by simp [ifHead]); have c3 := hH.at 3 (by simp [ifHead]); have c4 := hH.at 4 (by simp [ifHead])
    simp [ifHead] at c0 c1 c2 c3 c4
    have lt64 := (s.x 31).toNat_lt
    have va : s2.m ((s.x 31).toNat - 8) = VA env := by
      rw [m2 _ (by omega) (fun k hk _ => by
        have := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk; omega), v1]
    have vb : s2.m ((s.x 31).toNat - 8 - 8) = VB env := by
      rw [v2]; exact hB.stable env1 env (fun k hk => ag1 k (sB k hk))
    have ea0 : ea (s2.x 31) 0 = (s.x 31).toNat - 8 - 8 := by simp [ea, p2]
    have ea8 : ea (s2.x 31) 8 = (s.x 31).toNat - 8 := by simp [ea, p2]; omega
    have ea16 : ea (s2.x 31) 16 = (s.x 31).toNat := by simp [ea, p2]; omega
    let s3 : St := ⟨upd (upd (upd s2.x 6 (VB env)) 5 (VA env)) 31 (UInt64.ofNat (s.x 31).toNat), s2.m, s2.b, s2.wk⟩
    have r3 : run C 3 (pc + la + lb, s2) = some (pc + la + lb + 3, s3) := by
      simp [run, step, c0, c1, c2, wr, ea0, ea8, va, vb, upd_other _ _ (show (31:Nat) ≠ 6 by decide),
        upd_other _ _ (show (31:Nat) ≠ 5 by decide), ea16, s3]
    have x31 : (s3.x 31).toNat = (s.x 31).toNat := by simp [s3, upd]
    have x30 : s3.x 30 = s.x 30 := by simp [s3, upd, e302, e301]
    have x8 : s3.x 8 = s.x 8 := by simp [s3, upd, e82, e81]
    have x5 : s3.x 5 = VA env := by simp [s3, upd]
    have x6 : s3.x 6 = VB env := by simp [s3, upd]
    have I3 : Inv s3 := hI s2 s3 I2 (by simp [s3, upd]) (by simp [s3, upd]) (by simp [s3, upd]) (by simp [s3, upd])
      (fun a _ => rfl)
    have z3 : s3.x 0 = 0 := by simp [s3, upd, z2]
    have F3 : Frame p nl s3 env2 := fun k hk => by
      show s2.m (slotAddr p (s3.x 8).toNat k) = env2 k
      rw [x8, ← e81, ← e82]; exact F2 k hk
    have O3 : FrameOK p nl s3 := ⟨by rw [x31, x8]; omega, o2, by rw [x8]; omega⟩
    have mm : ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → (WA k ∨ WB k) → a ≠ slotAddr p (s.x 8).toNat k) →
        s3.m a = s.m a := by
      intro a ha hw
      show s2.m a = s.m a
      rw [m2 a (by omega) (fun k hk wk => hw k hk (Or.inr wk)), m1 a ha (fun k hk wk => hw k hk (Or.inl wk))]
    have ag : ∀ k, ¬ WA k → ¬ WB k → env2 k = env k := fun k h1 h2 => by rw [ag2 k h2, ag1 k h1]
    have st3 : Star C (pc, s) (pc + la + lb + 3, s3) := (r1.trans r2).trans (run_star r3)
    by_cases hc : VA env = VB env
    · have sb : step C (pc + la + lb + 3, s3) = some (pc + la + lb + 5, s3) := by
        simp [step, c3, x5, x6, hc]; omega
      obtain ⟨s4, env4, r4, I4, z4, p4, v4, e84, e304, F4, ag4, m4⟩ :=
        hT.run s3 env2 I3 z3 F3 O3 (by rw [x30, x31]; omega)
      let s5 := wr s4 0 (UInt64.ofNat (s4.b + s4.w * (pc + la + lb + 5 + lt + 1)))
      have w5 : s5 = s4 := by simp [s5, wr]
      have sj : step C (pc + la + lb + 5 + lt, s4) = some (pc + (la + lb + 6 + lt + le), s5) := by
        simp [step, hJ, s5]; omega
      rw [w5] at sj
      refine ⟨s4, env4, (st3.tail sb |>.trans r4).tail sj, I4, z4, ?_, ?_, ?_, ?_, F4, ?_, ?_⟩
      · rw [p4, x31]
      · rw [x31] at v4; rw [v4, if_pos hc]; exact hT.stable env2 env (fun k hk => ag k (sT k hk).1 (sT k hk).2)
      · rw [e84, x8]
      · rw [e304, x30]
      · intro k hk; simp only [not_or] at hk; rw [ag4 k hk.2.2.1, ag k hk.1 hk.2.1]
      · intro a ha hw
        rw [m4 a (by rw [x31]; exact ha) (fun k hk wk => by rw [x8]; exact hw k hk (Or.inr (Or.inr (Or.inl wk))))]
        exact mm a ha (fun k hk wk => hw k hk (by rcases wk with w | w <;> simp [w]))
    · have sb : step C (pc + la + lb + 3, s3) = some (pc + la + lb + 4, s3) := by
        simp [step, c3, x5, x6, hc]
      let s5 := wr s3 0 (UInt64.ofNat (s3.b + s3.w * (pc + la + lb + 4 + 1)))
      have w5 : s5 = s3 := by simp [s5, wr]
      have sj0 : step C (pc + la + lb + 4, s3) = some (pc + la + lb + 6 + lt, s5) := by
        simp [step, c4, s5]; omega
      rw [w5] at sj0
      obtain ⟨s6, env6, r6, I6, z6, p6, v6, e86, e306, F6, ag6, m6⟩ :=
        hE.run s3 env2 I3 z3 F3 O3 (by rw [x30, x31]; omega)
      refine ⟨s6, env6, ?_, I6, z6, ?_, ?_, ?_, ?_, F6, ?_, ?_⟩
      · have : pc + la + lb + 6 + lt + le = pc + (la + lb + 6 + lt + le) := by omega
        rw [← this]; exact ((st3.tail sb).tail sj0).trans r6
      · rw [p6, x31]
      · rw [x31] at v6; rw [v6, if_neg hc]; exact hE.stable env2 env (fun k hk => ag k (sE k hk).1 (sE k hk).2)
      · rw [e86, x8]
      · rw [e306, x30]
      · intro k hk; simp only [not_or] at hk; rw [ag6 k hk.2.2.2, ag k hk.1 hk.2.1]
      · intro a ha hw
        rw [m6 a (by rw [x31]; exact ha) (fun k hk wk => by rw [x8]; exact hw k hk (Or.inr (Or.inr (Or.inr wk))))]
        exact mm a ha (fun k hk wk => hw k hk (by rcases wk with w | w <;> simp [w]))

/-- **IF (<, unsigned) under EV**: A; B; head; T; jal END; E.  Scoping: B reads none of A's lets; T and E read none of A's or B's. -/
theorem ifE_lt {C : List J} {pc la lb lt le n p nl : Nat} {Inv : St → Prop} {RA WA RB WB RT WT RE WE : Nat → Prop}
    {VA VB VT VE : (Nat → UInt64) → UInt64} (hI : InvOK p Inv)
    (hA : EV C pc la n p nl Inv RA WA VA) (hB : EV C (pc + la) lb n p nl Inv RB WB VB)
    (hH : At C (pc + la + lb) (ifHeadLt lt)) (hT : EV C (pc + la + lb + 5) lt n p nl Inv RT WT VT)
    (hJ : C[pc + la + lb + 5 + lt]? = some (.jal 0 ((le : Int) + 1)))
    (hE : EV C (pc + la + lb + 6 + lt) le n p nl Inv RE WE VE)
    (sB : ∀ k, RB k → ¬ WA k) (sT : ∀ k, RT k → ¬ WA k ∧ ¬ WB k) (sE : ∀ k, RE k → ¬ WA k ∧ ¬ WB k) (hn : 1 ≤ n) :
    EV C pc (la + lb + 6 + lt + le) (n + 1) p nl Inv (fun k => RA k ∨ RB k ∨ RT k ∨ RE k) (fun k => WA k ∨ WB k ∨ WT k ∨ WE k)
      (fun env => if (VA env).toNat < (VB env).toNat then VT env else VE env) where
  stable := fun env env' h => by
    rw [hA.stable env env' (fun k hk => h k (Or.inl hk)), hB.stable env env' (fun k hk => h k (Or.inr (Or.inl hk))),
      hT.stable env env' (fun k hk => h k (Or.inr (Or.inr (Or.inl hk)))),
      hE.stable env env' (fun k hk => h k (Or.inr (Or.inr (Or.inr hk))))]
  run := fun s env I0 z0 F0 O0 room => by
    obtain ⟨o1, o2, o3⟩ := O0
    obtain ⟨s1, env1, r1, I1, z1, p1, v1, e81, e301, F1, ag1, m1⟩ := hA.run s env I0 z0 F0 ⟨o1, o2, o3⟩ (by omega)
    obtain ⟨s2, env2, r2, I2, z2, p2, v2, e82, e302, F2, ag2, m2⟩ := hB.run s1 env1 I1 z1 F1
      ⟨by rw [p1, e81]; omega, o2, by rw [e81]; omega⟩ (by rw [e301, p1]; omega)
    rw [p1] at p2 v2 m2
    rw [e81] at m2
    have c0 := hH.at 0 (by simp [ifHeadLt]); have c1 := hH.at 1 (by simp [ifHeadLt])
    have c2 := hH.at 2 (by simp [ifHeadLt]); have c3 := hH.at 3 (by simp [ifHeadLt]); have c4 := hH.at 4 (by simp [ifHeadLt])
    simp [ifHeadLt] at c0 c1 c2 c3 c4
    have lt64 := (s.x 31).toNat_lt
    have va : s2.m ((s.x 31).toNat - 8) = VA env := by
      rw [m2 _ (by omega) (fun k hk _ => by
        have := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk; omega), v1]
    have vb : s2.m ((s.x 31).toNat - 8 - 8) = VB env := by
      rw [v2]; exact hB.stable env1 env (fun k hk => ag1 k (sB k hk))
    have ea0 : ea (s2.x 31) 0 = (s.x 31).toNat - 8 - 8 := by simp [ea, p2]
    have ea8 : ea (s2.x 31) 8 = (s.x 31).toNat - 8 := by simp [ea, p2]; omega
    have ea16 : ea (s2.x 31) 16 = (s.x 31).toNat := by simp [ea, p2]; omega
    let s3 : St := ⟨upd (upd (upd s2.x 6 (VB env)) 5 (VA env)) 31 (UInt64.ofNat (s.x 31).toNat), s2.m, s2.b, s2.wk⟩
    have r3 : run C 3 (pc + la + lb, s2) = some (pc + la + lb + 3, s3) := by
      simp [run, step, c0, c1, c2, wr, ea0, ea8, va, vb, upd_other _ _ (show (31:Nat) ≠ 6 by decide),
        upd_other _ _ (show (31:Nat) ≠ 5 by decide), ea16, s3]
    have x31 : (s3.x 31).toNat = (s.x 31).toNat := by simp [s3, upd]
    have x30 : s3.x 30 = s.x 30 := by simp [s3, upd, e302, e301]
    have x8 : s3.x 8 = s.x 8 := by simp [s3, upd, e82, e81]
    have x5 : s3.x 5 = VA env := by simp [s3, upd]
    have x6 : s3.x 6 = VB env := by simp [s3, upd]
    have I3 : Inv s3 := hI s2 s3 I2 (by simp [s3, upd]) (by simp [s3, upd]) (by simp [s3, upd]) (by simp [s3, upd])
      (fun a _ => rfl)
    have z3 : s3.x 0 = 0 := by simp [s3, upd, z2]
    have F3 : Frame p nl s3 env2 := fun k hk => by
      show s2.m (slotAddr p (s3.x 8).toNat k) = env2 k
      rw [x8, ← e81, ← e82]; exact F2 k hk
    have O3 : FrameOK p nl s3 := ⟨by rw [x31, x8]; omega, o2, by rw [x8]; omega⟩
    have mm : ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → (WA k ∨ WB k) → a ≠ slotAddr p (s.x 8).toNat k) →
        s3.m a = s.m a := by
      intro a ha hw
      show s2.m a = s.m a
      rw [m2 a (by omega) (fun k hk wk => hw k hk (Or.inr wk)), m1 a ha (fun k hk wk => hw k hk (Or.inl wk))]
    have ag : ∀ k, ¬ WA k → ¬ WB k → env2 k = env k := fun k h1 h2 => by rw [ag2 k h2, ag1 k h1]
    have st3 : Star C (pc, s) (pc + la + lb + 3, s3) := (r1.trans r2).trans (run_star r3)
    by_cases hc : (VA env).toNat < (VB env).toNat
    · have sb : step C (pc + la + lb + 3, s3) = some (pc + la + lb + 5, s3) := by
        simp [step, c3, x5, x6, hc]; omega
      obtain ⟨s4, env4, r4, I4, z4, p4, v4, e84, e304, F4, ag4, m4⟩ :=
        hT.run s3 env2 I3 z3 F3 O3 (by rw [x30, x31]; omega)
      let s5 := wr s4 0 (UInt64.ofNat (s4.b + s4.w * (pc + la + lb + 5 + lt + 1)))
      have w5 : s5 = s4 := by simp [s5, wr]
      have sj : step C (pc + la + lb + 5 + lt, s4) = some (pc + (la + lb + 6 + lt + le), s5) := by
        simp [step, hJ, s5]; omega
      rw [w5] at sj
      refine ⟨s4, env4, (st3.tail sb |>.trans r4).tail sj, I4, z4, ?_, ?_, ?_, ?_, F4, ?_, ?_⟩
      · rw [p4, x31]
      · rw [x31] at v4; rw [v4, if_pos hc]; exact hT.stable env2 env (fun k hk => ag k (sT k hk).1 (sT k hk).2)
      · rw [e84, x8]
      · rw [e304, x30]
      · intro k hk; simp only [not_or] at hk; rw [ag4 k hk.2.2.1, ag k hk.1 hk.2.1]
      · intro a ha hw
        rw [m4 a (by rw [x31]; exact ha) (fun k hk wk => by rw [x8]; exact hw k hk (Or.inr (Or.inr (Or.inl wk))))]
        exact mm a ha (fun k hk wk => hw k hk (by rcases wk with w | w <;> simp [w]))
    · have sb : step C (pc + la + lb + 3, s3) = some (pc + la + lb + 4, s3) := by
        simp [step, c3, x5, x6, hc]
      let s5 := wr s3 0 (UInt64.ofNat (s3.b + s3.w * (pc + la + lb + 4 + 1)))
      have w5 : s5 = s3 := by simp [s5, wr]
      have sj0 : step C (pc + la + lb + 4, s3) = some (pc + la + lb + 6 + lt, s5) := by
        simp [step, c4, s5]; omega
      rw [w5] at sj0
      obtain ⟨s6, env6, r6, I6, z6, p6, v6, e86, e306, F6, ag6, m6⟩ :=
        hE.run s3 env2 I3 z3 F3 O3 (by rw [x30, x31]; omega)
      refine ⟨s6, env6, ?_, I6, z6, ?_, ?_, ?_, ?_, F6, ?_, ?_⟩
      · have : pc + la + lb + 6 + lt + le = pc + (la + lb + 6 + lt + le) := by omega
        rw [← this]; exact ((st3.tail sb).tail sj0).trans r6
      · rw [p6, x31]
      · rw [x31] at v6; rw [v6, if_neg hc]; exact hE.stable env2 env (fun k hk => ag k (sE k hk).1 (sE k hk).2)
      · rw [e86, x8]
      · rw [e306, x30]
      · intro k hk; simp only [not_or] at hk; rw [ag6 k hk.2.2.2, ag k hk.1 hk.2.1]
      · intro a ha hw
        rw [m6 a (by rw [x31]; exact ha) (fun k hk wk => by rw [x8]; exact hw k hk (Or.inr (Or.inr (Or.inr wk))))]
        exact mm a ha (fun k hk wk => hw k hk (by rcases wk with w | w <;> simp [w]))

/-! ## popping w words into consecutive slots (`g26`: top → slot k0+w−1, …, deepest → slot k0) -/
def popN (p k0 : Nat) : Nat → List J
  | 0 => []
  | w + 1 => popSlot p (k0 + w) ++ popN p k0 w

theorem popN_len (p k0 : Nat) : ∀ w, (popN p k0 w).length = 3 * w
  | 0 => rfl
  | w + 1 => by simp [popN, popSlot, popN_len p k0 w]; omega

/-- one pop: the top word goes to slot k, t6 += 8 (t0 clobbered) -/
theorem popSlot_run {C : List J} {pc p k : Nat} (s : St) (hS : At C pc (popSlot p k))
    (hlt : (s.x 31).toNat + 8 < 2 ^ 64) :
    run C 3 (pc, s) = some (pc + 3, ⟨upd (upd s.x 5 (s.m (s.x 31).toNat)) 31 (UInt64.ofNat ((s.x 31).toNat + 8)),
      upd s.m (slotAddr p (s.x 8).toNat k) (s.m (s.x 31).toNat), s.b, s.wk⟩) := by
  have c0 := hS.at 0 (by simp [popSlot]); have c1 := hS.at 1 (by simp [popSlot]); have c2 := hS.at 2 (by simp [popSlot])
  simp [popSlot] at c0 c1 c2
  have ea0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have ea8 : ea (upd s.x 5 (s.m (s.x 31).toNat) 31) 8 = (s.x 31).toNat + 8 := by simp [ea, upd]; omega
  have eaK : ∀ v w, ea (upd (upd s.x 5 v) 31 w 8) (slotOff p k) = slotAddr p (s.x 8).toNat k := by
    intro v w; simp [ea, upd, slotAddr]
  simp [run, step, c0, c1, c2, wr, ea0, ea8, eaK, upd_other _ _ (show (5:Nat) ≠ 31 by decide), upd_same]

theorem At.app_left' {C pos l1 l2} (h : At C pos (l1 ++ l2)) : At C pos l1 := h.left
theorem At.app_right' {C pos l1 l2} (h : At C pos (l1 ++ l2)) : At C (pos + l1.length) l2 := h.right

/-- **pop w words into slots k0 … k0+w−1** (word at t6 + 8i goes to slot k0 + w − 1 − i) -/
theorem popN_run {C : List J} {p k0 : Nat} : ∀ (w pc : Nat) (s : St), At C pc (popN p k0 w) →
    (s.x 31).toNat + 8 * w < 2 ^ 63 →
    (∀ j j', j < w → j' < w → slotAddr p (s.x 8).toNat (k0 + j) = slotAddr p (s.x 8).toNat (k0 + j') → j = j') →
    (∀ j i, j < w → i < w → slotAddr p (s.x 8).toNat (k0 + j) ≠ (s.x 31).toNat + 8 * i) →
    ∃ s', run C (3 * w) (pc, s) = some (pc + 3 * w, s') ∧ (s'.x 31).toNat = (s.x 31).toNat + 8 * w ∧
      s'.x 8 = s.x 8 ∧ (∀ r, r ≠ 5 → r ≠ 31 → s'.x r = s.x r) ∧ s'.b = s.b ∧
      (∀ j, j < w → s'.m (slotAddr p (s.x 8).toNat (k0 + j)) = s.m ((s.x 31).toNat + 8 * (w - 1 - j))) ∧
      ∀ a, (∀ j, j < w → a ≠ slotAddr p (s.x 8).toNat (k0 + j)) → s'.m a = s.m a
  | 0, pc, s, _, _, _, _ => ⟨s, by simp [run], by simp, rfl, fun _ _ _ => rfl, rfl, fun j h => absurd h (by omega),
      fun _ _ => rfl⟩
  | w + 1, pc, s, hC, hlt, hinj, hdis => by
    have hC' : At C pc (popSlot p (k0 + w) ++ popN p k0 w) := hC
    have A1 : At C pc (popSlot p (k0 + w)) := hC'.left
    have A2 : At C (pc + 3) (popN p k0 w) := by have := hC'.right; simpa [popSlot] using this
    have r1 := popSlot_run (k := k0 + w) s A1 (by omega)
    generalize hs1 : (⟨upd (upd s.x 5 (s.m (s.x 31).toNat)) 31 (UInt64.ofNat ((s.x 31).toNat + 8)),
      upd s.m (slotAddr p (s.x 8).toNat (k0 + w)) (s.m (s.x 31).toNat), s.b, s.wk⟩ : St) = s1 at r1
    have t1 : (s1.x 31).toNat = (s.x 31).toNat + 8 := by subst hs1; simp [upd]; omega
    have x81 : s1.x 8 = s.x 8 := by subst hs1; simp [upd]
    have m1 : ∀ a, s1.m a = if a = slotAddr p (s.x 8).toNat (k0 + w) then s.m (s.x 31).toNat else s.m a := by
      intro a; subst hs1; simp [upd]
    obtain ⟨s', r', p', e8', ex', eb', ms', mo'⟩ := popN_run w (pc + 3) s1 A2 (by rw [t1]; omega)
      (fun j j' hj hj' e => hinj j j' (by omega) (by omega) (by rw [x81] at e; exact e))
      (fun j i hj hi => by rw [x81, t1]; have := hdis j (i + 1) (by omega) (by omega); omega)
    refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show 3 * (w + 1) = 3 + 3 * w by omega, run_add r1, r']; congr 2; omega
    · rw [p', t1]; omega
    · rw [e8', x81]
    · intro r h5 h31; rw [ex' r h5 h31]; subst hs1; simp [upd, h5, h31]
    · rw [eb']; subst hs1; rfl
    · intro j hj
      rw [x81] at ms' mo'
      by_cases hjw : j = w
      · subst hjw
        rw [mo' _ (fun j' hj' e => by have := hinj j j' (by omega) (by omega) e; omega), m1, if_pos rfl]
        congr 1; omega
      · rw [ms' j (by omega), t1, m1, if_neg (by have := hdis w (w - j) (by omega) (by omega); omega)]
        congr 1; omega
    · intro a ha
      rw [x81] at mo'
      rw [mo' a (fun j hj => ha j (by omega)), m1, if_neg (ha w (by omega))]

/-! ## multi-word values (PAIR, LET of width w, CONTINUE's state) -/

/-- the w-word ENVIRONMENT contract: pushes `V env` (length w; component i at old t6 − 8(i+1)) -/
structure EVw (C : List J) (pc len n p nl : Nat) (Inv : St → Prop) (R W : Nat → Prop) (w : Nat)
    (V : (Nat → UInt64) → List UInt64) : Prop where
  vlen : ∀ env, (V env).length = w
  run : ∀ (s : St) (env : Nat → UInt64), Inv s → s.x 0 = 0 → Frame p nl s env → FrameOK p nl s →
    (s.x 30).toNat + 8 * n ≤ (s.x 31).toNat →
    ∃ s' env', Star C (pc, s) (pc + len, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 * w ∧
      (∀ i, i < w → s'.m ((s.x 31).toNat - 8 * (i + 1)) = (V env).getD i 0) ∧ s'.x 8 = s.x 8 ∧ s'.x 30 = s.x 30 ∧
      Frame p nl s' env' ∧ (∀ k, ¬ W k → env' k = env k) ∧
      ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → W k → a ≠ slotAddr p (s.x 8).toNat k) → s'.m a = s.m a
  stable : ∀ env env', (∀ k, R k → env k = env' k) → V env = V env'

theorem getD_app_l (a b : List UInt64) (i : Nat) (h : i < a.length) : (a ++ b).getD i 0 = a.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem getD_app_r (a b : List UInt64) (i : Nat) (h : a.length ≤ i) : (a ++ b).getD i 0 = b.getD (i - a.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- **PAIR** (two parts): A then B; B reads none of A's lets -/
theorem pairE {C : List J} {pc la lb n p nl wa wb : Nat} {Inv : St → Prop} {RA WA RB WB : Nat → Prop}
    {VA VB : (Nat → UInt64) → List UInt64}
    (hA : EVw C pc la n p nl Inv RA WA wa VA) (hB : EVw C (pc + la) lb n p nl Inv RB WB wb VB)
    (sB : ∀ k, RB k → ¬ WA k) :
    EVw C pc (la + lb) (n + wa) p nl Inv (fun k => RA k ∨ RB k) (fun k => WA k ∨ WB k) (wa + wb)
      (fun env => VA env ++ VB env) where
  vlen := fun env => by simp [hA.vlen, hB.vlen]
  stable := fun env env' h => by
    rw [hA.stable env env' (fun k hk => h k (Or.inl hk)), hB.stable env env' (fun k hk => h k (Or.inr hk))]
  run := fun s env I0 z0 F0 O0 room => by
    obtain ⟨o1, o2, o3⟩ := O0
    obtain ⟨s1, env1, r1, I1, z1, p1, v1, e81, e301, F1, ag1, m1⟩ := hA.run s env I0 z0 F0 ⟨o1, o2, o3⟩ (by omega)
    obtain ⟨s2, env2, r2, I2, z2, p2, v2, e82, e302, F2, ag2, m2⟩ := hB.run s1 env1 I1 z1 F1
      ⟨by rw [p1, e81]; omega, o2, by rw [e81]; omega⟩ (by rw [e301, p1]; omega)
    rw [p1] at p2 v2 m2; rw [e81] at m2
    have vB : VB env1 = VB env := hB.stable env1 env (fun k hk => ag1 k (sB k hk))
    refine ⟨s2, env2, by rw [← Nat.add_assoc]; exact r1.trans r2, I2, z2, ?_, ?_, ?_, ?_, F2, ?_, ?_⟩
    · rw [p2]; omega
    · intro i hi
      by_cases hi' : i < wa
      · rw [m2 _ (by omega) (fun k hk _ => by
          have := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk; omega), v1 i hi']
        rw [getD_app_l _ _ _ (by rw [hA.vlen]; exact hi')]
      · have := v2 (i - wa) (by omega)
        rw [show (s.x 31).toNat - 8 * wa - 8 * (i - wa + 1) = (s.x 31).toNat - 8 * (i + 1) by omega, vB] at this
        rw [this, getD_app_r _ _ _ (by rw [hA.vlen]; omega), hA.vlen]
    · rw [e82, e81]
    · rw [e302, e301]
    · intro k hk; simp only [not_or] at hk; rw [ag2 k hk.2, ag1 k hk.1]
    · intro a ha hw
      rw [m2 a (by omega) (fun k hk wk => hw k hk (Or.inr wk)), m1 a ha (fun k hk wk => hw k hk (Or.inl wk))]

/-- slots k0, k0+1, … get the words of `vs` -/
def setSlots (env : Nat → UInt64) (k0 : Nat) (vs : List UInt64) : Nat → UInt64 :=
  fun k => if k0 ≤ k ∧ k < k0 + vs.length then vs.getD (k - k0) 0 else env k

/-- **LET** (width w): the w-word value; pop into slots k0 … k0+w−1 (g26); body.  Scoping: the body reads none of
the value's own lets (other than through the bound slots). -/
theorem letW {C : List J} {pc lv lb n p nl k0 w wb : Nat} {Inv : St → Prop} {Rv Wv Rb Wb : Nat → Prop}
    {Vv Vb : (Nat → UInt64) → List UInt64} (hI : InvOK p Inv)
    (hv : EVw C pc lv n p nl Inv Rv Wv w Vv) (hS : At C (pc + lv) (popN p k0 w))
    (hb : EVw C (pc + lv + 3 * w) lb n p nl Inv Rb Wb wb Vb)
    (hk0 : k0 + w ≤ nl) (hsc : ∀ k, Rb k → ¬ (k0 ≤ k ∧ k < k0 + w) → ¬ Wv k) (hn : w ≤ n) :
    EVw C pc (lv + 3 * w + lb) n p nl Inv (fun k => Rv k ∨ (Rb k ∧ ¬ (k0 ≤ k ∧ k < k0 + w)))
      (fun k => Wv k ∨ (k0 ≤ k ∧ k < k0 + w) ∨ Wb k) wb (fun env => Vb (setSlots env k0 (Vv env))) where
  vlen := fun env => hb.vlen _
  stable := fun env env' h => by
    have e1 : Vv env = Vv env' := hv.stable env env' (fun k hk => h k (Or.inl hk))
    apply hb.stable; intro k hk
    unfold setSlots; rw [e1]
    split
    · rfl
    · rename_i hk'; rw [hv.vlen] at hk'; exact h k (Or.inr ⟨hk, hk'⟩)
  run := fun s env I0 z0 F0 O0 room => by
    obtain ⟨s1, env1, r1, I1, z1, p1, v1, e81, e301, F1, ag1, m1⟩ := hv.run s env I0 z0 F0 O0 room
    obtain ⟨o1, o2, o3⟩ := O0
    have lt64 := (s.x 31).toNat_lt
    have T1 : (s1.x 31).toNat + 8 * w = (s.x 31).toNat := by rw [p1]; omega
    obtain ⟨s2, r2, p2, e82, ex2, eb2, ms2, mo2⟩ := popN_run (p := p) (k0 := k0) w (pc + lv) s1 hS (by omega)
      (fun j j' hj hj' e => by have := slotAddr_inj (nl := nl) (by rw [e81]; omega) (by omega) (by omega) e; omega)
      (fun j i hj hi => by
        rw [e81]; have := slotAddr_ge (T := (s.x 31).toNat) (k := k0 + j) (by omega) o2 (by omega); omega)
    rw [e81] at ms2 mo2
    have x31 : (s2.x 31).toNat = (s.x 31).toNat := by rw [p2, T1]
    have x8 : s2.x 8 = s.x 8 := by rw [e82, e81]
    have x30 : s2.x 30 = s.x 30 := by rw [ex2 30 (by decide) (by decide), e301]
    let env2 := setSlots env1 k0 (Vv env)
    have F2 : Frame p nl s2 env2 := by
      intro k hk
      show s2.m (slotAddr p (s2.x 8).toNat k) = env2 k
      rw [x8]
      by_cases e : k0 ≤ k ∧ k < k0 + w
      · have := ms2 (k - k0) (by omega)
        rw [show k0 + (k - k0) = k by omega] at this
        rw [this, show (s1.x 31).toNat + 8 * (w - 1 - (k - k0)) = (s.x 31).toNat - 8 * (k - k0 + 1) by omega,
          v1 (k - k0) (by omega)]
        simp [env2, setSlots, hv.vlen, e]
      · rw [mo2 _ (fun j hj h => e (by have := slotAddr_inj (nl := nl) (by omega) hk (by omega) h; omega))]
        simp only [env2, setSlots, hv.vlen, e, if_false]; rw [← e81]; exact F1 k hk
    have I2 : Inv s2 := by
      apply hI s1 s2 I1 (by rw [e82]) (ex2 28 (by decide) (by decide)) (ex2 29 (by decide) (by decide))
        (ex2 30 (by decide) (by decide))
      intro a ha
      apply mo2 a; intro j hj e; apply ha; rw [e301, e81, e]
      exact ⟨by have := slotAddr_ge (T := (s.x 31).toNat) (k := k0 + j) (by omega) o2 (by omega); omega,
        slotAddr_lt (nl := nl) (by omega) (by omega)⟩
    have z2 : s2.x 0 = 0 := by rw [ex2 0 (by decide) (by decide), z1]
    obtain ⟨s3, env3, r3, I3, z3, p3, v3, e83, e303, F3, ag3, m3⟩ :=
      hb.run s2 env2 I2 z2 F2 ⟨by rw [x31, x8]; omega, o2, by rw [x8]; omega⟩ (by rw [x30, x31]; exact room)
    refine ⟨s3, env3, ?_, I3, z3, ?_, ?_, ?_, ?_, F3, ?_, ?_⟩
    · have : pc + lv + 3 * w + lb = pc + (lv + 3 * w + lb) := by omega
      rw [← this]; exact (r1.trans (run_star r2)).trans r3
    · rw [p3, x31]
    · intro i hi; rw [x31] at v3; rw [v3 i hi]
      congr 1; apply hb.stable; intro k hk
      simp only [env2, setSlots]
      by_cases e : k0 ≤ k ∧ k < k0 + w
      · simp [hv.vlen, e]
      · simp only [hv.vlen, e, if_false]; exact ag1 k (hsc k hk e)
    · rw [e83, x8]
    · rw [e303, x30]
    · intro k hk; simp only [not_or] at hk
      rw [ag3 k hk.2.2]; simp only [env2, setSlots, hv.vlen, hk.2.1, if_false]; exact ag1 k hk.1
    · intro a ha hW
      rw [m3 a (by rw [x31]; exact ha) (fun k hk wk => by rw [x8]; exact hW k hk (Or.inr (Or.inr wk)))]
      rw [mo2 a (fun j hj e => hW (k0 + j) (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩)) e)]
      exact m1 a ha (fun k hk wk => hW k hk (Or.inl wk))

/-- **CONTINUE** (tail of a fuel def's step arm): the new state (npw−1 words); pop into slots 1 … npw−1; jal HEAD.
Reaches HEAD with t6 restored, the frame holding the state in slots 1 … npw−1 and the fragment's own lets
changed; everything else as before (the shape loop_ok's continue branch needs). -/
theorem contE {C : List J} {pc le n p nl H : Nat} {dH : Int} {Inv : St → Prop} {R W : Nat → Prop}
    {Ve : (Nat → UInt64) → List UInt64} (hI : InvOK p Inv)
    (he : EVw C pc le n p nl Inv R W (p - 1) Ve) (hS : At C (pc + le) (popN p 1 (p - 1)))
    (hJ : C[pc + le + 3 * (p - 1)]? = some (.jal 0 dH)) (hdH : ((pc + le + 3 * (p - 1) : Nat) + dH).toNat = H)
    (hp : 1 ≤ p) (hpn : p ≤ nl) (hn : p - 1 ≤ n) :
    ∀ (s : St) (env : Nat → UInt64), Inv s → s.x 0 = 0 → Frame p nl s env → FrameOK p nl s →
      (s.x 30).toNat + 8 * n ≤ (s.x 31).toNat →
      ∃ s' env', Star C (pc, s) (H, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat ∧
        s'.x 8 = s.x 8 ∧ s'.x 30 = s.x 30 ∧ Frame p nl s' (setSlots env' 1 (Ve env)) ∧
        (∀ k, ¬ W k → env' k = env k) := by
  intro s env I0 z0 F0 O0 room
  obtain ⟨s1, env1, r1, I1, z1, p1, v1, e81, e301, F1, ag1, m1⟩ := he.run s env I0 z0 F0 O0 room
  obtain ⟨o1, o2, o3⟩ := O0
  have lt64 := (s.x 31).toNat_lt
  have T1 : (s1.x 31).toNat + 8 * (p - 1) = (s.x 31).toNat := by rw [p1]; omega
  obtain ⟨s2, r2, p2, e82, ex2, eb2, ms2, mo2⟩ := popN_run (p := p) (k0 := 1) (p - 1) (pc + le) s1 hS (by omega)
    (fun j j' hj hj' e => by have := slotAddr_inj (nl := nl) (by rw [e81]; omega) (by omega) (by omega) e; omega)
    (fun j i hj hi => by
      rw [e81]; have := slotAddr_ge (T := (s.x 31).toNat) (k := 1 + j) (nl := nl) (by omega) o2 (by omega); omega)
  rw [e81] at ms2 mo2
  have x31 : (s2.x 31).toNat = (s.x 31).toNat := by rw [p2, T1]
  have x8 : s2.x 8 = s.x 8 := by rw [e82, e81]
  have x30 : s2.x 30 = s.x 30 := by rw [ex2 30 (by decide) (by decide), e301]
  have F2 : Frame p nl s2 (setSlots env1 1 (Ve env)) := by
    intro k hk
    show s2.m (slotAddr p (s2.x 8).toNat k) = setSlots env1 1 (Ve env) k
    rw [x8]
    by_cases e : 1 ≤ k ∧ k < 1 + (p - 1)
    · have := ms2 (k - 1) (by omega)
      rw [show 1 + (k - 1) = k by omega] at this
      rw [this, show (s1.x 31).toNat + 8 * (p - 1 - 1 - (k - 1)) = (s.x 31).toNat - 8 * (k - 1 + 1) by omega,
        v1 (k - 1) (by omega)]
      simp [setSlots, he.vlen, e]
    · rw [mo2 _ (fun j hj h => e (by have := slotAddr_inj (nl := nl) (by omega) hk (by omega) h; omega))]
      simp only [setSlots, he.vlen, e, if_false]; rw [← e81]; exact F1 k hk
  have I2 : Inv s2 := by
    apply hI s1 s2 I1 (by rw [e82]) (ex2 28 (by decide) (by decide)) (ex2 29 (by decide) (by decide))
      (ex2 30 (by decide) (by decide))
    intro a ha
    apply mo2 a; intro j hj e; apply ha; rw [e301, e81, e]
    exact ⟨by have := slotAddr_ge (T := (s.x 31).toNat) (k := 1 + j) (nl := nl) (by omega) o2 (by omega); omega,
      slotAddr_lt (nl := nl) (by omega) (by omega)⟩
  have z2 : s2.x 0 = 0 := by rw [ex2 0 (by decide) (by decide), z1]
  have sj : step C (pc + le + 3 * (p - 1), s2) = some (H, s2) := by
    simp [step, hJ, wr]; exact hdH
  refine ⟨s2, env1, ((r1.trans (run_star r2)).tail sj), I2, z2, x31, x8, x30, ?_, ag1⟩
  exact F2

end Templates
