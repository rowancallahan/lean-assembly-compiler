/- rv2arm's block correctness on DeepMind's machine: `RelD` (the DeepMind version of ArmBlock's `RelA`) and one
theorem per J kind, `blk_*`: from `RelD` at `(pc, s)` the block of `C[pc]` runs (≤ 4 DeepMind steps) to `RelD` at
J's next state. -/
import Blocks.Frame
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Proven.Apc.Blocks
open CallProbe Proven.Arm ArmBlock

/-! ## the register map -/
theorem live_lt {r : Nat} (h : live r) : r < 32 := by
  unfold live pi at h; split at h <;> omega
theorem live_of_wr {r : Nat} (h : wrOK r) (h0 : r ≠ 0) : live r := by
  unfold wrOK at h; unfold live; refine ⟨?_, h0⟩; unfold pi at h ⊢; split at h <;> simp_all
theorem live_of_rd {r : Nat} (h : rdOK r) (h0 : r ≠ 0) : live r := live_of_wr h h0
theorem pi_injF : ∀ r r' : Fin 32, pi r < 31 → r.val ≠ 0 → pi r' < 31 → r'.val ≠ 0 → pi r = pi r' → r = r' := by
  decide
theorem pi_inj {r r' : Nat} (h : live r) (h' : live r') (e : pi r = pi r') : r = r' := by
  have := pi_injF ⟨r, live_lt h⟩ ⟨r', live_lt h'⟩ h.1 h.2 h'.1 h'.2 e; simpa using congrArg Fin.val this
theorem pi_rngF : ∀ r : Fin 32, pi r < 31 → r.val ≠ 0 → pi r ≠ 16 ∧ pi r ≠ 17 ∧ (pi r < 18 ∨ 29 < pi r) := by decide
theorem pi_rng {r : Nat} (h : live r) : pi r ≠ 16 ∧ pi r ≠ 17 ∧ (pi r < 18 ∨ 29 < pi r) :=
  pi_rngF ⟨r, live_lt h⟩ h.1 h.2

/-! ## the relation -/
/-- registers: J register `r` (live) in A64 `x[π r]`; x18..x29 kept -/
def RegsOK (a : AState) (s : St) (K : Nat → BitVec 64) : Prop :=
  (∀ r, live r → a.x (pi r) = (s.x r).toBitVec) ∧ (∀ r, 18 ≤ r → r ≤ 29 → a.x r = K r)

/-- the data cells `D`: 8 readable/writable bytes each, little-endian = J's cell -/
def MemOK (D : Nat → Prop) (m : Nat → UInt64) (mem : Arm64.Memory) : Prop :=
  ∀ a, D a → a % 8 = 0 ∧ a + 8 < 2 ^ 64 ∧ ∀ k < 8, mem.canRead (ad (a + k)) 1 = true ∧
    mem.canWrite (ad (a + k)) 1 = true ∧ mem.read8 (ad (a + k)) = (m a).toBitVec.extractLsb' (8 * k) 8

/-- **`RelD C D K (pc, s) t`**: DeepMind state `t` represents J state `(pc, s)` (ArmBlock's `RelA`, with `abs`/`Memory`
in place of `Machine.observe`; scratch x16/x17, NZCV and everything else are free) -/
structure RelD (C : List J) (D : Nat → Prop) (K : Nat → BitVec 64) (ps : Nat × St) (t : Arm64.State) : Prop where
  run : t.status = .Running
  pc : t.pc = ad (ps.2.b + 16 * ps.1)
  code : CodeOK C ps.2.b t.mem
  regs : RegsOK (abs t) ps.2 K
  zero : ps.2.x 0 = 0
  sp : t.sp = K 31
  ly : ps.2.ly = LinkLay.lin 3
  mem : MemOK D ps.2.m t.mem

theorem RelD.mid {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {j : J} (h : RelD C D K (pc, s) t)
    (hj : C[pc]? = some j) : Mid C s.b pc j 0 t := ⟨h.run, by rw [h.pc]; simp, h.code, hj⟩

/-- end of a block: `Mid … 4` and the J effect give `RelD` at `pc + 1` -/
theorem relD_next {C : List J} {D K} {pc : Nat} {s s' : St} {j : J} {t t' : Arm64.State} (h : RelD C D K (pc, s) t)
    (hm : Mid C s.b pc j 4 t') (hr : RegsOK (abs t') s' K) (hsp : t'.sp = t.sp) (hmem : MemOK D s'.m t'.mem)
    (hb : s'.b = s.b) (hz : s'.x 0 = 0) (hw : s'.ly = s.ly) : RelD C D K (pc + 1, s') t' :=
  ⟨hm.run, by rw [hm.pc, hb]; show ad _ = ad _; congr 1, hb ▸ hm.code, hr, hz, hsp.trans h.sp, hw.trans h.ly, hmem⟩

theorem regs_wr {a : AState} {s : St} {K} (h : RegsOK a s K) {rd : Nat} (hl : live rd) (V : UInt64) :
    RegsOK (a.setX (pi rd) V.toBitVec) (wr s rd V) K := by
  have h31 : pi rd ≠ 31 := by have := hl.1; omega
  refine ⟨fun r hr => ?_, fun r h1 h2 => ?_⟩
  · simp only [AState.setX, h31, ite_false, wr, hl.2, upd]
    by_cases e : r = rd
    · subst e; simp
    · have : pi r ≠ pi rd := fun x => e (pi_inj hr hl x)
      simp [this, e, h.1 r hr]
  · have := pi_rng hl
    simp only [AState.setX, h31, ite_false]
    simp only [show r ≠ pi rd by omega, ite_false]; exact h.2 r h1 h2

theorem regs_scr {a : AState} {s : St} {K} (h : RegsOK a s K) {d : Nat} (hd : d = 16 ∨ d = 17) (v : BitVec 64) :
    RegsOK (a.setX d v) s K := by
  refine ⟨fun r hr => ?_, fun r h1 h2 => ?_⟩
  · have := pi_rng hr
    simp only [AState.setX]; rcases hd with rfl | rfl <;> simp [show pi r ≠ 16 by omega, show pi r ≠ 17 by omega, h.1 r hr]
  · simp only [AState.setX]; rcases hd with rfl | rfl <;> simp [show r ≠ 16 by omega, show r ≠ 17 by omega, h.2 r h1 h2]

/-! ## block shapes -/
/-- one real word `w0` (falls through, memory unchanged) then PADs -/
theorem one_pads {C : List J} {b i : Nat} {j : J} {t : Arm64.State} {A : AState} (h : Mid C b i j 0 t)
    (hS : At t (bw j 0) → ∃ t', Arm64.Step Pg t t' ∧ abs t' = A ∧ Post t t' (t.pc + 4) t.mem)
    (hp : PadsFrom j 1) :
    Reach t fun t' => Mid C b i j 4 t' ∧ abs t' = A ∧ t'.sp = t.sp ∧ t'.mem = t.mem := by
  obtain ⟨t1, s1, m1, a1, p1, q1⟩ := seq1 h (by omega) (hS (h.at (by omega)))
  refine Reach.cons s1 ((pads 3 1 rfl m1 hp).mono ?_)
  intro t' ⟨m', a', p', q'⟩; exact ⟨m', a'.trans a1, p'.trans p1, q'.trans q1⟩

/-- word `k` (falls through, memory unchanged), then PADs -/
theorem word_pads {C : List J} {b i : Nat} {j : J} {k : Nat} {t : Arm64.State} {A : AState} (h : Mid C b i j k t)
    (hk : k < 4) (hS : At t (bw j k) → ∃ t', Arm64.Step Pg t t' ∧ abs t' = A ∧ Post t t' (t.pc + 4) t.mem)
    (hp : PadsFrom j (k + 1)) :
    Reach t fun t' => Mid C b i j 4 t' ∧ abs t' = A ∧ t'.sp = t.sp ∧ t'.mem = t.mem := by
  obtain ⟨t1, s1, m1, a1, p1, q1⟩ := seq1 h hk (hS (h.at hk))
  refine Reach.cons s1 ((pads (3 - k) (k + 1) (by omega) m1 hp).mono ?_)
  intro t' ⟨m', a', p', q'⟩; exact ⟨m', a'.trans a1, p'.trans p1, q'.trans q1⟩

/-- `bw j k` from the list of block words -/
theorem bw_of {j : J} {l : List Nat} (h : blockJ j = l) (k : Nat) : bw j k = wd (l.getD k 0) := by
  simp only [bw, h]

end Proven.Apc.Blocks
