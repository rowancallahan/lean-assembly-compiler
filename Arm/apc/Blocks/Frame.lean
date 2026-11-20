/- The frame for running one rv2arm block (4 words) on DeepMind's machine: `CodeOK` (the block words sit,
executable, at `b + 16 i + 4 k`), `Mid` (inside block `i` at word `k`), one word step (`seq1`), PAD runs (`pads`). -/
import Blocks.Enc
import Blocks.Imm
set_option linter.unusedSimpArgs false
namespace Proven.Apc.Blocks
open CallProbe Proven.Arm

abbrev ad (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

/-- word `k` of the block of `j` -/
def bw (j : J) (k : Nat) : BitVec 32 := wd ((ArmBlock.blockJ j).getD k 0)

/-- the code of `C` at base `b`: every block word fetchable -/
structure CodeOK (C : List J) (b : Nat) (m : Arm64.Memory) : Prop where
  lt : b + 16 * C.length < 2 ^ 64
  b4 : b % 4 = 0
  w : ∀ i j, C[i]? = some j → ∀ k < 4,
    m.canExec (ad (b + 16 * i + 4 * k)) 4 = true ∧ m.read32 (ad (b + 16 * i + 4 * k)) = bw j k

/-- inside block `i` (instruction `j`), at word `k` -/
structure Mid (C : List J) (b i : Nat) (j : J) (k : Nat) (t : Arm64.State) : Prop where
  run : t.status = .Running
  pc : t.pc = ad (b + 16 * i + 4 * k)
  code : CodeOK C b t.mem
  hj : C[i]? = some j

/-- reachable by DeepMind steps -/
def Reach (t : Arm64.State) (Q : Arm64.State → Prop) : Prop := ∃ t', Arm64.Steps Pg t t' ∧ Q t'

theorem Reach.done {t : Arm64.State} {Q : Arm64.State → Prop} (h : Q t) : Reach t Q := ⟨t, .refl t, h⟩
theorem Reach.cons {t t1 : Arm64.State} {Q : Arm64.State → Prop} (h : Arm64.Step Pg t t1) (h1 : Reach t1 Q) : Reach t Q :=
  let ⟨t', s, q⟩ := h1; ⟨t', .step h s, q⟩
theorem Reach.mono {t : Arm64.State} {Q R : Arm64.State → Prop} (h : Reach t Q) (f : ∀ t', Q t' → R t') : Reach t R :=
  let ⟨t', s, q⟩ := h; ⟨t', s, f t' q⟩

theorem Mid.lt {C : List J} {b i : Nat} {j : J} {k : Nat} {t : Arm64.State} (h : Mid C b i j k t) (hk : k ≤ 4) :
    b + 16 * i + 4 * k < 2 ^ 64 := by
  have hi : i < C.length := by
    rcases Nat.lt_or_ge i C.length with h' | h'
    · exact h'
    · have := h.hj; rw [List.getElem?_eq_none h'] at this; cases this
  have := h.code.lt; omega

/-- the word at the PC -/
theorem Mid.at {C : List J} {b i : Nat} {j : J} {k : Nat} {t : Arm64.State} (h : Mid C b i j k t) (hk : k < 4) :
    At t (bw j k) := by
  have hl := h.lt (by omega)
  obtain ⟨he, hr⟩ := h.code.w i j h.hj k hk
  refine ⟨h.run, ?_, by rw [h.pc]; exact he, by rw [h.pc]; exact hr⟩
  rw [h.pc]; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]; have := h.code.b4; omega

/-- one word that falls through, memory unchanged -/
theorem seq1 {C : List J} {b i : Nat} {j : J} {k : Nat} {t : Arm64.State} {A : AState} (h : Mid C b i j k t)
    (hk : k < 4) (hS : ∃ t', Arm64.Step Pg t t' ∧ abs t' = A ∧ Post t t' (t.pc + 4) t.mem) :
    ∃ t', Arm64.Step Pg t t' ∧ Mid C b i j (k + 1) t' ∧ abs t' = A ∧ t'.sp = t.sp ∧ t'.mem = t.mem := by
  obtain ⟨t', hs, ha, hp⟩ := hS
  refine ⟨t', hs, ⟨hp.run, ?_, by rw [hp.mem]; exact h.code, h.hj⟩, ha, hp.sp, hp.mem⟩
  rw [hp.pc, h.pc]; apply BitVec.eq_of_toNat_eq; simp; omega

theorem setX_same (a : AState) (d : Nat) : a.setX d (a.x d) = a := by
  unfold AState.setX; split
  · rfl
  · congr 1; funext i; split <;> simp_all

/-- PAD = `add x16, x16, #0`: nothing visible changes -/
theorem pad_ok {C : List J} {b i : Nat} {j : J} {k : Nat} {t : Arm64.State} (h : Mid C b i j k t) (hk : k < 4)
    (hw : bw j k = wd ArmBlock.PAD) :
    ∃ t', Arm64.Step Pg t t' ∧ Mid C b i j (k + 1) t' ∧ abs t' = abs t ∧ t'.sp = t.sp ∧ t'.mem = t.mem := by
  have hA := h.at hk; rw [hw] at hA
  refine seq1 h hk ?_
  have := dm_addi (by decide) (by decide) (by decide) hA
  have e : ((wd ArmBlock.PAD).extractLsb' 0 5).toNat = 16 := by decide
  have e2 : ((wd ArmBlock.PAD).extractLsb' 5 5).toNat = 16 := by decide
  have e3 : ((wd ArmBlock.PAD).extractLsb' 10 12).setWidth 64 = 0 := by decide
  rw [e, e2, e3] at this; simpa [setX_same] using this

/-- the rest of the block, words `k..3`, is PAD -/
def PadsFrom (j : J) (k : Nat) : Prop := ∀ k', k ≤ k' → k' < 4 → bw j k' = wd ArmBlock.PAD

theorem pads {C : List J} {b i : Nat} {j : J} : ∀ n k {t : Arm64.State}, k + n = 4 → Mid C b i j k t → PadsFrom j k →
    Reach t fun t' => Mid C b i j 4 t' ∧ abs t' = abs t ∧ t'.sp = t.sp ∧ t'.mem = t.mem
  | 0, k, t, hn, h, _ => Reach.done ⟨by rw [show 4 = k by omega]; exact h, rfl, rfl, rfl⟩
  | n + 1, k, t, hn, h, hp => by
    obtain ⟨t1, s1, m1, a1, p1, q1⟩ := pad_ok h (by omega) (hp k (Nat.le_refl _) (by omega))
    refine Reach.cons s1 ((pads n (k + 1) (by omega) m1 fun k' h1 h2 => hp k' (by omega) h2).mono ?_)
    intro t' ⟨m', a', p', q'⟩; exact ⟨m', a'.trans a1, p'.trans p1, q'.trans q1⟩

end Proven.Apc.Blocks
