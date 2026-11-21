/- GenArm's templates as A64 runs on `NMid` (M3; `C/GenArm.lean` at native-arm d6db803): one lemma per template, a
straight-line composition of ArmNat's instruction steps.  Words are stated as `A[h + i]? = some …` with ArmEnc's
encoders (GenArm's `a1`…`a36` produce the same numbers; that equality is M4's business). -/
import Nano.V2Self.Proof.Machine.ArmNat
namespace JT
open Proven.Top SimW CallProbe ArmEnc

theorem condV_lo (a b : UInt64) : condV 3 a b = decide (a.toNat < b.toNat) := by simp [condV]

variable {M : Machine} {X W : M.State → Nat → Prop} {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St}

/-- **push `r`** (`a10`): `sub x11, x11, #8; subs x16, x11, x10; b.lo 1; str xr, [x11]`.  Out of room (new t6 < t5):
at word 1 (the out-of-memory stub) with t6 moved; otherwise the cell is written and the template is passed. -/
theorem n_push (S : A64SemN M X W) {h r : Nat} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hL : A.length < 2 ^ 18) (h1 : 1 ≤ A.length)
    (a0 : A[h]? = some (ArmEnc.subi (armReg 31) (armReg 31) 8))
    (a1 : A[h + 1]? = some (ArmEnc.subsR (armReg 31) (armReg 30)))
    (a2 : A[h + 2]? = some (ArmEnc.bc 3 ((1 : Int) - (h + 2))))
    (a3 : A[h + 3]? = some (ArmEnc.str (armReg r) (armReg 31) 0))
    (hr : mapped r = true) (hr0 : r ≠ 0)
    (hw : ¬ (st.x 31 - 8).toNat < (st.x 30).toNat → wok K (st.x 31 - 8).toNat) :
    let st1 := CallProbe.wr st 31 (st.x 31 - 8)
    ∃ s', Runs M s s' ∧
      if (st1.x 31).toNat < (st1.x 30).toNat then NMid X W K A s0 st1 1 s'
      else NMid X W K A s0 { st1 with m := CallProbe.upd st1.m (st1.x 31).toNat (st1.x r) } (h + 4) s' := by
  intro st1
  obtain ⟨s1, r1, N1⟩ := n_subi S hM hB a0 (by decide) (by decide) (by decide) (by decide) (by decide)
  have e31 : st1.x 31 = st.x 31 - 8 := by simp [st1, CallProbe.wr, CallProbe.upd]
  have e30 : st1.x 30 = st.x 30 := by simp [st1, CallProbe.wr, CallProbe.upd]
  obtain ⟨s2, r2, N2⟩ := n_cmpbr (q' := 1) S N1 hB a1 (by
      have : ((1 : Nat) : Int) - (((h + 1 : Nat) : Int) + 1) = (1 : Int) - (h + 2) := by push_cast; omega
      rw [this]; exact a2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by omega) hL
  change NMid X W K A s0 st1 _ s2 at N2
  by_cases hlt : (st1.x 31).toNat < (st1.x 30).toNat
  · rw [if_pos (by rw [condV_lo]; exact decide_eq_true hlt)] at N2
    exact ⟨s2, Runs.trans r1 r2, by rw [if_pos hlt]; exact N2⟩
  · rw [if_neg (by rw [condV_lo]; simpa using hlt)] at N2
    obtain ⟨s3, r3, N3⟩ := n_str (a := (st1.x 31).toNat) S N2 hB a3 (armReg_lt hr hr0)
      (N2.x r (by omega) (mapped_lt hr)) (by decide) (N2.x 31 (by omega) (by omega)) (by decide) (by decide)
      (by omega) (by rw [e31]; exact hw (by rw [e31, e30] at hlt; exact hlt))
    exact ⟨s3, Runs.trans (Runs.trans r1 r2) r3, by rw [if_neg hlt]; exact N3⟩

end JT
