/- T10 (M3): the def prologue `a26` (Testing/notes/NATIVE_ARM_TEMPLATES.md section 12) as an A64 run on `NMid`:
`push x30; push x8; add x8, x11, #0; sub x11, x11, #8r; subs x16, x11, x10; b.lo 1` (12 words).
Three room checks, each exiting to word 1 (the out-of-memory stub) with the view as it stands. -/
import Nano.Run.NatT.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop} {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St}

/-- the two pushes and `add x8, x11, #0` (words h .. h+8); result at word h+9, or word 1 if a push is out of room -/
theorem n_proHead (S : A64SemN M X W) {h : Nat} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hL : A.length < 2 ^ 18) (h1 : 1 ≤ A.length)
    (a0 : A[h]? = some (ArmEnc.subi (armReg 31) (armReg 31) 8))
    (a1 : A[h + 1]? = some (ArmEnc.subsR (armReg 31) (armReg 30)))
    (a2 : A[h + 2]? = some (ArmEnc.bc 3 ((1 : Int) - (h + 2))))
    (a3 : A[h + 3]? = some (ArmEnc.str (armReg 1) (armReg 31) 0))
    (a4 : A[h + 4]? = some (ArmEnc.subi (armReg 31) (armReg 31) 8))
    (a5 : A[h + 5]? = some (ArmEnc.subsR (armReg 31) (armReg 30)))
    (a6 : A[h + 6]? = some (ArmEnc.bc 3 ((1 : Int) - (h + 6))))
    (a7 : A[h + 7]? = some (ArmEnc.str (armReg 8) (armReg 31) 0))
    (a8 : A[h + 8]? = some (ArmEnc.addi (armReg 8) (armReg 31) 0))
    (hw1 : ¬ (st.x 31 - 8).toNat < (st.x 30).toNat → wok K (st.x 31 - 8).toNat) :
    let p1 := CallProbe.wr st 31 (st.x 31 - 8)
    let q1 := { p1 with m := CallProbe.upd p1.m (p1.x 31).toNat (p1.x 1) }
    let p2 := CallProbe.wr q1 31 (q1.x 31 - 8)
    let q2 := { p2 with m := CallProbe.upd p2.m (p2.x 31).toNat (p2.x 8) }
    (¬ (q1.x 31 - 8).toNat < (q1.x 30).toNat → wok K (q1.x 31 - 8).toNat) →
    ∃ s', Runs M s s' ∧
      if (p1.x 31).toNat < (p1.x 30).toNat then NMid X W K A s0 p1 1 s'
      else if (p2.x 31).toNat < (p2.x 30).toNat then NMid X W K A s0 p2 1 s'
      else NMid X W K A s0 (CallProbe.wr q2 8 (q2.x 31 + UInt64.ofNat 0)) (h + 9) s' := by
  intro p1 q1 p2 q2 hw2
  obtain ⟨s1, r1, N1⟩ := n_push S (r := 1) hM hB hL h1 a0 a1 a2 a3 (by decide) (by decide) hw1
  by_cases c1 : (p1.x 31).toNat < (p1.x 30).toNat
  · rw [if_pos c1] at N1
    exact ⟨s1, r1, by rw [if_pos c1]; exact N1⟩
  · rw [if_neg c1] at N1
    obtain ⟨s2, r2, N2⟩ := n_push S (r := 8) N1 hB hL h1 a4 a5 a6 a7 (by decide) (by decide) hw2
    by_cases c2 : (p2.x 31).toNat < (p2.x 30).toNat
    · rw [if_pos c2] at N2
      exact ⟨s2, Runs.trans r1 r2, by rw [if_neg c1, if_pos c2]; exact N2⟩
    · rw [if_neg c2] at N2
      obtain ⟨s3, r3, N3⟩ := n_addi S N2 hB a8 (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨s3, Runs.trans (Runs.trans r1 r2) r3, by rw [if_neg c1, if_neg c2]; exact N3⟩

/-- **def prologue**, `r ≥ 1` locals (`a26`): head, `sub x11, x11, #8r; subs x16, x11, x10; b.lo 1` -/
theorem n_prologue (S : A64SemN M X W) {h r : Nat} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hL : A.length < 2 ^ 18) (h1 : 1 ≤ A.length)
    (a0 : A[h]? = some (ArmEnc.subi (armReg 31) (armReg 31) 8))
    (a1 : A[h + 1]? = some (ArmEnc.subsR (armReg 31) (armReg 30)))
    (a2 : A[h + 2]? = some (ArmEnc.bc 3 ((1 : Int) - (h + 2))))
    (a3 : A[h + 3]? = some (ArmEnc.str (armReg 1) (armReg 31) 0))
    (a4 : A[h + 4]? = some (ArmEnc.subi (armReg 31) (armReg 31) 8))
    (a5 : A[h + 5]? = some (ArmEnc.subsR (armReg 31) (armReg 30)))
    (a6 : A[h + 6]? = some (ArmEnc.bc 3 ((1 : Int) - (h + 6))))
    (a7 : A[h + 7]? = some (ArmEnc.str (armReg 8) (armReg 31) 0))
    (a8 : A[h + 8]? = some (ArmEnc.addi (armReg 8) (armReg 31) 0))
    (a9 : A[h + 9]? = some (ArmEnc.subi (armReg 31) (armReg 31) (8 * r)))
    (a10 : A[h + 10]? = some (ArmEnc.subsR (armReg 31) (armReg 30)))
    (a11 : A[h + 11]? = some (ArmEnc.bc 3 ((1 : Int) - (h + 11)))) (hr : 8 * r < 4096)
    (hw1 : ¬ (st.x 31 - 8).toNat < (st.x 30).toNat → wok K (st.x 31 - 8).toNat) :
    let p1 := CallProbe.wr st 31 (st.x 31 - 8)
    let q1 := { p1 with m := CallProbe.upd p1.m (p1.x 31).toNat (p1.x 1) }
    let p2 := CallProbe.wr q1 31 (q1.x 31 - 8)
    let q2 := { p2 with m := CallProbe.upd p2.m (p2.x 31).toNat (p2.x 8) }
    let q3 := CallProbe.wr q2 8 (q2.x 31 + UInt64.ofNat 0)
    let q4 := CallProbe.wr q3 31 (q3.x 31 - UInt64.ofNat (8 * r))
    (¬ (q1.x 31 - 8).toNat < (q1.x 30).toNat → wok K (q1.x 31 - 8).toNat) →
    ∃ s', Runs M s s' ∧
      if (p1.x 31).toNat < (p1.x 30).toNat then NMid X W K A s0 p1 1 s'
      else if (p2.x 31).toNat < (p2.x 30).toNat then NMid X W K A s0 p2 1 s'
      else NMid X W K A s0 q4 (if (q4.x 31).toNat < (q4.x 30).toNat then 1 else h + 12) s' := by
  intro p1 q1 p2 q2 q3 q4 hw2
  obtain ⟨s1, r1, N1⟩ := n_proHead S hM hB hL h1 a0 a1 a2 a3 a4 a5 a6 a7 a8 hw1 hw2
  by_cases c1 : (p1.x 31).toNat < (p1.x 30).toNat
  · rw [if_pos c1] at N1
    exact ⟨s1, r1, by rw [if_pos c1]; exact N1⟩
  · rw [if_neg c1] at N1
    by_cases c2 : (p2.x 31).toNat < (p2.x 30).toNat
    · rw [if_pos c2] at N1
      exact ⟨s1, r1, by rw [if_neg c1, if_pos c2]; exact N1⟩
    · rw [if_neg c2] at N1
      obtain ⟨s2, r2, N2⟩ := n_subi S N1 hB a9 (by decide) (by decide) (by decide) (by decide) hr
      change NMid X W K A s0 q4 (h + 10) s2 at N2
      obtain ⟨s3, r3, N3⟩ := n_cmpbr (q' := 1) S N2 hB a10 (by
          have : ((1 : Nat) : Int) - (((h + 10 : Nat) : Int) + 1) = (1 : Int) - (h + 11) := by push_cast; omega
          rw [this]; exact a11) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) hL
      rw [condV_lo] at N3
      refine ⟨s3, Runs.trans r1 (Runs.trans r2 r3), ?_⟩
      rw [if_neg c1, if_neg c2]
      by_cases c3 : (q4.x 31).toNat < (q4.x 30).toNat
      · rw [if_pos (decide_eq_true c3)] at N3
        rw [if_pos c3]; exact N3
      · rw [if_neg (by simpa using c3)] at N3
        rw [if_neg c3]; exact N3

/-- **def prologue**, no locals (`r = 0`: `a5` emits `add x11, x11, #0`) -/
theorem n_prologue0 (S : A64SemN M X W) {h : Nat} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hL : A.length < 2 ^ 18) (h1 : 1 ≤ A.length)
    (a0 : A[h]? = some (ArmEnc.subi (armReg 31) (armReg 31) 8))
    (a1 : A[h + 1]? = some (ArmEnc.subsR (armReg 31) (armReg 30)))
    (a2 : A[h + 2]? = some (ArmEnc.bc 3 ((1 : Int) - (h + 2))))
    (a3 : A[h + 3]? = some (ArmEnc.str (armReg 1) (armReg 31) 0))
    (a4 : A[h + 4]? = some (ArmEnc.subi (armReg 31) (armReg 31) 8))
    (a5 : A[h + 5]? = some (ArmEnc.subsR (armReg 31) (armReg 30)))
    (a6 : A[h + 6]? = some (ArmEnc.bc 3 ((1 : Int) - (h + 6))))
    (a7 : A[h + 7]? = some (ArmEnc.str (armReg 8) (armReg 31) 0))
    (a8 : A[h + 8]? = some (ArmEnc.addi (armReg 8) (armReg 31) 0))
    (a9 : A[h + 9]? = some (ArmEnc.addi (armReg 31) (armReg 31) 0))
    (a10 : A[h + 10]? = some (ArmEnc.subsR (armReg 31) (armReg 30)))
    (a11 : A[h + 11]? = some (ArmEnc.bc 3 ((1 : Int) - (h + 11))))
    (hw1 : ¬ (st.x 31 - 8).toNat < (st.x 30).toNat → wok K (st.x 31 - 8).toNat) :
    let p1 := CallProbe.wr st 31 (st.x 31 - 8)
    let q1 := { p1 with m := CallProbe.upd p1.m (p1.x 31).toNat (p1.x 1) }
    let p2 := CallProbe.wr q1 31 (q1.x 31 - 8)
    let q2 := { p2 with m := CallProbe.upd p2.m (p2.x 31).toNat (p2.x 8) }
    let q3 := CallProbe.wr q2 8 (q2.x 31 + UInt64.ofNat 0)
    let q4 := CallProbe.wr q3 31 (q3.x 31 + UInt64.ofNat 0)
    (¬ (q1.x 31 - 8).toNat < (q1.x 30).toNat → wok K (q1.x 31 - 8).toNat) →
    ∃ s', Runs M s s' ∧
      if (p1.x 31).toNat < (p1.x 30).toNat then NMid X W K A s0 p1 1 s'
      else if (p2.x 31).toNat < (p2.x 30).toNat then NMid X W K A s0 p2 1 s'
      else NMid X W K A s0 q4 (if (q4.x 31).toNat < (q4.x 30).toNat then 1 else h + 12) s' := by
  intro p1 q1 p2 q2 q3 q4 hw2
  obtain ⟨s1, r1, N1⟩ := n_proHead S hM hB hL h1 a0 a1 a2 a3 a4 a5 a6 a7 a8 hw1 hw2
  by_cases c1 : (p1.x 31).toNat < (p1.x 30).toNat
  · rw [if_pos c1] at N1
    exact ⟨s1, r1, by rw [if_pos c1]; exact N1⟩
  · rw [if_neg c1] at N1
    by_cases c2 : (p2.x 31).toNat < (p2.x 30).toNat
    · rw [if_pos c2] at N1
      exact ⟨s1, r1, by rw [if_neg c1, if_pos c2]; exact N1⟩
    · rw [if_neg c2] at N1
      obtain ⟨s2, r2, N2⟩ := n_addi S N1 hB a9 (by decide) (by decide) (by decide) (by decide) (by decide)
      change NMid X W K A s0 q4 (h + 10) s2 at N2
      obtain ⟨s3, r3, N3⟩ := n_cmpbr (q' := 1) S N2 hB a10 (by
          have : ((1 : Nat) : Int) - (((h + 10 : Nat) : Int) + 1) = (1 : Int) - (h + 11) := by push_cast; omega
          rw [this]; exact a11) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) hL
      rw [condV_lo] at N3
      refine ⟨s3, Runs.trans r1 (Runs.trans r2 r3), ?_⟩
      rw [if_neg c1, if_neg c2]
      by_cases c3 : (q4.x 31).toNat < (q4.x 30).toNat
      · rw [if_pos (decide_eq_true c3)] at N3
        rw [if_pos c3]; exact N3
      · rw [if_neg (by simpa using c3)] at N3
        rw [if_neg c3]; exact N3

end JT
