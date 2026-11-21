/- T05: the small prims ISIZE / LEN (push x13) and BSIZE (`a13` prims 1, 3, 6; notes 8.1, 8.4). -/
import Nano.Run.NatT.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop} {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St}

/-- **ISIZE / LEN** (`pushA 1 q 29`): `n_push` with `r = 29` (x13) -/
theorem n_lenPush (S : A64SemN M X W) {h : Nat} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hL : A.length < 2 ^ 18) (h1 : 1 ≤ A.length)
    (a0 : A[h]? = some (ArmEnc.subi (armReg 31) (armReg 31) 8))
    (a1 : A[h + 1]? = some (ArmEnc.subsR (armReg 31) (armReg 30)))
    (a2 : A[h + 2]? = some (ArmEnc.bc 3 ((1 : Int) - (h + 2))))
    (a3 : A[h + 3]? = some (ArmEnc.str (armReg 29) (armReg 31) 0))
    (hw : ¬ (st.x 31 - 8).toNat < (st.x 30).toNat → wok K (st.x 31 - 8).toNat) :
    let st1 := CallProbe.wr st 31 (st.x 31 - 8)
    ∃ s', Runs M s s' ∧
      if (st1.x 31).toNat < (st1.x 30).toNat then NMid X W K A s0 st1 1 s'
      else NMid X W K A s0 { st1 with m := CallProbe.upd st1.m (st1.x 31).toNat (st1.x 29) } (h + 4) s' :=
  n_push (r := 29) S hM hB hL h1 a0 a1 a2 a3 (by decide) (by decide) hw

/-- **ISIZE** (prim 1) and **LEN** (prim 3) are the same A64 word sequence -/
abbrev n_isize := @n_lenPush
abbrev n_len := @n_lenPush

/-- **BSIZE** (`a13` prim 6): `ldr x5, [x11]; ldr x5, [x5]; str x5, [x11]` -/
theorem n_bsize (S : A64SemN M X W) {h : Nat} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (a0 : A[h]? = some (ArmEnc.ldr (armReg 5) (armReg 31) 0))
    (a1 : A[h + 1]? = some (ArmEnc.ldr (armReg 5) (armReg 5) 0))
    (a2 : A[h + 2]? = some (ArmEnc.str (armReg 5) (armReg 31) 0))
    (hw : wok K (st.x 31).toNat) :
    let st1 := CallProbe.wr st 5 (st.m (st.x 31).toNat)
    let st2 := CallProbe.wr st1 5 (st1.m (st1.x 5).toNat)
    wok K (st1.x 5).toNat → wok K (st2.x 31).toNat →
    ∃ s', Runs M s s' ∧
      NMid X W K A s0 { st2 with m := CallProbe.upd st2.m (st2.x 31).toNat (st2.x 5) } (h + 3) s' := by
  intro st1 st2 hw1 hw2
  obtain ⟨s1, r1, N1⟩ := n_ldr (a := (st.x 31).toNat) S hM hB a0 (by decide) (by decide) (by decide)
    (hM.x 31 (by omega) (by omega)) (by decide) (by decide) (by omega) hw
  obtain ⟨s2, r2, N2⟩ := n_ldr (a := (st1.x 5).toNat) S N1 hB a1 (by decide) (by decide) (by decide)
    (N1.x 5 (by omega) (by omega)) (by decide) (by decide) (by omega) hw1
  change NMid X W K A s0 st2 _ s2 at N2
  obtain ⟨s3, r3, N3⟩ := n_str (a := (st2.x 31).toNat) S N2 hB a2 (by decide) (N2.x 5 (by omega) (by omega))
    (by decide) (N2.x 31 (by omega) (by omega)) (by decide) (by decide) (by omega) hw2
  exact ⟨s3, Runs.trans (Runs.trans r1 r2) r3, N3⟩

end JT
