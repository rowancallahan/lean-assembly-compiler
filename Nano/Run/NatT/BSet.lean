/- T08: BSET (`Nano/Codegen/GenArm.lean` prim 8, NATIVE_ARM_TEMPLATES.md 8.6) as an A64 run on `NMid`. -/
import Nano.Run.NatT.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop} {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St}

/-- **BSET** (`a13` prim 8): `ldp x14, x6, [x11]; ldr x5, [x11, #16]; add x11, x11, #16; ldr x7, [x5];
subs x16, x6, x7; b.hs END; add x16, x5, x6, lsl #3; str x14, [x16, #16]` (END = word `h + 8`).
Unlike the J template, x6 keeps the index (J: t1 = buf + 8·index) in range; x16 holds the cell address. -/
theorem n_bset (S : A64SemN M X W) {h : Nat} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hL : A.length < 2 ^ 18) (he : h + 8 ≤ A.length)
    (a0 : A[h]? = some (ArmEnc.ldp (armReg 14) (armReg 6) (armReg 31)))
    (a1 : A[h + 1]? = some (ArmEnc.ldr (armReg 5) (armReg 31) 16))
    (a2 : A[h + 2]? = some (ArmEnc.addi (armReg 31) (armReg 31) 16))
    (a3 : A[h + 3]? = some (ArmEnc.ldr (armReg 7) (armReg 5) 0))
    (a4 : A[h + 4]? = some (ArmEnc.subsR (armReg 6) (armReg 7)))
    (a5 : A[h + 5]? = some (ArmEnc.bc 2 3))
    (a6 : A[h + 6]? = some (ArmEnc.addLsl3 16 (armReg 5) (armReg 6)))
    (a7 : A[h + 7]? = some (ArmEnc.str (armReg 14) 16 16))
    (hw : wok K (st.x 31).toNat) (hw8 : wok K ((st.x 31).toNat + 8)) (hw16 : wok K ((st.x 31).toNat + 16)) :
    let st1 := CallProbe.wr (CallProbe.wr st 14 (st.m (st.x 31).toNat)) 6 (st.m ((st.x 31).toNat + 8))
    let st2 := CallProbe.wr st1 5 (st1.m ((st1.x 31).toNat + 16))
    let st3 := CallProbe.wr st2 31 (st2.x 31 + UInt64.ofNat 16)
    let st4 := CallProbe.wr st3 7 (st3.m (st3.x 5).toNat)
    wok K (st3.x 5).toNat →
    (¬ (st4.x 7).toNat ≤ (st4.x 6).toNat → wok K ((st4.x 5 + (st4.x 6 <<< 3)).toNat + 16)) →
    ∃ s', Runs M s s' ∧
      NMid X W K A s0 (if (st4.x 7).toNat ≤ (st4.x 6).toNat then st4
        else { st4 with m := CallProbe.upd st4.m ((st4.x 5 + (st4.x 6 <<< 3)).toNat + 16) (st4.x 14) }) (h + 8) s' := by
  intro st1 st2 st3 st4 hw5 hst
  have e31 : st1.x 31 = st.x 31 := by simp [st1, CallProbe.wr, CallProbe.upd]
  obtain ⟨s1, r1, N1⟩ := n_ldp S hM hB a0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (hM.x 31 (by omega) (by omega)) hw hw8
  obtain ⟨s2, r2, N2⟩ := n_ldr (a := (st1.x 31).toNat + 16) S N1 hB a1 (by decide) (by decide) (by decide)
    (N1.x 31 (by omega) (by omega)) (by decide) (by decide) rfl (by rw [e31]; exact hw16)
  change NMid X W K A s0 st2 _ s2 at N2
  obtain ⟨s3, r3, N3⟩ := n_addi S N2 hB a2 (by decide) (by decide) (by decide) (by decide) (by decide)
  change NMid X W K A s0 st3 _ s3 at N3
  obtain ⟨s4, r4, N4⟩ := n_ldr (a := (st3.x 5).toNat) S N3 hB a3 (by decide) (by decide) (by decide)
    (N3.x 5 (by omega) (by omega)) (by decide) (by decide) (by omega) hw5
  change NMid X W K A s0 st4 _ s4 at N4
  obtain ⟨s5, r5, N5⟩ := n_cmpbr (q' := h + 8) S N4 hB a4 (by
      have : (((h + 8 : Nat) : Int) - (((h + 4 : Nat) : Int) + 1)) = 3 := by push_cast; omega
      rw [this]; exact a5) (by decide) (by decide) (by decide) (by decide) (by decide) he hL
  rw [condV_hs] at N5
  by_cases hc : (st4.x 7).toNat ≤ (st4.x 6).toNat
  · rw [if_pos (decide_eq_true hc)] at N5
    exact ⟨s5, Runs.trans (Runs.trans (Runs.trans (Runs.trans r1 r2) r3) r4) r5, by rw [if_pos hc]; exact N5⟩
  · rw [if_neg (by simpa using hc)] at N5
    obtain ⟨s6, r6, N6, o6⟩ := n_addLsl3_16 S N5 hB a6 (by decide) (by decide) (by decide) (by decide)
    obtain ⟨s7, r7, N7⟩ := n_str (a := (st4.x 5 + (st4.x 6 <<< 3)).toNat + 16) S N6 hB a7 (by decide)
      (N6.x 14 (by omega) (by omega)) (by decide) o6 (by decide) (by decide) rfl (hst hc)
    exact ⟨s7, Runs.trans (Runs.trans (Runs.trans (Runs.trans (Runs.trans (Runs.trans r1 r2) r3) r4) r5) r6) r7,
      by rw [if_neg hc]; exact N7⟩

end JT
