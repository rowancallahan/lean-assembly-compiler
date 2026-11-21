/- T07: BGET (GenArm `a13` prim 7, Testing/notes/NATIVE_ARM_TEMPLATES.md 8.5) as an A64 run on `NMid`.
x6 = index, x5 = buffer afterwards (the J temporaries t0/t1 differ: dead at the boundary). -/
import Nano.Run.NatT.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop} {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St}

/-- **BGET** (`a13` prim 7): `ldp x6, x5, [x11]; add x11, x11, #8; ldr x7, [x5]; movz x14, #0; subs x16, x6, x7;
b.hs .+3; add x16, x5, x6, lsl #3; ldr x14, [x16, #16]; str x14, [x11]` (index on top, buffer below; the element, or 0
when the index is out of range, replaces both) -/
theorem n_bget (S : A64SemN M X W) {h : Nat} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hL : A.length < 2 ^ 18)
    (a0 : A[h]? = some (ArmEnc.ldp (armReg 6) (armReg 5) (armReg 31)))
    (a1 : A[h + 1]? = some (ArmEnc.addi (armReg 31) (armReg 31) 8))
    (a2 : A[h + 2]? = some (ArmEnc.ldr (armReg 7) (armReg 5) 0))
    (a3 : A[h + 3]? = some (ArmEnc.movz (armReg 14) 0))
    (a4 : A[h + 4]? = some (ArmEnc.subsR (armReg 6) (armReg 7)))
    (a5 : A[h + 5]? = some (ArmEnc.bc 2 3))
    (a6 : A[h + 6]? = some (ArmEnc.addLsl3 16 (armReg 5) (armReg 6)))
    (a7 : A[h + 7]? = some (ArmEnc.ldr (armReg 14) 16 16))
    (a8 : A[h + 8]? = some (ArmEnc.str (armReg 14) (armReg 31) 0))
    (hw : wok K (st.x 31).toNat) (hw8 : wok K ((st.x 31).toNat + 8)) :
    let st1 := CallProbe.wr (CallProbe.wr st 6 (st.m (st.x 31).toNat)) 5 (st.m ((st.x 31).toNat + 8))
    let st2 := CallProbe.wr st1 31 (st1.x 31 + UInt64.ofNat 8)
    let st3 := CallProbe.wr st2 7 (st2.m (st2.x 5).toNat)
    let st4 := CallProbe.wr st3 14 (UInt64.ofNat 0)
    let st5 := CallProbe.wr st4 14 (st4.m ((st4.x 5 + (st4.x 6 <<< 3)).toNat + 16))
    let st6 := if (st4.x 7).toNat ≤ (st4.x 6).toNat then st4 else st5
    wok K (st2.x 5).toNat →
    (¬ (st4.x 7).toNat ≤ (st4.x 6).toNat → wok K ((st4.x 5 + (st4.x 6 <<< 3)).toNat + 16)) →
    wok K (st2.x 31).toNat →
    ∃ s', Runs M s s' ∧
      NMid X W K A s0 { st6 with m := CallProbe.upd st6.m (st6.x 31).toNat (st6.x 14) } (h + 9) s' := by
  intro st1 st2 st3 st4 st5 st6 hw5 hel hw31
  have h8 := (List.getElem?_eq_some_iff.1 a8).1
  have e31 : st4.x 31 = st2.x 31 := by simp [st4, st3, CallProbe.wr, CallProbe.upd]
  have e31' : st5.x 31 = st2.x 31 := by simp [st5, st4, st3, CallProbe.wr, CallProbe.upd]
  obtain ⟨s2, r2, N2⟩ := n_pop2 S hM hB a0 a1 (by decide) hw hw8
  change NMid X W K A s0 st2 _ s2 at N2
  obtain ⟨s3, r3, N3⟩ := n_ldr (a := (st2.x 5).toNat) (nb := armReg 5) S N2 hB a2 (by decide) (by decide)
    (by decide) (N2.x 5 (by omega) (by omega)) (by decide) (by decide) (by omega) hw5
  change NMid X W K A s0 st3 _ s3 at N3
  obtain ⟨s4, r4, N4⟩ := n_movz S N3 hB a3 (by decide) (by decide) (by decide)
  change NMid X W K A s0 st4 _ s4 at N4
  obtain ⟨s5, r5, N5⟩ := n_cmpbr (q' := h + 8) S N4 hB a4 (by
      have : ((h + 8 : Nat) : Int) - (((h + 2 + 1 + 1 : Nat) : Int) + 1) = 3 := by push_cast; omega
      rw [this]; exact a5) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) hL
  rw [condV_hs] at N5
  have fin : ∀ {sp : M.State} {sv : CallProbe.St}, NMid X W K A s0 sv (h + 8) sp → sv.x 31 = st2.x 31 →
      ∃ s', Runs M sp s' ∧
        NMid X W K A s0 { sv with m := CallProbe.upd sv.m (sv.x 31).toNat (sv.x 14) } (h + 9) s' := fun N e =>
    n_str (a := (sv.x 31).toNat) S N hB a8 (by decide) (N.x 14 (by omega) (by omega)) (by decide)
      (N.x 31 (by omega) (by omega)) (by decide) (by decide) (by omega) (by rw [e]; exact hw31)
  by_cases hc : (st4.x 7).toNat ≤ (st4.x 6).toNat
  · rw [if_pos (decide_eq_true hc)] at N5
    have e6 : st6 = st4 := if_pos hc
    obtain ⟨s6, r6, N6⟩ := fin N5 e31
    exact ⟨s6, Runs.trans (Runs.trans (Runs.trans (Runs.trans r2 r3) r4) r5) r6, by rw [e6]; exact N6⟩
  · rw [if_neg (by simpa using hc)] at N5
    have e6 : st6 = st5 := if_neg hc
    obtain ⟨s6, r6, N6, hr16⟩ := n_addLsl3_16 S N5 hB a6 (by decide) (by decide) (by decide) (by decide)
    obtain ⟨s7, r7, N7⟩ := n_ldr (a := (st4.x 5 + (st4.x 6 <<< 3)).toNat + 16) (nb := 16) S N6 hB a7 (by decide)
      (by decide) (by decide) hr16 (by decide) (by decide) rfl (hel hc)
    change NMid X W K A s0 st5 _ s7 at N7
    obtain ⟨s8, r8, N8⟩ := fin N7 e31'
    exact ⟨s8, Runs.trans (Runs.trans (Runs.trans (Runs.trans (Runs.trans r2 r3) r4) r5) r6)
      (Runs.trans r7 r8), by rw [e6]; exact N8⟩

end JT
