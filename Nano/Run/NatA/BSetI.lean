/- T08 (round 2): the atom `bsetI` (BSET's address tail `slli 6 6 3; alu 1 6 5 6; sd 14 6 16`) ↔
`add x16, x5, x6, lsl #3; str x14, [x16, #16]`. -/
import Nano.Run.NatA.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop}

private theorem ea16 (b : UInt64) : CallProbe.ea b 16 = b.toNat + 16 := by unfold CallProbe.ea; omega

theorem asim_bsetI (S : A64SemN M X W) (hok : (NTm.bsetI).ok = true) : ASim M X W NTm.bsetI := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  have c0 : C[q]? = some (.slli 6 6 3) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  have c1 : C[q + 1]? = some (.alu 1 6 5 6) := by simpa [NTm.j] using hJ 1 (by simp [NTm.j])
  have c2 : C[q + 1 + 1]? = some (.sd 14 6 16) := by simpa [NTm.j] using hJ 2 (by simp [NTm.j])
  have h3 : ((3 : Nat).toUInt64) = (3 : UInt64) := by decide
  have h5 : v.x 5 = st.x 5 := hag.x 5 (by omega) (by omega) (fun hD => by simpa [NTm.reads] using hrd 5 hD)
  have h6 : v.x 6 = st.x 6 := hag.x 6 (by omega) (by omega) (fun hD => by simpa [NTm.reads] using hrd 6 hD)
  have h14 : v.x 14 = st.x 14 := hag.x 14 (by omega) (by omega) (fun hD => by simpa [NTm.reads] using hrd 14 hD)
  have hft' : π (q + 1 + 1 + 1) = h + 2 := by
    have e1 : q + NTm.bsetI.j.length = q + 1 + 1 + 1 := rfl
    have e2 : NTm.bsetI.alen = 2 := rfl
    rw [e1, e2] at hft; exact hft
  cases hrun with
  | head hS hs hrest =>
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  cases hrest with
  | refl => exact absurd rfl (hz 1 (by decide) (by simp [NTm.j]))
  | head hS2 hs2 hrest2 =>
  simp only [CallProbe.step, c1, Option.some.injEq] at hs2; subst hs2
  cases hrest2 with
  | refl => exact absurd rfl (hz 2 (by decide) (by simp [NTm.j]))
  | head hS3 hs3 hrest3 =>
  simp only [CallProbe.step, c2, Option.some.injEq] at hs3; subst hs3
  obtain ⟨st2, hst2⟩ : ∃ st2 : CallProbe.St, st2 = CallProbe.wr (CallProbe.wr st 6 (st.x 6 <<< (3 : Nat).toUInt64)) 6
      (CallProbe.aluf 1 ((CallProbe.wr st 6 (st.x 6 <<< (3 : Nat).toUInt64)).x 5)
        ((CallProbe.wr st 6 (st.x 6 <<< (3 : Nat).toUInt64)).x 6)) := ⟨_, rfl⟩
  rw [← hst2] at hS3 hrest3
  have hw : wok K (CallProbe.ea (st2.x 6) 16) := by
    have hh := hS3
    simp only [SafeX, c2] at hh
    exact hh.2.2.2.2.2
  have e6 : st2.x 6 = st.x 5 + (st.x 6 <<< 3) := by
    simp [hst2, CallProbe.wr, CallProbe.upd, CallProbe.aluf, h3]
  have e14 : st2.x 14 = st.x 14 := by simp [hst2, CallProbe.wr, CallProbe.upd]
  have hm2 : st2.m = st.m := by simp [hst2, CallProbe.wr]
  rw [e6, ea16] at hw
  rw [e6, ea16, e14, hm2] at hrest3
  have a0 : A[h]? = some (ArmEnc.addLsl3 16 (armReg 5) (armReg 6)) := by
    simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
  have a1 : A[h + 1]? = some (ArmEnc.str (armReg 14) 16 16) := by
    simpa [NTm.a] using hA 1 (by simp [NTm.alen, NTm.a])
  obtain ⟨s1, r1, N1, o1⟩ := n_addLsl3_16 S hM hB a0 (by decide) (by decide) (by decide) (by decide)
  rw [h5, h6] at o1
  obtain ⟨s2, r2, N2⟩ := n_str (a := (st.x 5 + (st.x 6 <<< 3)).toNat + 16) (v := st.x 14) S N1 hB a1 (by decide)
    (by rw [N1.x 14 (by omega) (by omega)]; exact h14) (by decide) o1 (by decide) (by decide) rfl hw
  refine ⟨2, (q + 1 + 1 + 1, { st2 with m := CallProbe.upd st.m ((st.x 5 + (st.x 6 <<< 3)).toNat + 16) (st.x 14) }),
    { v with m := CallProbe.upd v.m ((st.x 5 + (st.x 6 <<< 3)).toNat + 16) (st.x 14) }, s2, by omega,
    (by have e : ∀ k, k + 1 + 1 - 2 = k := fun k => by omega
        rw [e]; exact hrest3), Runs.trans r1 r2, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, Or.inl (by simp [NTm.j])⟩
  · show NMid X W K A s0 _ (π (q + 1 + 1 + 1)) s2
    rw [hft']; exact N2
  · intro j h0 h32 hn
    have hj6 : j ≠ 6 := fun e => hn (Or.inr (by subst e; simp [NTm.kills]))
    have hD : ¬ D j := fun hd => hn (Or.inl ⟨hd, by simp [NTm.writes]⟩)
    have := hag.x j h0 h32 hD
    simp [hst2, CallProbe.wr, CallProbe.upd, hj6, this]
  · simp [hag.m]
  · simp [hst2, CallProbe.wr, CallProbe.upd, hag.x0]
  · show st2.b = st.b
    rw [hst2, CallProbe.wr_b, CallProbe.wr_b]
  · show st2.ly = st.ly
    rw [hst2, CallProbe.wr_w, CallProbe.wr_w]

end JT
