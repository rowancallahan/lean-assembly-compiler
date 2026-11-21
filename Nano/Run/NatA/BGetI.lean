/- T07 (round 2): the atom `bgetI`, BGET's address tail `slli 6 6 3; alu 1 5 5 6; ld 14 5 16`
↔ `add x16, x5, x6, lsl #3; ldr x14, [x16, #16]`.  J 5 and 6 are dead afterwards (`kills`), 14 is written. -/
import Nano.Run.NatA.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop}

section
variable {C : List J} {pc : Nat} {s : CallProbe.St}

theorem stp_slli {rd rs sh : Nat} (h : C[pc]? = some (.slli rd rs sh)) :
    CallProbe.step C (pc, s) = some (pc + 1, CallProbe.wr s rd (s.x rs <<< sh.toUInt64)) := by
  simp [CallProbe.step, h]

theorem stp_alu {op rd a b : Nat} (h : C[pc]? = some (.alu op rd a b)) :
    CallProbe.step C (pc, s) = some (pc + 1, CallProbe.wr s rd (CallProbe.aluf op (s.x a) (s.x b))) := by
  simp [CallProbe.step, h]

theorem stp_ld {rd rs : Nat} {off : Int} (h : C[pc]? = some (.ld rd rs off)) :
    CallProbe.step C (pc, s) = some (pc + 1, CallProbe.wr s rd (s.m (CallProbe.ea (s.x rs) off))) := by
  simp [CallProbe.step, h]
end

theorem asim_bgetI (S : A64SemN M X W) : ASim M X W NTm.bgetI := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  have c0 : C[q]? = some (.slli 6 6 3) := (hJ 0 (by simp [NTm.j])).trans (by simp [NTm.j])
  have c1 : C[q + 1]? = some (.alu 1 5 5 6) := (hJ 1 (by simp [NTm.j])).trans (by simp [NTm.j])
  have c2 : C[q + 1 + 1]? = some (.ld 14 5 16) := (hJ 2 (by simp [NTm.j])).trans (by simp [NTm.j])
  have h3 : ((3 : Nat).toUInt64) = (3 : UInt64) := by decide
  have hft' : π (q + 1 + 1 + 1) = h + 2 := by
    have h1 : q + NTm.bgetI.j.length = q + 1 + 1 + 1 := rfl
    have h2 : NTm.bgetI.alen = 2 := rfl
    rw [h1, h2] at hft; exact hft
  cases hrun with
  | head hS0 hs0 hr1 =>
  have e0 := (Option.some.inj ((stp_slli c0).symm.trans hs0)).symm
  subst e0
  cases hr1 with
  | refl => exact ((hz 1 (by omega) (by simp [NTm.j])) rfl).elim
  | head hS1 hs1 hr2 =>
  have e1 := (Option.some.inj ((stp_alu c1).symm.trans hs1)).symm
  subst e1
  cases hr2 with
  | refl => exact ((hz 2 (by omega) (by simp [NTm.j])) rfl).elim
  | head hS2 hs2 hr3 =>
  have e2 := (Option.some.inj ((stp_ld c2).symm.trans hs2)).symm
  subst e2
  obtain ⟨st1, hst1⟩ : ∃ st1 : CallProbe.St, st1 = CallProbe.wr st 6 (st.x 6 <<< (3 : Nat).toUInt64) := ⟨_, rfl⟩
  rw [← hst1] at hS2 hr3
  obtain ⟨st2, hst2⟩ : ∃ st2 : CallProbe.St, st2 = CallProbe.wr st1 5 (CallProbe.aluf 1 (st1.x 5) (st1.x 6)) := ⟨_, rfl⟩
  rw [← hst2] at hS2 hr3
  obtain ⟨st3, hst3⟩ : ∃ st3 : CallProbe.St, st3 = CallProbe.wr st2 14 (st2.m (CallProbe.ea (st2.x 5) 16)) := ⟨_, rfl⟩
  rw [← hst3] at hr3
  have hwk : wok K (CallProbe.ea (st2.x 5) 16) := by
    have h := hS2
    simp only [SafeX, c2] at h
    first | exact h.2.2.2.2.2 | exact h.2.2.2.2 | exact h.2.2.2 | exact h.2.2 | exact h.2 | exact h
  have hx5 : st2.x 5 = st.x 5 + (st.x 6 <<< 3) := by
    simp [hst2, hst1, CallProbe.wr, CallProbe.upd, CallProbe.aluf, h3]
  have hm2 : st2.m = st.m := by simp [hst2, hst1, CallProbe.wr]
  have vx5 : v.x 5 = st.x 5 := hag.x 5 (by omega) (by omega) (fun hD => by simpa [NTm.reads] using hrd 5 hD)
  have vx6 : v.x 6 = st.x 6 := hag.x 6 (by omega) (by omega) (fun hD => by simpa [NTm.reads] using hrd 6 hD)
  have hea : CallProbe.ea (st2.x 5) 16 = (v.x 5 + (v.x 6 <<< 3)).toNat + 16 := by
    rw [hx5, vx5, vx6]; unfold CallProbe.ea; omega
  have a0 : A[h]? = some (ArmEnc.addLsl3 16 (armReg 5) (armReg 6)) := by
    simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
  have a1 : A[h + 1]? = some (ArmEnc.ldr (armReg 14) 16 16) := by
    simpa [NTm.a] using hA 1 (by simp [NTm.alen, NTm.a])
  obtain ⟨s1, r1, N1, hr16⟩ := n_addLsl3_16 S hM hB a0 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s2, r2, N2⟩ := n_ldr (a := (v.x 5 + (v.x 6 <<< 3)).toNat + 16) (nb := 16) S N1 hB a1 (by decide)
    (by decide) (by decide) hr16 (by decide) (by decide) rfl (hea ▸ hwk)
  have hval : v.m ((v.x 5 + (v.x 6 <<< 3)).toNat + 16) = st2.m (CallProbe.ea (st2.x 5) 16) := by
    rw [hag.m, hea, hm2]
  refine ⟨2, (q + 1 + 1 + 1, st3), CallProbe.wr v 14 (v.m ((v.x 5 + (v.x 6 <<< 3)).toNat + 16)), s2, by omega,
    (by have e : ∀ k, k + 1 + 1 - 2 = k := fun k => by omega
        rw [e]; exact hr3), Runs.trans r1 r2, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_,
    Or.inl ⟨by simp [NTm.j], rfl⟩⟩
  · show NMid X W K A s0 _ (π (q + 1 + 1 + 1)) s2
    rw [hft']; exact N2
  · intro j h0 h32 hn
    by_cases e : j = 14
    · subst e
      show (CallProbe.wr v 14 _).x 14 = st3.x 14
      rw [hst3, hval]; simp [CallProbe.wr, CallProbe.upd]
    · have h5 : j ≠ 5 := fun e5 => hn (Or.inr (by subst e5; simp [NTm.kills]))
      have h6 : j ≠ 6 := fun e6 => hn (Or.inr (by subst e6; simp [NTm.kills]))
      have hD : ¬ D j := fun hD => hn (Or.inl ⟨hD, by simpa [NTm.writes] using e⟩)
      have := hag.x j h0 h32 hD
      simp [hst3, hst2, hst1, CallProbe.wr, CallProbe.upd, e, h5, h6, this]
  · simp [hst3, hst2, hst1, CallProbe.wr, hag.m]
  · simp [hst3, hst2, hst1, CallProbe.wr, CallProbe.upd, hag.x0]
  · rw [hst3, CallProbe.wr_b, hst2, CallProbe.wr_b, hst1, CallProbe.wr_b]
  · rw [hst3, CallProbe.wr_w, hst2, CallProbe.wr_w, hst1, CallProbe.wr_w]

end JT
