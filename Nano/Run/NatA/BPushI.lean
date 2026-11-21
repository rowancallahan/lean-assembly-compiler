/- T09 (round 2): atom `bpushI` = J `slli 15 7 3; alu 1 15 15 5` ↔ `add x15, x5, x7, lsl #3`. -/
import Nano.Run.NatA.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop}

/-! ## for ArmNat -/

/-- `add xd, xn, xm, lsl #3` into a mapped register -/
theorem n_addLsl3 {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St} {q : Nat} (S : A64SemN M X W)
    (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    {d n m : Nat} (hA : A[q]? = some (ArmEnc.addLsl3 (armReg d) (armReg n) (armReg m))) (hd : mapped d = true)
    (h0 : d ≠ 0) (hn : mapped n = true) (hn0 : n ≠ 0) (hm : mapped m = true) (hm0 : m ≠ 0) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (st.x n + (st.x m <<< 3))) (q + 1) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.addLsl3 s _ _ _ hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (armReg_lt hd h0) (armReg_lt hn hn0) (armReg_lt hm hm0) (nmid_word hM hA hB)
  rw [hM.x n (by omega) (mapped_lt hn), hM.x m (by omega) (mapped_lt hm)] at this
  exact nmid_set hM hd h0 this

theorem wr_wr15 (s : CallProbe.St) (x y : UInt64) :
    CallProbe.wr (CallProbe.wr s 15 x) 15 y = CallProbe.wr s 15 y := by
  simp only [CallProbe.wr]
  rw [if_neg (by decide), if_neg (by decide)]
  congr 1
  funext i
  simp [CallProbe.upd]
  split <;> rfl

theorem asim_bpushI (S : A64SemN M X W) (hok : (NTm.bpushI).ok = true) : ASim M X W NTm.bpushI := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  have c0 : C[q]? = some (.slli 15 7 3) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  have c1 : C[q + 1]? = some (.alu 1 15 15 5) := by simpa [NTm.j] using hJ 1 (by simp [NTm.j])
  cases hrun with
  | head hS hs hrest =>
  simp only [SafeX, c0] at hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  cases hrest with
  | refl => exact absurd rfl (hz 1 (by decide) (by simp [NTm.j]))
  | head hS2 hs2 hrest2 =>
  simp only [SafeX, c1] at hS2
  simp only [CallProbe.step, c1, Option.some.injEq] at hs2; subst hs2
  rw [wr_wr15] at hrest2
  have vx : v.x 5 = st.x 5 := hag.x 5 (by omega) (by omega) (fun hD => by simpa [NTm.reads] using hrd 5 hD)
  have vy : v.x 7 = st.x 7 := hag.x 7 (by omega) (by omega) (fun hD => by simpa [NTm.reads] using hrd 7 hD)
  have a0 : A[h]? = some (ArmEnc.addLsl3 (armReg 15) (armReg 5) (armReg 7)) := by
    simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
  obtain ⟨s', r, N⟩ := n_addLsl3 S hM hB a0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e : ∀ x : UInt64, CallProbe.aluf 1 ((CallProbe.wr st 15 x).x 15) ((CallProbe.wr st 15 x).x 5) = st.x 5 + x := by
    intro x; simp [CallProbe.wr, CallProbe.upd, CallProbe.aluf, UInt64.add_comm]
  have s3 : ((3 : Nat).toUInt64) = (3 : UInt64) := rfl
  rw [e, s3] at hrest2
  rw [vx, vy] at N
  refine ⟨1, (q + 1 + 1, CallProbe.wr st 15 (st.x 5 + (st.x 7 <<< 3))), CallProbe.wr v 15 (st.x 5 + (st.x 7 <<< 3)), s', by omega, by simpa using hrest2, r, ?_, ?_, CallProbe.wr_b _ _ _, CallProbe.wr_w _ _ _, Or.inl rfl⟩
  · rw [show π (q + 1 + 1) = _ from hft]; simpa [NTm.alen, NTm.a] using N
  · exact (agree_wr hag 15 _).mono (fun r hr => Or.inl ⟨hr.1, by simp only [NTm.writes, beq_eq_false_iff_ne]; exact fun e => hr.2 e⟩)

end JT
