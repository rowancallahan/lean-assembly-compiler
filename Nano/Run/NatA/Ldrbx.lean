import Nano.Run.NatA.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop}

private theorem wr_m' (s : CallProbe.St) (r : Nat) (v : UInt64) : (CallProbe.wr s r v).m = s.m := by
  unfold CallProbe.wr; split <;> rfl

private theorem ea_zero (v : UInt64) : CallProbe.ea v 0 = v.toNat := by simp [CallProbe.ea]

/-- **atom `ldrbx d n m`**: `alu 1 d n m; lbu d d 0` ↔ `ldrb wd, [xn, xm]` -/
theorem asim_ldrbx (S : A64SemN M X W) {d n m : Nat} (hok : (NTm.ldrbx d n m).ok = true) :
    ASim M X W (NTm.ldrbx d n m) := by
  intro K C A s0 s v st z N π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, Bool.and_eq_true, mr_iff] at hok
  obtain ⟨⟨⟨hd, hd0⟩, hx, hx0⟩, hy, hy0⟩ := hok
  have c0 : C[q]? = some (.alu 1 d n m) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  have c1 : C[q + 1]? = some (.lbu d d 0) := by simpa [NTm.j] using hJ 1 (by simp [NTm.j])
  have vx : v.x n = st.x n := hag.x n (by omega) (mapped_lt hx) (fun hD => by simpa [NTm.reads] using hrd n hD)
  have vy : v.x m = st.x m := hag.x m (by omega) (mapped_lt hy) (fun hD => by simpa [NTm.reads] using hrd m hD)
  have e1 : CallProbe.aluf 1 (st.x n) (st.x m) = st.x n + st.x m := by simp [CallProbe.aluf]
  cases hrun with
  | head hS hs hrest =>
  simp only [SafeX, c0] at hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  cases hrest with
  | refl => exact absurd rfl (hz 1 (by omega) (by simp [NTm.j]))
  | head hS2 hs2 hrest2 =>
  simp only [SafeX, c1] at hS2
  obtain ⟨-, -, -, -, -, hbok⟩ := hS2
  simp only [CallProbe.step, c1, Option.some.injEq] at hs2; subst hs2
  rw [wr_same _ hd0, e1, ea_zero] at hbok
  have eJ : CallProbe.wr (CallProbe.wr st d (CallProbe.aluf 1 (st.x n) (st.x m))) d
      (CallProbe.lbm (CallProbe.wr st d (CallProbe.aluf 1 (st.x n) (st.x m))).m
        (CallProbe.ea ((CallProbe.wr st d (CallProbe.aluf 1 (st.x n) (st.x m))).x d) 0)) =
      CallProbe.wr st d (CallProbe.lbm st.m (st.x n + st.x m).toNat) := by
    rw [wr_same _ hd0, wr_m', e1, ea_zero, wr_wr]
  rw [eJ] at hrest2
  have hπ : π (q + 1 + 1) = h + 1 := by simpa [NTm.j, NTm.alen, NTm.a] using hft
  obtain ⟨s', r, N'⟩ := n_ldrbR S hM hB (by simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])) hd hd0 hx hx0 hy hy0
    (by rw [vx, vy]; exact hbok)
  rw [vx, vy, hag.m] at N'
  have hagr : Agree (outD (NTm.ldrbx d n m) D) (CallProbe.wr v d (CallProbe.lbm st.m (st.x n + st.x m).toNat))
      (CallProbe.wr st d (CallProbe.lbm st.m (st.x n + st.x m).toNat)) :=
    (agree_wr hag d _).mono (fun r hr => Or.inl ⟨hr.1, by
      simp only [NTm.writes, beq_eq_false_iff_ne]; exact fun e => hr.2 e.symm⟩)
  refine ⟨1, (q + 1 + 1, CallProbe.wr st d (CallProbe.lbm st.m (st.x n + st.x m).toNat)),
    CallProbe.wr v d (CallProbe.lbm st.m (st.x n + st.x m).toNat), s', by omega, by simpa using hrest2, r,
    by rw [hπ]; exact N', hagr, CallProbe.wr_b _ _ _, CallProbe.wr_w _ _ _, Or.inl ⟨rfl, rfl⟩⟩

end JT
