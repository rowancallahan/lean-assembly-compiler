/- T04 (round 2): the atom `cj c a b off` (`b<c> a b 2; jal 0 off` ↔ `subs; b.<not c>`). -/
import Nano.Run.NatA.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop}

/-- the first J instruction of `cj` -/
private def jhead (c : NCmp) (a b : Nat) : J :=
  match c with | .geu => .bgeu a b 2 | .ltu => .bltu a b 2 | .eq => .beq a b 2

private theorem cj_j (c : NCmp) (a b : Nat) (off : Int) : (NTm.cj c a b off).j = [jhead c a b, .jal 0 off] := by
  cases c <;> rfl

/-- J's compare is true (go to q+2) iff the A64 branch is not taken -/
private theorem cj_step0 (c : NCmp) (x y : Nat) {C : List J} {q : Nat} (s : CallProbe.St) (hc : C[q]? = some (jhead c x y)) :
    CallProbe.step C (q, s) = some ((if condV (NTm.cjC c) (s.x x) (s.x y) then q + 1 else q + 2), s) := by
  have h2 : ((q : Int) + 2).toNat = q + 2 := by omega
  cases c <;> simp only [jhead] at hc
  · by_cases h : (s.x y).toNat ≤ (s.x x).toNat
    · simp [CallProbe.step, hc, condV, NTm.cjC, h, h2, Nat.not_lt.2 h]
    · simp [CallProbe.step, hc, condV, NTm.cjC, h, Nat.lt_of_not_le h]
  · by_cases h : (s.x x).toNat < (s.x y).toNat
    · simp [CallProbe.step, hc, condV, NTm.cjC, h, h2, Nat.not_le.2 h]
    · simp [CallProbe.step, hc, condV, NTm.cjC, h, Nat.le_of_not_lt h]
  · by_cases h : s.x x = s.x y <;> simp [CallProbe.step, hc, condV, NTm.cjC, h, h2]

theorem asim_cj (S : A64SemN M X W) {c : NCmp} {x y : Nat} {off : Int} (hok : (NTm.cj c x y off).ok = true) :
    ASim M X W (NTm.cj c x y off) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, Bool.and_eq_true, mr_iff] at hok
  obtain ⟨⟨hx, hx0⟩, hy, hy0⟩ := hok
  have c0 : C[q]? = some (jhead c x y) := by simpa [cj_j] using hJ 0 (by simp [cj_j])
  have c1 : C[q + 1]? = some (.jal 0 off) := by simpa [cj_j] using hJ 1 (by simp [cj_j])
  have a0 : A[h]? = some (ArmEnc.subsR (armReg x) (armReg y)) := by
    simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
  have a1 : A[h + 1]? = some (ArmEnc.bc (NTm.cjC c) ((π (NTm.jt q (1 + off)) : Int) - ((h : Int) + 1))) := by
    simpa [NTm.a] using hA 1 (by simp [NTm.alen, NTm.a])
  have hq' : π (NTm.jt q (1 + off)) ≤ A.length := htg _ (by simp [NTm.tg])
  have vx : v.x x = st.x x := hag.x x (by omega) (mapped_lt hx) (fun hD => by simpa [NTm.reads] using hrd x hD)
  have vy : v.x y = st.x y := hag.x y (by omega) (mapped_lt hy) (fun hD => by simpa [NTm.reads] using hrd y hD)
  have hft2 : π (q + 2) = h + 2 := by simpa [cj_j, NTm.alen, NTm.a] using hft
  obtain ⟨s', r, N⟩ := n_cmpbr (c := NTm.cjC c) (q' := π (NTm.jt q (1 + off))) S hM hB a0 a1 (by cases c <;> decide)
    hx hx0 hy hy0 hq' hL
  rw [vx, vy] at N
  have hag' : Agree (outD (NTm.cj c x y off) D) v st :=
    hag.mono (fun r hr => Or.inl ⟨hr, by simp [NTm.writes]⟩)
  cases hrun with
  | head hS hs hrest =>
  rw [cj_step0 c x y st c0] at hs
  simp only [Option.some.injEq] at hs
  by_cases hcv : condV (NTm.cjC c) (st.x x) (st.x y) = true
  · rw [if_pos hcv] at hs; subst hs
    rw [if_pos hcv] at N
    cases hrest with
    | refl => exact ((hz 1 (by omega) (by simp [cj_j])) rfl).elim
    | head hS' hs' hrest' =>
      simp only [CallProbe.step, c1, Option.some.injEq] at hs'; subst hs'
      have e : (((q + 1 : Nat) : Int) + off).toNat = NTm.jt q (1 + off) := by simp [NTm.jt]; omega
      rw [e, wr_zero] at hrest'
      refine ⟨1, (NTm.jt q (1 + off), st), v, s', by omega, by simpa using hrest', r, N, hag', rfl, rfl, Or.inr (Or.inl ?_)⟩
      simp [NTm.tg]
  · rw [if_neg hcv] at hs; subst hs
    rw [if_neg hcv] at N
    refine ⟨0, _, v, s', Nat.zero_le _, hrest, r, ?_, hag', rfl, rfl, Or.inl (by simp [cj_j])⟩
    rw [hft2]; exact N

end JT
