/- T05: the atom `bgeu a b off` ↔ `subs x16, xa, xb; b.hs target` (one J step; `n_cmpbr` with c = 2). -/
import Nano.Run.NatA.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop}

private theorem condV_hs' (a b : UInt64) : condV 2 a b = decide (b.toNat ≤ a.toNat) := by simp [condV]

theorem asim_bgeu (S : A64SemN M X W) {a b : Nat} {off : Int} (hok : (NTm.bgeu a b off).ok = true) :
    ASim M X W (NTm.bgeu a b off) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, Bool.and_eq_true, mr_iff] at hok
  obtain ⟨⟨ha, ha0⟩, hb', hb0⟩ := hok
  have c0 : C[q]? = some (.bgeu a b off) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  have a0 : A[h]? = some (ArmEnc.subsR (armReg a) (armReg b)) := by
    simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
  have a1 : A[h + 1]? = some (ArmEnc.bc 2 ((π (NTm.jt q off) : Int) - ((h : Int) + 1))) := by
    simpa [NTm.a] using hA 1 (by simp [NTm.alen, NTm.a])
  have hq' : π (NTm.jt q off) ≤ A.length := htg _ (by simp [NTm.tg])
  have hft' : π (q + 1) = h + 2 := by simpa [NTm.j, NTm.alen, NTm.a] using hft
  have va : v.x a = st.x a := hag.x a (by omega) (mapped_lt ha) (fun hD => by simpa [NTm.reads] using hrd a hD)
  have vb : v.x b = st.x b := hag.x b (by omega) (mapped_lt hb') (fun hD => by simpa [NTm.reads] using hrd b hD)
  cases hrun with
  | head hS hs hrest =>
  simp only [CallProbe.step, c0, Option.some.injEq] at hs
  obtain ⟨s', r, N⟩ := n_cmpbr (q' := π (NTm.jt q off)) S hM hB a0 a1 (by decide) ha ha0 hb' hb0 hq' hL
  rw [condV_hs', va, vb] at N
  have hag' : Agree (outD (NTm.bgeu a b off) D) v st :=
    hag.mono (fun r hr => Or.inl ⟨hr, by simp [NTm.writes]⟩)
  by_cases hc : (st.x b).toNat ≤ (st.x a).toNat
  · rw [if_pos hc] at hs; subst hs
    rw [if_pos (decide_eq_true hc)] at N
    exact ⟨0, _, v, s', Nat.zero_le _, by simpa using hrest, r, N, hag', rfl, rfl, Or.inr (Or.inl (by simp [NTm.tg, NTm.jt]))⟩
  · rw [if_neg hc] at hs; subst hs
    rw [if_neg (by simpa using hc)] at N
    exact ⟨0, _, v, s', Nat.zero_le _, by simpa using hrest, r, by rw [hft']; exact N, hag', rfl, rfl,
      Or.inl ⟨by simp [NTm.j], rfl⟩⟩

end JT
