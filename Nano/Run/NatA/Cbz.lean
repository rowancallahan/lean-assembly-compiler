/- Round 2 / T06: the compare-with-zero atoms `lpz`, `bnez`, `beqz` (Testing/notes/NATIVE_ARM_ATOM_TASKS.md). -/
import Nano.Run.NatA.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop}


/-- **`bnez r off`** = `bne r 0 off` ↔ `cbnz xr, target` -/
theorem asim_bnez (S : A64SemN M X W) {r : Nat} {off : Int} (hok : (NTm.bnez r off).ok = true) :
    ASim M X W (NTm.bnez r off) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, mr_iff] at hok
  obtain ⟨hr, hr0⟩ := hok
  have c0 : C[q]? = some (.bne r 0 off) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  cases hrun with
  | head hS hs hrest =>
  simp only [SafeX, c0] at hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  have vr : v.x r = st.x r := hag.x r (by omega) (mapped_lt hr) (fun hD => by simpa [NTm.reads] using hrd r hD)
  have a0 : A[h]? = some (ArmEnc.cbnz (armReg r) ((π (NTm.jt q off) : Int) - h)) := by
    simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
  have tgt : π (NTm.jt q off) ≤ A.length := htg _ (by simp [NTm.tg])
  obtain ⟨s', rn, N⟩ := n_cbnz S hM hB a0 hr hr0 tgt hL
  have hag' : Agree (outD (NTm.bnez r off) D) v st :=
    hag.mono (fun r' hr' => Or.inl ⟨hr', by simp [NTm.writes]⟩)
  rw [vr] at N
  have hft1 : π (q + 1) = h + 1 := by simpa [NTm.j, NTm.alen, NTm.a] using hft
  by_cases e : st.x r = 0
  · rw [if_pos e] at N
    rw [hag.x0, if_neg (fun hne => hne e)] at hrest
    exact ⟨0, (q + 1, st), v, s', Nat.zero_le _, hrest, rn,
      by show NMid X W K A s0 v (π (q + 1)) s'; rw [hft1]; exact N, hag', rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rw [if_neg e] at N
    rw [hag.x0, if_pos e] at hrest
    exact ⟨0, (((q : Int) + off).toNat, st), v, s', Nat.zero_le _, hrest, rn, N, hag', rfl, rfl,
      Or.inr (Or.inl (by simp [NTm.tg, NTm.jt]))⟩

/-- **`beqz r off`** = `beq r 0 off` ↔ `cbz xr, target` -/
theorem asim_beqz (S : A64SemN M X W) {r : Nat} {off : Int} (hok : (NTm.beqz r off).ok = true) :
    ASim M X W (NTm.beqz r off) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, mr_iff] at hok
  obtain ⟨hr, hr0⟩ := hok
  have c0 : C[q]? = some (.beq r 0 off) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  cases hrun with
  | head hS hs hrest =>
  simp only [SafeX, c0] at hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  have vr : v.x r = st.x r := hag.x r (by omega) (mapped_lt hr) (fun hD => by simpa [NTm.reads] using hrd r hD)
  have a0 : A[h]? = some (ArmEnc.cbz (armReg r) ((π (NTm.jt q off) : Int) - h)) := by
    simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
  have tgt : π (NTm.jt q off) ≤ A.length := htg _ (by simp [NTm.tg])
  obtain ⟨s', rn, N⟩ := n_cbz S hM hB a0 hr hr0 tgt hL
  have hag' : Agree (outD (NTm.beqz r off) D) v st :=
    hag.mono (fun r' hr' => Or.inl ⟨hr', by simp [NTm.writes]⟩)
  rw [vr] at N
  have hft1 : π (q + 1) = h + 1 := by simpa [NTm.j, NTm.alen, NTm.a] using hft
  by_cases e : st.x r = 0
  · rw [if_pos e] at N
    rw [hag.x0, if_pos e] at hrest
    exact ⟨0, (((q : Int) + off).toNat, st), v, s', Nat.zero_le _, hrest, rn, N, hag', rfl, rfl,
      Or.inr (Or.inl (by simp [NTm.tg, NTm.jt]))⟩
  · rw [if_neg e] at N
    rw [hag.x0, if_neg e] at hrest
    exact ⟨0, (q + 1, st), v, s', Nat.zero_le _, hrest, rn,
      by show NMid X W K A s0 v (π (q + 1)) s'; rw [hft1]; exact N, hag', rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- **`lpz r off`** = `beq r 0 2; jal 0 off` ↔ `cbnz xr, target` (1 or 2 J steps) -/
theorem asim_lpz (S : A64SemN M X W) {r : Nat} {off : Int} (hok : (NTm.lpz r off).ok = true) :
    ASim M X W (NTm.lpz r off) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, mr_iff] at hok
  obtain ⟨hr, hr0⟩ := hok
  have c0 : C[q]? = some (.beq r 0 2) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  have c1 : C[q + 1]? = some (.jal 0 off) := by simpa [NTm.j] using hJ 1 (by simp [NTm.j])
  cases hrun with
  | head hS hs hrest =>
  simp only [SafeX, c0] at hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  have vr : v.x r = st.x r := hag.x r (by omega) (mapped_lt hr) (fun hD => by simpa [NTm.reads] using hrd r hD)
  have a0 : A[h]? = some (ArmEnc.cbnz (armReg r) ((π (NTm.jt q (1 + off)) : Int) - h)) := by
    simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
  have tgt : π (NTm.jt q (1 + off)) ≤ A.length := htg _ (by simp [NTm.tg])
  obtain ⟨s', rn, N⟩ := n_cbnz S hM hB a0 hr hr0 tgt hL
  have hag' : Agree (outD (NTm.lpz r off) D) v st :=
    hag.mono (fun r' hr' => Or.inl ⟨hr', by simp [NTm.writes]⟩)
  rw [vr] at N
  have hft2 : π (q + 2) = h + 1 := by simpa [NTm.j, NTm.alen, NTm.a] using hft
  by_cases e : st.x r = 0
  · rw [if_pos e] at N
    have h2 : ((q : Int) + 2).toNat = q + 2 := by omega
    rw [hag.x0, if_pos e, h2] at hrest
    exact ⟨0, (q + 2, st), v, s', Nat.zero_le _, hrest, rn,
      by show NMid X W K A s0 v (π (q + 2)) s'; rw [hft2]; exact N, hag', rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rw [if_neg e] at N
    rw [hag.x0, if_neg e] at hrest
    cases hrest with
    | refl => exact absurd rfl (hz 1 (by omega) (by simp [NTm.j]))
    | head hS2 hs2 hrest2 =>
    simp only [CallProbe.step, c1, Option.some.injEq] at hs2; subst hs2
    have ht : (((q + 1 : Nat) : Int) + off).toNat = NTm.jt q (1 + off) := by unfold NTm.jt; congr 1; push_cast; omega
    have hw : CallProbe.wr st 0 (UInt64.ofNat (st.b + st.lo (q + 1 + 1))) = st := by simp [CallProbe.wr]
    rw [ht, hw] at hrest2
    exact ⟨1, (NTm.jt q (1 + off), st), v, s', by omega, by simpa using hrest2, rn, N, hag', rfl, rfl,
      Or.inr (Or.inl (by simp [NTm.tg]))⟩

end JT
