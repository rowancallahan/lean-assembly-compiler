/- T02: the `addi` atom with a nonzero source register (`add` / `sub` immediate; `n = 0` is `li`, T01). -/
import Nano.Run.NatA.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop}

theorem asim_addi_nz (S : A64SemN M X W) {d n : Nat} {imm : Int} (hok : (NTm.addi d n imm).ok = true) (hn0 : n ≠ 0) :
    ASim M X W (NTm.addi d n imm) := by
  intro K C A s0 s v st z m π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, Bool.and_eq_true, mr_iff, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hd, hd0⟩, hn⟩, hi⟩, -⟩ := hok
  have c0 : C[q]? = some (.addi d n imm) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  cases hrun with
  | head hS hs hrest =>
  simp only [SafeX, c0] at hS
  obtain ⟨-, -, h1, h2, h3, h4⟩ := hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  have vn : v.x n = st.x n := hag.x n (by omega) (mapped_lt hn) (fun hD => by simpa [NTm.reads] using hrd n hD)
  have hl : (NTm.addi d n imm).alen = 1 := by
    by_cases him : imm < 0 <;> simp [NTm.alen, NTm.a, hn0, him]
  have hagr : Agree (outD (NTm.addi d n imm) D) (CallProbe.wr v d (UInt64.ofNat (CallProbe.ea (st.x n) imm)))
      (CallProbe.wr st d (UInt64.ofNat (CallProbe.ea (st.x n) imm))) :=
    (agree_wr hag d (UInt64.ofNat (CallProbe.ea (st.x n) imm))).mono (fun r' hr' => Or.inl ⟨hr'.1, by
    simp only [NTm.writes, beq_eq_false_iff_ne]; exact fun e => hr'.2 e.symm⟩)
  by_cases him : imm < 0
  · have a0 : A[h]? = some (ArmEnc.subi (armReg d) (armReg n) imm.natAbs) := by
      have := hA 0 (by rw [hl]; omega); simpa [NTm.a, hn0, him] using this
    obtain ⟨s', r, N⟩ := n_subi S hM hB a0 hd hd0 hn hn0 (by omega)
    have e : st.x n - UInt64.ofNat imm.natAbs = UInt64.ofNat (CallProbe.ea (st.x n) imm) := by
      apply UInt64.toNat_inj.1
      have := UInt64.toNat_lt (st.x n)
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_ofNat_lt (by omega)]; unfold CallProbe.ea at *; omega),
        toNat_ofNat_lt (by omega), toNat_ofNat_lt (by unfold CallProbe.ea; omega)]
      unfold CallProbe.ea; omega
    rw [vn, e] at N
    exact ⟨0, _, _, s', Nat.zero_le _, hrest, r, by rw [show π (q + 1) = _ from hft, hl]; exact N, hagr,
      CallProbe.wr_b _ _ _, CallProbe.wr_w _ _ _, Or.inl ⟨rfl, rfl⟩⟩
  · have a0 : A[h]? = some (ArmEnc.addi (armReg d) (armReg n) imm.toNat) := by
      have := hA 0 (by rw [hl]; omega); simpa [NTm.a, hn0, him] using this
    obtain ⟨s', r, N⟩ := n_addi S hM hB a0 hd hd0 hn hn0 (by omega)
    have e : st.x n + UInt64.ofNat imm.toNat = UInt64.ofNat (CallProbe.ea (st.x n) imm) := by
      apply UInt64.toNat_inj.1
      rw [UInt64.toNat_add, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by unfold CallProbe.ea; omega)]
      unfold CallProbe.ea; omega
    rw [vn, e] at N
    exact ⟨0, _, _, s', Nat.zero_le _, hrest, r, by rw [show π (q + 1) = _ from hft, hl]; exact N, hagr,
      CallProbe.wr_b _ _ _, CallProbe.wr_w _ _ _, Or.inl ⟨rfl, rfl⟩⟩

end JT
