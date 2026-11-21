/- T10 (M3 round 2): the atoms `jal rd off` (`rd = 0`: `b`; `rd = 1`: `bl`) and `jalr rs` (`br`). -/
import Nano.Run.NatA.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop}

theorem asim_jal (S : A64SemN M X W) {rd : Nat} {off : Int} (hok : (NTm.jal rd off).ok = true) :
    ASim M X W (NTm.jal rd off) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, decide_eq_true_eq] at hok
  have c0 : C[q]? = some (.jal rd off) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  cases hrun with
  | head hS hs hrest =>
  simp only [SafeX, c0] at hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  have ht : π (NTm.jt q off) ≤ A.length := htg _ (by simp [NTm.tg])
  have hL25 : A.length < 2 ^ 25 := by omega
  have hmem : (((q : Int) + off).toNat) ∈ (NTm.jal rd off).tg q := by simp [NTm.tg, NTm.jt]
  rcases hok with rfl | rfl
  · have a0 : A[h]? = some (ArmEnc.bB ((π (NTm.jt q off) : Int) - (h : Int))) := by
      simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
    obtain ⟨s', r, N⟩ := n_b S hM hB a0 ht hL25
    have e : ∀ x, CallProbe.wr st 0 x = st := fun x => if_pos rfl
    rw [e] at hrest
    exact ⟨0, _, v, s', Nat.zero_le _, hrest, r, N,
      hag.mono (fun r hr => Or.inl ⟨hr, rfl⟩), rfl, rfl, Or.inr (Or.inl hmem)⟩
  · have a0 : A[h]? = some (ArmEnc.blB ((π (NTm.jt q off) : Int) - (h : Int))) := by
      simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
    obtain ⟨s', r, N⟩ := n_bl S hM hB a0 ht hL25
    have hlo' : st.lo (q + 1) = 4 * (h + 1) := by simpa [NTm.j, NTm.alen, NTm.a] using hlo rfl
    have el : UInt64.ofNat (st.b + st.lo (q + 1)) = UInt64.ofNat (K.base + 4 * (h + 1)) := by rw [hb, hlo']
    rw [el] at hrest
    exact ⟨0, _, _, s', Nat.zero_le _, hrest, r, N,
      (agree_wr hag 1 _).mono (fun r hr => Or.inl ⟨hr.1, rfl⟩),
      CallProbe.wr_b _ _ _, CallProbe.wr_w _ _ _, Or.inr (Or.inl hmem)⟩

theorem asim_jalr (S : A64SemN M X W) {rs : Nat} (hok : (NTm.jalr rs).ok = true) :
    ASim M X W (NTm.jalr rs) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, decide_eq_true_eq] at hok
  have hm : mapped rs = true := by rcases hok with rfl | rfl <;> decide
  have hn0 : rs ≠ 0 := by omega
  have c0 : C[q]? = some (.jalr 0 rs) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  cases hrun with
  | head hS hs hrest =>
  simp only [SafeX, c0] at hS
  obtain ⟨-, -, j, hj⟩ := hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  have e : ∀ x, CallProbe.wr st 0 x = st := fun x => if_pos rfl
  rw [e] at hrest
  have hj' : st.ly.un ((st.x rs).toNat - st.b) = j := by
    rw [hj, hb, Nat.add_sub_cancel_left]; exact st.ly.inv j
  have hlt : st.lo j < 2 ^ 64 := by have := (st.x rs).toNat_lt; omega
  obtain ⟨hl1, -⟩ := hlk j hlt
  have vx : v.x rs = st.x rs := hag.x rs (by omega) (mapped_lt hm) (fun hD => by simpa [NTm.reads] using hrd rs hD)
  have hv : v.x rs = UInt64.ofNat (K.base + 4 * π j) := by
    rw [vx]; apply UInt64.toNat_inj.1
    have := (st.x rs).toNat_lt
    rw [UInt64.toNat_ofNat']; omega
  have a0 : A[h]? = some (ArmEnc.brR (armReg rs)) := by
    simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
  obtain ⟨s', r, N⟩ := n_br S hM hB a0 hm hn0 hv
  exact ⟨0, _, v, s', Nat.zero_le _, hrest, r, by dsimp only; rw [hj']; exact N,
    hag.mono (fun r hr => Or.inl ⟨hr, rfl⟩), rfl, rfl, Or.inr (Or.inr (by dsimp only; rw [hj']; exact hlt))⟩

end JT
