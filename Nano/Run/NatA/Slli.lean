/- The atom `slli d n sh` ↔ `lsl xd, xn, #sh` (register-exact index scaling of BGET / BSET). -/
import Nano.Run.NatA.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop}

-- for ArmNat
/-- `lsl xd, xn, #sh` -/
theorem n_lslI {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St} {q : Nat} (S : A64SemN M X W)
    (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    {d n sh : Nat} (hA : A[q]? = some (ArmEnc.lslI (armReg d) (armReg n) sh)) (hd : mapped d = true)
    (h0 : d ≠ 0) (hn : mapped n = true) (hn0 : n ≠ 0) (h1 : 0 < sh) (h2 : sh < 64) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (st.x n <<< sh.toUInt64)) (q + 1) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.lslI s _ _ sh hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (armReg_lt hd h0) (armReg_lt hn hn0) h1 h2 (nmid_word hM hA hB)
  rw [hM.x n (by omega) (mapped_lt hn)] at this
  exact nmid_set hM hd h0 this

theorem asim_slli (S : A64SemN M X W) {d x sh : Nat} (hok : (NTm.slli d x sh).ok = true) :
    ASim M X W (NTm.slli d x sh) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, Bool.and_eq_true, mr_iff, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hd, hd0⟩, hx, hx0⟩, h1, h2⟩ := hok
  have c0 : C[q]? = some (.slli d x sh) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  cases hrun with
  | head hS hs hrest =>
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  have vx : v.x x = st.x x := hag.x x (by omega) (mapped_lt hx) (fun hD => by simpa [NTm.reads] using hrd x hD)
  have a0 : A[h]? = some (ArmEnc.lslI (armReg d) (armReg x) sh) := by
    simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
  obtain ⟨s', r, N⟩ := n_lslI S hM hB a0 hd hd0 hx hx0 h1 h2
  refine ⟨0, _, _, s', Nat.zero_le _, hrest, r, by rw [show π (q + 1) = _ from hft]; simpa [NTm.alen, NTm.a] using N,
    (by rw [vx]; exact (agree_wr hag d _).mono (fun r hr => Or.inl ⟨hr.1, by
      simp only [NTm.writes, beq_eq_false_iff_ne]; exact fun e => hr.2 e.symm⟩)),
    CallProbe.wr_b _ _ _, CallProbe.wr_w _ _ _, Or.inl ⟨rfl, rfl⟩⟩

end JT
