/- Safe retrofit, part 1 (Opus box A): the leaf template runs as SAFE runs (`SimW.SStar`), so the Sail lift
`SimW.sim_starW` applies.  Spec: for each leaf run lemma `X_run` (Expr / Heap / Call / CallA / Templates) a twin
`X_srun` with the same hypotheses plus exactly the `SimW.Safe` side conditions of the instructions it executes:
  * addi: the sum does not wrap (follows from the run lemma's own bounds where it can);
  * ld / sd: the effective address is a work cell (`wok K a`: lo ≤ a, a + 8 ≤ hi, 8-aligned);
  * lbu: the aligned cell containing the byte is a work cell (input bytes live in the work region);
  * jal: the target is inside the code (< |C|);  jalr: the target is base + 4j;
  * registers < 32, branch offsets 2, ALU op 1..8 with rd ≠ 0 (structural, discharged here).
Tool: `sstar_of_run` — a deterministic run whose every intermediate state is `Safe` is an `SStar`. -/
import Nano.V2Self.Proof.SimW
import Nano.V2Self.Proof.Expr
namespace SafeRun
open CallProbe SimW

theorem SStar.trans {K : LayW} {C : List J} {a b c : Nat × St} (h1 : SStar K C a b) (h2 : SStar K C b c) : SStar K C a c := by
  induction h1 with
  | refl => exact h2
  | head hs st _ ih => exact .head hs st (ih h2)

theorem SStar.one {K : LayW} {C : List J} {a b : Nat × St} (hs : Safe K C a) (st : step C a = some b) : SStar K C a b :=
  .head hs st (.refl b)

/-- a deterministic run whose every intermediate state is safe -/
theorem sstar_of_run {K : LayW} {C : List J} : ∀ {k : Nat} {a b : Nat × St}, run C k a = some b →
    (∀ j, j < k → ∀ c, run C j a = some c → Safe K C c) → SStar K C a b
  | 0, a, b, h, _ => by simp [run] at h; subst h; exact .refl _
  | k + 1, a, b, h, hs => by
    simp only [run] at h
    cases e : step C a with
    | none => simp [e] at h
    | some c =>
      simp [e] at h
      refine .head (hs 0 (by omega) a rfl) e (sstar_of_run h fun j hj d hd => hs (j + 1) (by omega) d ?_)
      simp [run, e, hd]

theorem SStar.star {K : LayW} {C : List J} {a b : Nat × St} (h : SStar K C a b) : Star C a b := by
  induction h with
  | refl => exact .refl _
  | head _ st _ ih => exact (Star.one st).trans ih

/-! ## push -/

theorem push_srun {K : LayW} {C pc s r oom} (hC : At C pc (push r oom)) (hr : r ≠ 31) (hr0 : r ≠ 0) (hr32 : r < 32)
    (hh : (s.x 30).toNat + 8 ≤ (s.x 31).toNat) (hw : wok K ((s.x 31).toNat - 8)) :
    SStar K C (pc, s) (pc + 4, ⟨upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8)),
                                 upd s.m ((s.x 31).toNat - 8) (s.x r), s.b⟩) := by
  refine sstar_of_run (push_run hC hr hr0 hh) fun j hj c hc => ?_
  have h0 := hC.at 0 (by simp [push]); have h1 := hC.at 1 (by simp [push])
  have h3 := hC.at 3 (by simp [push])
  simp only [push, Nat.add_zero] at h0 h1 h3
  simp at h0 h1 h3
  have lt : (s.x 31).toNat < 2 ^ 64 := (s.x 31).toNat_lt
  have e : ea (s.x 31) (-8) = (s.x 31).toNat - 8 := by simp [ea]; omega
  have t6' : (UInt64.ofNat ((s.x 31).toNat - 8)).toNat = (s.x 31).toNat - 8 := by simp [UInt64.toNat_ofNat]; omega
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · simp [run] at hc; subst hc; simp [Safe, h0]; omega
  · simp [run, step, h0] at hc; subst hc; simp [Safe, h1]
  · have c2 : (s.x 30).toNat ≤ (s.x 31).toNat - 8 := by omega
    simp [run, step, h0, h1, wr, e, upd_same, upd_other _ _ (show (30:Nat) ≠ 31 by decide), t6', c2,
      show ((pc : Int) + 1 + 2).toNat = pc + 3 by omega] at hc
    subst hc
    simp [Safe, h3, hr32, ea, upd_same, t6']; exact hw

theorem len_srun {K : LayW} {C pc tgt} (s : St) (hC : At C pc (lenT tgt pc)) (hh : (s.x 30).toNat + 8 ≤ (s.x 31).toNat)
    (hw : wok K ((s.x 31).toNat - 8)) :
    SStar K C (pc, s) (pc + 4, ⟨upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8)), upd s.m ((s.x 31).toNat - 8) (s.x 29), s.b⟩) :=
  push_srun (by simpa [lenT, pushA] using hC) (by decide) (by decide) (by decide) hh hw

/-! ## BIN -/

theorem bin_srun {K : LayW} {C pc op} (s : St) (hC : At C pc (binT op)) (hlt : (s.x 31).toNat + 16 < 2 ^ 63)
    (hop : 1 ≤ op ∧ op ≤ 8) (w0 : wok K (s.x 31).toNat) (w8 : wok K ((s.x 31).toNat + 8)) :
    SStar K C (pc, s) (pc + 5,
      ⟨upd (upd (upd (upd s.x 6 (s.m (s.x 31).toNat)) 5 (s.m ((s.x 31).toNat + 8))) 31 (UInt64.ofNat ((s.x 31).toNat + 8))) 5
          (aluf op (s.m ((s.x 31).toNat + 8)) (s.m (s.x 31).toNat)),
       upd s.m ((s.x 31).toNat + 8) (aluf op (s.m ((s.x 31).toNat + 8)) (s.m (s.x 31).toNat)), s.b⟩) := by
  refine sstar_of_run (bin_run s hC hlt) fun j hj c hc => ?_
  have h0 := hC.at 0 (by simp [binT]); have h1 := hC.at 1 (by simp [binT]); have h2 := hC.at 2 (by simp [binT])
  have h3 := hC.at 3 (by simp [binT]); have h4 := hC.at 4 (by simp [binT])
  simp [binT] at h0 h1 h2 h3 h4
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e8 : ea (s.x 31) 8 = (s.x 31).toNat + 8 := by simp [ea]; omega
  have t8' : (s.x 31 + 8).toNat = (s.x 31).toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have e8'' : ea (s.x 31 + 8) 0 = (s.x 31).toNat + 8 := by simp only [ea, t8']; omega
  have t8 : (UInt64.ofNat ((s.x 31).toNat + 8)).toNat = (s.x 31).toNat + 8 := by simp only [UInt64.toNat_ofNat']; omega
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl
  · simp [run] at hc; subst hc; simp [Safe, h0, e0]; exact w0
  · simp [run, step, h0, wr, upd_other _ _ (show (31:Nat) ≠ 6 by decide)] at hc; subst hc
    simp [Safe, h1, upd_other _ _ (show (31:Nat) ≠ 6 by decide), e8]; exact ⟨by omega, w8⟩
  · simp [run, step, h0, h1, wr, upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide)] at hc
    subst hc
    simp [Safe, h2, upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide)]; omega
  · simp [run, step, h0, h1, h2, wr] at hc; subst hc; simp [Safe, h3]; omega
  · simp [run, step, h0, h1, h2, h3, wr, e0, e8, upd_same, upd_other _ _ (show (31:Nat) ≠ 6 by decide),
      upd_other _ _ (show (31:Nat) ≠ 5 by decide)] at hc
    subst hc
    simp [Safe, h4, upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_same, ea, t8]
    refine ⟨by omega, ?_⟩
    have : ((((s.x 31).toNat : Int) + 8) % 18446744073709551616).toNat = (s.x 31).toNat + 8 := by omega
    rw [this]; exact w8

/-! ## BSIZE -/

theorem bsize_srun {K : LayW} {C pc} (s : St) (hC : At C pc bsizeT) (w0 : wok K (s.x 31).toNat)
    (w1 : wok K (s.m (s.x 31).toNat).toNat) :
    SStar K C (pc, s) (pc + 3, ⟨upd s.x 5 (s.m (s.m (s.x 31).toNat).toNat), upd s.m (s.x 31).toNat (s.m (s.m (s.x 31).toNat).toNat), s.b⟩) := by
  refine sstar_of_run (bsize_run s hC) fun j hj c hc => ?_
  have h0 := hC.at 0 (by simp [bsizeT]); have h1 := hC.at 1 (by simp [bsizeT]); have h2 := hC.at 2 (by simp [bsizeT])
  simp [bsizeT] at h0 h1 h2
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · simp [run] at hc; subst hc; simp [Safe, h0, ea]; exact w0
  · simp [run, step, h0, wr] at hc; subst hc; simp [Safe, h1, ea, upd_same]; exact w1
  · simp [run, step, h0, h1, wr, upd_same] at hc; subst hc
    simp [Safe, h2, ea, upd_other _ _ (show (31:Nat) ≠ 5 by decide)]; exact w0

end SafeRun
