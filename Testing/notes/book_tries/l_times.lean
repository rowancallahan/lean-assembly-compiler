import Riscv.Examples.LoopExamples
open LeanRV64D
namespace Proven
/-- book `times n k` (recursion on k) as tail recursion over 64-bit words -/
def timesDown (n k acc : BitVec 64) : BitVec 64 := if k = 0 then acc else timesDown n (k - 1) (acc + n)
termination_by k.toNat
decreasing_by exact sub_one_lt ‹_›

open Exp in
/-- `while a1 ≠ 0 do (a2 := a2 + a0; a1 := a1 - 1); a0 := a2` -/
def timesProg : Stmt :=
  .seq (.loop (var 1) (.seq (.assign 2 (bin .add (var 2) (var 0))) (.assign 1 (bin .sub (var 1) (const 1)))))
    (.assign 0 (var 2))

theorem timesProg_exec (σ : Env) : ∃ σ', Exec timesProg σ σ' ∧ σ' 0 = timesDown (σ 0) (σ 1) (σ 2) := by
  obtain ⟨σ₁, hl, hq⟩ := Exec.loop_inv (c := .var 1)
    (b := .seq (.assign 2 (.bin .add (.var 2) (.var 0))) (.assign 1 (.bin .sub (.var 1) (.const 1))))
    (fun τ => τ 0 = σ 0 ∧ timesDown (τ 0) (τ 1) (τ 2) = timesDown (σ 0) (σ 1) (σ 2)) (fun τ => τ 2 = timesDown (σ 0) (σ 1) (σ 2))
    (fun τ => (τ 1).toNat)
    (fun τ hI hc => ⟨_, .seq .assign .assign, by
      simp only [Exp.denote] at hc
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [Env.set] using hI.1
      · rw [← hI.2, timesDown.eq_def (τ 0), if_neg hc]; simp [Env.set, Exp.denote, Op.eval]
      · simp [Env.set, Exp.denote, Op.eval]; exact sub_one_lt hc⟩)
    (fun τ hI hc => by
      simp only [Exp.denote] at hc
      rw [← hI.2, timesDown.eq_def, if_pos hc])
    σ ⟨rfl, rfl⟩
  exact ⟨_, .seq hl .assign, by simp [Env.set, Exp.denote, hq]⟩

/-- the 64-bit loop computes the product mod 2^64 (so the book's `times` while n*k < 2^64) -/
theorem timesDown_eq' : ∀ (m : Nat) (n k acc : BitVec 64), k.toNat = m → timesDown n k acc = acc + n * k := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro n k acc h
    rw [timesDown.eq_def]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, ih (k - 1).toNat (by rw [← h]; exact sub_one_lt hk) n (k - 1) (acc + n) rfl]
      have h1 : n * k = n * (k - 1 + 1) := by rw [BitVec.sub_add_cancel]
      rw [h1, BitVec.mul_add, show n * (1 : BitVec 64) = n from by simp, BitVec.add_assoc, BitVec.add_comm n]

theorem timesDown_eq (n k acc : BitVec 64) : timesDown n k acc = acc + n * k := timesDown_eq' _ n k acc rfl

theorem timesProg_wf : timesProg.wf := by simp only [timesProg, Stmt.wf]; decide +kernel

theorem times_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileF timesProg)) (hok : codeOK pc (compileF timesProg).length)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      getX s' 10 = timesDown (getX s 10) (getX s 11) (getX s 12) ∧ Cfg s' ∧ s'.mem = s.mem ∧ calleeSavedKept s s' := by
  obtain ⟨σ', hex, hv⟩ := timesProg_exec (fun i => getX s (A i))
  exact runsTo_mono (compileF_ok timesProg_wf hex h hpc hc hok hra) fun s' ⟨h1, h2, h3⟩ =>
    ⟨h1, (h2 0).trans hv, h3⟩
end Proven
