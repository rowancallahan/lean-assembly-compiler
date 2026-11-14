import Riscv.Examples.LoopExamples
open LeanRV64D
namespace Proven
/-- book `div n k` (repeated subtraction) over 64-bit words; k = 0 returns q (the book's version needs k>0) -/
def divSub (n k q : BitVec 64) : BitVec 64 :=
  if k = 0 then q else if n < k then q else divSub (n - k) k (q + 1)
termination_by n.toNat
decreasing_by
  have hk : k.toNat ≠ 0 := fun e => ‹¬k = 0› (BitVec.eq_of_toNat_eq (by simpa using e))
  have := ‹¬n < k›; rw [BitVec.lt_def] at this; rw [BitVec.toNat_sub]; omega

open Exp in
/-- a3 := n <u k; while (k ≠ 0 ∧ a3 = 0) do (n := n - k; q := q + 1; a3 := n <u k); a0 := q -/
def divProg : Stmt :=
  .seq (.assign 3 (bin .ult (var 0) (var 1)))
  (.seq (.loop (ite (var 1) (bin .xor (var 3) (const 1)) (const 0))
      (.seq (.assign 0 (bin .sub (var 0) (var 1)))
        (.seq (.assign 2 (bin .add (var 2) (const 1))) (.assign 3 (bin .ult (var 0) (var 1))))))
    (.assign 0 (var 2)))




theorem divProg_exec (σ : Env) : ∃ σ', Exec divProg σ σ' ∧ σ' 0 = divSub (σ 0) (σ 1) (σ 2) := by
  obtain ⟨σ₁, hl, hq⟩ := Exec.loop_inv
    (c := Exp.ite (.var 1) (.bin .xor (.var 3) (.const 1)) (.const 0))
    (b := .seq (.assign 0 (.bin .sub (.var 0) (.var 1)))
        (.seq (.assign 2 (.bin .add (.var 2) (.const 1))) (.assign 3 (.bin .ult (.var 0) (.var 1)))))
    (fun τ => τ 3 = (if τ 0 < τ 1 then 1 else 0) ∧ divSub (τ 0) (τ 1) (τ 2) = divSub (σ 0) (σ 1) (σ 2))
    (fun τ => τ 2 = divSub (σ 0) (σ 1) (σ 2))
    (fun τ => (τ 0).toNat)
    (fun τ hI hc => ⟨_, .seq .assign (.seq .assign .assign), by
      simp only [Exp.denote] at hc
      by_cases h1 : τ 1 = 0
      · simp [h1] at hc
      by_cases hlt : τ 0 < τ 1
      · simp [h1, hI.1, hlt, Op.eval] at hc
      have hk : (τ 1).toNat ≠ 0 := fun e => h1 (BitVec.eq_of_toNat_eq (by simpa using e))
      have hn : ¬ (τ 0).toNat < (τ 1).toNat := fun e => hlt (by rw [BitVec.lt_def]; exact e)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp [Env.set, Exp.denote, Op.eval]
      · rw [← hI.2, divSub.eq_def (τ 0), if_neg h1, if_neg hlt]
        simp [Env.set, Exp.denote, Op.eval]
      · simp [Env.set, Exp.denote, Op.eval, BitVec.toNat_sub]; omega⟩)
    (fun τ hI hc => by
      simp only [Exp.denote] at hc
      rw [← hI.2, divSub.eq_def]
      by_cases h1 : τ 1 = 0
      · simp [h1]
      · by_cases hlt : τ 0 < τ 1
        · simp [h1, hlt]
        · exact absurd (by simpa [hI.1, hlt, Op.eval] using hc) h1)
    (σ.set 3 (if σ 0 < σ 1 then 1 else 0)) ⟨by simp [Env.set], by simp [Env.set]⟩
  refine ⟨_, .seq .assign (.seq hl .assign), ?_⟩
  simp [Env.set, Exp.denote, hq]
end Proven
