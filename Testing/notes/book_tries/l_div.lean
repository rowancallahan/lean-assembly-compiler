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


end Proven
