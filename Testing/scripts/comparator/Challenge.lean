/- Held-out statement for `comparator` (trusted).  The proof is left open on purpose. -/
import Riscv.Direct.SortMachine

theorem sortCode_implements_check : Proven.ImplementsMapped Proven.sortCode (fun x => x.mergeSort Proven.leU) :=
  sorry
