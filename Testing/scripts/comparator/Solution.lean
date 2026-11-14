/- The solution: the same statement, proved by the project theorem. -/
import Riscv.Direct.SortMachine

theorem sortCode_implements_check : Proven.ImplementsMapped Proven.sortCode (fun x => x.mergeSort Proven.leU) :=
  Proven.sortCode_implements
