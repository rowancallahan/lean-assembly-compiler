-- separate files: LoopExamples/ArrExamples (sumProg_wf) and Pipe/Arr2Code (BExp) clash when imported together
import Riscv.Direct.SortMergeMachine
import Riscv.Back.Arr
#print axioms Proven.compileAF_ok
#print axioms Proven.sortCode_implements
#print axioms Proven.msortCode_implements
#print axioms Proven.Mach.Machine.compAF_ok
