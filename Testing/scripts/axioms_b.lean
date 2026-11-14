-- separate files: LoopExamples/ArrExamples (sumProg_wf) and Pipe/Arr2Code (BExp) clash when imported together
import Riscv.Direct.SortMergeMachine
import Riscv.Back.Arr
import Riscv.Steps.GenUse
#print axioms Proven.compileAF_ok
#print axioms Proven.sortCode_implements
#print axioms Proven.msortCode_implements
#print axioms Proven.Mach.Machine.compAF_ok
#print axioms Proven.G.step_add
#print axioms Proven.G.step_srai
#print axioms Proven.G.step_lui
#print axioms Proven.G.beq_t
#print axioms Proven.G.step_jalr
#print axioms Proven.G.step_ld
#print axioms Proven.G.step_sw
#print axioms Proven.G.law_mov_any
