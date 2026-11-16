import sys
rows=[l.rstrip('\n').split('\t') for l in open('cg.tsv') if l.strip()]
names=[r[1] for r in rows if r[0]=='def']
out=['import Riscv.Frontx.Translate','import Riscv.Frontx.IndCmd','import Riscv.Frontx.WaCmd','import Riscv.Back.Top','import Riscv.Back.IrTop','import Riscv.Back.Wide','import Compiler.Ir.Emit','import Compiler.Ir.IndLow','import Compiler.Opt.Sel','import Spec.Code','set_option maxHeartbeats 400000','set_option linter.all false','open Proven.Frontx','']
for n in names: out.append(f'-- P {n}\nfrontx_compile {n}')
open('P1.lean','w').write('\n'.join(out)+'\n'); print(len(names))
