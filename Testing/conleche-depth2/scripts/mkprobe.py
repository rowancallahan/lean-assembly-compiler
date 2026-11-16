# Build the depth-2 probe: header + verbatim con-leche (F2.lean.txt) + TExpr declaration + per-function probes.
# Name list = the 1103 names of the first probe (out/final.json 'first' keys); unresolved names fail in Lean.
import json,sys
F2=open('/home/user/scratch/cl/F2.lean.txt').read().split('\n')
names=sorted(json.load(open('/home/user/scratch/cl2/orig_final.json'))['first'])
hdr=['import Riscv.Frontx.Machine','import Riscv.Frontx.IndCmd','import Riscv.Frontx.IndGate']
assert F2[0]=='import Riscv.Frontx.Machine' and F2[1]=='import Riscv.Frontx.IndCmd'
cut=F2.index('-- ===== probes =====')  # the branch file carries the first probe's own probe section: drop it
body=F2[2:cut]
decl=['','-- ===== depth-2 declarations =====',
 'frontx_ind_type TExpr := ConLeche.Expr nesting ConLeche.Level, ConLeche.Name, List ConLeche.Level, ConLeche.Literal, List ConLeche.Expr, Option ConLeche.Expr','']
out=hdr+body+decl
meta=[]
for n in names:
    out.append(f'frontx_compile {n}'); meta.append((len(out),n,'compile'))
    out.append(f'frontx_ind_gate {n} on TExpr'); meta.append((len(out),n,'gate'))
open('/home/user/lean-assembly-compiler/Testing/conleche-depth2/out/F2P.lean','w').write('\n'.join(out)+'\n')
json.dump(meta,open('/home/user/scratch/cl2/meta.json','w'))
print(len(names),'names;',len(meta),'probe commands; file lines',len(out))
