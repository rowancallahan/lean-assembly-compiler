import json,re
rows=[l.rstrip('\n').split('\t') for l in open('cg.tsv') if l.strip()]
D={r[1]:r for r in rows if r[0]=='def'}
d=json.load(open('P1.json'))['fail']
# accepted types: (declared name, regex on signature, expression)
TY=[('TOp',r'Proven\.Op\b',None),('TMOp',r'Proven\.Mach\.MOp\b',None),('TCond',r'Proven\.Mach\.Cond\b',None),
('TWOp',r'Proven\.Mach\.WOp\b',None),('TLiStep',r'Proven\.Mach\.Riscv\.LiStep\b',None),('TEOp',r'Proven\.Ir\.EOp\b',None),
('TKd',r'Proven\.Mach\.Ind\.Kd\b',None),('TFld',r'Proven\.Mach\.Ind\.Fld\b',None),
('TTst',r'Proven\.Mach\.IR\.Tst Nat',None),('TArg',r'Proven\.Mach\.IR\.Arg Nat',None),('TIns',r'Proven\.Mach\.IR\.Ins Nat',None),
('TCode',r'Proven\.Mach\.IR\.Code Nat',None),('TIrArg',r'Proven\.Ir\.Arg Nat',None),('TIrInst',r'Proven\.Ir\.Inst Nat',None),
('TIrRhs',r'Proven\.Ir\.Rhs Nat',None),('TIrTerm',r'Proven\.Ir\.Term Nat',None),('TIrBlock',r'Proven\.Ir\.Block Nat',None),
('TSExp',r'Proven\.Mach\.Sel\.SExp\b',None),('TExp',r'Proven\.Exp\b',None),('TAExp',r'Proven\.AExp\b',None),
('TBExp',r'Proven\.Mach\.BExp\b',None),('TMBStmt',r'Proven\.Mach\.BStmt\b',None),('TStr',r'Proven\.Ir\.Val\b',None)]
body=[]
hit=0
for n,msg in sorted(d.items()):
    if n not in D or not re.match(r'frontx: unsupported (result|parameter) type',msg): continue
    sig=D[n][5]
    used=[t for t,p,_ in TY if re.search(p,sig)]
    if not used: continue
    hit+=1
    s=n.replace('Proven.','')
    body.append(f'-- P2 {s}\nfrontx_ind {n} on {used[0]}'+(' using '+' '.join(used[1:]) if len(used)>1 else ''))
print('candidates',hit)
src=open('T2head.lean').read()
types=[f'frontx_ind_type {t} := {e}' for t,e in [('TOp','Proven.Op'),('TMOp','Proven.Mach.MOp'),('TCond','Proven.Mach.Cond'),('TWOp','Proven.Mach.WOp'),('TLiStep','Proven.Mach.Riscv.LiStep'),('TEOp','Proven.Ir.EOp'),('TKd','Proven.Mach.Ind.Kd'),('TFld','Proven.Mach.Ind.Fld'),('TTst','Proven.Mach.IR.Tst Nat'),('TArg','Proven.Mach.IR.Arg Nat'),('TIns','Proven.Mach.IR.Ins Nat'),('TCode','Proven.Mach.IR.Code Nat'),('TIrArg','Proven.Ir.Arg Nat'),('TIrInst','Proven.Ir.Inst Nat'),('TIrRhs','Proven.Ir.Rhs Nat'),('TIrTerm','Proven.Ir.Term Nat'),('TIrBlock','Proven.Ir.Block Nat'),('TSExp','Proven.Mach.Sel.SExp'),('TExp','Proven.Exp'),('TAExp','Proven.AExp'),('TBExp','Proven.Mach.BExp'),('TMBStmt','Proven.Mach.BStmt'),('TStr','Proven.Ir.Val')]]
open('P2.lean','w').write(src+'\n'.join(types)+'\n\n'+'\n'.join(body)+'\n')
