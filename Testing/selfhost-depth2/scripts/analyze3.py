import sys,re,json,collections
sys.path.insert(0,'.')
from fullmsg import full
rows=[l.rstrip('\n').split('\t') for l in open('cg.tsv') if l.strip()]
D={r[1]:r for r in rows if r[0]=='def'}
P1=full('P1.out','P1run.lean'); P2=full('P2.out','P2.lean')
L1={}; L2={}
for i,l in enumerate(open('P1run.lean').read().split('\n'),1):
    if l.startswith('frontx_compile '): L1[i]=l.split()[1]
for i,l in enumerate(open('P2.lean').read().split('\n'),1):
    if l.startswith('frontx_ind '): L2[i]=l.split()[1]
P1f={L1[k]:v for k,v in P1.items() if k in L1}
P2f={L2[k]:v for k,v in P2.items() if k in L2}
P1ok={L1[i] for i in L1 if i not in P1}
P2ok={L2[i] for i in L2 if i not in P2}
GEN=re.compile(r'\.elim$|ctorElim|\.toCtorIdx|inst[A-Z]|instRepr|DecidableEq|decEq|\.repr$|Inhabited|\.raw$|\.default$|\.motive')
def is_gen(n,r):
    return bool(GEN.search(n)) or bool(re.search(r'(^|\s)(Type|Prop|Sort)\b\s*$|→ Type\b|→ Prop\b|Decidable', r[5]))
gen={n for n,r in D.items() if is_gen(n,r)}
prog=[n for n in D if n not in gen]
def feat(msg):
    m=re.search(r'unsupported (?:result|parameter) type (.*)',msg)
    if not m: return 'TRANS'
    t=m.group(1)
    if '→' in t: return 'HO'
    if re.match(r'(Type|Prop|Sort|Decidable|DecidableEq|Repr|Std\.Format|Inhabited)',t) or 'motive' in t: return 'NONCOMP'
    if re.search(r'Proven\.(Ir\.)?(SC|TC|GS|Func|Prog|Frame|Mem|Target|Lay|Env|Block|Inst|Out|Ctx|State|Outcome|Result|Alloc)\b|Mach\.(Wide|WideF|Base|Core|Machine|MachineF|MachineC|Ind\.Pg|Ind\.Cn|Ind\.C)\b|Ir\.Tst|Ir\.Func',t) and not re.search(r'List|Option',t): return 'REC'
    if re.search(r'BitVec (?!64\b)\d+|Fin \d+',t) and '×' not in t and 'List' not in t: return 'BV'
    if '×' in t: return 'TUP'
    if 'List' in t: return 'LIST'
    if re.search(r'Option|Except',t): return 'OPT'
    if re.search(r'\b(ρ|α|σ|β|k\.den|rk\.den)\b|\bNat\b|Proven\.Ir\.VReg',t) and re.search(r'\b(ρ|α|σ|β)\b',t): return 'POLY'
    if 'Proven.' in t: return 'IND'
    return 'OTHER'
final={}
for n in D:
    if n in gen: final[n]='GEN'
    elif n in P2ok or n in P1ok: final[n]='OK'
    else:
        msg=P2f.get(n) or P1f.get(n)
        final[n]=feat(msg) if msg is not None else 'NOMSG'
c=collections.Counter(final[n] for n in prog); print('program defs',len(prog),'OK',c['OK'],dict(c))
ex=collections.defaultdict(list)
for n in prog:
    if final[n] not in('OK',): ex[final[n]].append(n.replace('Proven.',''))
for k in ex: print(k,len(ex[k]),', '.join(ex[k][:4]))
json.dump(final,open('final.json','w'),indent=0)
# closure-based greedy (a node unblocked iff its own class is in S or it is OK/GEN, and all callees unblocked)
ADJ={n:[x for x in D[n][4].split(',') if x in D] for n in D}
def clo(n):
    s={n};st=[n]
    while st:
        x=st.pop()
        for y in ADJ[x]:
            if y not in s: s.add(y); st.append(y)
    return s
CL={n:clo(n) for n in D}
FEATS=['LIST','OPT','BV','TUP','HO','IND','REC','POLY','NONCOMP']
def unblocked(S,n): return all((final[m] in S or final[m] in ('OK','GEN')) for m in CL[n])
def cov(S): return sum(1 for n in prog if unblocked(S,n))
cur=set(); print('\nprogram defs unblocked by feature set (closure):')
print('baseline',cov(cur), 'of', len(prog))
for _ in range(len(FEATS)):
    best=max((f for f in FEATS if f not in cur),key=lambda f:cov(cur|{f}))
    cur.add(best); print('+',best,'->',cov(cur))
irs=[n for n in D if n.endswith('Ir.compile') or n=='Proven.Ir.compile']
print('Ir.compile closure size',len(CL['Proven.Ir.compile']),' blocked nodes:',collections.Counter(final[m] for m in CL['Proven.Ir.compile'] if final[m] not in('OK','GEN')))
print('compileW closure',len(CL['Proven.Ir.compileW']),collections.Counter(final[m] for m in CL['Proven.Ir.compileW'] if final[m] not in('OK','GEN')))
