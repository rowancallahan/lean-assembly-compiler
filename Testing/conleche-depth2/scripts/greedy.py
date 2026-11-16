import json,re,collections,sys
sys.path.insert(0,'/home/user/scratch/cl2')
import index as I
r=json.load(open('/home/user/scratch/cl2/res.json'))
an=json.load(open('/home/user/scratch/cl2/analysis.json'))
S=an['S']
D={d['full']:d for d in I.D}
names=sorted(r)
def sig(d):
    b=d['b']; i=b.find(':='); s=b[:i] if i>0 else b[:400]
    return ' '.join(re.split(r'\n\s*\|',s)[0].split())
FEAT={
 'monad / m α / CheckM / CheckCM / CoreFns (Type → Type)': r'Type → Type|\bm [A-Z(α]|→ m |: m |CheckC?M|CoreFns|StateT|ExceptT|Except|\[Monad|Squash',
 'multi-field structure outside the family (Env, FEnv, ConstantInfo, ProjTable, CheckMode, NestCtx, …)': r'\b(Env|FEnv|ConstantInfo|ConstantVal|InductiveVal|RecursorVal|ConstructorVal|ProjTable|ProjEntry|RecRule\w*|BlockShape|NestCtx|NestState|Declaration|PropWhen|CheckError|CheckMode|DeltaStep|WhnfStep|NatOpPinSet|ClassGen|ClassKey|FBase|TargetMajor|CState|\w+Shape)\b',
 'List / Array / Option of a non-Expr element (List Name, Array Expr, Option ConstantInfo)': r'\b(List|Array|Option) (?!Expr\b|Level\b|Name\b|Literal\b)[A-Z(]',
 'function-valued parameter (Name → …, Expr → m Expr)': r'\((?:\w+ )+: [^()]*→[^()]*\)',
 'HashMap / HashSet / memo state': r'HashMap|HashSet|Memo|BeqMap|BeqSt',
 'Int': r'\bInt\b',
 'String / Char': r'\bString\b|\bChar\b',
 'nullary constant (0-ary def)': r'^$',
}
def feats(n):
    d=D[n]; s=sig(d); out=set()
    for k,p in FEAT.items():
        if p=='^$': continue
        if re.search(p,s): out.add(k)
    if r[n]['compile'].startswith('ERR: frontx: no') and False: pass
    return out
F={n:feats(n) for n in names if n in D}
for n in names:
    if n in F and n in D and D[n]['b'].strip().find(':=')>=0:
        pass
# nullary: no parameters in the signature text before ':'
for n in list(F):
    s=sig(D[n]); head=s.split(':',1)[0] if ':' in s else s
    body_params=re.findall(r'\(\s*\w+(?:\s+\w+)*\s*:',s)
    if not body_params and not re.search(r'^[^:]*→',s.split(':=')[0]) and (' : ' in s):
        F[n].add('nullary constant (0-ary def)')
K=list(FEAT)
def covered(chosen):
    return {n for n in F if F[n]<=chosen or S[n][0]=='PASS_GATE'}
print('functions probed in D:',len(F),'of',len(names))
chosen=set(); seq=[]
allfeat=set().union(*F.values())
for step in range(len(allfeat)):
    best=None
    for k in allfeat-chosen:
        c=len(covered(chosen|{k}))
        if best is None or c>best[0]: best=(c,k)
    chosen.add(best[1]); seq.append((best[1],best[0]))
    print(step+1,best[0],'+',best[1])
print('\nper-feature: functions whose signature mentions it, and its direct first-blocker counts')
for k in K:
    m=[n for n in F if k in F[n]]
    print(len(m),k)
json.dump({'seq':seq,'F':{n:sorted(v) for n,v in F.items()}},open('/home/user/scratch/cl2/greedy.json','w'),indent=1)
