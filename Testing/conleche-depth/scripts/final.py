import json,re,collections,sys
sys.path.insert(0,'.')
import reach as R
D=R.D;E=R.edges
meta=json.load(open('F2meta.json')); idx={m[0]:m[3] for m in meta}; info={m[0]:m for m in meta}
fail=json.load(open('Ffail.json'))
L=open('/home/user/lean-assembly-compiler/Testing/conleche-depth/F4.lean').read().split('\n')
l2={i:l.split()[1] for i,l in enumerate(L,1) if l.startswith('frontx_ind ') and ' on ' in l}
ind={};cur=None
for l in open('F4.out'):
    m=re.match(r'.*F4\.lean:(\d+):\d+: error[^:]*: (.*)',l)
    if m:
        cur=int(m.group(1))
        if cur in l2 and l2[cur] not in ind: ind[l2[cur]]=m.group(2)
ACC_I={n for n in l2.values() if n not in ind}
ACC_C={n for n in idx if n not in fail}
ACC=ACC_I|ACC_C
def sig(d):
    b=d['b']; i=b.find(':='); s=b[:i] if i>0 else b[:400]
    return ' '.join(re.split(r'\n\s*\|',s)[0].split())
FEATS=[
 ('Expr (10 ctors, 3+ fields)',r'\bExpr\b'),
 ('Name (String/Nat payload)',r'\bName\b'),
 ('Level',r'\bLevel\b'),
 ('multi-field structure/record (Env, FEnv, ConstantInfo, ...)',r'\b(Env|FEnv|ConstantInfo|ConstantVal|InductiveVal|RecursorVal|ConstructorVal|ProjTable|ProjEntry|RecRule\w*|BlockShape|NestCtx|NestState|Declaration|PropWhen|WhnfStep|DeltaStep|CheckError|CheckMode|\w*Shape|\w*Ctx|\w*State|\w*Info|\w*Val)\b'),
 ('state monad / Except / [Monad m] (CheckM, CheckCM, CoreFns m)',r'CheckC?M\b|CheckCM|CoreFns|StateT|ExceptT|\bm [A-Z(α]|→ m |: m |\[Monad'),
 ('HashMap/HashSet/CState caches',r'HashMap|HashSet|CState|Memo|PKey'),
 ('List of non-bytes',r'\bList\b'),
 ('Array of heap objects',r'\bArray\b'),
 ('Option of heap object',r'Option'),
 ('String/Char',r'\bString\b|\bChar\b|Substring'),
 ('higher-order arg (fn-typed param)',r'\((?:\w+ )+: [^()]*→[^()]*\)'),
 ('type-class / universe / dependent args ([inst], Type, Decidable, a = b)',r'\[[A-Z]\w*[^\]]*\]|: Type|\bDecidable\b|\bα\b|\bβ\b|\bPrefix\b'),
 ('Int',r'\bInt\b'),
]
def feats(n):
    d=D[idx[n]]; s=sig(d); out=set()
    for k,p in FEATS:
        if re.search(p,s): out.add(k)
    if not re.search(r'→|\(',s.split(':')[0]) and ':=' in d['b'] and not out: pass
    return out
nullary=lambda n: 'introN' in fail.get(n,'')
S={n:feats(n) for n in idx}
for n in idx:
    if nullary(n): S[n].add('nullary constant (0-ary def)')
# body features (reading)
BODY=[('WF / termination_by','termination_by|decreasing_by'),('mutual / fuel','\\bfuel\\b|Fuel'),('mixHash / pointer-eq primitives','mixHash|withPtrEq|ptrEq|ptrAddr|isExclusive'),('big Nat ops (div/mod/gcd/pow/shift/land)','Nat\\.(div|mod|gcd|pow|shiftLeft|shiftRight|land|lor|xor)|\\^|\\bgcd\\b'),('for/while loops in do','\\bfor\\b.*\\bin\\b|\\bwhile\\b')]
B={n:{k for k,p in BODY if re.search(p,D[idx[n]]['b'])} for n in idx}
# first-failure message class
def first(n):
    if n in ACC: return None
    m=ind.get(n) or fail[n]
    return re.sub(r'ConLeche\.(Cached\.)?','',m)[:110]
json.dump({'S':{n:sorted(v) for n,v in S.items()},'B':{n:sorted(v) for n,v in B.items()},'first':{n:first(n) for n in idx},'acc':sorted(ACC)},open('final.json','w'))
N=len(idx); print(N,'functions probed;',len(ACC),'accepted:',sorted(a.replace('ConLeche.','') for a in ACC))
cF=collections.Counter(); 
for n in idx:
    for f in S[n]: cF[f]+=1
print('\nfunctions whose SIGNATURE mentions feature (reading):'); 
for k,v in cF.most_common(): print(f'{v:5d} {k}')
cB=collections.Counter(f for n in idx for f in B[n]); print('\nbody features:',cB.most_common())
# callee closure (transitive) on the over-approximate edge set
P={idx[n]:n for n in idx}
adj={n:[P[j] for j in E[idx[n]] if j in P] for n in idx}
def clo(n):
    s={n};st=[n]
    while st:
        x=st.pop()
        for y in adj[x]:
            if y not in s:s.add(y);st.append(y)
    return s
C={n:clo(n) for n in idx}
print('\n#blocked directly vs transitive (signature features):')
direct=collections.Counter(); trans=collections.Counter()
for k in cF:
    d=[n for n in idx if k in S[n] and n not in ACC]; direct[k]=len(d)
    trans[k]=sum(1 for n in idx if any(k in S[m] and m not in ACC for m in C[n]))
for k in sorted(cF,key=lambda k:-trans[k]):
    ex=sorted([n for n in idx if k in S[n]],key=lambda n:-D[idx[n]]['loc'])[:2]
    print(f'{direct[k]:5d} {trans[k]:5d} {k} | '+'; '.join(f"{e.replace('ConLeche.','')} {info[e][1]}:{info[e][2]}" for e in ex))
# greedy cover on signature features
allf=list(cF); cur=set()
def unb(Sset,closure=True): return sum(1 for n in idx if all((S[m]<=Sset) for m in (C[n] if closure else {n})))
print('\ngreedy (functions with all signature features available, own closure / alone):')
for _ in range(9):
    best=max((f for f in allf if f not in cur),key=lambda f:(unb(cur|{f}),unb(cur|{f},False)))
    cur.add(best); print(unb(cur),unb(cur,False),'+',best)
