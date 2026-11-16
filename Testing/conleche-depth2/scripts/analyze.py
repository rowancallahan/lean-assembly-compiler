import json,re,collections
r=json.load(open('/home/user/scratch/cl2/res.json'))
A=json.load(open('/home/user/scratch/cl2/all.json'))
ix={a['full']:i for i,a in enumerate(A)}
names=sorted(r)
def strip(n): return n.replace('ConLeche.','')
def status(n):
    c=r[n]['compile']; g=r[n]['gate']
    if g.startswith('ERR'): return 'UNRESOLVED',g
    if g.startswith('gate ok; arms ok'): return 'PASS_GATE',g
    if c=='OK': return 'PASS_COMPILE',c
    if g.startswith('gate ok; arms FAIL'): return 'ARMS_FAIL',g.split('arms FAIL: ')[1]
    return 'GATE_FAIL',g.split('gate FAIL: ')[1] if 'gate FAIL: ' in g else g
def klass(msg):
    m=re.sub(r'\s+',' ',msg)
    if 'unsupported parameter type' in m or 'unsupported result type' in m:
        ty=re.split(r'unsupported (?:parameter|result) type ',m)[1]
        ty=re.sub(r'ConLeche\.','',ty)
        if re.search(r'Type → Type|^m |CheckC?M|CoreFns|Except|StateT|Squash|\bm [A-Z(]',ty): return 'monad / higher-kinded (m α, CheckM, CheckCM, Type → Type)'
        if re.search(r'^Name → |→',ty): return 'function-valued parameter (Name → …)'
        if re.search(r'Env|ConstantInfo|ConstantVal|RecRuleFire|CheckError|ProjTable|NestCtx|CheckMode|FEnv|ProjEntry|RecRule',ty) and not re.search(r'^(List|Array|Option) ',ty): return 'multi-field structure / declared type outside shape (Env, FEnv, CheckMode, NestCtx, ConstantInfo, …)'
        if re.search(r'^(List|Array|Option) ',ty): return 'List / Array / Option of a non-Expr type (List Name, Array Expr, Option ConstantInfo, …)'
        return 'other unsupported type: '+ty[:50]
    if 'no argument of a declared type' in m or 'no structural' in m: return 'no argument of a declared (inductive) type (0-ary / Env-only / Level-only)'
    if 'more than one extra parameter' in m: return 'two declared-type parameters besides the structural one'
    if 'more than one scalar' in m: return 'two scalar parameters (only one allowed)'
    if 'type mismatch' in m: return 'type mismatch in the frontx_ind shape (CState field etc.)'
    if 'no equations' in m: return 'no equations (partial / no unfolding)'
    if 'no constructor pattern' in m: return 'body: pattern not on a constructor (Level/Expr literal match, ite, decEq)'
    if 'nested patterns' in m: return 'body: nested patterns not supported'
    if 'unsupported variable' in m: return 'body: unsupported variable (a dropped field)'
    if 'unsupported term' in m: return 'body: unsupported term'
    if 'comparison of an unsupported type' in m: return 'body: == / decEq on an unsupported type (Level, …)'
    if 'a pattern on another argument' in m: return 'body: pattern on a non-structural argument'
    if 'not a constant' in m: return 'body: not a constant'
    if 'recursive call not on a child' in m: return 'body: recursive call not on a child'
    return 'other: '+m[:60]
S={n:status(n) for n in names}
print('== status (1103 names) ==')
print(collections.Counter(S[n][0] for n in names))
top=collections.Counter(S[n][0] for n in names)
first={n:(klass(S[n][1]) if S[n][0] in('GATE_FAIL','ARMS_FAIL') else None) for n in names}
C=collections.Counter(first[n] for n in names if first[n])
print('\n== first-blocker class (direct) ==')
for k,v in C.most_common(): print(v,k)
# transitive: functions whose closure (name edges) contains a function whose own first blocker is class k
rest=[n for n in names if S[n][0] in('GATE_FAIL','ARMS_FAIL')]
bad={n for n in names if S[n][0] in ('GATE_FAIL',)}
def clo(n):
    s=set(); st=[ix[n]]
    while st:
        x=st.pop()
        for y in A[x]['edges']:
            if y not in s: s.add(y); st.append(y)
    return s
json.dump({'S':S,'first':first},open('/home/user/scratch/cl2/analysis.json','w'),indent=1)
for k in ['whnfBody','inferBody','defeqBody','Expr.instantiate1','Cached.checkDecls','checkDecl','whnfLoop','whnfStep','defeqLoop']:
    full='ConLeche.'+k
    if full in r: print('\n##',k,S[full][0],'|',S[full][1][:400])
    else: print('\n##',k,'not in probe list')
