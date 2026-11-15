import json,re,collections,glob,sys
r=json.load(open('res.json'));g=json.load(open('g.json'));G,L,T,seen=g['G'],g['L'],g['T'],g['seen']
# merge single reruns
for nf in glob.glob('one/o*.name'):
    n=open(nf).read()
    import os
    p=nf[:-5]+'.out'
    out=open(p,errors='replace').read() if os.path.exists(p) else 'EXIT 137'
    if 'EXIT' not in out: out+='EXIT 137'
    m=re.search(r'error: (.*)',out)
    if 'EXIT 137' in out or 'EXIT 124' in out: r[n]=('FAIL','RESOURCE: '+('killed (memory)' if '137' in out else 'timeout 240 s'))
    elif m:
        i=out.index(m.group(0)); r[n]=('FAIL',re.sub(r'\s+',' ',out[i+7:i+260].split('PANIC')[0]))
    elif re.search(r'frontx: \S+: \d+ variables',out): r[n]=('OK','')
    else: r[n]=('NOOUT','')
def feat(msg):
    m=msg
    if m.startswith('RESOURCE'): return 'resource: memory/time in the front end'
    t=re.search(r'unsupported (parameter|result) type (.*)',m)
    if t:
        ty=t.group(2); side=t.group(1)
        if re.search(r'Float',ty): return 'Float'
        if re.search(r'\bM\b |Except|StateM|Id ',ty) and not ty.startswith('Option'): return 'monadic type (Shape.M / StateM / Except result)'
        if 'Format' in ty or 'String' in ty or 'Char' in ty: return 'String / Std.Format / Char'
        if '→' in ty: return 'function-typed value (closure)'
        if re.search(r'\bInt\b|Fx|Mat\b|Pt\b',ty) and not re.search(r'LeanSvg\.(?!Fx|Mat|Pt)\w',ty) and 'Array' not in ty: return 'Int / Fx scalar (also Int tuples, Option Int)'
        if 'Array' in ty: return 'Array (of scalars, tuples or structures) as value'
        if 'ByteArray' in ty: return 'ByteArray as a result (or inside Option/tuple)'
        if ty.startswith('Option'): return 'Option of structure / tuple'
        if ' × ' in ty or 'Prod' in ty: return 'tuple result'
        return 'user structure / inductive as parameter or result'
    if 'no unfolding equation' in m or 'unknown free variable' in m or 'failed to generate equality' in m: return 'structure ctor / field projection / instance (user structure values)'
    if 'instHMul' in m or re.search(r'translated by one cond',m) and '*' in m: return 'variable x variable `*` (Nat), nonlinear bound'
    if 'instHDiv' in m or 'instHMod' in m: return '`/` `%` by a variable or non-2^k expression'
    if 'translated by one cond' in m: return '`/` `%` by a non-2^k constant (side condition not discharged)'
    if 'could not prove' in m or 'No goals' in m: return 'step proof fails (front-end limit; e.g. u8/shift facts)'
    if 'simp' in m or 'whnf' in m or 'heartbeats' in m or 'recursion depth' in m or 'maximum' in m: return 'resource: simp/whnf depth or heartbeats'
    if 'unsupported term have' in m or 'unsupported Bool have' in m or 'unsupported term match do' in m: return '`have`/`let` binding inside a term (Nat/Bool value)'
    if 'unsupported Bool match' in m or 'unsupported match' in m or 'unsupported term match' in m or 'Decidable.rec' in m or 'Nat.rec' in m: return 'match shape (multi-scrutinee, Bool-pair, literal patterns, Decidable.rec)'
    if 'not a scalar' in m: return 'body shape not a scalar (do-block / join point)'
    if 'recursive call' in m or 'recursion' in m: return 'recursion shape'
    if 'forIn' in m or 'foldl' in m: return 'loops other than `for i in [a:b]` over Id (for over Array/List, several foldl)'
    if 'mutable local' in m: return 'mutable local of structure type'
    if 'Option` locals' in m: return '`Option` locals with several components'
    if 'failed to synthesize OfNat' in m: return 'indexing Array of tuples/structures (`a[i]!` default value)'
    if 'projection of a term' in m: return 'projection of non-constructor term (tuple/structure values)'
    if 'Format' in m: return 'String / Std.Format / Char'
    return 'other: '+m[:60]
F={}
for n,(s,m) in r.items():
    if s=='FAIL': F[n]=feat(m)
    elif s=='OK': F[n]=None
real=[n for n in F if L[n]!='?']
# closure of blocked features
memo={}
def clo(n,stack=()):
    if n in memo: return memo[n]
    if n in stack: return frozenset()
    s=set()
    if F.get(n): s.add(F[n])
    for c in G.get(n,[]):
        if c in G: s|=clo(c,stack+(n,))
    memo[n]=frozenset(s); return memo[n]
import sys; sys.setrecursionlimit(100000)
direct=collections.Counter(F[n] for n in real if F[n])
reach=collections.Counter(); ex={}
for n in real:
    for f in clo(n): reach[f]+=1
for n in real:
    if F[n]: ex.setdefault(F[n],(n,L[n]))
json.dump(dict(F=F,direct=direct,reach=reach),open('ana.json','w'))
if __name__=='__main__':
    print(len(real),sum(1 for n in real if F[n] is None),'ok; no-result',sum(1 for n in r if r[n][0]=='NOOUT'))
    for f,v in sorted(reach.items(),key=lambda x:-x[1]): print(v,direct.get(f,0),f,ex.get(f))
