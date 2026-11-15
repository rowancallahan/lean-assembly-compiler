import json,re,collections
F=json.load(open('final.json'))
first=F['first']; S=F['S']
def feat(m):
    if m is None: return None
    if 'Unknown constant' in m: return 'UNRESOLVED'
    if 'introN' in m: return 'nullary constant (0-ary def)'
    if 'free variable' in m or 'unsupported match' in m or 'Char' in m: return 'String/Char'
    if 'no unfolding equation' in m: return 'partial def'
    if 'has no argument of a declared type' in m or 'no equations' in m or 'no constructor pattern' in m: return 'frontx_ind: body calls non-inductive fn / Decidable / mutual knot'
    ty=m.split('type ',1)[-1]
    if re.search(r'\bm\b|CheckC?M|CheckCM|CoreFns|Except|StateT|Squash|\bβ\b|\bα\b|Type|Decidable|Prop',ty): return 'monad / type-class / universe polymorphism'
    if 'HashMap' in ty or 'CState' in ty: return 'HashMap / cache state'
    if 'Int' in ty and 'parameter' in m: return 'Int'
    if re.search(r'Array',ty): return 'Array of heap objects'
    if re.search(r'Expr',ty): return 'Expr'
    if re.search(r'Env|FEnv|ConstantInfo|ConstantVal|ProjTable|ProjEntry|RecRule|BlockShape|CheckError|PropWhen|WhnfStep|DeltaStep|QuotKind|ReducibilityHint|CheckMode|BasisKind|Declaration|NestCtx|NestState|RecRuleFire|InductiveVal|\w+Shape|\w+Info|\w+Val',ty): return 'multi-field structure/record'
    if 'Name' in ty: return 'Name'
    if 'Level' in ty: return 'Level'
    if 'List' in ty or 'Option' in ty: return 'List/Option of other'
    return 'other: '+ty[:40]
c=collections.Counter(feat(m) for m in first.values())
for k,v in c.most_common(): print(v,k)
oth=[(n,first[n]) for n in first if (feat(first[n]) or '').startswith('other')][:6]; print(oth)
cand=json.load(open('Fcand4.json')); import re
F4=collections.Counter()
l2={}
