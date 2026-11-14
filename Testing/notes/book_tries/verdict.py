import re,json,csv,collections
D=json.load(open('/tmp/claude-0/s/decls.json'))
R=json.load(open('/tmp/claude-0/s/rows.json'))
utypes=set()
for d in D:
    if d['kind'] in('inductive','structure'): utypes.add(d['name'])
utypes-= {'Nat','Int','Bool','Option','List','Unit','Prod'}
UT=re.compile(r'\b('+'|'.join(sorted(map(re.escape,utypes),key=len,reverse=True))+r')\b')
MON=re.compile(r'\b(State|Reader|WithLog|Validate|Many|Except|ExceptT|StateT|ReaderT|Writer|Id|ToTrace|Counter|Config\w*|ConfigIO|CanFail|Serializer|Pair|Monads?|Functor|Applicative|Alternative|Seq|ReaderIO|Transformer|CountM|Coe|OfNat|CoeDep|CoeFun|CoeSort|HAppend|Append|HMul|Mul|Add|Hashable|BEq|Ord|Functor|Pure|Bind|Mutable|Mut\w*)\b')
rows=[]
def typelevel(h):
    return bool(re.search(r'^(?:partial\s+)?(def|abbrev)\s+\S+\s*(?:\([^)]*\)\s*|\{[^}]*\}\s*)*:\s*(Type|Prop|Sort|\w+\s*→\s*Type)',h)) or bool(re.search(r'\b(True|False)\s*[∧∨]|:\s*\d+\s*[+=<]|=\s*\d+',h.split(':=')[0]) and not re.search(r'→|\(\w+\s*:\s*\w',h))
def decide(r):
    h,b,s=r['hdr'],r['body'],r['src']
    sig=h
    feats=[];need=[];v='';why=''
    nm=r['name']
    if r['kind']=='instance':
        cls=re.sub(r'^instance(?:\s*\([^)]*\))?\s*:?\s*','',h).strip()
        if re.search(r'Lawful|Decidable|Inhabited|Repr|ToString|ToStream|OfNat|Coe|Hashable|BEq|Ord|HAdd|HMul|Add|Mul|Append|HAppend|Functor|Monad|Applicative|Alternative|Seq|Pure|Bind|Mutable',cls) : pass
        r['name']='instance '+cls[:60]
    # type-level / proofs
    if r['kind']!='instance' and typelevel(h): return 'X','type-level definition (type/Prop/proof), not a function','',[]
    if re.search(r'Lawful|\bProp\b|∧|∨|∀|∃',h) : return 'X','Prop/proof-level','',[]
    flt=re.search(r'\bFloat\b',s)
    if flt: return 'D','Float','Float',[]
    if re.search(r'\bIO\b|IO\.|println|\bBaseIO\b',s): return 'D','IO','IO',[]
    f=[]
    if re.search(r'\bString\b|\bChar\b|\bSubstring\b|s!"|"[^"]*"',s) and not re.search(r'^\s*(#|--)',s): f.append('strings')
    if UT.search(sig) or (r['kind']=='instance'): f.append('tagged data/structures')
    elif UT.search(b): f.append('tagged data/structures')
    if re.search(r'\bOption\b|×|\bProd\b|\bSum\b|⊕|\bExcept\b',sig): f.append('Option/Prod/Sum results (tagged data / output encoding)')
    if MON.search(sig) and re.search(r'→\s*\w+\s+\w|State|Reader|WithLog|Validate|Many|Except|Monad|Functor|Applicative',sig): f.append('higher-order by specialisation')
    if re.search(r'\bInt\b',s): f.append('Int (signed, unbounded)')
    if re.search(r'\*|\bmul\b|/|%|\bdiv\b|\bmod\b|\bpow\b|\^',re.sub(r'\^\^\^','',b)) and re.search(r'\bNat\b|\bInt\b|\bFin\b',s) and nm.split('.')[-1] not in('plus',) : f.append('multiply-divide')
    if re.search(r'\bArray\b',sig): f.append('Array (heap data)')
    if re.search(r'\bList\b',sig): f.append('List (heap data)')
    if re.search(r'\[\s*(Ord|BEq|Hashable|Add|Mul|ToString|Inhabited|DecidableEq|LT|LE|Max|Min)\b',sig): f.append('polymorphism by monomorphisation (type class)')
    elif re.search(r'\{?\(?\s*[αβγ]\b|\bType\b',sig): f.append('polymorphism by monomorphisation')
    if re.search(r'→\s*(Bool|Option|List|Array|α|β|Nat)\b.*→|\(\s*\w+\s*:\s*[^)]*→[^)]*\)|\(\s*(p|f|pred|predicate|k|g)\s*:',sig) or re.search(r'\b(Nat|α|β) → (Bool|β|γ|α)\)',sig): f.append('higher-order by specialisation')
    if re.search(r'List\s+\w+\)?\s*→.*List|\(\w+\s*:\s*List[^)]*\)\s*\(\w+\s*:\s*List|List\s+\w+\s*→\s*List\s+\w+\s*→|\bsameLength\b|\bzip\b|\bmerge\b',sig) and len(re.findall(r'List\s',sig))>=2 and 'two list inputs' not in f: f.append('two list inputs')
    rec=r['recursion']
    tail=bool(re.search(r'helper|Helper|Loop|soFar|accum|Tail\.',nm+h)) and rec=='structural'
    if rec=='structural' and not tail: f.append('non-tail recursion (calls + stack)')
    if rec=='wf': f.append('non-tail recursion (calls + stack)')
    if rec=='mutual': f.append('non-tail recursion (calls + stack)')
    if rec=='structural' and re.search(r'List|Tree|Expr|Arith|Prim',sig) and not tail and 'List (heap data)' not in f: pass
    if re.search(r'(::|\+\+|\.push|\bsome\b|\bnode\b|\.cons)',b) and ('List (heap data)' in f or 'Array (heap data)' in f or 'tagged data/structures' in f): f.append('allocator (new data)')
    # monad-style pure: treat as higher-order
    f=list(dict.fromkeys(f))
    heap=[x for x in f if x.startswith(('List','Array'))]
    nonheap=[x for x in f if not x.startswith(('List (h','Array (h'))]
    return None,'', '', f
for r in R:
    out=decide(r)
    if out[0] in('X','D'): r['verdict'],r['why'],r['feat']=out[0],out[1],out[2]; r['needs']=[]; continue
    r['feat']=out[3]
    r['needs']=out[3]
json.dump(R,open('/tmp/claude-0/s/rows2.json','w'))
c=collections.Counter()
for r in R:
    if r['pure'] and r.get('verdict') is None: c[len(r['needs'])]+=1
print(c, collections.Counter(r.get('verdict') for r in R if r['pure']))
