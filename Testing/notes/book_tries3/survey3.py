import json,re,csv,sys,os,collections,hashlib
sys.path.insert(0,os.path.dirname(__file__))
import gen,run
S=gen.S
R=json.load(open(S+'/results_all.json')); GT=json.load(open(S+'/gt.json'))
byk={(d['file'],d['line']):d for d in gen.D}
old=list(csv.DictReader(open(S+'/old/Testing/notes/book_survey.csv')))
oldst={}
for x in old:
    if x['status'] in('machine-thm','source-thm','not-on-main','likely-untried'):
        oldst.setdefault(x['file'],[]).append((int(x['line']),x['status'],x['name']))
def norm(src):
    s=re.sub(r'(?m)^(open|set_option)[^\n]* in\s*\n','',src); s=re.sub(r'--.*','',s); s=re.sub(r'\s+',' ',s).strip(); return s
def olds(f,l,e):
    return [(st,nm) for ln,st,nm in oldst.get(f,[]) if l<=ln<=e]
def gt_of(f,l,e):
    for g in GT:
        for gf,gl,ge,gn in g['fp']:
            if gf==f and gl==l: return g
    return None
def pick(r):
    tr=r['tries']
    for vn in ['ind','view1','view0','view2','helper0','helper1','wa','compile']:
        if vn in tr:
            e=[m for m in tr[vn]['msgs'] if m[1]=='error']
            if e: return vn,re.sub(r'\s+',' ',re.sub(r'PANIC at.*','',e[0][2],flags=re.S))
    return None,''
def defelab(r,T):
    t=open(f"{S}/runs/{T['id']}_compile.lean").read().split('\n')
    cl=[i+1 for i,l in enumerate(t) if l.startswith(('frontx_compile','frontx_ind','wa_','frontx_view'))][0]
    tl=[i+1 for i,l in enumerate(t) if l.startswith('-- TARGET')][0]
    e=[m for m in r['tries']['compile']['msgs'] if m[1]=='error']
    return [m for m in e if tl<=m[0]<cl]
BK=[ # (bucket, regex over "type text + message")
 ('dependent types / type-valued functions', r'Vect|HasCol|Subschema|Schema|\bRow\b|\bTable\b|asType|Finite|DBType|NestedPairs|Carrier|result type Type\b|result type Prop|type Type\b|DBExpr|Universe|MyList|Type of sort|natOrString|Fin '),
 ('monad / higher-kinded (`m α`, State/Reader/WithLog as functions, `do`)', r'Monad m|Pure \(|Monad \(|\bm [αβ]\b|result type m |forM|seq |do notation|forIn|Applicative|Functor|Alternative'),
 ('higher-order argument (function/predicate parameter)', r'→ Bool|UInt8 →|foldMap|parameter type [^ ]* ?→|\?α →|Monoid'),
 ('Int / signed arithmetic', r'\bInt\b'),
 ('String / Char', r'\bString\b|\bChar\b'),
 ('list of pairs / pair-of-lists / list of structures', r'UInt8 × UInt8|List \(|List α × List β|× List|NonEmptyList'),
 ('Array of non-bytes / generic Array code', r'wa_compile|Array'),
 ('needs a loop/recursion invariant hint (`with`) or proof', r'could not prove|rewrite. failed|termination'),
 ('list-view shapes not supported (non-`match` body, non-view recursive call, list result)', r'frontx_view|list result|no list parameter|does not reduce'),
 ('inductive / structure shapes not supported (no equations, nested patterns, `brecOn`, projections, hash)', r'frontx_ind|has no equations|nested patterns|brecOn|mixHash|type expected, got|Point'),
 ('multiply / divide by a variable (`unsupported term`)', r'unsupported term'),
 ('polymorphic result/parameter type (`α`, `Option α`, `Except ε α`) not instantiated', r'result type [αβ]|result type Option|result type Except|result type List|result type Array|parameter type [αβ]|result type\s*$|unsupported (?:parameter|result) type'),
 ('compiler error (unknown free variable / universe levels / introN)', r'free variable|universe levels|introN|EXIT'),
]
def bucket(vn,msg,T=None):
    if T is not None and any(re.search(r'\bFloat\b',d['src']) for d in gen.closure(T)): return 'Float'
    for b,rx in BK:
        if re.search(rx,msg): return b
    return 'other: '+msg[:60]
rows=[]
okset=[]
for r in R:
    T=byk[(r['file'],r['line'])]
    row=dict(file=r['file'],line=r['line'],end=r['end'],name=r['name'],src=T['src'])
    row['body']=hashlib.md5(norm(T['src']).replace(T['name'],'_',1).encode()).hexdigest()[:8]
    fn=run.sig_has_params(T['src'])
    row['old']=';'.join(f'{st}' for st,nm in olds(r['file'],r['line'],r['end']))
    if r['file']=='ExampleSupport.lean': row['status']='meta (Lean elaborator code, not book functions)'
    elif r['status']=='skip': row['status']='IO (skipped)'
    elif not fn: row['status']='not a function (constant / type)'
    elif r['status']=='ok':
        row['status']='compiled'; row['cmd']=r['variant']; okset.append(T)
    else:
        g=gt_of(r['file'],r['line'],r['end'])
        row['status']='?'
        row['g']=g
        row['T']=T; row['r']=r
    rows.append(row)
# callee-inlined: names referenced by compiled targets
used=set()  # (callee-inlined detection removed: token closure over-approximates)
for T in []:
    for d in gen.closure(T):
        used.add(d['id'])
for row in rows:
    if row['status']!='?': continue
    T=row['T']; r=row['r']; g=row['g']
    if g:
        row['status']='compiled on main (hand directive)'
        row['cmd']=(g['cmds'][0][1] if g['cmds'] else 'inlined in / wrapped by hand-written entry')+f"  [Riscv/Frontx/{g['main']}:{g['mline']}]"
        continue
    el=defelab(r,T)
    vn,msg=pick(r)
    if el:
        row['status']='not run: def does not elaborate in isolation'; row['msg']=re.sub(r'\s+',' ',el[0][2])[:140]; row['bucket']=bucket('def',row['msg'],T)
        continue
    if T['id'] in used:
        row['status']='callee inlined in a compiled function'; continue
    row['status']='blocked'; row['msg']=msg[:160]; row['variant']=vn
    row['bucket']=bucket(vn,msg,T)
# any-feature flags on all non-compiled function rows
FE={'user inductive / structure':r'__IND__','type class (`[C α]`, instances)':r'\[\s*[A-Z]\w*\s+[α-ωa-z]\w*\s*\]|\binstance\b','String / Char':r'\bString\b|\bChar\b|s!"','Int':r'\bInt\b','Float':r'\bFloat\b','dependent types':r'Vect|\bFin\b|asType|HasCol|Subschema|\(\w+ : Nat\) →.*Type','higher-order argument':r'\([\w\s]+: [^()]*→[^()]*\)','monad-style (`do`, `State`, `Except`, `m α`)':r'\bdo\b|\bState\b|\bReader\b|\bExcept\b|\bStateT\b|\bReaderT\b|\bExceptT\b|\bm [αβ]\b|Monad','Array':r'\bArray\b','pairs / tuples':r'×|Prod','polymorphism (`α`)':r'\bα\b|\bβ\b'}
anyc=collections.Counter(); nrows=0
for row in rows:
    if row['status'] in('blocked','not run: def does not elaborate in isolation'):
        T=byk[(row['file'],row['line'])]; txt=T['src']; nrows+=1
        inds=[d for d in gen.closure(T) if d['kind'] in('inductive','structure') and d is not T and re.search(r'(?<![\w.])'+re.escape(gen.last(d['name']))+r'(?![\w])',txt)]
        for k,rx in FE.items():
            if k.startswith('user ind'):
                if inds: anyc[k]+=1
            elif re.search(rx,txt): anyc[k]+=1
print('any-feature (blocked+not-run rows =',nrows,')'); 
for k,v in anyc.most_common(): print(v,k)
json.dump(dict(anyc),open(S+'/anyc.json','w'))
# print summary
c=collections.Counter(r['status'] for r in rows); print(c)
for k in ('compiled','compiled on main (hand directive)','callee inlined in a compiled function'): print(k, len({r['body'] for r in rows if r['status']==k}),'distinct bodies')
b=collections.Counter(r['bucket'] for r in rows if r['status']=='blocked'); 
for k,v in b.most_common(): print(v,k)
json.dump([{k:v for k,v in r.items() if k not in('T','r','g')} for r in rows],open(S+'/rows.json','w'))
