import re,json,csv,collections
D=json.load(open('/tmp/claude-0/s/decls.json'))
seen={};rows=[]
for d in D:
    if d['kind'] not in('def','abbrev','instance'): continue
    src=d['src']
    # header: up to first ':=' / 'where' / pattern-match '|' at line start
    m=re.search(r':=|\n\s*\||\n\s*where\b|\bwhere\b',src)
    hdr=src[:m.start()] if m else src
    hdr=' '.join(hdr.split())
    body=src[m.start():] if m else ''
    full=(d['ns']+'.' if d['ns'] else '')+d['name']
    key=(d['file'],full if d['kind']!='instance' else src[:80])
    if key in seen: seen[key]['variants']+=1; continue
    chap=d['file'].split('/')[1].replace('.lean','') if d['file'].startswith('Examples/') else d['file'].split('/')[0]
    if d['file'].count('/')>=2 and d['file'].startswith('Examples/'): chap=d['file'].split('/')[1]
    r=dict(chapter=chap,file=d['file'],line=d['line'],kind=d['kind'],name=full,sig=hdr[:200],variants=1,src=src,hdr=hdr,body=body)
    seen[key]=r;rows.append(r)
def has(p,s): return re.search(p,s) is not None
for r in rows:
    h,b,s=r['hdr'],r['body'],r['src']
    # effects
    eff=[]
    if has(r'\b(IO|EIO|BaseIO|StateT|ReaderT|ExceptT|StateM|ReaderM|ExceptM|OptionT|WriterT|Except|IO\.FS|Std\.Format)\b',h) and not has(r'\bExcept\b',h) : eff.append('IO/monad')
    if has(r'\b(IO|EIO|BaseIO|StateT|ReaderT|ExceptT|StateM|ReaderM|OptionT|WriterT|ST)\b',h): eff.append('monad')
    if has(r'\[Monad\s|\[Applicative|\[Functor|\{m\s*:|\(m\s*:|\bm \(?[α-ωA-Z]',h) : eff.append('monadpoly')
    if has(r'\bIO\.|\bIO\b|println|\(← |<-\s*(IO|get|read)|\bget\b.*\bset\b|throw|\bset\b\s',b) and 'do' in b and not has(r'Id\.run',b): eff.append('doeffect')
    if has(r'\bdbgTrace|panic!|unsafe',s): eff.append('unsafe/dbg')
    r['effects']=sorted(set(eff))
    r['pure']= not eff and r['kind']!='instance' or (r['kind']=='instance' and not eff)
    # types
    T=[]
    for pat,n in [(r'\bNat\b','Nat'),(r'\bInt\b','Int'),(r'\bBool\b','Bool'),(r'\bChar\b','Char'),(r'\bString\b|\bSubstring\b','String'),(r'\bList\b','List'),(r'\bArray\b','Array'),(r'\bOption\b','Option'),(r'\bFloat\b','Float'),(r'×|\bProd\b','Prod'),(r'\bFin\b','Fin'),(r'\bUInt(8|16|32|64)\b|\bUSize\b','UIntN'),(r'\bExcept\b','Except'),(r'\bSum\b|⊕','Sum'),(r'\bTree\b|\bBinTree\b|\bExpr\b|\bArith\b|\bPrim\b|\bSign\b|\bPos\b|\bNonEmptyList\b|\bPoint\b|\bPPoint\b|\bBTree\b','userType'),(r'→.*→|\(\s*\w+\s*:\s*[^)]*→[^)]*\)|\(f\s*:','higher-order'),(r'\bType\b|\bSort\b|\{\s*α|\(\s*α\s*:|\{\s*[α-ω]\s*:|\bα\b|\bβ\b','polymorphic'),(r'\[[A-Z]\w*\s+[α-ωa-z]\w*\]','typeclass'),(r'\bSubarray\b|\bByteArray\b','Subarray/ByteArray'),(r'\bUnit\b','Unit'),(r'\bDecidable|Prop\b|∀|∃','Prop/dependent')]:
        if has(pat,h): T.append(n)
    r['types']=T
    # recursion
    rec='none'
    nm=r['name'].split('.')[-1]
    selfcall= nm and has(r'(?<![\w.])'+re.escape(nm)+r'(?![\w])',b) or ('.'+nm in b)
    if has(r'\bmutual\b',s): rec='mutual'
    if selfcall and r['kind']!='instance' and not has(r'^\s*def\s+\w+\s*:=',s[:0]):
        rec='wf' if has(r'termination_by|decreasing_by|partial',s) or r['src'].startswith('partial') else 'structural'
    if has(r'\bfoldl|\bfoldr|\bfold\b|\.foldl|List\.map|\.map\b|\bfilter|\bzipWith|forIn|for\s+\w+\s+in|\.all\b|\.any\b|\.sum|\.length|\bmap\b',b) and rec=='none': rec='fold/map(via library)'
    if has(r'for\s+\w+.*\bin\b|\bwhile\b',b) and has(r'Id\.run',b): rec='loop(Id.run)'
    r['recursion']=rec
    r['strings']=has(r'\bString\b|\bChar\b|"|\bSubstring\b|toString|s!"',s)
    r['alloc']=has(r'::|\[\s*\w[^\]]*\]|#\[|\.push|\.cons|\bsome\b|\bnode\b|\(\s*\w+\s*,\s*\w+|\.mk\b|\{\s*\w+\s*:=|\.append|\+\+',b)
    r['floats']=has(r'\bFloat\b',s)
json.dump(rows,open('/tmp/claude-0/s/rows.json','w'))
print(len(rows),sum(r['pure'] for r in rows))
print(collections.Counter(r['chapter'] for r in rows if r['pure']))
