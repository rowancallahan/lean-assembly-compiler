import re,sys,os,json,glob
R='/tmp/claude-0/s/fp-lean/examples'
files=sorted(glob.glob(R+'/**/*.lean',recursive=True))
files=[f for f in files if '/.lake/' not in f and 'lakefile' not in f]
KW=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(private|protected|partial|unsafe|noncomputable)\s+)*(def|abbrev|instance|theorem|structure|inductive|class|example|opaque|axiom)\b')
out=[]
for f in files:
    rel=os.path.relpath(f,R)
    lines=open(f).read().split('\n')
    ns=[];blocks=[];cur=None
    for i,l in enumerate(lines):
        m=re.match(r'^namespace\s+(\S+)',l)
        if m: ns.append(m.group(1))
        m=re.match(r'^end\s+(\S+)',l)
        if m and ns and ns[-1]==m.group(1): ns.pop()
        if KW.match(l):
            if cur: blocks.append(cur)
            cur=dict(file=rel,line=i+1,ns='.'.join(ns),text=[l])
        elif cur is not None:
            if l and not l[0].isspace() and not l.startswith('--') and not l.startswith('|') and not l.startswith('where') and not l.startswith(')') and not l.startswith(']') and not l.startswith('}'):
                blocks.append(cur);cur=None
            else: cur['text'].append(l)
    if cur: blocks.append(cur)
    out+=blocks
res=[]
for b in out:
    t='\n'.join(x for x in b['text'] if not x.lstrip().startswith('--')).rstrip()
    m=KW.match(t); kind=m.group(2)
    rest=t[m.end():].strip()
    nm=re.match(r"([^\s:({\[\]]+)",rest)
    b['kind']=kind;b['name']=nm.group(1) if nm else '';b['src']=t
    del b['text']
    res.append(b)
json.dump(res,open('/tmp/claude-0/s/decls.json','w'))
from collections import Counter
print(len(res),Counter(r['kind'] for r in res))
