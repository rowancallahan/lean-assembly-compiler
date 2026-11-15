import re,glob,sys,json,collections
root='/tmp/claude-0/cl/con-leche/ConLeche/'
files=glob.glob(root+'Kernel/**/*.lean',recursive=True)+glob.glob(root+'Cached/*.lean')
# top-level decls: lines starting (after attrs) with def/theorem/abbrev/instance/structure/inductive...
pat=re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:private |protected |partial |unsafe |noncomputable )*(def|abbrev|theorem|lemma|structure|inductive|class|instance|opaque|mutual)\b\s*([^\s:({\[]*)')
decls=[]
for f in files:
    L=open(f).read().split('\n'); ns=[]; cur=None
    for i,l in enumerate(L,1):
        m=re.match(r'^namespace\s+(\S+)',l)
        if m: ns.append(m.group(1)); continue
        if re.match(r'^end\s+\S+',l) and ns and l.split()[1]==ns[-1]: ns.pop(); continue
        m=pat.match(l)
        if m and m.group(1) in('def','abbrev','theorem','lemma','opaque'):
            cur=dict(file=f[len(root):],line=i,kind=m.group(1),name=m.group(2),ns='.'.join(ns),body=[])
            decls.append(cur)
        elif m: cur=None
        if cur is not None: cur['body'].append(l)
for d in decls: d['body']='\n'.join(d['body']); d['loc']=d['body'].count('\n')+1
json.dump(decls,open('/tmp/claude-0/cl/s/decls.json','w'))
print(len(decls),collections.Counter(d['kind'] for d in decls))
