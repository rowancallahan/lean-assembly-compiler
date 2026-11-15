import json,re,collections,sys
D=[d for d in json.load(open('/tmp/claude-0/cl/s/decls.json')) if d['kind'] in('def','abbrev','opaque')]
# strip comments
def strip(b):
    b=re.sub(r'/-.*?-/','',b,flags=re.S); return re.sub(r'--[^\n]*','',b)
for d in D: d['b']=strip(d['body']); d['short']=d['name'].split('.')[-1]; d['full']=(d['ns']+'.'+d['name']).strip('.')
by=collections.defaultdict(list)
for i,d in enumerate(D): by[d['short']].append(i)
tok=re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?]*")
edges=[]
for i,d in enumerate(D):
    out=set()
    for t in set(tok.findall(d['b'])):
        parts=t.split('.')
        for k in range(len(parts)):  # try suffixes (x.foo field notation)
            s=parts[-1] if k==len(parts)-1 else None
        s=parts[-1]
        if len(s)<4 or s not in by or s==d['short'] and len(by[s])==1: continue
        c=by[s]
        # prefer same namespace chain / dotted match
        full=[j for j in c if t.endswith(D[j]['name']) ]
        c2=[j for j in c if D[j]['file']==d['file']] or c
        for j in (c2 if len(c2)<=3 else []): out.add(j)
    out.discard(i); edges.append(out)
json.dump([sorted(e) for e in edges],open('/tmp/claude-0/cl/s/edges.json','w'))
json.dump([[d['file'],d['line'],d['full'],d['loc']] for d in D],open('/tmp/claude-0/cl/s/D.json','w'))
def reach(names):
    st=[i for i,d in enumerate(D) if d['full'] in names]; seen=set(st)
    while st:
        x=st.pop()
        for y in edges[x]:
            if y not in seen: seen.add(y); st.append(y)
    return seen
if __name__=='__main__':
    for n in sys.argv[1:]:
        r=reach({n}); print(n,len(r),sum(D[i]['loc'] for i in r))
