# Index the concatenated con-leche file (F2.lean.txt): top-level defs, file (module) and original line.
import re,json,collections,sys
SRC='/home/user/scratch/cl/F2.lean.txt'
L=open(SRC).read().split('\n')
pat=re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:private |protected |partial |unsafe |noncomputable )*(def|abbrev|theorem|lemma|structure|inductive|class|instance|opaque|mutual)\b\s*([^\s:({\[]*)')
decls=[];ns=[];cur=None;mod=None;mline=0
for i,l in enumerate(L,1):
    m=re.match(r'^-- ===== (\S+) \((\d+) lines\) =====',l)
    if m: mod=m.group(1); mline=i; ns=[]; cur=None; continue
    m=re.match(r'^namespace\s+(\S+)',l)
    if m: ns.append(m.group(1)); continue
    if re.match(r'^end\s+\S+',l) and ns and l.split()[1]==ns[-1]: ns.pop(); continue
    m=pat.match(l)
    if m and m.group(1) in('def','abbrev','theorem','lemma','opaque'):
        cur=dict(mod=mod,f2line=i,orig=i-mline-1,kind=m.group(1),name=m.group(2),ns='.'.join(ns),body=[])
        decls.append(cur)
    elif m: cur=None
    if cur is not None: cur['body'].append(l)
for d in decls: d['body']='\n'.join(d['body']); d['loc']=d['body'].count('\n')+1
D=[d for d in decls if d['kind'] in('def','abbrev','opaque')]
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
        s=t.split('.')[-1]
        if len(s)<4 or s not in by or (s==d['short'] and len(by[s])==1): continue
        c=by[s]; c2=[j for j in c if D[j]['mod']==d['mod']] or c
        for j in (c2 if len(c2)<=3 else []): out.add(j)
    out.discard(i); edges.append(out)
def reach(names):
    st=[i for i,d in enumerate(D) if d['full'] in names]; seen=set(st)
    while st:
        x=st.pop()
        for y in edges[x]:
            if y not in seen: seen.add(y); st.append(y)
    return seen
if __name__=='__main__':
    print(len(decls),'decls;',len(D),'def/abbrev/opaque')
    roots={'ConLeche.whnfBody','ConLeche.inferBody','ConLeche.defeqBody','ConLeche.Expr.instantiate1','ConLeche.checkDecl','ConLeche.Cached.checkDecls'}
    seen=reach(roots)
    # same name-collapsing rule as mkprobe2.py
    cnt=collections.Counter(D[i]['full'] for i in seen if D[i]['full'] and not D[i]['name'].startswith('_'))
    sel=[i for i in sorted(seen,key=lambda i:(D[i]['mod'],D[i]['orig'])) if D[i]['full'] and not D[i]['name'].startswith('_') and cnt[D[i]['full']]==1]
    print('reached',len(seen),'probed',len(sel))
    json.dump([dict(full=D[i]['full'],mod=D[i]['mod'],orig=D[i]['orig'],f2line=D[i]['f2line'],loc=D[i]['loc'],sig=D[i]['b'].split(':=')[0][:600] if ':=' in D[i]['b'] else D[i]['b'][:600],body=D[i]['b'],edges=sorted(edges[i])) for i in sel],open('/home/user/scratch/cl2/probe_list.json','w'))
    json.dump([ {'full':D[i]['full'],'mod':D[i]['mod'],'orig':D[i]['orig'],'edges':sorted(edges[i])} for i in range(len(D))],open('/home/user/scratch/cl2/all.json','w'))
