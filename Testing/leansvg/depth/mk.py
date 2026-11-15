import json,collections,re,sys
sys.argv=['x']; exec(open('ana.py').read().split("if __name__")[0])
real=set(real)
def nxt(n):  # real callees, passing through non-real aux nodes
    out=[];seenx=set();st=list(G.get(n,[]))
    while st:
        c=st.pop()
        if c in seenx or c not in G: continue
        seenx.add(c)
        if c in real and not T[c].startswith('Type') and not T[c].rstrip().endswith('Type'): out.append(c)
        elif c not in real and not (c in F): st+=G.get(c,[])
    return out
sub={}
def size(n,stack=()):
    if n in sub: return sub[n]
    s={n}
    for c in nxt(n):
        if c not in stack: s|=size(c,stack+(n,))
    sub[n]=s; return s
root='LeanSvg.render'
rs=size(root)
short=lambda n:n.replace('LeanSvg.','')
def sig(n):
    t=T[n]; parts=[p.strip() for p in re.split(r' → ',t)]
    ok={'Nat','Bool','ByteArray','UInt8','UInt16','UInt32','UInt64','Unit'}
    bad=[p for p in parts[:-1] if p not in ok]; res=parts[-1]
    out=[]
    if bad: out.append('param '+', '.join(bad)[:60])
    if res not in ok and not res.startswith('Except String'): out.append('result '+res[:50])
    return '; '.join(out) or 'signature scalar'
def status(n):
    if F.get(n) is None: return 'compiles'
    if F[n].startswith('resource'): return 'blocked: front-end resource limit (%s); signature: %s'%(re.sub(r'\s+',' ',r[n][1])[:40].replace('|','/'),sig(n))
    return 'blocked: '+F[n].split(' (')[0]+' — '+re.sub(r'\s+',' ',r[n][1])[:70].replace('|','/')
lines=[]
def walk(n,d,maxd,pre='',seenp=set()):
    kids=sorted([c for c in nxt(n) if not (F.get(c) or '').startswith('structure ctor')],key=lambda c:-len(size(c)))
    nb=sum(1 for x in size(n) if F.get(x))
    lines.append(f"{'  '*d}- `{short(n)}` ({L[n].replace('(some LeanSvg.','').replace(')','').replace(' ','')}) — {status(n)}; below: {len(size(n))} defs, {nb} blocked")
    if d<maxd:
        for c in kids[:9]:
            if c in seenp: continue
            walk(c,d+1,maxd,pre,seenp|{n})
        if len(kids)>9: lines.append(f"{'  '*(d+1)}- … {len(kids)-9} more callees")
walk(root,0,4)
open('tree.md','w').write('\n'.join(lines))
ok=sorted(short(n) for n in rs if F.get(n) is None)
print(len(rs),'reachable real defs from render; ok:',len(ok))
# feature closure of render and greedy
need=clo(root); print(len(need))
for f in sorted(need,key=lambda f:-reach[f]): print(' ',f)
# greedy
fs={n:set(clo(n)) for n in real}
cov=set();order=[]
tot=len(real)
while True:
    unl={n for n in real if fs[n]<=cov}
    best=None;bg=0
    for f in set().union(*fs.values())-cov:
        g=sum(1 for n in real if fs[n]<=cov|{f})-len(unl)
        if g>bg: bg,best=g,f
    if not best: break
    cov.add(best); order.append((best,bg,len(unl)+bg))
    if 'render' and root in real and fs[root]<=cov: break
json.dump(order,open('greedy.json','w'))
for o in order: print(o)
# stats for rs
rb=collections.Counter(); 
for n in rs:
    if F.get(n): rb[F[n]]+=1
json.dump(dict(rs=len(rs),ok=ok,rb=rb),open('rs.json','w'))
