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
