import sys,collections
def load(p):
    d={}
    for l in open(p):
        if l.startswith('#'): continue
        f=l.rstrip('\n').split('\t'); d[f[0]]=f
    return d
A=load(sys.argv[1]); B=load(sys.argv[2]); out=sys.argv[3]
mods={f[1] for f in A.values()}
Bm={k:v for k,v in B.items() if v[1] in mods}
extra=len(B)-len(Bm)
same=[k for k in A if k in Bm and A[k][1:]==Bm[k][1:]]
chg=[k for k in A if k in Bm and A[k][1:]!=Bm[k][1:]]
onlyA=[k for k in A if k not in Bm]; onlyB=[k for k in Bm if k not in A]
print(f"A={len(A)} B(same modules)={len(Bm)} B other modules={extra} identical={len(same)} changed={len(chg)} onlyA={len(onlyA)} onlyB={len(onlyB)}")
def kind(k):
    a,b=A[k],Bm[k]; r=[]
    if a[1]!=b[1]: r.append('module')
    if a[2]!=b[2]: r.append('kind')
    if a[3]!=b[3]: r.append('univ')
    if a[4]!=b[4]: r.append('type')
    if a[5]!=b[5]: r.append('value')
    if a[6:]!=b[6:]: r.append('extra')
    return '+'.join(r)
c=collections.Counter(kind(k) for k in chg); print('changed by field:',dict(c))
ck=collections.Counter(A[k][2] for k in chg); print('changed by kind:',dict(ck))
print('onlyA kinds:',dict(collections.Counter(A[k][2] for k in onlyA)))
print('onlyB kinds:',dict(collections.Counter(Bm[k][2] for k in onlyB)))
with open(out+'.changed','w') as f:
    for k in sorted(chg): f.write(f"{k}\t{A[k][1]}\t{A[k][2]}\t{kind(k)}\n")
with open(out+'.onlyA','w') as f:
    for k in sorted(onlyA): f.write(f"{k}\t{A[k][1]}\t{A[k][2]}\n")
with open(out+'.onlyB','w') as f:
    for k in sorted(onlyB): f.write(f"{k}\t{Bm[k][1]}\t{Bm[k][2]}\n")
