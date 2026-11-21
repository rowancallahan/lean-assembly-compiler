import sys,collections
def load(p):
    d={}
    for l in open(p):
        f=l.rstrip('\n').split('\t'); d[f[0]]=f
    return d
A=load(sys.argv[1]); B=load(sys.argv[2]); out=sys.argv[3]
mods={f[1] for f in A.values()}; Bm={k:v for k,v in B.items() if v[1] in mods}
chg=[k for k in A if k in Bm and A[k][1:]!=Bm[k][1:]]
onlyA=[k for k in A if k not in Bm]; onlyB=[k for k in Bm if k not in A]
print(f"A={len(A)} B={len(Bm)} same={len(A)-len(chg)-len(onlyA)} changed={len(chg)} onlyA={len(onlyA)} onlyB={len(onlyB)}")
print('changed fields:',collections.Counter(('T' if A[k][3]!=Bm[k][3] else '')+('V' if A[k][4]!=Bm[k][4] else '')+('M' if A[k][1]!=Bm[k][1] else '') for k in chg))
print('by module:',collections.Counter(A[k][1].split('.')[-1] for k in chg).most_common())
open(out+'.changed','w').write(''.join(f"{k}\t{A[k][1]}\t{A[k][2]}\n" for k in sorted(chg)))
open(out+'.onlyA','w').write(''.join(f"{k}\t{A[k][1]}\t{A[k][2]}\n" for k in sorted(onlyA)))
open(out+'.onlyB','w').write(''.join(f"{k}\t{Bm[k][1]}\t{Bm[k][2]}\n" for k in sorted(onlyB)))
