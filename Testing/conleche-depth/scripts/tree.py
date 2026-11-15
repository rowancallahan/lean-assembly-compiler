import json,sys,re
sys.path.insert(0,'.')
import reach as R
D=R.D;E=R.edges
F=json.load(open('final.json')); meta=json.load(open('F2meta.json')); idx={m[0]:m[3] for m in meta}; info={m[0]:m for m in meta}
P={idx[n]:n for n in idx}
def st(n):
    f=F['first'][n]
    if f is None: return 'COMPILES'
    f=re.sub(r'frontx(_ind)?: ','',f); f=f.replace('unsupported ','').replace('\n',' ')
    return 'blocked: '+f[:52]
def tree(n,depth,seen,ind=''):
    c=[P[j] for j in sorted(E[idx[n]]) if j in P and 'Name' not in D[j]['name'][-4:] and D[j]['kind']!='theorem']
    print(f"{ind}{n.replace('ConLeche.','')} [{info[n][1].replace('.lean','')}:{info[n][2]}] {st(n)}")
    if depth==0: return
    k=0
    for y in c:
        if y in seen: continue
        seen.add(y); k+=1
        if k>7: print(ind+'  ...(+%d more)'%(len(c)-7)); break
        tree(y,depth-1,seen,ind+'  ')
for r in sys.argv[2:]: tree(r,int(sys.argv[1]),{r}); print()
