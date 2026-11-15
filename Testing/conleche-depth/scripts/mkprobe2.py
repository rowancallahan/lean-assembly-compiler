import json,re,sys
sys.path.insert(0,'/tmp/claude-0/cl/s')
import reach as R
D=R.D
roots=['ConLeche.whnfBody','ConLeche.inferBody','ConLeche.defeqBody','ConLeche.Expr.instantiate1','ConLeche.checkDecl','ConLeche.Cached.checkDecls']
seen=R.reach(set(roots))
probe=open('/home/user/lean-assembly-compiler/Testing/conleche-depth/Full.lean').read()
files=set()
names=[]
for i in sorted(seen):
    d=D[i]
    if True and d['kind'] in('def','abbrev') and d['name'] and not d['name'].startswith('_'):
        names.append((d['full'],d['file'],d['line'],i))
# dedupe full names
cnt={}
for n in names: cnt[n[0]]=cnt.get(n[0],0)+1
out=['','-- ===== probes =====','frontx_ind_type TName := ConLeche.Name','frontx_ind_type TLevel := ConLeche.Level']
meta=[]
for n,f,l,i in names:
    if cnt[n]>1: continue
    out.append(f'#guard_msgs (drop all) in\n#check @{n}'); 
    out.append(f'frontx_compile {n}'); meta.append((n,f,l,i))
open('/tmp/claude-0/cl/s/F2.lean','w').write(probe+'\n'.join(out)+'\n')
json.dump(meta,open('/tmp/claude-0/cl/s/F2meta.json','w'))
print(len(names),len(meta))
