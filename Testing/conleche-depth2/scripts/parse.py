# Parse F2P.out against meta.json. Compile failure = positioned error on the compile line; gate/compile success are unpositioned.
# Continuation lines (indented, or starting with '(') belong to the preceding message.
import re,json,collections,sys
meta=json.load(open('/home/user/scratch/cl2/meta.json'))
cl={ln:n for ln,n,k in meta if k=='compile'}; gl={ln:n for ln,n,k in meta if k=='gate'}
err=collections.defaultdict(list); ok=set(); gate={}
cur=None  # ('err',name) or ('gate',name)
for l in open(sys.argv[1]).read().split('\n'):
    m=re.match(r'^\S*F2P\.lean:(\d+):\d+: (error|warning|info)[^:]*: (.*)',l)
    if m:
        ln=int(m.group(1)); cur=None
        if ln in cl and m.group(2)=='error': err[cl[ln]].append(m.group(3).strip()); cur=('err',cl[ln])
        elif ln in gl and m.group(2)=='error': gate[gl[ln]]='ERR: '+m.group(3).strip()
        continue
    if cur and (l.startswith(' ') or l.startswith('(')) and l.strip():
        if cur[0]=='err': err[cur[1]][-1]+=' '+l.strip()
        else: gate[cur[1]]+=' '+l.strip()
        continue
    cur=None
    m=re.match(r'^frontx: (\S+?): ',l)
    if m: ok.add(m.group(1))
    m=re.match(r'^frontx_ind_gate (\S+?): (.*)',l)
    if m: gate[m.group(1)]=m.group(2).strip(); cur=('gate',m.group(1))
res={}
for ln,n in cl.items():
    res.setdefault(n,{})
    res[n]['compile']=('ERR: '+err[n][0]) if err.get(n) else ('OK' if n in ok else 'SILENT')
for ln,n in gl.items():
    res.setdefault(n,{}); res[n]['gate']=gate.get(n,'SILENT')
json.dump(res,open(sys.argv[2],'w'),indent=1)
c=collections.Counter()
for n in res:
    c[('compile',res[n]['compile'].split(':')[0])]+=1; c[('gate',res[n]['gate'].split(':')[0].split(';')[0])]+=1
for k,v in sorted(c.items(),key=lambda x:-x[1]): print(v,k)
