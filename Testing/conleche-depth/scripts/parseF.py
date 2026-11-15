import re,json,collections
meta=json.load(open('F2meta.json'))
L=open('/home/user/lean-assembly-compiler/Testing/conleche-depth/F2.lean').read().split('\n')
line2n={}
for i,l in enumerate(L,1):
    m=re.match(r'frontx_compile (\S+)$',l)
    if m: line2n[i]=m.group(1)
res={}
cur=None
for l in open('F2.out'):
    m=re.match(r'.*F2\.lean:(\d+):\d+: (error|warning|info)[^:]*: (.*)',l)
    if m:
        n=int(m.group(1)); cur=n if n in line2n else None
        if cur and m.group(2)=='error' and cur not in res: res[cur]=[m.group(3)]
        elif cur and m.group(2)=='info' and cur not in res: res.setdefault(('ok',cur),[m.group(3)])
        continue
    if cur and cur in res and len(res[cur])<3 and l.startswith('  ') : res[cur].append(l.strip())
ok=[line2n[k[1]] for k in res if isinstance(k,tuple)]
fail={line2n[k]:' '.join(v) for k,v in res.items() if not isinstance(k,tuple)}
print(len(line2n),'fns',len(fail),'fail',len(ok),'ok',len(line2n)-len(fail)-len(ok),'silent')
json.dump(fail,open('Ffail.json','w'),indent=0)
c=collections.Counter(re.sub(r'ConLeche\.\S+','T',v)[:90] for v in fail.values())
for k,v in c.most_common(40): print(v,k)
print(ok)
