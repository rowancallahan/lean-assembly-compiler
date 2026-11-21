import sys,re,collections
sys.argv=sys.argv
exec(open(sys.argv[1]).read().split('def toks')[0])  # reuse blocks()
A=blocks(sys.argv[2]); B=blocks(sys.argv[3])
res=collections.defaultdict(list)
for n in open(sys.argv[4]).read().split():
    k=n.replace('LeanRV64D.Functions.','').replace('LeanRV64D.','')
    a,b=A.get(k,''),B.get(k,'')
    t=[]
    if b.count('<&&>')+b.count('<||>')>0: t.append('SC')
    if len(re.findall(r':\s*Sail\w*\s+(?:\w+\s+)?Unit\)',b))>len(re.findall(r':\s*Sail\w*\s+(?:\w+\s+)?Unit\)',a)): t.append('UNITASC')
    if 'match' in a and a.count('match')>b.count('match')+3: t.append('MATCH2IF')
    if not a: t.append('NOSRC')
    res['+'.join(t) or 'REST'].append(k)
for c,v in sorted(res.items(),key=lambda x:-len(x[1])): print(f"{len(v)}\t{c}\t{' '.join(v)}")
