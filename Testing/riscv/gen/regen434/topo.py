import re,sys,os
root=sys.argv[1]; pkg=sys.argv[2]
deps={}
def mods():
    for f in os.listdir(os.path.join(root,pkg)):
        if f.endswith('.lean'): yield pkg+'.'+f[:-5]
for m in mods():
    src=open(os.path.join(root,*m.split('.'))+'.lean').read()
    deps[m]=[d for d in re.findall(r'^import\s+(\S+)',src,re.M) if d.startswith(pkg+'.')]
out=[];seen=set()
def v(m):
    if m in seen: return
    seen.add(m)
    for d in deps.get(m,[]): v(d)
    out.append(m)
for m in sorted(deps): v(m)
print('\n'.join(out))
