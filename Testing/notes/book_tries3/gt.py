import json,re,glob,os
S=os.environ['BS3_ROOT']
M=json.load(open(S+'/mainx/decls.json')); F=json.load(open(S+'/decls.json'))
def norm(d):
    s=re.sub(r'(?m)^(open|set_option)[^\n]* in\s*\n','',d['src']); s=re.sub(r'--.*','',s); s=re.sub(r'/-.*?-/','',s,flags=re.S)
    s=re.sub(r'\s+',' ',s).strip()
    if d.get('name'):
        ln=re.escape(d['name'].split('.')[-1]); s=re.sub(r'(?<![\w.])(?:\w+\.)*'+ln+r'(?![\w])','_N_',s)
    return re.sub(r'\b(Proven\.|Frontx\.)','',s)
fk={}
for d in F:
    if d['kind'] in('def','abbrev') and d.get('name'): fk.setdefault(norm(d),[]).append(d)
# commands per main file
CMD=re.compile(r'^(frontx_(?:compile|view|ind|rec|entry|tailcopy|spec|rec_entry)|wa_compile)\s+([\w.?!\']+)(.*)$',re.M)
cmds={}
for f in glob.glob('/home/user/lean-assembly-compiler/Riscv/Frontx/*.lean'):
    rel=os.path.basename(f)
    for i,l in enumerate(open(f).read().split('\n')):
        m=CMD.match(l)
        if m: cmds.setdefault(rel,[]).append((i+1,l.strip()))
out=[]
for m in M:
    if m['kind'] in('def','abbrev') and m.get('name') and m['file'].endswith('.lean'):
        k=norm(m)
        if k in fk:
            nm=m['name'].split('.')[-1]
            c=[(ln,t) for ln,t in cmds.get(os.path.basename(m['file']),[]) if ln>m['end']-1 and re.search(r'(?<![\w.])'+re.escape(m['name'])+r'(?![\w])|(?<![\w])'+re.escape(nm)+r'\b',t) and ln<m['end']+60]
            out.append(dict(main=m['file'],mline=m['line'],mname=m['name'],ns=m['ns'],fp=[(x['file'],x['line'],x['end'],x['name']) for x in fk[k]],cmds=c[:4]))
json.dump(out,open(S+'/gt.json','w'),indent=1)
print(len(out))
for o in out: print(o['main'],o['mline'],o['mname'],'|',o['fp'][0][:2],'|',[c[1][:70] for c in o['cmds'][:2]])
