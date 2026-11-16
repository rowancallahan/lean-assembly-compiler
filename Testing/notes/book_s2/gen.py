# gen.py: build a verbatim test file for a target decl: dependency closure from the same file + imported example files
import json, re, os, sys
S=os.environ['BS3_ROOT']
D=json.load(open(S+'/decls.json'))
for i,d in enumerate(D): d['id']=i; d['q']=(d['ns']+'.' if d['ns'] else '')+d.get('name','')
R=S+'/fp-lean/examples'
def imports(rel):
    out=[]
    for l in open(R+'/'+rel):
        m=re.match(r'^import (Examples[\w.]*|DirTree)',l)
        if m:
            p=m.group(1).replace('.','/')+'.lean'
            if p=='DirTree.lean': p='douglib/DirTree.lean'
            out.append(p)
    return out
def closure_files(rel,seen=None):
    seen=seen if seen is not None else []
    for p in imports(rel):
        if p in seen or not os.path.exists(R+'/'+p): continue
        closure_files(p,seen)
        if p not in seen: seen.append(p)
    return seen
BYFILE={}
for d in D: BYFILE.setdefault(d['file'],[]).append(d)
def last(n): return n.split('.')[-1]
gen_last=last
TOK=re.compile(r"[A-Za-z_][\w'!?]*(?:\.[A-Za-z_][\w'!?]*)*")
def toks(src):
    src=re.sub(r'--.*','',src); src=re.sub(r'"[^"]*"','""',src)
    return set(TOK.findall(src))
def header(src):
    return re.split(r':=|\bwhere\b|\n\s*\|',src,1)[0]
def closure(T):
    files=closure_files(T['file'])+[T['file']]
    pool=[]
    for f in files:
        for d in BYFILE.get(f,[]):
            if f==T['file'] and d['line']>=T['line']: continue
            pool.append(d)
    order={d['id']:i for i,d in enumerate(pool)}
    inc={T['id']:T}
    queue=[T]
    def nearest(name):
        best=None
        for p in pool:
            if p['kind'] in('instance','deriving','syntax','local','macro','infixl','mutual','section'): continue
            if not p.get('name'): continue
            if last(p['name'])==last(name):
                # dotted token: require prefix match loosely
                best=p
        return best
    CORE={'Bool','Nat','Option','List','Prod','Sum','Unit','String','Char','Int','Fin','Array','Except','Id','Functor','Monad','Applicative','Pure','Bind','Seq','Add','Mul','ToString','Ord','BEq','Hashable','Inhabited','Decidable','Coe','OfNat','Ordering','Empty','Nonempty','Subtype','HAdd','HMul','HAppend','Append'}
    def opened_of(x):
        o=set()
        for s in [x['src']]+[c for sc in x['scope'] for c in sc['cmds']]:
            for m in re.finditer(r'(?m)^\s*open\s+([^\n]*?)(?:\s+in\s*)?$',s):
                for w in re.findall(r'[A-Za-z_][\w.]*',m.group(1).split('(')[0]): o.add(w)
        return o
    def visible(p,x,op):
        return p['ns']=='' or x['ns']==p['ns'] or x['ns'].startswith(p['ns']+'.') or p['ns'] in op or any(p['ns'].startswith(w+'.') or p['ns']==w for w in op)
    DEFK_=('def','abbrev','structure','inductive','class','theorem')
    while queue:
        x=queue.pop(); op=opened_of(x)
        for tk in toks(x['src']+'\n'+'\n'.join(c for s in x['scope'] for c in s['cmds'])):
            cands=[]
            for p in pool:
                if p['kind'] not in DEFK_ or not p.get('name') or p['id']==T['id']: continue
                if p['ns']=='' and p['name'] in CORE and p['kind'] in('inductive','structure','class'): continue
                if '.' not in tk:
                    # plain identifier: its written name, or fully qualified within namespace
                    if (p['name']==tk or (p['ns'] and p['q']==tk)) and visible(p,x,op): cands.append(p)
                    elif p['name'].endswith('.'+tk) and False: pass
                else:
                    if p['q']==tk or p['q'].endswith('.'+tk) or p['name']==tk or tk.endswith('.'+p['name']):
                        if visible(p,x,op) or p['q']==tk: cands.append(p)
                    elif '.' in p['name'] and gen_last(p['name'])==gen_last(tk) and visible(p,x,op): cands.append(p)   # field notation n.plus
            byq={}
            for p in cands: byq[p['q']]=p
            for p in byq.values():
                if p['id'] not in inc and p['id']!=x['id'] and order.get(p['id'],-1)<order.get(x['id'],10**9):
                    inc[p['id']]=p; queue.append(p)
    # namespaces opened by the closure
    opened=set()
    for x in list(inc.values()):
        for s in [x['src']]+[c for sc in x['scope'] for c in sc['cmds']]:
            for m in re.finditer(r'(?m)^\s*open\s+([^\n]*?)(?:\s+in\s*)?$',s):
                for w in re.findall(r'[A-Za-z_][\w.]*',m.group(1).split('(')[0]): opened.add(w)
    for p in pool:
        if p['kind'] in('instance','deriving') or not p.get('name'): continue
        if any(p['ns']==w or p['ns'].startswith(w+'.') for w in opened if w not in ('Nat','List','Option','String','Array','Int')):
            if p['id'] not in inc: inc[p['id']]=p; queue.append(p)
    # instances / deriving
    names={p['name'] for p in inc.values() if p.get('name')}
    allnames={p['name'] for p in pool if p.get('name')}
    changed=True
    while changed:
        changed=False
        names={last(p['name']) for p in inc.values() if p.get('name')}
        for p in pool:
            if p['id'] in inc or p['kind'] not in ('instance','deriving'): continue
            h=toks(header(p['src']))
            h={last(a) for a in h}
            local=h&{last(a) for a in allnames}
            if local and local<=names:
                # instance of included things; its body deps
                inc[p['id']]=p; queue.append(p); changed=True
        while queue:
            x=queue.pop()
            for tk in toks(x['src']):
                cands=[p for p in pool if p.get('name') and p['kind'] not in('instance','deriving') and last(p['name'])==last(tk) and p['id'] not in inc and p['id']!=T['id']]
                byq={}
                for p in cands: byq[p['q']]=p
                for p in byq.values():
                    if order.get(p['id'],-1)<order.get(x['id'],10**9):
                        inc[p['id']]=p; queue.append(p); changed=True
    items=sorted(inc.values(),key=lambda d:(files.index(d['file']),d['line']))
    # one definition per qualified name (nearest wins) except target
    seen={}
    for d in items:
        if d.get('name') and d['kind'] in('def','abbrev','structure','inductive','class'):
            seen[d['q']]=d
    items=[d for d in items if not d.get('name') or d['kind'] not in('def','abbrev','structure','inductive','class') or seen[d['q']] is d or d is T]
    return items
def emit(d, extra=''):
    d=dict(d); d['src']=re.sub(r'(?m)^(open|set_option)\s+[^\n]*(SubVerso|ExampleSupport|guard_msgs)[^\n]*\bin\s*\n','',d['src'])
    out=[]; ends=[]
    for s in d['scope']:
        if s['kind']=='namespace': out.append('namespace '+s['name']); ends.append('end '+s['name'])
        elif s['kind']=='section': out.append('section'); ends.append('end')
        out+= [c for c in s['cmds'] if not re.search(r'SubVerso|ExampleSupport|guard_msgs|Lean\.|linter',c)]
    return '\n'.join(['section']+out+[d['src']]+([extra] if extra else [])+['end']*(1)+list(reversed(ends))[:0]) if False else '\n'.join(['section']+out+[d['src']]+([extra] if extra else [])+list(reversed(ends))+['end'])
HEAD="""import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
"""
def gen(T, cmd):
    items=closure(T)
    parts=[HEAD+'namespace Proven.Frontx.Run\n']
    marks=[]
    for d in items:
        if d is T: continue
        parts.append(f"-- ctx {d['file']}:{d['line']}-{d['end']}\n"+emit(d))
    parts.append('#eval IO.println "@@MARK@@"')
    parts.append(f"-- TARGET {T['file']}:{T['line']}-{T['end']}\n"+emit(T,cmd))
    parts.append('end Proven.Frontx.Run\n')
    return '\n\n'.join(parts)
if __name__=='__main__':
    f,l=sys.argv[1],int(sys.argv[2])
    T=[d for d in D if d['file']==f and d['line']==l][0]
    print(gen(T,sys.argv[3] if len(sys.argv)>3 else ''))
