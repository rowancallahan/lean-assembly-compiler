import json, re, os, subprocess, sys, concurrent.futures as cf
sys.path.insert(0,os.path.dirname(__file__))
import gen
S=gen.S
W=S+'/work'; RUNS=S+'/runs'; os.makedirs(RUNS,exist_ok=True)
PATHENV=dict(os.environ); PATHENV['PATH']=os.environ['LEAN_BIN']+':'+PATHENV['PATH']
IO=re.compile(r'\bIO\b|IO\.|\bEIO\b|\bBaseIO\b|println|getLine|stdin|stdout|stderr|\bmain\b|FS\.|IO\.FS|\bpanic|ExceptT[^\n]*IO|StateT[^\n]*IO|ReaderT[^\n]*IO|Handle')
def sig_has_params(src):
    h=gen.header(src)
    return bool(re.search(r'[({\[]',h.split(':')[0] if ':' in h else h)) or '→' in h or '->' in h
def inst(d):
    h=re.split(r'\bwhere\b|:=|\n',d['src'],1)[0]
    h=re.sub(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|partial|unsafe|noncomputable)\s+)*(inductive|structure|class)\s+\S+','',h)
    n=sum(len(re.findall(r"[\w']+",m.split(':')[0])) for m in re.findall(r'[({]([^)}]*:[^)}]*)[)}]',h))
    return ' '.join([ (d['q'] or d['name']) ]+['Nat']*n) if n==0 else '('+' '.join([d['q'] or d['name']]+['Nat']*n)+')'
def variants(T):
    n=T['q'] if T['q'] else T['name']
    hdr=gen.header(T['src'])
    items=gen.closure(T)
    inds=[d for d in items if d['kind'] in('inductive','structure') and d is not T and re.search(r'(?<![\w.])'+re.escape(gen.last(d['name']))+r'(?![\w])',hdr)]
    v=[('compile',f'frontx_compile {n}')]
    if re.search(r'\bList\b',hdr):
        for k in range(3):
            v.append((f'view{k}',f'frontx_view {n}\nfrontx_compile {n}.view from {n}.view.eq measure fun B i'+' _'*k+' => B.size - i'))
        m=re.search(r':=\s*([\w.]+)',T['src'])
        if m and m.group(1)!=n:
            c=m.group(1)
            for k in range(3):
                v.append((f'helper{k}',f'frontx_view {c}\nfrontx_compile {c}.view from {c}.view.eq measure fun B i'+' _'*k+' => B.size - i'))
    if inds:
        pre='\n'.join(f'frontx_ind_type TT{T["id"]}_{a} := {inst(d)}' for a,d in enumerate(inds[:2]))
        v.append(('ind',pre+f'\nfrontx_ind {n} on TT{T["id"]}_0'+(f' using TT{T["id"]}_1' if len(inds)>1 else '')))
    if re.search(r'Array|ByteArray',hdr):
        v.append(('wa',f'wa_compile {n}'))
    return v
def runone(name, text):
    p=f'{RUNS}/{name}.lean'
    open(p,'w').write(text)
    try:
        r=subprocess.run(['lake','env','lean','--tstack=400000',p],cwd=W,env=PATHENV,capture_output=True,text=True,timeout=int(os.environ.get('TMO','400')))
        return r.stdout+r.stderr+f'\nEXIT {r.returncode}\n'
    except subprocess.TimeoutExpired:
        return 'TIMEOUT'
def analyse(text,out):
    lines=text.split('\n')
    tl=[i+1 for i,l in enumerate(lines) if l.startswith('-- TARGET')][0]
    pre,_,post=out.partition('@@MARK@@')
    out=post
    errs=[]
    for m in re.finditer(r'^[^\n]*?\.lean:(\d+):(\d+): (error|warning)(?:\([^)]*\))?: (.*?)(?=\n[^\s][^\n]*?\.lean:\d+:\d+: |\Z)',out,re.S|re.M):
        errs.append((int(m.group(1)),m.group(3),m.group(4).strip()))
    ctx=[e for e in re.findall(r'error',pre)]
    tgt=errs
    return tl,ctx,tgt
def attempt(T):
    res={'file':T['file'],'line':T['line'],'end':T['end'],'name':T['q'] or T['name']}
    if out_of_scope(T): res['status']='skip'; return res
    for vn,cmd in variants(T):
        text=gen.gen(T,cmd+f"\n#check @{T['q'] or T['name']}")
        out=runone(f"{T['id']}_{vn}",text)
        tl,ctx,tgt=analyse(text,out)
        res.setdefault('tries',{})[vn]={'ctx_errors':len(ctx),'msgs':[ (a,b,c[:300]) for a,b,c in tgt][:4]}
        sig=re.findall(r'^\S.* : (.*)$',out,re.M)
        post=out.partition('@@MARK@@')[2]
        ok=bool(re.search(r'^(frontx[_a-z]*: .*|wa_compile.*)$',post,re.M)) and not any(b=='error' or 'sorry' in c for a,b,c in tgt) and 'PANIC' not in post and 'stack overflow' not in out.lower()
        res['tries'][vn]['exit']=out.rstrip().split('\n')[-1]
        res['tries'][vn]['okmsg']=[l[:200] for l in out.split('\n') if re.search(r'^frontx[_a-z]*:|wa_compile:|^frontx_ind',l)][:2]
        if vn=='compile': res['out']=out[-1500:] if False else ''
        if ok and 'TIMEOUT' not in out:
            res['status']='ok'; res['variant']=vn; return res
    res['status']='fail'; return res
def out_of_scope(T):
    if T['kind'] not in('def','abbrev') or not T.get('name'): return True
    if IO.search(T['src']): return True
    return False
if __name__=='__main__':
    sel=sys.argv[1] if len(sys.argv)>1 else 'all'
    ids=json.loads(sel) if sel!='all' else None
    todo=[d for d in gen.D if d['kind'] in('def','abbrev') and d.get('name')]
    if ids: todo=[d for d in todo if d['id'] in ids]
    with cf.ThreadPoolExecutor(int(os.environ.get('J','3'))) as ex:
        results=list(ex.map(attempt,todo))
    json.dump(results,open(S+'/results_'+(os.environ.get('TAG','x'))+'.json','w'),indent=1)
    from collections import Counter
    print(Counter(r['status'] for r in results))
