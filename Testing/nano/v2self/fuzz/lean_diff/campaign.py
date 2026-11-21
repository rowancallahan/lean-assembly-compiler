#!/usr/bin/env python3
"""campaign.py NAME COMPILER.bin SEED0 [N=300]: loop forever: generate N programs, run nano vs Lean, minimize+classify each
divergence, append to LOG (jsonl), keep tally. Stops when file STOP exists. UNPROVEN test glue."""
import os, sys, json, glob, random, shutil, collections, time, tempfile, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
name, cc, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]); N=int(sys.argv[4]) if len(sys.argv)>4 else 300
sys.argv=[sys.argv[0],cc,"/nonexistent"]
import ld, mini, gen_ld
from multiprocessing import Pool
OUT=os.environ.get("OUT","/tmp/claude-0/camp"); os.makedirs(OUT,exist_ok=True)
LOG=f"{OUT}/{name}.jsonl"
def split(src):
    m=re.search(r"^-- input \(hex\): *(.*)\n",src); return (bytes.fromhex(m.group(1).replace(" ","")) if m else b""), re.sub(r"^-- input \(hex\):.*\n","",src)
def verdict(body, inp):
    n=ld.nano(body,inp)
    if n.startswith("REJECT") or n=="TIMEOUT": return "x",n,""
    l=ld.lean(body,inp)
    if l=="TIMEOUT": return "x",n,l
    if l.startswith("REJ"): return "NANO-ACCEPTS-LEAN-REJECTS",n,l
    if n.split()[1]!=l.split()[1]: return "RESULT-DIFF",n,l
    return "same",n,l
def work(f):
    full=open(f,newline="").read(); inp,body=split(full)
    st,n,l=verdict(body,inp)
    if os.environ.get("ARMC") and st in("same","x") and n!="TIMEOUT" and random.random()<float(os.environ.get("ARMP","0.3")):
        a=ld.arm(body,inp)
        if a.startswith("ACCEPT"):
            if st=="same" and a!=n: return "ARM-RESULT-DIFF",dict(file=f,kind="ARM-RESULT-DIFF",cls="ARM",min=body,inp=inp.hex(),nano=n,lean=a,orig=body)
            if st=="x":  # RV rejected, ARM accepts: the invariant applies to ARM too
                l2=ld.lean(body,inp)
                if l2.startswith("REJ") or (l2.startswith("ACC") and l2!=a): return "ARM-ONLY-"+("REJ" if l2.startswith("REJ") else "DIFF"),dict(file=f,kind="ARM-ONLY",cls="ARM",min=body,inp=inp.hex(),nano=a,lean=l2[:120],orig=body)
        elif st=="same": return "arm-stricter",None
    if st in("x","same"): return st,None
    key=lambda l: re.sub(r"[^a-zA-Z' ]","",l.split("error")[-1])[:25]
    def pred(b): 
        s2,n2,l2=verdict(b,inp); return s2==st and (st=="RESULT-DIFF" or key(l2)==key(l))
    m=mini.ddmin(body,pred); s2,n2,l2=verdict(m,inp)
    return st,dict(file=f,kind=st,cls=mini.classify(m,n2,l2),min=m,inp=inp.hex(),nano=n2,lean=l2[:120],orig=body)
if __name__=="__main__":
    tally=collections.Counter(); seen=set(); t0=time.time(); it=0
    while not os.path.exists(f"{OUT}/STOP"):
        d=f"{OUT}/{name}_cases"; shutil.rmtree(d,ignore_errors=True); os.makedirs(d)
        import subprocess; subprocess.run([sys.executable,os.path.join(os.path.dirname(os.path.abspath(__file__)),"gen_ld.py"),str(seed),str(N),d],check=True); seed+=1
        with Pool(int(os.environ.get("J","3"))) as p:
            for st,r in p.imap_unordered(work,sorted(glob.glob(d+"/*.lean"))):
                tally[st]+=1
                if r:
                    sig=(r["cls"],re.sub(r"\d+","N",r["min"]).strip()); tally["cls:"+r["cls"]]+=1
                    if sig in seen: continue
                    seen.add(sig); open(LOG,"a").write(json.dumps(r)+"\n")
        it+=1; open(f"{OUT}/{name}.tally","w").write(f"{name} iters={it} seed={seed} t={int(time.time()-t0)}s "+json.dumps(dict(tally))+"\n")
