#!/usr/bin/env python3
"""ld.py COMPILER.bin DIR [ARM=1]: differential nano vs real Lean 4.34.1. For each DIR/*.lean (nano program; optional header
`-- input (hex): ..`): nano compile (nanorun) + run; Lean = `import Nano.Main.Prelude` + src + `#eval m input`.
Prints only divergences (NANO-ACCEPTS-LEAN-REJECTS / RESULT-DIFF / ARM-DIFF) + a tally. Env: NR, LEAN, LP (oleans), ARMC (native_arm dir). UNPROVEN glue."""
import os, re, subprocess, sys, tempfile, glob, collections
from multiprocessing import Pool
E=os.environ; NR=E.get("NR","/tmp/claude-0/nr/nanorun"); LEAN=E.get("LEAN","/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"); LP=E.get("LP","/tmp/claude-0/ol")
ARMC=E.get("ARMC","/home/user/lean-assembly-compiler/Testing/nano/v2self/native_arm")
CC=sys.argv[1]; DIR=sys.argv[2]; ARM=len(sys.argv)>3 or E.get("ARM")=="1"
def run(cmd, **k):
    return subprocess.run(cmd, capture_output=True, text=True, timeout=int(E.get('TO','25')), **k)
def nano(src, inp):
    with tempfile.TemporaryDirectory() as t:
        open(f"{t}/p.lean","w",newline="").write(re.sub(r"^-- input \(hex\):.*\n","",src)); open(f"{t}/in","wb").write(inp)
        try: run([NR,CC,f"{t}/p.lean",f"{t}/p.bin","120"])
        except subprocess.TimeoutExpired: return "TIMEOUT"
        if not os.path.exists(f"{t}/p.bin") or os.path.getsize(f"{t}/p.bin")==0: return "REJECT"
        try: r=run([NR,f"{t}/p.bin",f"{t}/in",f"{t}/out"])
        except subprocess.TimeoutExpired: return "TIMEOUT"
        o="ACCEPT out="+(open(f"{t}/out","rb").read().hex() if os.path.exists(f"{t}/out") else "?")
        return o
def arm(src, inp):
    """native AArch64 (GA_arm.bin front end + GenArm) under qemu-aarch64: REJECT | ACCEPT out=hex"""
    with tempfile.TemporaryDirectory() as t:
        open(f"{t}/s","w",newline="").write(re.sub(r"^--.*\n","",src,flags=re.M)); open(f"{t}/in","wb").write(inp)
        a=subprocess.run(["bash",f"{ARMC}/compile.sh",f"{t}/s"],capture_output=True,timeout=int(E.get('TO','25')))
        if a.returncode or not a.stdout: return "REJECT"
        open(f"{t}/a64","wb").write(a.stdout)
        subprocess.run(["bash",f"{ARMC}/run.sh",f"{t}/a64",f"{t}/in",f"{t}/out"],capture_output=True,timeout=int(E.get('TO','25')))
        return "ACCEPT out="+(open(f"{t}/out","rb").read().hex() if os.path.exists(f"{t}/out") else "?")
def lean(src, inp):
    with tempfile.TemporaryDirectory() as t:
        l=", ".join(str(b) for b in inp)
        open(f"{t}/p.lean","w",newline="").write("import Nano.Main.Prelude\n"+src+f"\n#eval m [{l}]\n")
        try: r=run([LEAN,f"{t}/p.lean"],env=dict(os.environ,LEAN_PATH=LP))
        except subprocess.TimeoutExpired: return "TIMEOUT"
        o=r.stdout+r.stderr
        if r.returncode!=0 or "error" in o:
            e=[x for x in o.split("\n") if "error" in x]
            return "REJECT "+(e[0].split("error:")[-1].strip()[:70] if e else "?")
        m=re.search(r"\[([0-9, ]*)\]\s*$",o.strip())
        return "ACCEPT out="+bytes(int(x) for x in m.group(1).split(",") if x.strip()).hex() if m else "ACCEPT ?"+o[:60]
def one(f):
    s=open(f,newline="").read(); m=re.search(r"^-- input \(hex\): *(.*)$",s,re.M); inp=bytes.fromhex(m.group(1).replace(" ","")) if m else b""
    n=nano(s,inp)
    if n.startswith("REJECT") or n=="TIMEOUT": return f,"nano-stricter" if n!="TIMEOUT" else "TIMEOUT",n,""
    l=lean(s,inp)
    if l=="TIMEOUT": return f,"TIMEOUT",n,l
    if l.startswith("REJ"): return f,"NANO-ACCEPTS-LEAN-REJECTS",n,l
    if n.split()[1]!=l.split()[1]: return f,"RESULT-DIFF",n,l
    if "ARM-DIFF" in n or "ARM=REJECT" in n: return f,"ARM-DIFF",n,l
    return f,"same",n,l
if __name__=="__main__":
    c=collections.Counter()
    with Pool(int(E.get("J","8"))) as p:
        for f,st,n,l in p.imap_unordered(one,sorted(glob.glob(DIR+"/*.lean"))):
            c[st]+=1
            if st not in("same","nano-stricter"): print(f"{os.path.basename(f)[:-5]:28} {st:26} nano: {n:34} lean: {l}",flush=True)
    print("TALLY",dict(c))
