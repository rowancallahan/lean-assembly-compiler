#!/usr/bin/env python3
# PATHS are hard-coded at the top (/tmp/claude-0/...): nanorun, B2.bin, lean 4.34.1, LEAN_PATH with Nano.Main.Prelude olean. Edit before use. UNPROVEN test glue.
"""diff.py DIR: for each DIR/*.lean (a nano program, optional header `-- input (hex): ..`), run real nano (B2.bin via nanorun)
and real Lean 4.34.1 (Nano.Main.Prelude + `#eval m input`); print one verdict line per case."""
import os, re, subprocess, sys, tempfile, glob
NR="/tmp/claude-0/nr/nanorun"; B2="/tmp/claude-0/wt/Testing/nano/v2self/B2.bin"
LEAN="/tmp/claude-0/lean/lean-4.34.1-linux/bin/lean"; env=dict(os.environ, LEAN_PATH="/tmp/claude-0/ol")
def run(cmd, **k): return subprocess.run(cmd, capture_output=True, text=True, timeout=600, **k)
def nano(src, inp):
    with tempfile.TemporaryDirectory() as t:
        open(f"{t}/p.lean","w",newline="").write(src); open(f"{t}/in","wb").write(inp)
        run([NR,B2,f"{t}/p.lean",f"{t}/p.bin","120"])
        if not os.path.exists(f"{t}/p.bin") or os.path.getsize(f"{t}/p.bin")==0: return "REJECT"
        r=run([NR,f"{t}/p.bin",f"{t}/in",f"{t}/out"]); 
        return "ACCEPT out="+(open(f"{t}/out","rb").read().hex() if os.path.exists(f"{t}/out") else "?")+" ["+r.stderr.strip().replace("nanorun: ","")[:40]+"]"
def lean(src, inp):
    with tempfile.TemporaryDirectory() as t:
        l=", ".join(str(b) for b in inp)
        open(f"{t}/p.lean","w",newline="").write("import Nano.Main.Prelude\n"+src+f"\n#eval m [{l}]\n")
        r=run([LEAN,f"{t}/p.lean"],env=env); o=r.stdout+r.stderr
        if r.returncode!=0 or "error" in o:
            e=[x for x in o.split("\n") if "error" in x]
            return "REJECT "+(e[0].split("error:")[-1].strip()[:70] if e else "?")
        m=re.search(r"\[([0-9, ]*)\]\s*$",o.strip()); 
        return "ACCEPT out="+bytes(int(x) for x in m.group(1).split(",") if x.strip()).hex() if m else "ACCEPT ?"+o[:60]
for f in sorted(glob.glob(sys.argv[1]+"/*.lean")):
    s=open(f,newline="").read(); m=re.search(r"^-- input \(hex\): *(.*)$",s,re.M); inp=bytes.fromhex(m.group(1).replace(" ","")) if m else b""
    n,l=nano(s,inp),lean(s,inp)
    st="same" if n.split(" ")[0]==l.split(" ")[0] and (n.startswith("REJECT") or n.split(" ")[1]==l.split(" ")[1]) else ("NANO-ACCEPTS-LEAN-REJECTS" if n.startswith("ACC") and l.startswith("REJ") else ("RESULT-DIFF" if n.startswith("ACC") else "nano-stricter"))
    print(f"{os.path.basename(f)[:-5]:28} {st:26} nano: {n:34} lean: {l}")
