import subprocess,os,tempfile
from multiprocessing import Pool
ks=open("/tmp/claude-0/lr/h/kw.txt").read().split("\n")
forms={"let":"def m (x : UInt64) : UInt64 := let {k} := x; {k}",
       "param":"def m ({k} : UInt64) : UInt64 := {k}",
       "defname":"def {k} (x : UInt64) : UInt64 := x\ndef m (x : UInt64) : UInt64 := {k} x"}
def t(a):
    k,f=a
    with tempfile.TemporaryDirectory() as d:
        open(d+"/a.lean","w").write("import Nano.Main.Prelude\n"+forms[f].format(k=k)+"\n")
        r=subprocess.run(["lean",d+"/a.lean"],capture_output=True,text=True)
        return (k,f,"error" in r.stdout+r.stderr)
if __name__=="__main__":
    with Pool(8) as p: res=p.map(t,[(k,f) for k in ks for f in forms])
    bad={f:sorted(k for k,ff,b in res if b and ff==f) for f in forms}
    for f in forms: print(f,len(bad[f]),bad[f])
    open("reserved.txt","w").write("\n".join(sorted(set(sum(bad.values(),[])))))
