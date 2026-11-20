#!/usr/bin/env python3
"""uniform_est.py RV_CODE RV2ARM_CODE INPUT: estimate a UNIFORM-block A64 back end (K words per J instruction, K = 2, 3, 4)
from rv2arm's per-instruction sequences (non-PAD words of each 4-word block) and the RISC-V run's per-PC execution
counts (QEMU exec log).  Pads are counted as executed unless the block ends in an unconditional jump.  Blocks over 2
words are listed (they are the stubs / start code; movn makes them fit).  Model, not an implemented back end."""
import os,sys,subprocess,collections,struct
rv,tr,inp=sys.argv[1:4]
PAD=0x91000210  # add x16,x16,#0
p=subprocess.Popen(['qemu-riscv64','-one-insn-per-tb','-d','nochain,exec','-D','/dev/stdout',os.environ.get('NA', '/tmp/claude-0/na') + '/shim_rv',rv],stdin=open(inp,'rb'),stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
c=collections.Counter(); base=None
for l in p.stdout:
    if not l.startswith(b'Trace'): continue
    pc=int(l.split(b'[')[1].split(b'/')[1],16)
    if pc<1<<24: continue
    c[pc]+=1
g=collections.Counter();
for k,v in c.items(): g[k>>24]+=v
hi=g.most_common(1)[0][0]; base=min(k for k in c if k>>24==hi and k%4096==0); c=collections.Counter({(k-base)//4:v for k,v in c.items() if 0<=k-base<4*(len(open(rv,'rb').read())//4)})
w=open(tr,'rb').read(); W=struct.unpack('<%dI'%(len(w)//4),w)
nb=len(W)//4; real=[];jump=[]
for i in range(nb):
    b=[x for x in W[4*i:4*i+4] if x!=PAD]; real.append(len(b))
    last=b[-1] if b else 0
    jump.append(b!=[] and ((last>>26) in (5,0x25) or (last&0xFFFFFC1F)==0xD61F0000))
nrv=len(open(rv,'rb').read())//4
assert nb==nrv
K=max(real); hist=collections.Counter(real)
dynrv=sum(c.values())
for k in [2,3,4]:
    s=k*nb; d=sum(n*((min(real[i],k) if jump[i] else k)) for i,n in c.items())
    print(f"K={k} static {s} ({s/nrv:.2f}x rv) dyn {d} ({d/dynrv:.2f}x rv)")
dv=sum(n*real[i] for i,n in c.items())
print("rv2arm real-word hist",dict(hist),"dyn real words",dv,f"({dv/dynrv:.2f}x)")

print('blocks over 2 words at RV word', [i for i in range(nb) if real[i]>2], 'executed', sum(c[i] for i in range(nb) if real[i]>2))
