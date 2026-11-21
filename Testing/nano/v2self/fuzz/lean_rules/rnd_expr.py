import random,sys
random.seed(int(sys.argv[1])); N=int(sys.argv[2]); D="/tmp/claude-0/lr/rnd"
ops=["|||","&&&","+","-","*","<<<",">>>"]
def leaf():
    r=random.random()
    if r<0.5: return f"rd x {random.randint(0,3)}"
    if r<0.9: return str(random.choice([0,1,2,3,7,255,256,65535,4294967296,18446744073709551615,18446744073709551616,random.randint(0,99)]))
    return f"(rd x {random.randint(0,3)})"
def ex(d):
    if d==0 or random.random()<0.25: return leaf()
    r=random.random()
    if r<0.12: return f"(if {ex(d-1)} {random.choice(['==','<'])} {ex(d-1)} then {ex(d-1)} else {ex(d-1)})"
    o=random.choice(ops)
    a=ex(d-1)
    b=str(random.choice([0,1,2,63,64,65,100])) if o in("<<<",">>>") else ex(d-1)
    s=f"{a} {o} {b}"
    return f"({s})" if random.random()<0.5 else s
import os
for f in os.listdir(D): os.remove(f"{D}/{f}")
for i in range(N):
    open(f"{D}/r{i:03}.lean","w").write("-- input (hex): 05 f7 03 81\ndef m (x : List UInt8) : List UInt8 := put [] ("+ex(3)+")\n")
