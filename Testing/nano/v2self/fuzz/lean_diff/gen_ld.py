#!/usr/bin/env python3
"""gen_ld.py SEED N DIR: write N random nano-subset programs (families expr/let/match/loop/buf + token/layout/trivia mutations).
Edge numerals, shifts, truncated sub, literal-only trees, reserved words, comments/doc/attr/namespace. UNPROVEN test glue."""
import random, sys, os, re
R=random
EDGE=[0,1,2,3,7,63,64,65,127,128,255,256,257,65535,65536,2**31,2**32-1,2**32,2**32+1,2**63-1,2**63,2**63+1,2**64-2,2**64-1,2**64,2**64+1,2**65,10**20,R.randint(0,999)]
RES=[l.strip() for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)),"../lean_rules/lean_reserved_words.txt")) if l.strip() and not l.startswith("#")] if os.path.exists(os.path.join(os.path.dirname(os.path.abspath(__file__)),"../lean_rules/lean_reserved_words.txt")) else ["let","at","in","fun","do","by","from","Type","Prop","sorry","if","then","else","match","with","where"]
BIN=["|||","&&&","+","-","*"]
def lit(): 
    v=R.choice(EDGE); 
    return R.choice([str(v),str(v),str(v),hex(v) if R.random()<0.05 else str(v)])
class G:
    def __init__(s,vars_): s.vars=list(vars_); s.n=0
    def leaf(s):
        r=R.random()
        if s.vars and r<0.3: return R.choice(s.vars)
        if r<0.65: return f"rd x {R.randint(0,5)}"
        return lit()
    def ex(s,d):
        if d<=0 or R.random()<0.2: return s.leaf()
        r=R.random()
        if r<0.10:
            c=R.choice(["==","<"]); return f"(if {s.ex(d-1)} {c} {s.ex(d-1)} then {s.ex(d-1)} else {s.ex(d-1)})"
        if r<0.12 and SH: return f"({s.ex(d-1)} {R.choice(['<<<','>>>'])} {R.choice([0,1,2,31,32,63,64,65,100,128,130])})"
        if r<0.25:
            v=f"v{s.n}"; s.n+=1; e=s.ex(d-1); s.vars.append(v); b=s.ex(d-1); s.vars.pop()
            return f"(let {v} := {e}; {b})"
        if r<0.31:
            pats=R.sample(range(0,6),R.randint(1,3)) if R.random()<0.85 else [R.choice(EDGE) for _ in range(R.randint(1,3))]
            arms=" ".join(f"| {p} => {s.ex(d-1)}" for p in pats)
            return f"(match {s.ex(d-1)} with {arms} | _ => {s.ex(d-1)})"
        if r<0.35:
            return f"(let (a{s.n}, b{s.n}) := ({s.ex(d-1)}, {s.ex(d-1)}); a{s.n} {R.choice(BIN)} b{s.n})"
        o=R.choice(BIN); t=f"{s.ex(d-1)} {o} {s.ex(d-1)}"
        return f"({t})" if R.random()<0.6 else t
SH=True
HDR="def m (x : List UInt8) : List UInt8 := "
def rinput(): return bytes(R.choice([0,1,2,3,97,127,128,255,R.randint(0,255)]) for _ in range(R.randint(0,8)))
def p_expr(): return HDR+"put [] ("+G([]).ex(R.randint(1,4))+")\n"
def p_cmp(): # literal-heavy comparisons
    g=G([]); return HDR+f"put [] (if {g.ex(2)} {R.choice(['==','<'])} {g.ex(2)} then 1 else 2)\n"
def p_let(): 
    g=G([]); a=g.ex(2); g.vars=["a"]; b=g.ex(2); g.vars=["a","b"]
    use=R.choice([f"if a {R.choice(['==','<'])} b then 1 else 2",f"b {R.choice(BIN)} a",f"if {g.ex(1)} == b then a else b", "put_dummy"])
    if use=="put_dummy": use="a"
    return HDR+f"let a := {a}; let b := {b}; put [] ({use})\n"
def p_loop():
    fuel=R.choice(["len' x","0","1","3",str(R.choice(EDGE))]); g=G(["i","a"]); body=g.ex(2)
    st=R.choice(["0","1",lit()])
    return ("def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64\n  | 0, x, i, a => a\n  | n + 1, x, i, a => f n x (i + 1) ("+body+")\n"
            +HDR+f"put [] (f {fuel} x 0 {st})\n")
def p_buf():
    g=G(["i","a"]); k=lit()
    return ("def f : Nat → List UInt8 → Buf → UInt64 → Buf\n  | 0, x, b, i => b\n  | n + 1, x, b, i => f n x (bset (bpush b ("+g.ex(1)+f")) ({lit()}) ({g.ex(1)})) (i + 1)\n"
            +HDR+f"put [] (bget (f (len' x) x bnew 0) ({lit()}))\n")
def p_def():
    return f"def g (a : UInt64) (b : UInt64) : UInt64 := {G(['a','b']).ex(3)}\n"+HDR+f"put [] (g ({G([]).ex(2)}) ({G([]).ex(2)}))\n"
class L(G):
    def leaf(s): return lit() if R.random()<0.85 else (R.choice(s.vars) if s.vars else lit())
def p_lit():
    g=L([]); t=R.choice(["cmp","let","tup","match","arg"])
    if t=="cmp": b=f"if {g.ex(2)} {R.choice(['==','<'])} {g.ex(2)} then 1 else 2"
    elif t=="let": b=f"let a := {g.ex(2)}; if a {R.choice(['==','<'])} {lit()} then 1 else 2"
    elif t=="tup": b=f"let (a, b) := ({g.ex(2)}, {g.ex(1)}); if a {R.choice(['==','<'])} b then 1 else 2"
    elif t=="match": b=f"match {g.ex(2)} with | {R.choice(EDGE)} => 1 | {R.choice(EDGE)} => 3 | _ => 2"
    else: b=g.ex(3)
    return HDR+"put [] ("+b+")\n"
FAM=[p_lit,p_lit,p_lit,p_expr,p_expr,p_cmp,p_cmp,p_let,p_let,p_loop,p_buf,p_def]
# ---- mutations
TOK=re.compile(r"[A-Za-z_][A-Za-z0-9_']*|\d+|:=|=>|<<<|>>>|\|\|\||&&&|==|[^\sA-Za-z0-9_]")
WS=[" ","  ","\n","\n  ","\n    ","\n\t"," /- c -/ "," -- c\n","\r\n","\n\n","  /-- d -/ "," /-! m -/ "]
def mut(src):
    toks=TOK.findall(src); ws=re.findall(r"\s+",src)
    for _ in range(R.randint(1,3)):
        k=R.random(); i=R.randrange(len(toks))
        if k<0.25: toks.insert(i,R.choice(RES))
        elif k<0.45: toks[i]=R.choice(RES+["_","'a'","'x","x'","id","ite","<-","<|","$","a.b","⟨","!","?"])
        elif k<0.6: del toks[i]
        elif k<0.7 and len(toks)>2: j=R.randrange(len(toks)); toks[i],toks[j]=toks[j],toks[i]
        elif k<0.8: toks.insert(i,R.choice(["--","<-","<","-","|","@[inline]","private","/-- d -/","namespace A","end A","open Nat","(",")",";",","]))
        else: toks[i]=str(R.choice(EDGE))
    out=""
    for t in toks:
        out+=t+(R.choice(WS) if R.random()<0.3 else " ")
    return out
def layoutmut(src):
    toks=src.replace("\n"," \n ").split(" ")
    return re.sub(r"[ ]+(?=(then|else|with|\|\s|=>|:=))",lambda m:R.choice([" ","\n","\n  ","\n    "]),src) if R.random()<0.7 else re.sub(r"\n  ",lambda m:R.choice(["\n","\n ","\n  ","\n   ","\n    "]),src)
def wrap(src):
    k=R.random()
    pre=R.choice(["@[inline] ","@[noinline] ","private ","/-- doc -/ ","@[inline] private ","/-- d -/ @[inline] ","@[reducible] ","@[simp] ","@[bogus] ","@[implemented_by id] ","protected ","unsafe ","partial ","noncomputable ","private @[inline] ","@[inline]\n","/-- d -/\n"])
    src=re.sub(r"^def",pre+"def",src,count=1,flags=re.M) if R.random()<0.6 else src
    if k<0.15: src="namespace A\n"+src+"end A\n"
    elif k<0.25: src="namespace A\n"+src+"end B\n"
    elif k<0.32: src="open Nat\n"+src
    elif k<0.38: src="section\n"+src+"end\n"
    elif k<0.42: src="namespace A.B\n"+src+"end A.B\n"
    elif k<0.46: src=src+"end\n"
    return src
def gen():
    s=R.choice(FAM)()
    r=R.random()
    if r<0.35: s=mut(s)
    elif r<0.5: s=layoutmut(s)
    elif r<0.65: s=wrap(s)
    elif r<0.7: s=wrap(mut(s))
    return s
if __name__=="__main__":
    R.seed(int(sys.argv[1])); SH=R.random()<0.3; N=int(sys.argv[2]); D=sys.argv[3]; os.makedirs(D,exist_ok=True)
    for i in range(N):
        s=gen(); inp=rinput()
        open(f"{D}/g{sys.argv[1]}_{i:04}.lean","w",newline="").write(f"-- input (hex): {inp.hex(' ')}\n"+s)
