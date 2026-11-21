#!/usr/bin/env python3
"""Token/construct inventory of the stripped C source (the self-language S). usage: inventory.py"""
import re,collections,glob
txt=""
for f in ["Base","Asm","Expand","Lex","Inl","Parse","Main"]:
    inC=False
    for l in open(f"Legacy/Nano/V2Self/Legacy/C/{f}.lean").read().split("\n"):
        if inC:
            if "-/" in l: inC=False
        elif l.startswith("/-"):
            if "-/" not in l: inC=True
        elif l.startswith(("import","--","namespace","end ")): pass
        else: txt+=l+"\n"
tok=re.findall(r"[A-Za-z_][A-Za-z_0-9']*|\d+|:=|=>|≤|≠|==|<<<|>>>|&&&|&&|\|\|\||\|\||<|>|\+|-|\*|/|%|\(|\)|,|;|:|→|×|<<<|>>>|\S",txt)
c=collections.Counter()
kw={"def","let","if","then","else","UInt64","Nat","Buf","List","UInt8"}
for t in tok:
    if t in kw or not re.match(r"[A-Za-z_\d]",t): c[t]+=1
c["numeral"]=sum(1 for t in tok if t.isdigit())
for k in ["rd","len","put","len'","bnew","bsize","bget","bset","bpush"]: c["prim:"+k]=tok.count(k)
c["defs"]=len(re.findall(r"^def ",txt,re.M))
c["pattern-arms |"]=len(re.findall(r"^\s*\| ",txt,re.M))
c["let (tuple pattern)"]=len(re.findall(r"let \(",txt))
c["tuple literal (a, b, ...)"]=len(re.findall(r"\(\w+, ",txt))
c["tokens total"]=len(tok)
for k,v in sorted(c.items(),key=lambda x:-x[1]): print(f"{v:6d}  {k}")
