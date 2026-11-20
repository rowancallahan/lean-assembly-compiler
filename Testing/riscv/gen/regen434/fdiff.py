import sys,re,os,difflib
def blocks(d):
    B={}
    for f in os.listdir(d):
        s=open(os.path.join(d,f)).read()
        s=re.sub(r'/--.*?-/','',s,flags=re.S); s=re.sub(r'--[^\n]*','',s)
        parts=re.split(r'\n(?=(?:noncomputable |partial |private |@\[[^\]]*\]\s*)*(?:def|abbrev|theorem|instance|termination_by|decreasing_by|end|namespace|section|mutual|structure|inductive|open)\b)',s)
        for p in parts:
            m=re.match(r'(?:noncomputable |partial |private |@\[[^\]]*\]\s*)*(?:def|abbrev)\s+(\S+)',p)
            if m: B[m.group(1)]=p
    return B
def toks(s): return re.findall(r'"(?:[^"\\]|\\.)*"|[A-Za-z_][\w.\'!?]*|\d\w*|\S',s)
A=blocks(sys.argv[1]); Bb=blocks(sys.argv[2])
for n in open(sys.argv[3]).read().split():
    n=n.replace('LeanRV64D.Functions.','').replace('LeanRV64D.','')
    a,b=A.get(n),Bb.get(n)
    if a is None or b is None: print(f"## {n}: block missing old={a is not None} new={b is not None}"); continue
    ta,tb=toks(a),toks(b)
    ta=['sail_assert' if t=='assert' else t for t in ta]
    sm=difflib.SequenceMatcher(None,ta,tb,autojunk=False)
    hs=[(' '.join(ta[i1:i2]),' '.join(tb[j1:j2])) for op,i1,i2,j1,j2 in sm.get_opcodes() if op!='equal']
    print(f"## {n}: {len(hs)} hunks")
    for x,y in hs[:6]: print(f"   - {x[:150]!r}\n   + {y[:150]!r}")
