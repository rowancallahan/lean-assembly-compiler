#!/usr/bin/env python3
"""Mutation sanity for the fuzz harnesses: write a copy of a case file with a deliberate error.
usage: fuzz_mutate.py {word|exp} IN OUT
 word: in the first program flip an immediate/register bit of every 5th code word (blk/var8 files: `words`; triple files: `rv`)
 exp : make the expected values of the first program / case wrong (`e=`, `ev=`, `eb=`, or the last field of `t` lines)"""
import sys
mode, src, dst = sys.argv[1:4]
out = []; seen = 0; done_exp = False
for l in open(src):
    k, _, r = l.rstrip("\n").partition(" ")
    if k in ("prog", "case"): seen += 1
    first = seen <= 1 or mode == "exp"   # wrong expected values: every program; wrong word: first program only
    if mode == "word" and first and k in ("words", "rv"):
        ws = r.split(); ws = [("%08x" % (int(w, 16) ^ 0x00100000)) if i % 5 == 2 else w for i, w in enumerate(ws)]
        l = f"{k} {' '.join(ws)}\n"
    if mode == "exp" and k in ("in", "t") and (k == "t" or True):
        if k == "t":
            f = r.split(); f[-1] = "%x" % (int(f[-1], 16) ^ 1); l = f"t {' '.join(f)}\n"
        else:
            toks = r.split(); new = []
            for t in toks:
                a, _, v = t.partition("=")
                if a == "e" and v != "-": v = v[:-1] + ("%x" % (int(v[-1], 16) ^ 1))
                elif a == "ev": vs = v.split(","); i = next(j for j, x in enumerate(vs) if x != "?"); vs[i] = str(int(vs[i]) ^ 1); v = ",".join(vs)
                elif a == "eb": bs = v.split(":"); i = next((j for j, x in enumerate(bs) if x not in ("-", "")), None); 
                if a == "eb" and i is not None: bs[i] = "%02x" % (int(bs[i][:2], 16) ^ 1) + bs[i][2:]; v = ":".join(bs)
                new.append(f"{a}={v}" if v is not None and _ else t)
            l = f"in {' '.join(new)}\n"
    out.append(l)
open(dst, "w").writelines(out)
