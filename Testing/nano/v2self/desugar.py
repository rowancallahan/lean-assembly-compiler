#!/usr/bin/env python3
"""Rewrite `if COND then` conditions with && || ≤ ≠ into S1 form (only == and < in the atoms, nested ifs yielding 0/1):
  a ≤ b -> (if b < a then k0 else k1)   a ≠ b -> (if a == b then k0 else k1)
  A && B -> (if A == 1 then B else 0)   A || B -> (if A == 1 then 1 else B)   cond -> `if E == 1 then`
Conditions that are already one `==`/`<` atom are left alone.  usage: desugar.py FILE... (in place; comment blocks untouched)"""
import re, sys
TOK = re.compile(r"\s+|[A-Za-z_][A-Za-z_0-9']*|\d+|:=|=>|≤|≠|==|<<<|>>>|&&&|&&|\|\|\||\|\||[-+*<()|,;:→×\[\]]|.")
def toks(s): return [t for t in TOK.findall(s)]
def split_top(ts, op):
    out, cur, d = [], [], 0
    for t in ts:
        if t == "(": d += 1
        if t == ")": d -= 1
        if t == op and d == 0: out.append(cur); cur = []
        else: cur.append(t)
    out.append(cur); return out
def strip_paren(ts):
    ts = [t for t in ts]
    while ts and ts[0].isspace(): ts = ts[1:]
    while ts and ts[-1].isspace(): ts = ts[:-1]
    if ts and ts[0] == "(":
        d = 0
        for i, t in enumerate(ts):
            if t == "(": d += 1
            if t == ")":
                d -= 1
                if d == 0: return strip_paren(ts[1:-1]) if i == len(ts) - 1 else ts
    return ts
J = lambda ts: "".join(ts).strip()
def cond(ts, lets):
    """append let-bindings (0/1 words, eager: all atoms are pure and total) and return the name of the result"""
    ts = strip_paren(ts)
    def fresh(e):
        CNT[0] += 1; v = f"v{CNT[0]}"; lets.append(f"let {v} := {e};"); return v
    for op, mk in (("||", "{} ||| {}"), ("&&", "{} * {}")):
        parts = split_top(ts, op)
        if len(parts) > 1:
            r = cond(parts[0], lets)
            for q in parts[1:]: r = fresh(mk.format(r, cond(q, lets)))
            return r
    for op in ["≤", "≠", "==", "<"]:
        parts = split_top(ts, op)
        if len(parts) == 2:
            a, b = J(parts[0]), J(parts[1])
            if op == "≤": return fresh(f"(if {b} < {a} then k0 else k1)")
            if op == "≠": return fresh(f"(if {a} == {b} then k0 else k1)")
            return fresh(f"(if {a} {op} {b} then k1 else k0)")
    raise Exception("atom without comparison: " + J(ts))
def simple(ts):
    ts = strip_paren(ts)
    if any(t in ("&&", "||", "≤", "≠") for t in ts): return False
    return True
CNT = [99]
def rewrite(s):
    ts = toks(s); out = []; i = 0
    while i < len(ts):
        if ts[i] == "if":
            d = 0; j = i + 1
            while not (ts[j] == "then" and d == 0):
                if ts[j] == "(": d += 1
                if ts[j] == ")": d -= 1
                j += 1
            c = ts[i + 1:j]
            if simple(c): out.append("if"); out += c
            else:
                lets = []; v = cond(c, lets); out.append(" ".join(lets) + f" if {v} == k1 ")
            i = j; continue
        out.append(ts[i]); i += 1
    return "".join(out)
def main():
    for f in sys.argv[1:]:
        txt = open(f).read()
        parts = re.split(r"(/-.*?-/)", txt, flags=re.S)
        new = "".join(p if p.startswith("/-") else "\n".join(l if l.startswith(("import", "namespace", "end ", "--")) else rewrite(l) if False else l for l in p.split("\n")) for p in parts)
        # conditions never span lines in the source: rewrite per line is unsafe for multi-line ifs, so rewrite per part
        new = "".join(p if p.startswith("/-") else rewrite(p) for p in parts)
        open(f, "w").write(new)
    
if __name__ == '__main__': main()
