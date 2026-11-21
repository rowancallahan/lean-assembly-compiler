#!/usr/bin/env python3
"""mini.py: minimize a diverging program (token-level ddmin keeping the same divergence kind + Lean error kind) and classify into M-classes.
Used by campaign.py. UNPROVEN test glue."""
import re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
TOK=re.compile(r"\s*(?:[A-Za-z_][A-Za-z0-9_'.]*|\d+|:=|=>|<<<|>>>|\|\|\||&&&|==|<-|--[^\n]*|/-|-/|[^\sA-Za-z0-9_])\s*|\s+")
def toks(s): return TOK.findall(s)
def ddmin(src, pred):
    """src: str; pred(str)->bool. Line-level then token-level chunk removal."""
    lines=src.split("\n")
    def tryp(parts,j): 
        return pred(j.join(parts))
    for unit,j in((lines,"\n"),(toks(src),"")):
        n=2
        cur=unit
        if unit is not lines: cur=toks("\n".join(lines))
        while len(cur)>=2:
            ch=max(1,len(cur)//n); removed=False
            for i in range(0,len(cur),ch):
                cand=cur[:i]+cur[i+ch:]
                if cand and pred(j.join(cand)): cur=cand; removed=True; break
            if removed: n=max(2,n-1); continue
            if ch==1: break
            n=min(len(cur),n*2)
        if unit is lines: lines=cur
        else: return j.join(cur)
        # continue with tokens from joined lines
        src="\n".join(lines)
    return src
RES=None
def classify(src, nano, lean):
    s=src
    if lean.startswith("ACCEPT"): kind="RESULT"
    else: kind="LEANREJ"
    if re.search(r"implemented_by|@\[extern",s): return "M13"
    if re.search(r"<-|<\||<\$",s) and "unexpected token '<" in lean: return "M3"
    if "already been declared" in lean: return "M8"
    if "redundantMatchAlt" in lean or "Redundant" in lean: return "M11"
    if re.search(r"Invalid name after|no current scope|unknown namespace|Missing name after|Unexpected name|Invalid `end`",lean): return "M5"
    if re.search(r"\bnamespace\b",s) and "nknown" in lean: return "M4"
    if re.search(r"[<>]{3}",s) and (kind=="RESULT" or "synthInstanceFailed" in lean or "mismatch" in lean): return "M12"
    if kind=="RESULT":
        if re.search(r"\d{20}",s) and re.search(r"\bf\b",s): return "M2"
        return "M1"
    if re.search(r"@\[|\bprivate\b|/--|/-!",s): return "M13/M14"
    if "right-hand-side" in lean or "Missing cases" in lean: return "M9"
    if "expected ')', ',' or ':'" in lean or "expected ';' or line break" in lean: return "M9/M10"
    if re.search(r"(^|[^A-Za-z0-9_'])_([^A-Za-z0-9_']|$)|'",s): return "M7"
    from_res=set(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),"../lean_rules/lean_reserved_words.txt")).read().split())
    if any(t in from_res for t in re.findall(r"[A-Za-z_][A-Za-z0-9_']*",s)) and ("unexpected token" in lean or "expected" in lean): return "M6"
    if "Type mismatch" in lean or "type mismatch" in lean: return "M10?"
    return "NEW?"
