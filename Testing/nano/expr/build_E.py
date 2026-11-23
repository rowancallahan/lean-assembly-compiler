#!/usr/bin/env python3
"""build_E.py OUT : E's source text in nano's self-language: C's base + lexer + parser text (as build_self_S.py),
the numeral check NumC (with Gen's g33), the phrase table, the emitter, and the driver `m x = e99 x`. Lean-only lines (imports, namespace, set_option,
comments) are dropped, as in boot/fixpoint.sh."""
import os, re, sys
OUT = os.path.abspath(sys.argv[1])
os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../.."))
parts = ["Nano/Main/Chain", "Nano/Lexer/Lex2", "Nano/Parser/Par1", "Nano/Parser/NumC", "Nano/Expr/EmitStr", "Nano/Expr/Emit"]
out = []
# NumC (u10, the numeral check) calls Gen's prim-arity table g33 only
g = open("Nano/Codegen/Gen.lean").read()
out.append(re.search(r"^def g33 .*?\n\n", g, re.M | re.S).group(0))
for p in parts:
    t = re.sub(r"/-.*?-/", "", open(p + ".lean").read(), flags=re.S)
    t = "\n".join(l.split("--")[0].rstrip() for l in t.split("\n")
                  if not l.startswith(("import", "namespace", "end C", "set_option", "open")))
    out.append(t.strip("\n") + "\n")
out.append("def m (x : List UInt8) : List UInt8 := e99 x\n")
s = re.sub(r"\n\n+", "\n\n", "\n".join(out))
assert "--" not in s and "/-" not in s
open(OUT, "w").write(s)
