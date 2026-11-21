#!/usr/bin/env python3
"""lean-4.34: rewrite lakefile.toml's `Chain434` roots = every Nano/<stages> module whose import closure does not reach the
RISC-V Sail model (LeanRV64D), minus Legacy/Nano/V2Self/Legacy (old chain; pulls in unported old Nano modules).  Prints the
excluded modules.  Run from the repo root after adding or removing modules: python3 Testing/scripts/chain434_roots.py"""
import os, re, glob, functools
def path(m): return m.replace('.', '/') + '.lean'
@functools.lru_cache(None)
def imps(m):
    p = path(m)
    return tuple(re.findall(r'^import\s+(\S+)', open(p).read(), re.M)) if os.path.exists(p) else ()
@functools.lru_cache(None)
def sail(m): return m.startswith('LeanRV64D') or any(sail(i) for i in imps(m))
ms = sorted(f[:-5].replace('/', '.') for f in [g for s in ['Lexer', 'Parser', 'Ownership', 'Codegen', 'Run', 'SelfHost', 'Main', 'Tests'] for g in glob.glob('Nano/%s/**/*.lean' % s, recursive=True)])
roots = [m for m in ms if not sail(m)]
s = open('lakefile.toml').read()
new = 'roots = [' + ', '.join('"%s"' % m for m in roots) + ']'
s2, n = re.subn(r'(name = "Chain434"\n)roots = \[[^\]]*\]', lambda mt: mt.group(1) + new, s)
assert n == 1, "Chain434 lib not found in lakefile.toml"
open('lakefile.toml', 'w').write(s2)
print(len(roots), "roots; excluded (reach the RISC-V model):")
for m in ms:
    if sail(m): print("  " + m)
