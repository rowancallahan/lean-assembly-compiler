#!/usr/bin/env python3
"""run_check.py SRC... : the Expr spot check. nano's reference emitter (emit_ref.lean) vs Lean's normalized Expr
(lean_side.sh), per def. Prints the counts and one line per non-match with its category:
  literal-typing  equal once every UInt64/Nat-specific constant is renamed NUM (Lean typed a literal-only
                  subterm as Nat where nano has UInt64); a heuristic LABEL only, never counted as a match
  lean-rejects    nano accepts the program, Lean has no such def (invariant 1 violation)
  other           anything else
Sources nano rejects are counted, not checked. Exit 1 on `other` or `lean-rejects`."""
import subprocess, sys, os, tempfile, collections
R = os.path.dirname(os.path.abspath(__file__)); TOP = os.path.abspath(os.path.join(R, '../../..'))
srcs = [os.path.abspath(s) for s in sys.argv[1:]]; W = tempfile.mkdtemp()
r = subprocess.run([f'{TOP}/Testing/scripts/lean_run.sh', 'Testing/nano/expr/emit_ref.lean'] + srcs, cwd=TOP,
                   capture_output=True, text=True)
assert r.returncode == 0, 'emit_ref failed: ' + r.stderr[-2000:]
nano = r.stdout.splitlines()
assert subprocess.run([f'{R}/lean_side.sh', f'{W}/lean.S'] + srcs).returncode == 0, 'lean_side.sh failed'
lean = {}
for l in open(f'{W}/lean.S').read().splitlines():
    t = l.split(' ', 2); lean[t[1]] = t[2] if t[0] == 'D' else None
def num(t): return 'NUM' if ('UInt64' in t or 'Nat' in t) and t != 'Nat.casesOn.{1}' else t
cnt = collections.Counter(); rej = []
for l in nano:
    t = l.split(' ', 2)
    if t[0] == 'R': rej.append(l); cnt['nano-rejects (program)'] += 1; continue
    n, e = t[1], t[2]; L = lean[n]
    if L == e: cnt['match'] += 1; continue
    if L is None: cat = 'lean-rejects'
    else:
        a, b = e.split(), L.split()
        cat = 'literal-typing' if list(map(num, a)) == list(map(num, b)) else 'other'
    cnt[cat] += 1; print(f'{cat:15} {n}')
for l in rej: print('nano-rejects   ', l)
print(dict(cnt))
sys.exit(1 if cnt['other'] or cnt['lean-rejects'] else 0)
