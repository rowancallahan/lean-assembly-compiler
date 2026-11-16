"""Builds Riscv/Frontx/ConLecheS0.lean and the numbered target list (CONLECHE_S0.md).
usage: python3 Testing/conleche-s0/make_s0.py <dir with F2.txt, batchA.lean, batchB.lean>
F2.txt = origin/conleche-depth:Testing/conleche-depth/out/F2.lean.txt (con-leche @6810492c1, all files concatenated);
batchA.lean = origin/conleche-batch-a:Testing/conleche-batches/batchA.lean; batchB.lean = origin/conleche-batch-b:...batchB.lean.
Numbering: every top-level def/abbrev in batchA then batchB (file order), 1-based; targets = numbers % 4 == 0.
The file keeps F2 verbatim except lines starting with `frontx` (probe commands) or `#` (stray tokens); then the gates.
Second stage: pass the gate-ok list (`gate_ok.txt`) to add `frontx_ind` lines (run with the 2nd argument)."""
import re, sys, json
S = sys.argv[1]
DEF = re.compile(r'^(@\[[^\]]*\]\s*)?((?:unsafe|partial|private|noncomputable|protected)\s+)*(def|abbrev)\s+(\S+)')
funcs, stack = [], []
for fname in ['batchA', 'batchB']:
    stack = []
    for i, l in enumerate(open(f'{S}/{fname}.lean').read().split('\n')):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: stack.append(('ns', m.group(1))); continue
        if re.match(r'^section\b', l): stack.append(('sec', '')); continue
        if re.match(r'^end\b', l):
            if stack: stack.pop()
            continue
        m = DEF.match(l)
        if m:
            pre = '.'.join(x for k, x in stack if k == 'ns' and x)
            funcs.append(dict(file=fname, line=i + 1, fq=(pre + '.' if pre else '') + m.group(4)))
targets = [dict(num=n, **f) for n, f in enumerate(funcs, 1) if n % 4 == 0]
seen, uniq = set(), []
for t in targets:
    if t['fq'] not in seen: seen.add(t['fq']); uniq.append(t)
json.dump(targets, open(f'{S}/targets.json', 'w'), indent=1)
F2 = open(f'{S}/F2.txt').read().split('\n')
body = [l for l in F2 if not re.match(r'^(frontx|#)', l)]
out = ['import Riscv.Frontx.IndGate'] + body + ['', 'namespace Proven.Frontx.ExprEx',
  'frontx_ind_type TExpr := ConLeche.Expr nesting ConLeche.Level, ConLeche.Name, List ConLeche.Level, ConLeche.Literal,',
  '  List ConLeche.Expr, Option ConLeche.Expr', '']
out += [f'frontx_ind_gate {t["fq"]} on TExpr' for t in uniq]
if len(sys.argv) > 2:
    out += [f'frontx_ind {n} on TExpr' for n in open(sys.argv[2]).read().split()]
out += ['end Proven.Frontx.ExprEx', '']
open('/home/user/lean-assembly-compiler/Testing/conleche-s0/ConLecheS0.gen.lean', 'w').write('\n'.join(out))
print('functions', len(funcs), 'targets', len(targets), 'unique targets', len(uniq))
