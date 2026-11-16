import sys, json, os
from gen import items, targets, sel, report, E, fqn_of, DECL, S, REPO, GL
from extract import parse
mode = sys.argv[1]               # 'gate' (diagnostic, all targets), 'full' (diagnostic + frontx_ind), 'final' (passing only)
import json as _j
passing = set(json.load(open(S + '/passing.json'))) if mode in ('full', 'final') else set()
def wrap(frames, body_lines):
    out = []
    for kind, name, lines in frames:
        out.append(f'namespace {name}' if kind == 'namespace' else 'section')
        out += lines
    out += body_lines
    for kind, name, lines in reversed(frames):
        out.append(f'end {name}' if kind == 'namespace' else 'end')
    return out
head = ['import Riscv.Frontx.IndGate', 'import Riscv.Frontx.ExprExamples', 'import Std.Data.HashMap',
        'import Std.Data.HashMap.Lemmas', 'import Std.Data.HashSet', 'set_option maxErrors 100000',
        'open Proven.Frontx.ExprEx', '']
emit_idx = set()
if mode == 'final':
    from gen import deps_of
    for n in passing:
        d = report[n]['def_idx']; emit_idx |= {d} | deps_of(items[d], None)
    emit_idx = set(i for i in emit_idx if fqn_of(items[i]) not in E)
    sel = [t for t in sel if t['name'] in passing]
else:
    for r in report.values(): emit_idx |= set(i for i in r['closure'] if fqn_of(items[i]) not in E)
seen = set(); keep = set()
for i in sorted(emit_idx):
    f = fqn_of(items[i])
    if f is None or f not in seen:
        keep.add(i); seen.add(f) if f else None
emit_idx = keep; print("pre-dedupe", len(set().union(*[set(r["closure"]) for r in report.values()])), "E-filtered", len(set(i for r in report.values() for i in r["closure"] if fqn_of(items[i]) not in E)), "keep", len(keep))
out = head + [g for g in GL if g.startswith("universe")] + ['']
ranges = []
for it in items:
    if it['idx'] not in emit_idx: continue
    out += ['']
    st = len(out) + 1
    out += wrap(it['frames'], it['pre'] + it['body'])
    ranges.append((st, len(out), fqn_of(it) or it['kind'] + str(it['idx'])))
json.dump(ranges, open(S + '/ranges.json', 'w'))
# the gate (and frontx_ind) lines of the selected targets, after their definitions
for t in sel:
    n = t['name']
    fr = t['frames']
    if fqn_of(items[report[n]['def_idx']]) in E:
        out += ['', f'-- {n}: already compiled in Riscv/Frontx (ExprExamples)']
        continue
    out += ['']
    q = report[n]['fqn']
    out += [f'frontx_ind_gate {q} on TExpr']
    if mode in ('full', 'final') and n in passing:
        out += [f'frontx_ind {q} on TExpr']
open(os.environ.get('OUT', REPO + '/Riscv/Frontx/ConLecheS1.lean'), 'w').write('\n'.join(out) + '\n')
print('items emitted', len(emit_idx), 'lines', len(out))
