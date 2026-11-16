import json, re
S = '/tmp/claude-0/-home-user-lean-assembly-compiler/cb2be246-7981-56ed-8b40-bf0e337fe02d/scratchpad'
import io, contextlib, sys
ARGV = list(sys.argv); sys.argv = ['x', 'gate']
with contextlib.redirect_stdout(io.StringIO()):
    import gen
from extract import fqn_of
R = json.load(open(S + '/ranges.json'))
def item_at(ln):
    for a, b, n in R:
        if a <= ln <= b: return n
    return None
log = open(ARGV[1]).read().split('\n')
errs = {}   # item name -> list of (line, msg)
gates = {}
for l in log:
    m = re.match(r'(?:\S+/)?ConLecheS1\w*\.lean:(\d+):\d+: error[^:]*: ?(.*)', l) or re.match(r'.*\.lean:(\d+):\d+: error(?:\([^)]*\))?: ?(.*)', l)
    if m:
        ln = int(m.group(1)); msg = m.group(2).strip()
        n = item_at(ln)
        errs.setdefault(n or '<gate>', []).append((ln, msg))
    m2 = re.match(r'frontx_ind_gate (\S+): (.*)', l)
    if m2: gates[m2.group(1)] = m2.group(2)
rows = []
for name, r in sorted(gen.report.items(), key=lambda kv: kv[1]['num']):
    if name in gates:
        gate = gates[name]
        rows.append((r['num'], name, 'verdict', gate)); continue
    # the first error among the target and its closure, in file order
    cands = []
    for i in r['closure']:
        f = fqn_of(gen.items[i])
        if f in errs: cands.append((min(l for l, _ in errs[f]), f, errs[f][0][1]))
    own = [c for c in cands if c[1] == fqn_of(gen.items[r['def_idx']])]
    if own: rows.append((r['num'], name, 'own-def error', own[0][2][:160] + ' @' + own[0][1]))
    elif cands:
        c = min(cands); rows.append((r['num'], name, 'dep error', c[2][:140] + ' in ' + c[1]))
    else:
        rows.append((r['num'], name, 'no error seen', ''))
for row in rows: print(' | '.join(str(x) for x in row))
