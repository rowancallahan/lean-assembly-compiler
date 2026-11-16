import re, sys, json, glob
from extract import parse, fqn_of, ns_str
S = '/tmp/claude-0/-home-user-lean-assembly-compiler/cb2be246-7981-56ed-8b40-bf0e337fe02d/scratchpad'
REPO = '/home/user/lean-assembly-compiler'
DECL = ('def', 'abbrev', 'structure', 'inductive', 'theorem', 'mutual')

A, _ = parse(S + '/batchA.lean'); B, GL = parse(S + '/batchB.lean')
GL = parse(S + '/batchA.lean')[1] + GL
items = A + B
for n, it in enumerate(items): it['idx'] = n
# existing declarations (already compiled in Riscv/Frontx) are not re-emitted
E = set()
for f in [g for g in glob.glob(REPO + '/Riscv/Frontx/*.lean') if not g.endswith('ConLecheS1.lean')]:
    its, _ = parse(f)
    for it in its:
        if it['kind'] in DECL and fqn_of(it): E.add(fqn_of(it))
targets = [it for it in items if it['kind'] == 'target']
assert len(targets) == 257, len(targets)

def resolve(t):
    """the decl item a `-- frontx_ind X` line names: nearest preceding decl with the name in the line's namespace"""
    ns = [f[1] for f in t['frames'] if f[0] == 'namespace']
    cands = set()
    for k in range(len(ns), -1, -1):
        cands.add('.'.join(ns[:k] + [t['name']]))
    best = None
    for it in items[:t['idx']]:
        f = fqn_of(it)
        if it['kind'] in DECL and f and (f == t['name'] or f.endswith('.' + t['name'])): best = it
    assert best is not None, t['name']
    return best

TOK = {}
def tokens(it):
    if it['idx'] in TOK: return TOK[it['idx']]
    TOK[it['idx']] = _tokens(it); return TOK[it['idx']]
def _tokens(it):
    src = '\n'.join(it['pre'] + it['body'])
    src = re.sub(r'/-.*?-/', ' ', src, flags=re.S)
    src = re.sub(r'--[^\n]*', ' ', src)
    return set(re.findall(r"[A-Za-z_][A-Za-z0-9_'!?.]*", src))
def _tokens_old(it):
    return set(re.findall(r"[A-Za-z_][A-Za-z0-9_'!?.]*", '\n'.join(it['pre'] + it['body'])))

def matches(tok, f):
    parts = tok.split('.')
    for k in range(len(parts)):
        p = '.'.join(parts[k:])
        if len(p) < 2: continue
        if f == p or f.endswith('.' + p): return True
    return False

decls = [it for it in items if it['kind'] in DECL and fqn_of(it)]
FQ = {it['idx']: fqn_of(it) for it in items}
def prefixes(it):
    ns = [f[1] for f in it['frames'] if f[0] == 'namespace']
    out = ['']
    for k in range(1, len(ns) + 1): out.append('.'.join(ns[:k]))
    return out
def resolves(tok, pre, f):
    if tok.startswith('.') or len(tok) < 2: return False
    for p in pre:
        cand = (p + '.' + tok) if p else tok
        if f == cand or f.startswith(cand + '.') and False: return True
    parts = tok.split('.')
    for k in range(1, len(parts)):
        sub = '.'.join(parts[:k])
        for p in pre:
            cand = (p + '.' + sub) if p else sub
            if f == cand and len(sub) >= 2: return True
    if '.' in tok and tok.split('.')[0][:1].islower():
        last = tok.split('.')[-1]
        if len(last) >= 2 and f.endswith('.' + last): return True
    return False
def deps_of(it, seen):
    stack = [it]; out = set()
    while stack:
        cur = stack.pop()
        toks = tokens(cur); pre = prefixes(cur)
        for d in decls:
            if d['idx'] in out or d is cur: continue
            f = FQ[d['idx']]
            if any(resolves(t, pre, f) for t in toks):
                out.add(d['idx']); stack.append(d)
    return out

sel = []
for t in targets:
    if (t['idx'] and (targets.index(t) + 1) % 4 == 1):
        sel.append(t)
report = {}
for k, t in enumerate(sel):
    d = resolve(t)
    cl = deps_of(d, None)
    cl.add(d['idx'])
    if re.search(r'=|decide|Decidable|BEq|Hashable|Subsingleton', '\n'.join(d['pre'] + d['body'])) or any(
            re.search(r'=|decide|Decidable|BEq|Hashable', '\n'.join(items[j]['body'])) for j in list(cl)):
        for ins in [it for it in items if it['kind'] == 'instance']:
            cl |= {ins['idx']} | deps_of(ins, None)
    report[t['name']] = dict(num=targets.index(t) + 1, def_idx=d['idx'], fqn=fqn_of(d), closure=sorted(cl),
                             exists=fqn_of(d) in E)
json.dump(report, open(S + '/plan.json', 'w'), indent=1)
print(len(sel), 'selected')
for n, r in report.items():
    print(r['num'], n, r['fqn'], 'exists' if r['exists'] else '', len(r['closure']))
