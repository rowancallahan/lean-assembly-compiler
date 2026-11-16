# Build Testing/dashboard/data.json from the depth-probe outputs (self-hosting: exact call graph; con-leche: call graph read from source text).
# Usage: python3 build.py <dir with sh_cg.tsv, sh_final.json, sh_blockers_per_def.tsv, cl_greedy.json, cl_results_gate_compile.json, all.json> <out.json>
import sys, json, csv
src, out = sys.argv[1], sys.argv[2]
P = lambda f: f"{src}/{f}"

def sccs(nodes, edges):  # iterative Tarjan; returns node -> component id
    idx, low, on, st, comp, n = {}, {}, set(), [], {}, 0
    for s in nodes:
        if s in idx: continue
        work = [(s, iter(edges[s]))]; idx[s] = low[s] = n; n += 1; st.append(s); on.add(s)
        while work:
            v, it = work[-1]
            w = next(it, None)
            if w is None:
                work.pop()
                if work: low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == idx[v]:
                    while True:
                        x = st.pop(); on.discard(x); comp[x] = v
                        if x == v: break
            elif w not in idx:
                idx[w] = low[w] = n; n += 1; st.append(w); on.add(w); work.append((w, iter(edges[w])))
            elif w in on: low[v] = min(low[v], idx[w])
    return comp

def finish(nodes, roots):
    names = list(nodes)
    edges = {k: [c for c in nodes[k]['calls'] if c in nodes and c != k] for k in names}
    comp = sccs(names, edges)
    for k in names: nodes[k]['calls'] = edges[k]; nodes[k]['scc'] = comp[k]
    assert all(r in nodes for r in roots), [r for r in roots if r not in nodes]
    return {'nodes': nodes, 'roots': roots}

# --- self-hosting (exact call graph from the Lean environment)
sh = {}
fin = json.load(open(P('sh_final.json')))
msg = {r['name']: (r['P2_frontx_ind_msg'] or r['P1_frontx_compile_msg']) for r in csv.DictReader(open(P('sh_blockers_per_def.tsv')), delimiter='\t')}
for line in open(P('sh_cg.tsv')):
    f = line.rstrip('\n').split('\t')
    if len(f) != 7 or f[0] != 'def': continue
    cls = fin[f[1]]
    st = 'ok' if cls == 'OK' else 'gen' if cls == 'GEN' else 'blocked'
    sh[f[1]] = dict(mod=f[2], st=st, cls=cls, why=msg.get(f[1], '')[:220], calls=[c for c in f[4].split(',') if c])
assert len(sh) == 858, len(sh)
shRoots = ['Proven.Top.compile', 'Proven.Ir.compile']

# --- con-leche (call graph from source text, approximate)
F = json.load(open(P('cl_greedy.json')))['F']
R = json.load(open(P('cl_results_gate_compile.json')))
A = json.load(open(P('all.json')))
cl = {}
for name, feats in F.items():
    r = R.get(name, {})
    ok = not r.get('compile', 'ERR').startswith('ERR') or r.get('gate', '').startswith('gate ok; arms ok')
    why = '; '.join(feats) if feats else r.get('gate', '')
    cl[name] = dict(mod='', st='ok' if ok else 'blocked', cls=(feats[0].split(' (')[0] if feats else 'translator shape'), why=why[:220], calls=[])
for d in A:
    if d['full'] in cl:
        cl[d['full']]['mod'] = d['mod']
        cl[d['full']]['calls'] += [A[j]['full'] for j in d['edges']]
for v in cl.values(): v['calls'] = sorted(set(v['calls']))
nok = sum(v['st'] == 'ok' for v in cl.values())
assert nok == 46, nok
clRoots = ['ConLeche.Cached.checkDecls', 'ConLeche.Cached.checkDeclC', 'ConLeche.whnfBody', 'ConLeche.inferBody', 'ConLeche.defeqBody', 'ConLeche.Expr.instantiate1']

json.dump({'selfhost': finish(sh, shRoots), 'conleche': finish(cl, clRoots)}, open(out, 'w'), separators=(',', ':'))
print('selfhost', sum(v['st'] == 'ok' for v in sh.values()), '/', sum(v['st'] != 'gen' for v in sh.values()), '; conleche', nok, '/', len(cl))

# page: template + data inline
import os
here = os.path.dirname(os.path.abspath(__file__))
page = open(f'{here}/page.html').read()
assert page.count('/*DATA*/null') == 1
open(out.replace('.json', '.html'), 'w').write(page.replace('/*DATA*/null', open(out).read().replace('</', '<\\/')))
