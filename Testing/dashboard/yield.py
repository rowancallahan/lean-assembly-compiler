# Blocker yield: lowest blockers and feature unlock counts for both depth-probe graphs.
# Usage: python3 yield.py <dir with sh_cg.tsv, sh_final.json, sh_blockers_per_def.tsv, cl_greedy.json, cl_results_gate_compile.json, all.json> <out yield.json> [F2.lean.txt]
# Reads the same input dir as build.py. The optional F2.lean.txt gives con-leche bodies for 0-ary constants.
import sys, json, csv, re
src, out = sys.argv[1], sys.argv[2]
f2 = sys.argv[3] if len(sys.argv) > 3 else None
repo = sys.argv[4] if len(sys.argv) > 4 else None
P = lambda f: f"{src}/{f}"

FEATS = ['translator shape (no type named)', '0-ary constant', 'inductive / structure type',
         'monad / higher-kinded (Type → Type, m α)', 'polymorphic type variable', 'List / Array / Option of non-scalar element',
         'sized BitVec / Fin', 'tuple (×)', 'function-valued parameter or result', 'HashMap / HashSet / memo state',
         'String / Char / Int', 'non-computational (Type / Prop / Sort / Decidable)', 'several non-structural parameters']
T, Z, IND, MON, POLY, COL, BV, TUP, HO, MEMO, STR, NC, MULTI = FEATS
CL_MAP = {'multi-field structure': IND, 'monad': MON, 'List / Array / Option': COL, 'nullary constant': Z,
          'HashMap': MEMO, 'function-valued': HO, 'String / Char': STR, 'Int': STR}
SCALARS = r'\b(Nat|Bool|UInt8|UInt16|UInt32|UInt64|Int|String|Char|Unit|Reg|Name|Expr|Level|Id|Std|Type|Prop|Sort|Decidable)\b'
TRANS_RE = r'Unknown constant|no argument of a declared type|equation|brecOn|instantiateForall|Application type mismatch|type mismatch|PANIC|motive|Sim|kernel|match'

def sh_feats(msg, typ):
    f = set()
    for t in re.findall(r'unsupported (?:parameter|result) type ([^\n|]*?)(?= PANIC|\s*$|\s*\|)', msg):
        if 'Type → Type' in t: f.add(MON)
        elif '→' in t: f.add(HO)
        if re.search(r'\bType\b|\bProp\b|\bSort\b|Decidable', t): f.add(NC)
        if '×' in t: f.add(TUP)
        if re.search(r'BitVec|\bFin\b', t): f.add(BV)
        if re.search(r'\b(List|Array|Option|Except)\b', t): f.add(COL)
        if re.search(r'\b(String|Char|Int)\b', t): f.add(STR)
        if re.search(r'HashMap|HashSet|Memo', t): f.add(MEMO)
        if re.search(r'\bX\b|\b[ρασβγ]\b', t): f.add(POLY)
        if re.search(r'\b(?!(?:%s)\b)[A-Z][A-Za-z0-9_.]*' % '|'.join(['List','Array','Option','Except','BitVec','Fin','Nat','Bool','Int','String','Char','UInt8','UInt16','UInt32','UInt64','Unit','Type','Prop','Sort','Decidable','Reg','X','Name','Expr','Id','Std','HashMap','HashSet']), t): f.add(IND)
    if re.search(r'more than one extra parameter|scalar parameter needs', msg): f.add(MULTI)
    if re.search(TRANS_RE, msg): f.add(T)
    if not f: f.add(T)
    return f

def sccs(nodes, edges):  # iterative Tarjan (same as build.py)
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

def analyse(name, nodes):
    """nodes: name -> dict(st in ok|gen|blocked, calls, feats, msg, mod, typ, body)."""
    names = list(nodes); ix = {k: i for i, k in enumerate(names)}
    edges = {k: [c for c in nodes[k]['calls'] if c in nodes and c != k] for k in names}
    comp = sccs(names, edges)
    for k in names: nodes[k]['scc'] = comp[k]; nodes[k]['calls'] = edges[k]
    # reachability bitmasks (closure includes the node itself)
    clos = []
    for k in names:
        seen, stack = {ix[k]}, [k]
        while stack:
            x = stack.pop()
            for y in edges[x]:
                if ix[y] not in seen: seen.add(ix[y]); stack.append(y)
        m = 0
        for s in seen: m |= 1 << s
        clos.append(m)
    anc = [0] * len(names)
    for j, m in enumerate(clos):
        for i in range(len(names)):
            if m >> i & 1 and i != j: anc[i] += 1
    blocked = [k for k in names if nodes[k]['st'] == 'blocked']
    lowest = []
    for k in blocked:
        if all(nodes[c]['st'] in ('ok', 'gen') or nodes[c]['scc'] == nodes[k]['scc'] for c in edges[k]):
            lowest.append(k)
    lowest.sort(key=lambda k: (-anc[ix[k]], k))
    bl = [ix[k] for k in blocked]
    feat_of = {ix[k]: nodes[k]['feats'] for k in blocked}
    def unlocks(S):  # blocked functions whose whole closure is OK/gen or blocked only by features in S
        notclear = 0
        for i in bl:
            if not feat_of[i] <= S: notclear |= 1 << i
        return sum(1 for i in bl if clos[i] & notclear == 0)
    per = {}
    for F in FEATS:
        per[F] = dict(lowest_blockers=[k for k in lowest if F in nodes[k]['feats']], unlocks=unlocks({F}))
    lowrows = [dict(rank=r + 1, name=k, module=nodes[k]['mod'], above=anc[ix[k]], features=sorted(nodes[k]['feats']),
                    first_error=nodes[k]['msg'][:200], typ=nodes[k].get('typ', ''), body=nodes[k].get('body') and {x: nodes[k]['body'][x] for x in ('chars', 'kind')})
               for r, k in enumerate(lowest)]
    return dict(per=per, unlocks=unlocks, lowest=lowrows, nblocked=len(blocked), nok=sum(nodes[k]['st'] == 'ok' for k in names))

def greedy(unl_fns, steps=6):
    S, seq, cum = set(), [], 0
    for _ in range(steps):
        best = max(FEATS, key=lambda F: sum(u(S | {F}) for u in unl_fns) if F not in S else -1)
        val = sum(u(S | {best}) for u in unl_fns)
        if best in S or val <= cum: break
        S.add(best); seq.append(dict(feature=best, unlocks_total=val, gain=val - cum)); cum = val
    return seq

# --- self-hosting graph
fin = json.load(open(P('sh_final.json')))
rows = {r['name']: r for r in csv.DictReader(open(P('sh_blockers_per_def.tsv')), delimiter='\t')}
sh = {}
for line in open(P('sh_cg.tsv')):
    f = line.rstrip('\n').split('\t')
    if len(f) != 7 or f[0] != 'def': continue
    r = rows[f[1]]
    msg = r['P2_frontx_ind_msg'] or r['P1_frontx_compile_msg']
    cls = fin[f[1]]
    st = 'ok' if cls == 'OK' else 'gen' if cls == 'GEN' else 'blocked'
    feats = set()
    if st == 'blocked':
        feats = sh_feats(msg, f[5])
        if '→' not in f[5] and '∀' not in f[5] and f[5].strip(): feats.add(Z)
    sh[f[1]] = dict(mod=f[2], st=st, calls=[c for c in f[4].split(',') if c], msg=msg, feats=feats, typ=f[5])
assert len(sh) == 858, len(sh)

# --- con-leche graph
F = json.load(open(P('cl_greedy.json')))['F']
R = json.load(open(P('cl_results_gate_compile.json')))
A = json.load(open(P('all.json')))
cl = {}
for name, fl in F.items():
    r = R.get(name, {})
    ok = not r.get('compile', 'ERR').startswith('ERR') or r.get('gate', '').startswith('gate ok; arms ok')
    feats = set()
    for lab in fl:
        feats |= {v for k, v in CL_MAP.items() if lab.startswith(k) or k in lab}
    if not ok and not feats: feats = {T}
    msg = r.get('compile', '') if r.get('gate', '').startswith('gate ok; arms ok') else r.get('gate', '')
    if name in ('ConLeche.checkDecl', 'ConLeche.checkDeclKind') or name.startswith('beside.'): continue  # unresolved names (CONLECHE_DEPTH2 §2)
    cl[name] = dict(mod='', st='ok' if ok else 'blocked', calls=[], msg=msg, feats=feats if not ok else set(), typ='')
for d in A:
    if d['full'] in cl:
        cl[d['full']]['calls'] += [A[j]['full'] for j in d['edges']]
for v in cl.values(): v['calls'] = sorted(set(v['calls']))
for d in A:
    if d['full'] in cl: cl[d['full']]['mod'] = d['mod']
assert sum(v['st'] == 'ok' for v in cl.values()) == 46

# 0-ary constants: source text (con-leche from F2.lean.txt, self-hosting from the repo checkout)
def f2_bodies(path):
    out_, ns, cur, pat = {}, [], None, re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:private |protected |partial |unsafe |noncomputable )*(def|abbrev|theorem|lemma|structure|inductive|class|instance|opaque|mutual)\b\s*([^\s:({\[]*)')
    for l in open(path).read().split('\n'):
        if re.match(r'^-- ===== (\S+) ', l): ns, cur = [], None; continue
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: ns.append(m.group(1)); continue
        if re.match(r'^end\s+\S+', l) and ns and l.split()[1] == ns[-1]: ns.pop(); continue
        m = pat.match(l)
        if m and m.group(1) in ('def', 'abbrev', 'opaque'):
            cur = []; out_.setdefault('.'.join(x for x in ns + [m.group(2)] if x), []).append(cur)
        elif m: cur = None
        if cur is not None: cur.append(l)
    return {k: v[0] for k, v in out_.items() if len(v) == 1}

def repo_body(repo, mod, short):
    import os
    want = mod.replace('.', '/') + '.lean'
    hits = [os.path.join(d, f) for d, _, fs in os.walk(repo) for f in fs if os.path.join(d, f).endswith('/' + want)]
    if len(hits) != 1: return None
    L = open(hits[0]).read().split('\n')
    head = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable )*(?:def|abbrev)\s+%s(?=\s|:|$)' % re.escape(short))
    starts = [i for i, l in enumerate(L) if head.match(l)]
    if len(starts) != 1: return None
    body = []
    for l in L[starts[0] + 1:]:
        if re.match(r'^(?:@\[|/--|private |protected |noncomputable |def |abbrev |theorem |lemma |instance |structure |inductive |namespace |end |section |class |opaque |mutual |open |#|\S)', l) and body: break
        body.append(l)
    txt = '\n'.join(body)
    return txt.split(':=', 1)[1] if ':=' in txt else None

bodies_cl = f2_bodies(f2) if f2 else {}
for k, v in cl.items():
    if Z in v['feats'] and k in bodies_cl:
        b = re.sub(r'/-.*?-/', '', '\n'.join(bodies_cl[k]), flags=re.S); b = re.sub(r'--[^\n]*', '', b)
        if ':=' in b: v['body'] = dict(chars=len(b.split(':=', 1)[1].strip()), text=b.split(':=', 1)[1].strip())
if repo:
    for k, v in sh.items():
        if Z in v['feats'] and v['st'] == 'blocked':
            t = repo_body(repo, v['mod'], k.split('.')[-1])
            if t is not None:
                t = re.sub(r'/-.*?-/', '', t, flags=re.S); t = re.sub(r'--[^\n]*', '', t)
                v['body'] = dict(chars=len(t.strip()), text=t.strip())

def body_kind(text, name):
    t = re.sub(r'by\s+[^\n]*', ' ', text)  # tactic proofs inside constructors
    t = re.sub(r'"[^"]*"|`[^\s,\]\)]+|\b\d+\b|\b(?:mkStr|mkNum|mkSimple|str|num|anonymous|mk)\b', ' ', t)
    short = name.split('.')[-1]
    if re.search(r'\b%s\b' % re.escape(short), t) and len(short) > 2: return 'recursion or self-reference'
    lows = [w for w in re.findall(r'\b[a-z_][A-Za-z0-9_\']*\b', t) if w not in ('fun', 'let', 'in', 'if', 'then', 'else', 'match', 'with', 'true', 'false', 'some', 'none', 'by', 'do')]
    return 'calls functions' if lows or re.search(r'\b[A-Z]\w*\.[a-z]\w*', t) else 'literal data (names/strings/nats/constructors)'

for nodes in (sh, cl):
    for k, v in nodes.items():
        if v.get('body'): v['body']['kind'] = body_kind(v['body']['text'], k)

res = {}
for name, nodes in (('selfhost', sh), ('conleche', cl)):
    res[name] = analyse(name, nodes)

def tot(S): return res['selfhost']['unlocks'](S) + res['conleche']['unlocks'](S)
out_json = {g: {F_: dict(lowest_blockers=res[g]['per'][F_]['lowest_blockers'], unlocks=res[g]['per'][F_]['unlocks']) for F_ in FEATS} for g in res}
out_json['combined'] = {F_: dict(unlocks=res['selfhost']['per'][F_]['unlocks'] + res['conleche']['per'][F_]['unlocks']) for F_ in FEATS}
out_json['greedy'] = [dict(scope='selfhost', steps=greedy([res['selfhost']['unlocks']])),
                      dict(scope='conleche', steps=greedy([res['conleche']['unlocks']])),
                      dict(scope='combined', steps=greedy([res['selfhost']['unlocks'], res['conleche']['unlocks']]))]
out_json['lowest'] = {g: res[g]['lowest'] for g in res}
out_json['features'] = FEATS
out_json['counts'] = {g: dict(blocked=res[g]['nblocked'], ok=res[g]['nok'], lowest=len(res[g]['lowest'])) for g in res}
json.dump(out_json, open(out, 'w'), ensure_ascii=False, indent=1)
for g in res: print(g, out_json['counts'][g])
for g in out_json['greedy']: print(g['scope'], [(s['feature'][:25], s['gain']) for s in g['steps']])
