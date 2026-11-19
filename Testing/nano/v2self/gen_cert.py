#!/usr/bin/env python3
"""C-wide certificate generator (see Testing/notes/NANO_V2_MAIN.md, HANDOFF C-wide certificate).
usage: gen_cert.py self_S.lean ast.txt OUTDIR [chunk]
ast.txt: one line per def `id|npw|nslots|kind|nres|repr body` (refParse dump).  Emits MainCertC<k>.lean with, per plain def,
`D<i>` and `c<i> : pdefMean inp ms D<i> [args] = .ok [C.f args]` under the callee equations."""
import re, sys

def parse_sigs(path):
    sigs = []
    for line in open(path):
        if not line.startswith('def '): continue
        name = line.split()[1]
        rest = line[len('def ' + name):]
        if rest.lstrip().startswith(':') and '→' in rest.split(':=')[0]:
            tys = [t.strip() for t in rest.split(':=')[0].lstrip()[1:].split('→')]
            sigs.append((name, True, tys[:-1], tys[-1]))
        else:
            head = rest.split(':=')[0]
            params = []
            head = head.strip()
            while head.startswith('('):
                g, head = head[1:head.index(')')], head[head.index(')') + 1:].strip()
                ns, ty = g.split(':')
                params += [ty.strip()] * len(ns.split())
            res = head.lstrip(':').strip()
            sigs.append((name, False, params, res))
    return sigs

ENC = {'UInt64': 'w', 'Buf': 'b', 'Nat': 'w'}

def simple(sig):
    return all(t in ENC or t == 'List UInt8' for t in sig[2]) and sig[3] in ('UInt64', 'Buf')

def args(sig, pre):
    """(binders, encoded list, lean application args)"""
    bs, enc, app = [], [], []
    k = 0
    for t in sig[2]:
        if t == 'List UInt8': app.append('inp'); continue
        v = f'{pre}{k}'; k += 1
        bs.append(f'({v} : {"UInt64" if t != "Buf" else "List UInt64"})')
        enc.append(f'.{ENC[t]} {v}')
        app.append(f'{v}.toNat' if t == 'Nat' else v)
    return bs, enc, app

def stmt(sig, F, pre):
    bs, enc, app = args(sig, pre)
    r = ENC[sig[3]]
    call = ' '.join(['C.' + sig[0]] + app)
    q = f'∀ {" ".join(bs)}, ' if bs else ''
    return f'{q}{F} [{", ".join(enc)}] = .ok [.{r} ({call})]'

# ---- AST (repr of ParSpec.Nd, constructors written `.name`) ----
def parse_nd(t):
    pos = 0
    def ws():
        nonlocal pos
        while pos < len(t) and t[pos] in ' \n': pos += 1
    def atom():
        nonlocal pos
        ws()
        if t[pos] == '(':
            pos += 1; r = node(); ws(); assert t[pos] == ')'; pos += 1; return r
        if t[pos] == '[':
            pos += 1; xs = []
            ws()
            if t[pos] == ']': pos += 1; return xs
            while True:
                xs.append(node()); ws()
                if t[pos] == ',': pos += 1; continue
                assert t[pos] == ']'; pos += 1; return xs
        if t[pos] == '.': return node()
        m = re.match(r'\d+', t[pos:]); pos += m.end(); return int(m.group())
    AR = {'const': 1, 'loc': 2, 'bin': 3, 'ite': 5, 'letE': 4, 'pair': 1, 'call': 2, 'prim': 2, 'loop': 2, 'cont': 1}
    def node():
        nonlocal pos
        ws(); assert t[pos] == '.', t[pos:pos + 20]
        m = re.match(r'\.(\w+)', t[pos:]); pos += m.end(); c = m.group(1)
        return (c,) + tuple(atom() for _ in range(AR[c]))
    r = node(); ws(); assert pos == len(t); return r

def nd_txt(nd):
    if isinstance(nd, int): return str(nd)
    if isinstance(nd, list): return '[' + ', '.join(nd_txt(x) for x in nd) + ']'
    return '(.' + nd[0] + ''.join(' ' + nd_txt(x) for x in nd[1:]) + ')'

class Unsupported(Exception): pass
BIN = {1: 'ev_add', 2: 'ev_sub', 3: 'ev_mul', 4: 'ev_and', 5: 'ev_or', 6: 'ev_shl', 7: 'ev_shr', 8: 'ev_xor'}
PRIMK = {2: 'w', 3: 'w', 5: 'b', 6: 'w', 7: 'w', 8: 'b', 9: 'b'}
PRIMR = {2: 'ev_rd', 3: 'ev_len', 5: 'ev_bnew', 6: 'ev_bsize', 7: 'ev_bget', 8: 'ev_bset', 9: 'ev_bpush'}

class Gen:
    """explicit proof term `Ev inp ms n env _` for a value-mode node; env = list of (kind, lean expr)"""
    def __init__(self, sigs): self.sigs, self.n = sigs, 0
    def env_txt(self, env): return '[' + ', '.join(e if k == 'raw' else f'W.{k} {e}' for k, e in env) + ']'
    def tail(self, nd, env, rk, ih):
        """tail-mode term `EvK inp ms n env (LoopK ..) _` for a loop's step arm; rk = result kind, ih = IH application"""
        c = nd[0]
        if c == 'ite':
            (_, a), (_, b) = self.go(nd[2], env), self.go(nd[3], env)
            return f'(ev_iteK{nd[1]} (fun x => [W.{rk} x]) {a} {b} {self.tail(nd[4], env, rk, ih)} {self.tail(nd[5], env, rk, ih)})'
        if c == 'letE':
            if nd[2] != 1: raise Unsupported('wide let')
            k, v = self.go(nd[3], env)
            self.n += 1; y = f'y{self.n}'
            env2 = list(env); env2[nd[1]] = (k, y)
            return f'(ev_letK{k.upper()} (E := fun {y} => {self.env_txt(env2)}) {v} (fun _ => rfl) (fun {y} => {self.tail(nd[4], env2, rk, ih)}))'
        if c == 'cont':
            e = nd[1]
            if e[0] == 'pair':
                xs = 'evL_nil'
                for a in reversed(e[1]): xs = f'(evL_cons {self.go(a, env)[1]} {xs})'
                pay = f'(ev_pair {xs})'
            else: pay = self.go(e, env)[1]
            return f'(ev_contK {pay} rfl {ih})'
        return f'(ev_valK {self.go(nd, env)[1]})'
    def go(self, nd, env):
        c = nd[0]
        if c == 'const': return 'w', f'(ev_const {nd[1]})'
        if c == 'loc':
            if nd[2] != 1: raise Unsupported('wide loc')
            k, e = env[nd[1]]
            if k == 'raw': raise Unsupported('raw slot read')
            return k, f'(ev_loc (s := {nd[1]}) (w := 1) (env := {self.env_txt(env)}) (vs := [W.{k} {e}]) (Nat.le_of_ble_eq_true rfl) rfl)'
        if c == 'bin':
            (_, a), (_, b) = self.go(nd[2], env), self.go(nd[3], env)
            return 'w', f'({BIN[nd[1]]} {a} {b})'
        if c == 'ite':
            (_, a), (_, b) = self.go(nd[2], env), self.go(nd[3], env)
            (k, t), (k2, e) = self.go(nd[4], env), self.go(nd[5], env)
            assert k == k2
            return k, f'(ev_ite{nd[1]} (fun x => [W.{k} x]) {a} {b} {t} {e})'
        if c == 'letE':
            if nd[2] != 1: raise Unsupported('wide let')
            k, v = self.go(nd[3], env)
            self.n += 1; y = f'y{self.n}'
            env2 = list(env); env2[nd[1]] = (k, y)
            kb, b = self.go(nd[4], env2)
            return kb, f'(ev_let{k.upper()} (E := fun {y} => {self.env_txt(env2)}) {v} (fun _ => rfl) (fun {y} => {b}))'
        if c == 'call':
            sig = self.sigs[nd[1]]
            if not simple(sig): raise Unsupported('callee')
            asn = nd[2]; lenf = bool(asn) and asn[0] == ('prim', 1, [])
            if lenf: asn = asn[1:]
            xs = 'evL_nil'
            for a in reversed(asn): xs = f'(evL_cons {self.go(a, env)[1]} {xs})'
            nargs = sum(1 for t in sig[2] if t != 'List UInt8') - (1 if lenf else 0)
            us = ' _' * nargs
            if lenf: return ENC[sig[3]], f'(ev_callL {xs} h{nd[1]} (l{nd[1]}{us}))'
            return ENC[sig[3]], f'(ev_call {xs} h{nd[1]} (e{nd[1]}{us}))'
        if c == 'prim':
            if nd[1] not in PRIMR: raise Unsupported(f'prim {nd[1]}')
            return PRIMK[nd[1]], '(' + ' '.join([PRIMR[nd[1]]] + [self.go(a, env)[1] for a in nd[2]]) + ')'
        raise Unsupported(c)

def lenstmt(sig, j):
    """the `len' x`-fuel form of a loop callee's equation"""
    if not sig[1]: return ''
    bs, enc, app = args(sig, 'a')
    r = ENC[sig[3]]
    call = ' '.join(['C.' + sig[0], "(len' inp)"] + app[1:])
    q = f'∀ {" ".join(bs[1:])}, ' if bs[1:] else ''
    return f' (l{j} : {q}LenC (F{j} [{", ".join([".w inp.length.toUInt64"] + enc[1:])}] = .ok [.{r} ({call})]))'

def main():
    sigs = parse_sigs(sys.argv[1])
    ast = [l.rstrip('\n').split('|', 5) for l in open(sys.argv[2])]
    assert len(sigs) == len(ast), (len(sigs), len(ast))
    out, chunk = sys.argv[3], int(sys.argv[4]) if len(sys.argv) > 4 else 20
    todo, skipped = [], []
    for i, (a, sig) in enumerate(zip(ast, sigs)):
        body = a[5].replace('ParSpec.Nd.', '.')
        callees = sorted(set(int(x) for x in re.findall(r'\.call (\d+)', body)))
        ok = simple(sig) and all(simple(sigs[j]) for j in callees)
        term = None
        hyps = '' if not ok else ''.join(f' {{F{j} : Fn}} (h{j} : ms[{j}]? = some F{j}) (e{j} : {stmt(sigs[j], f"F{j}", "a")})' + lenstmt(sigs[j], j) for j in callees)
        if ok and a[3] == '1':
            try:
                nd = parse_nd(body); assert nd[0] == 'loop'
                bs, enc, app = args(sig, 'x')
                r = ENC[sig[3]]
                nloc = int(a[2]) - int(a[1])
                ls = [f'l{q}' for q in range(nloc)]
                aenv = [(e[1], e[3:]) for e in enc[1:]] + [('raw', l) for l in ls]
                g = Gen(sigs)
                zt = g.go(nd[1], [('w', 'N')] + aenv)[1]
                ih = '(ih M.toNat_lt M' + ' _' * (len(enc) - 1 + nloc) + ')'
                st = g.tail(nd[2], [('w', 'M')] + aenv, r, ih)
                Z = body  # full loop node text; arms are re-extracted in Lean by `rfl` on D.body
                lb = (' (' + ' '.join(ls) + ' : W)') if ls else ''
                ab = ' '.join(bs[1:])
                call = lambda f: ' '.join(['C.' + sig[0], f] + app[1:])
                envt = lambda h: '[' + ', '.join([f'W.w {h}'] + enc[1:] + ls) + ']'
                hn = ''.join(f' h{j} e{j}' + (f' l{j}' if sigs[j][1] else '') for j in callees)
                intro = ' '.join(['N'] + [b.split()[0][1:] for b in bs[1:]] + ls)
                txt = f'''def D{i} : DefA := ⟨{a[0]}, {a[1]}, {a[2]}, {a[3]}, {a[4]}, {body}⟩
def Z{i} : Nd := {nd_txt(nd[1])}
def S{i} : Nd := {nd_txt(nd[2])}
theorem L{i} (inp : List UInt8) (ms : List Fn){hyps} : ∀ n : Nat, n < 2 ^ 64 → ∀ (N : UInt64) {ab}{lb},
    loopRun (fun e => pev inp ms Z{i} e) (fun e => pev inp ms S{i} e) n {envt("N")} = .ok [.{r} ({call("n")})] := by
  intro n
  induction n with
  | zero =>
    intro _ {intro}
    apply loop_zero
    case h => exact {zt}
    case hf => rfl
  | succ n ih =>
    intro hn {intro}
    obtain ⟨M, rfl⟩ : ∃ M : UInt64, M.toNat = n := ⟨UInt64.ofNat n, by simp; omega⟩
    apply loop_succ (env1 := {envt("M")}) rfl
    case hk => exact {st}
    case hf => rfl
theorem c{i} (inp : List UInt8) (ms : List Fn){hyps} {" ".join(bs)} :
    pdefMean inp ms D{i} [{", ".join(enc)}] = .ok [.{r} ({call("x0.toNat")})] :=
  pdef_loop (z := Z{i}) (s := S{i}) [{", ".join(enc[1:] + [".w 0"] * nloc)}] rfl (by decide) rfl rfl
    (L{i} inp ms{hn} x0.toNat x0.toNat_lt x0 {" ".join([b.split()[0][1:] for b in bs[1:]] + ["(.w 0)"] * nloc)}) rfl
'''
                todo.append((i, txt)); continue
            except Unsupported as ex: ok = False
        ok = ok and a[3] == '0'
        if ok:
            bs0, enc0, _ = args(sig, 'x')
            env = [(e[1], e[3:]) for e in enc0] + [('w', '0')] * (int(a[2]) - int(a[1]))
            try: term = Gen(sigs).go(parse_nd(body), env)[1]
            except Unsupported as ex: ok = False
        (todo if ok else skipped).append(i)
        if not ok: continue
        bs, enc, app = args(sig, 'x')
        r = ENC[sig[3]]
        call = ' '.join(['C.' + sig[0]] + app)
        todo[-1] = (i, f'''def D{i} : DefA := ⟨{a[0]}, {a[1]}, {a[2]}, {a[3]}, {a[4]}, {body}⟩
theorem c{i} (inp : List UInt8) (ms : List Fn){hyps} {" ".join(bs)} :
    pdefMean inp ms D{i} [{", ".join(enc)}] = .ok [.{r} ({call})] := by
  apply pdef_env [{", ".join(enc + [".w 0"] * (int(a[2]) - int(a[1])))}] rfl (by decide) rfl
  case hb => exact {term}
  case hr => rfl
  case hf => rfl
''')
    for k in range(0, len(todo), chunk):
        with open(f'{out}/MainCertC{k // chunk}.lean', 'w') as f:
            f.write('/- GENERATED by Testing/nano/v2self/gen_cert.py: per-def certificates (plain defs). -/\n'
                    'import Nano.V2Self.Proof.MainCertRules\nset_option maxRecDepth 100000\nnamespace NanoMain.CertC\nopen ParSpec\n\n')
            f.write('\n'.join(t[1] for t in todo[k:k + chunk]))
            f.write('\nend NanoMain.CertC\n')
    print('plain certs:', len(todo), 'skipped:', len(skipped), skipped)

main()
