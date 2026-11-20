#!/usr/bin/env python3
"""Reference model (Python) of the ownership stage `Linear` (Testing/notes/NANO_V2_OWN.md) over a Par1 AST dump.
usage: own_ref.py AST.bin [--verbose]  -> prints accept/reject (+ first violation). Kinds: True = may hold a buffer."""
import struct, sys
PA = {1: 0, 2: 1, 3: 0, 4: 2, 5: 0, 6: 1, 7: 2, 8: 3, 9: 2}
def decode(w):
    i = [1]
    def node():
        t = w[i[0]]; i[0] += 1
        if t == 1: v = w[i[0]]; i[0] += 1; return ('c', v)
        if t == 2: s, ww = w[i[0]], w[i[0] + 1]; i[0] += 2; return ('l', s, ww)
        if t == 3: op = w[i[0]]; i[0] += 1; return ('b', op, node(), node())
        if t == 4: c = w[i[0]]; i[0] += 1; return ('i', c, node(), node(), node(), node())
        if t == 5: s, ww = w[i[0]], w[i[0] + 1]; i[0] += 2; return ('L', s, ww, node(), node())
        if t == 6: n = w[i[0]]; i[0] += 1; return ('p', [node() for _ in range(n)])
        if t == 8: cid, n = w[i[0]], w[i[0] + 1]; i[0] += 2; return ('C', cid, [node() for _ in range(n)])
        if t == 9: p = w[i[0]]; i[0] += 1; return ('P', p, [node() for _ in range(PA[p])])
        if t == 10: return ('o', node(), node())
        if t == 11: return ('k', node())
        raise ValueError(t)
    assert w[0] == 2
    defs = []
    while i[0] < len(w):
        assert w[i[0]] == 20; _, did, npw, ns, kind, nres = w[i[0]:i[0] + 6]; i[0] += 6
        b = node(); assert w[i[0]] == 21; i[0] += 1
        defs.append(dict(id=did, npw=npw, ns=ns, kind=kind, nres=nres, body=b))
    return defs

class Rej(Exception): pass

DSP = {1: [], 2: [0], 3: [], 4: [1, 0], 5: [], 6: [2], 7: [2, 0], 8: [1, 0, 0], 9: [1, 0]}

def width(n, R):
    t = n[0]
    if t in ('c', 'b', 'P'): return 1
    if t == 'l': return n[2]
    if t == 'i': return width(n[4], R) or width(n[5], R)
    if t == 'L': return width(n[4], R)
    if t == 'p': return sum(width(c, R) for c in n[1])
    if t == 'C': return len(R[n[1]])
    if t == 'o': return width(n[1], R) or width(n[2], R)
    if t == 'k': return 0

def infer(d, P, R):
    """PASS 1 (heuristic, unverified: pass 2 re-checks everything): param kinds 0 word, 1 owned buffer, 2 read-only.
    Destinations per word: 0 word, 1 transfer with buffer evidence, 2 borrow, ('st', q) CONTINUE state q, ('sl', s) LET slot s, None result."""
    ns, npw = d['ns'], d['npw']; ev = [False] * ns; edges = []; occ = []
    def walk(n, ds):
        t = n[0]
        if t == 'l':
            for j in range(n[2]):
                s = n[1] + j; kd = ds[j] if ds is not None and j < len(ds) else None
                occ.append((s, kd))
                if kd in (1, 2): ev[s] = True
                elif isinstance(kd, tuple): edges.append((s, kd[1]))
        elif t == 'b': walk(n[2], [0]); walk(n[3], [0])
        elif t == 'i': walk(n[2], [0]); walk(n[3], [0]); walk(n[4], ds); walk(n[5], ds)
        elif t == 'L': walk(n[3], [('sl', n[1] + j) for j in range(n[2])]); walk(n[4], ds)
        elif t in ('p', 'C', 'P'):
            cs = n[1] if t == 'p' else n[2]
            dd = ds if t == 'p' else (P[n[1]] if t == 'C' else DSP[n[1]])
            off = 0
            for c in cs:
                w = width(c, R); walk(c, dd[off:off + w] if dd is not None else None); off += w
        elif t == 'o': walk(n[1], ds); walk(n[2], ds)
        elif t == 'k': walk(n[1], [('st', q) for q in range(1, npw)])
    walk(d['body'], None)
    ch = True
    while ch:
        ch = False
        for a, b in edges:
            if ev[b] and not ev[a]: ev[a] = True; ch = True
    K = [1 if ev[s] else 0 for s in range(ns)]
    ro = [ev[s] and s < npw for s in range(ns)]
    ch = True
    while ch:
        ch = False
        for s, kd in occ:
            if ro[s] and not (kd == 2 or kd == ('st', s) and ro[s]): ro[s] = False; ch = True
    for s in range(npw):
        if ro[s]: K[s] = 2
    return K

def check(defs, verbose=False):
    P = []; R = []
    for d in defs:
        ns, npw = d['ns'], d['npw']
        K = infer(d, P, R)
        for s in range(npw, ns): K[s] = 0   # let slots: set by LET from the value kinds
        def lst(cs, ds, F):
            """argument list: ds = per-word destination kinds (None = transfer: all 1)"""
            k = []; pins = []; off = 0; F = list(F)
            for c in cs:
                if c[0] == 'l':
                    for j in range(c[2]):
                        s = c[1] + j; ks = K[s]; kd = 1 if ds is None else (ds[off + j] if off + j < len(ds) else -1)
                        if kd == -1: raise Rej("arg width")
                        if ks == 1 and kd == 0 or ks == 2 and kd != 2: raise Rej(f"slot {s} kind {ks} into dest {kd}")
                        if ks == 1:
                            if F[s]: raise Rej(f"use of consumed slot {s}")
                            pins.append((s, kd))
                        k.append(min(ks, 1))
                    off += c[2]
                else:
                    F, kc = chk(c, F)
                    for j, x in enumerate(kc):
                        kd = 1 if ds is None else (ds[off + j] if off + j < len(ds) else -1)
                        if kd == -1: raise Rej("arg width")
                        if x == 1 and kd == 0: raise Rej("buffer value into a word destination")
                    k += kc; off += len(kc)
            if ds is not None and off != len(ds): raise Rej("arg width")
            for s, kd in pins:
                if kd == 1:
                    if F[s]: raise Rej(f"pinned slot {s} consumed by a sibling (or twice)")
                    F[s] = True
            for s, kd in pins:
                if kd == 2 and F[s]: raise Rej(f"borrowed slot {s} consumed by a sibling")
            return F, k
        def chk(n, F):
            t = n[0]
            if t == 'c': return F, [0]
            if t == 'l': return lst([n], None, F)
            if t == 'b': F, _ = lst([n[2], n[3]], [0, 0], F); return F, [0]
            if t == 'i':
                F, _ = lst([n[2], n[3]], [0, 0], F)
                Ft, kt = chk(n[4], F); Fe, ke = chk(n[5], F)
                return [a or b for a, b in zip(Ft, Fe)], join(kt, ke)
            if t == 'L':
                s, w = n[1], n[2]
                F, kv = chk(n[3], F)
                if len(kv) != w: raise Rej("let width")
                F = list(F)
                for j in range(w): K[s + j] = kv[j]; F[s + j] = False
                return chk(n[4], F)
            if t == 'p': return lst(n[1], None, F)
            if t == 'C':
                F, _ = lst(n[2], P[n[1]], F); return F, list(R[n[1]])
            if t == 'P':
                F, _ = lst(n[2], DSP[n[1]], F); return F, [1 if n[1] in (4, 5, 8, 9) else 0]
            if t == 'o':
                L0 = [False] * ns
                _, kz = chk(n[1], L0); _, ks = chk(n[2], L0)
                return F, join(kz, ks)
            if t == 'k':
                F, _ = lst(n[1][1] if n[1][0] == 'p' else [n[1]], K[1:npw], F)
                return F, []
        def join(a, b):
            if not a: return b
            if not b: return a
            if len(a) != len(b): raise Rej("branch widths")
            return [max(x, y) for x, y in zip(a, b)]
        try:
            _, kb = chk(d['body'], [False] * ns)
        except Rej as e:
            return f"REJECT def {d['id']}: {e}"
        P.append(K[:npw]); R.append(kb)
        if verbose: print(d['id'], 'params', ''.join('wBr'[x] for x in K[:npw]), 'res', ''.join('wB'[x] for x in kb))
    return "ACCEPT"

if __name__ == '__main__':
    b = open(sys.argv[1], 'rb').read(); w = struct.unpack('<%dQ' % (len(b) // 8), b)
    if not w: print("EMPTY"); sys.exit(0)
    r = check(decode(w), '--verbose' in sys.argv); print(r); sys.exit(0 if r == "ACCEPT" else 3)
