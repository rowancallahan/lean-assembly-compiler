#!/usr/bin/env python3
"""Differential fuzzer: the compiler on ARM vs on RISC-V (nanorun), and the programs it emits.

usage: fuzz_arm.py WORKDIR SHARD/NSHARD [MAX_CASES]     (run forever if MAX_CASES omitted or 0)
       fuzz_arm.py WORKDIR replay SEED                  (re-run one case, print its result)

Per case: mutate a compiler source (an example with comments stripped, or self_S_input.txt).
  1. compile: nanorun B2.bin vs qemu-aarch64 shim_arm B2_arm.bin. (status, bytes) must be equal.
  2. if accepted (status 0, non-empty): translate with rv2arm.sh (ARM translator under qemu), then run the
     program on 3 inputs: nanorun vs qemu shim_arm. (status, bytes) must be equal.
Mismatch, one-sided crash, or a run over HANG_S seconds: the case is saved in WORKDIR/findings and minimized.
Needs: cc, aarch64-linux-gnu-gcc, qemu-aarch64-static (QEMU env overrides).
"""
import os, re, sys, random, subprocess, time, glob, json

HERE = os.path.dirname(os.path.abspath(__file__))
V = os.path.abspath(os.path.join(HERE, '..', '..'))        # Testing/nano/v2self
ARMD = os.path.join(V, 'arm')
B2 = os.path.join(V, 'B2.bin')
B2A = os.path.join(ARMD, 'B2_arm.bin')
RV2ARM = os.path.join(ARMD, 'rv2arm.sh')
RV2ARM_ARM = os.path.join(ARMD, 'rv2arm_arm.bin')
QEMU = os.environ.get('QEMU') or 'qemu-aarch64-static'
HANG_S = 120
MIN_BUDGET_S = 900
STATUS_EVERY_S = 1800

W = os.path.abspath(sys.argv[1])
MODE = sys.argv[2]
MAX = int(sys.argv[3]) if len(sys.argv) > 3 else 0
NR = os.path.join(W, 'nanorun')
SH = os.path.join(W, 'shim_arm')
RV_RE = re.compile(r'nanorun: a0 = (-?\d+) .*?a1 = (\d+) output bytes')
ARM_RE = re.compile(r'shim_arm: status (-?\d+), (-?\d+) output bytes')

KW = ['def', 'match', 'with', 'let', 'in', 'fun', 'if', 'then', 'else', 'where', 'Nat', 'List', 'UInt8', 'UInt64',
      'Bool', 'true', 'false', 'put', 'len', 'rd', 'f', 'm', 'x', 'n', 'a', 'i']
NUMS = ['0', '1', '2', '7', '8', '9', '15', '16', '31', '32', '63', '64', '127', '128', '255', '256', '65535',
        '65536', '4294967295', '4294967296', '9223372036854775807', '9223372036854775808', '18446744073709551615',
        '18446744073709551616', '340282366920938463463374607431768211456', '99999999999999999999999999999999',
        '0x10', '01', '00', '-1']
PUNCT = list("()[]{}:=|,.;_'\"\\-+*<>!?@#$%&^~`\n\t ")
TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_']*|[0-9]+|\s+|.", re.S)
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
NUMRE = re.compile(r"(?<![A-Za-z0-9_'])[0-9]+")


# ---------- running ----------
def run(args, inp=None, out=None, env=None):
    fi = open(inp, 'rb') if inp else subprocess.DEVNULL
    fo = open(out, 'wb') if out else subprocess.DEVNULL
    try:
        p = subprocess.run(args, stdin=fi, stdout=fo, stderr=subprocess.PIPE, timeout=HANG_S,
                           env=dict(os.environ, **env) if env else None)
        return p.returncode, p.stderr.decode('latin-1')
    except subprocess.TimeoutExpired:
        return 'HANG', ''
    finally:
        if inp: fi.close()
        if out: fo.close()


def read(p):
    return open(p, 'rb').read() if os.path.exists(p) else b''


def norm_rv(res, out):
    rc, err = res
    if rc == 'HANG': return ('HANG',)
    m = RV_RE.search(err)
    if not m: return ('CRASH', rc)
    st, n = int(m.group(1)), int(m.group(2))
    if rc != (0 if st in (0, 1) else 1): return ('CRASH', rc)
    if st not in (0, 1): return ('ST', st)
    data = read(out)
    if len(data) != n: return ('CRASH', 'len')
    return ('ST', st, data)


def norm_arm(res, out):
    rc, err = res
    if rc == 'HANG': return ('HANG',)
    m = ARM_RE.search(err)
    if not m: return ('CRASH', rc)
    st, n = int(m.group(1)), int(m.group(2))
    if rc != (0 if st in (0, 1) else 1): return ('CRASH', rc)
    if st not in (0, 1): return ('ST', st)
    data = read(out)
    if len(data) != n: return ('CRASH', 'len')
    return ('ST', st, data)


def build():
    os.makedirs(W, exist_ok=True)
    if not os.path.exists(NR):
        run(['cc', '-O2', os.path.join(V, 'run', 'nanorun.c'), '-o', NR])
    if not os.path.exists(SH):
        run(['aarch64-linux-gnu-gcc', '-O2', '-static', os.path.join(V, 'run', 'shim', 'shim_arm.c'), '-o', SH])
    assert os.path.exists(NR) and os.path.exists(SH), 'build failed'


# ---------- mutations (on latin-1 text) ----------
def m_del_line(s, r):
    L = s.split('\n'); i = r.randrange(len(L)); del L[i]
    return '\n'.join(L), f'del_line {i}'


def m_dup_line(s, r):
    L = s.split('\n'); i = r.randrange(len(L)); L.insert(r.randrange(len(L) + 1), L[i])
    return '\n'.join(L), f'dup_line {i}'


def m_swap_lines(s, r):
    L = s.split('\n'); i, j = r.randrange(len(L)), r.randrange(len(L)); L[i], L[j] = L[j], L[i]
    return '\n'.join(L), f'swap_lines {i} {j}'


def m_dup_block(s, r):
    L = s.split('\n'); i = r.randrange(len(L)); k = r.randint(1, 12)
    B = L[i:i + k]; L[r.randrange(len(L) + 1):r.randrange(len(L) + 1)] = B
    return '\n'.join(L), f'dup_block {i} {k}'


def m_tok(s, r):
    T = TOK.findall(s); idx = [k for k, t in enumerate(T) if not t.isspace()]
    if not idx: return s, 'tok_noop'
    op = r.choice(['del', 'dup', 'swap'])
    i = r.choice(idx)
    if op == 'del': del T[i]
    elif op == 'dup': T.insert(i, T[i])
    else: j = r.choice(idx); T[i], T[j] = T[j], T[i]
    return ''.join(T), f'tok_{op} {i}'


def m_trunc(s, r):
    k = r.randrange(len(s) + 1)
    return s[:k], f'trunc {k}'


def m_ins_bytes(s, r):
    k = r.randrange(len(s) + 1); n = r.randint(1, 4)
    add = ''.join(chr(r.randrange(256)) if r.random() < 0.4 else r.choice(PUNCT) for _ in range(n))
    return s[:k] + add + s[k:], f'ins_bytes {k} {n}'


def m_del_range(s, r):
    k = r.randrange(len(s) + 1); n = r.randint(1, 30)
    return s[:k] + s[k + n:], f'del_range {k} {n}'


def m_num(s, r):
    ms = list(NUMRE.finditer(s))
    if not ms: return s, 'num_noop'
    mt = r.choice(ms)
    if r.random() < 0.6:
        new = r.choice(NUMS)
    else:
        new = str(max(0, int(mt.group()) + r.choice([-1, 1])))
    return s[:mt.start()] + new + s[mt.end():], f'num {mt.group()}->{new} @{mt.start()}'


def m_ident_one(s, r):
    ms = list(IDENT.finditer(s))
    if not ms: return s, 'ident_noop'
    mt = r.choice(ms)
    new = r.choice(KW) if r.random() < 0.5 else r.choice(ms).group()
    return s[:mt.start()] + new + s[mt.end():], f'ident_one {mt.group()}->{new} @{mt.start()}'


def m_ident_all(s, r):
    ms = list(IDENT.finditer(s))
    if not ms: return s, 'ident_noop'
    old = r.choice(ms).group()
    new = old + r.choice(['x', '_', "'", '1']) if r.random() < 0.5 else ''.join(r.choice('abcxyz') for _ in range(r.randint(1, 6)))
    return re.sub(r"(?<![A-Za-z0-9_'])" + re.escape(old) + r"(?![A-Za-z0-9_'])", new, s), f'ident_all {old}->{new}'


def m_long_ident(s, r):
    ms = list(IDENT.finditer(s))
    if not ms: return s, 'ident_noop'
    mt = r.choice(ms); n = r.choice([63, 64, 255, 256, 1000, 4097])
    new = (r.choice('abc') * n)[:n]
    return s[:mt.start()] + new + s[mt.end():], f'long_ident {n} @{mt.start()}'


def m_indent(s, r):
    L = s.split('\n'); i = r.randrange(len(L))
    body = L[i].lstrip(' \t')
    L[i] = (' ' * r.randint(0, 6) if r.random() < 0.8 else '\t' * r.randint(1, 2)) + body
    return '\n'.join(L), f'indent {i}'


def m_comment(s, r):
    L = s.split('\n'); i = r.randrange(len(L)); L.insert(i, '-- ' + 'c' * r.randint(0, 20))
    return '\n'.join(L), f'comment_ins {i}'


def m_ws(s, r):
    ms = list(re.finditer(r'\s+', s))
    if not ms: return s, 'ws_noop'
    mt = r.choice(ms); new = r.choice([' ', '\n', '\t', '', '  \n  '])
    return s[:mt.start()] + new + s[mt.end():], f'ws {mt.start()}'


def m_high(s, r):
    if not s: return s, 'high_noop'
    k = r.randrange(len(s))
    return s[:k] + chr(r.randint(0x80, 0xff)) + s[k + 1:], f'high_byte {k}'


def m_empty(s, r):
    return '', 'empty'


OPS = [m_del_line, m_dup_line, m_swap_lines, m_dup_block, m_tok, m_tok, m_trunc, m_ins_bytes, m_del_range,
       m_num, m_num, m_ident_one, m_ident_all, m_long_ident, m_indent, m_comment, m_ws, m_high, m_empty]


def mutate(s, r):
    descs = []
    for _ in range(r.choice([1, 1, 1, 2, 2, 3, 5])):
        s, d = r.choice(OPS)(s, r)
        descs.append(d)
    return s, '; '.join(descs)


# ---------- cases ----------
def strip_comments(text):
    return ''.join(l + '\n' for l in text.split('\n') if not l.startswith('--'))


def base_sources():
    ex = sorted(glob.glob(os.path.join(V, 'examples', '*.lean')))
    out = [(os.path.basename(p), strip_comments(open(p, encoding='latin-1').read())) for p in ex]
    out.append(('self_S', open(os.path.join(V, 'self_S_input.txt'), encoding='latin-1').read()))
    return out


BASES = None


def make_case(seed):
    global BASES
    if BASES is None: BASES = base_sources()
    r = random.Random(seed)
    if r.random() < 0.02:
        name, s = 'empty', ''
    else:
        name, s = r.choice(BASES[:-1] if r.random() > 0.12 else BASES[-1:])
    desc = 'none'
    if r.random() < 0.9:
        s, desc = mutate(s, r)
    inputs = [b'', bytes(r.randrange(256) for _ in range(r.randint(1, 40))),
              bytes(r.choice([0, 0xff, 0x10, 0x7f, 0x80, 0x14, 0x0a, 0x41]) if r.random() < 0.3 else r.randrange(256)
                    for _ in range(r.randint(41, 300)))]
    return s.encode('latin-1'), name, desc, inputs


def check(srcb, inputs, d):
    """Returns (kind, detail). kind None means agreement (and records accepted/program stats)."""
    os.makedirs(d, exist_ok=True)
    sp, rv, ar, parm = (os.path.join(d, f) for f in ('src', 'p.rv', 'b.arm', 'p.arm'))
    for f in (rv, ar, parm):
        if os.path.exists(f): os.remove(f)
    open(sp, 'wb').write(srcb)
    nr = norm_rv(run([NR, B2, sp, rv]), rv)
    ac = norm_arm(run([QEMU, SH, B2A], inp=sp, out=ar), ar)
    S = {'compile_rv': nr[:2] if nr[0] == 'ST' else nr, 'compile_arm': ac[:2] if ac[0] == 'ST' else ac}
    if 'HANG' in (nr[0], ac[0]): return 'hang', S
    if 'CRASH' in (nr[0], ac[0]): return 'crash', S
    if nr != ac: return 'compile', S
    if not (nr[1] == 0 and len(nr[2]) > 0):
        return None, {'accepted': False, 'st': nr[1]}
    t = run(['sh', RV2ARM, rv], out=parm, env={'RUN': f'{QEMU} {SH} {RV2ARM_ARM}'})
    if t[0] != 0:
        return 'translate', dict(S, translate_rc=t[0], err=t[1][-300:])
    for i, inp_b in enumerate(inputs):
        ip = os.path.join(d, f'in{i}'); open(ip, 'wb').write(inp_b)
        o_rv, o_arm = os.path.join(d, f'o{i}.rv'), os.path.join(d, f'o{i}.arm')
        for f in (o_rv, o_arm):
            if os.path.exists(f): os.remove(f)
        rr = norm_rv(run([NR, rv, ip, o_rv]), o_rv)
        ra = norm_arm(run([QEMU, SH, parm], inp=ip, out=o_arm), o_arm)
        if 'HANG' in (rr[0], ra[0]): return 'hang', dict(S, input=i)
        if rr[0] == 'CRASH' and ra[0] == 'CRASH': S.setdefault('both_trap', 0); S['both_trap'] += 1; continue
        if rr != ra: return 'program', dict(S, input=i, prog_rv=rr[:2] if rr[0] == 'ST' else rr,
                                             prog_arm=ra[:2] if ra[0] == 'ST' else ra)
    return None, dict(S, accepted=True, prog_len=len(open(rv, 'rb').read()))


def minimize(srcb, inputs, kind, d):
    t0 = time.time()
    pred = lambda b: check(b, inputs, os.path.join(d, 'min'))[0] == kind
    data = srcb; n = 2
    while len(data) >= 2 and time.time() - t0 < MIN_BUDGET_S:
        chunk = max(1, len(data) // n); reduced = False
        for st in range(0, len(data), chunk):
            cand = data[:st] + data[st + chunk:]
            if time.time() - t0 > MIN_BUDGET_S: break
            if cand != data and pred(cand):
                data = cand; n = max(n - 1, 2); reduced = True; break
        if not reduced:
            if n >= len(data): break
            n = min(len(data), n * 2)
    return data


def report(seed, name, desc, kind, S, srcb, inputs, shard_dir):
    fd = os.path.join(shard_dir, 'findings', f'{kind}_{seed}')
    os.makedirs(fd, exist_ok=True)
    open(os.path.join(fd, 'src.bin'), 'wb').write(srcb)
    mn = minimize(srcb, inputs, kind, fd) if kind != 'hang' else srcb
    open(os.path.join(fd, 'min.bin'), 'wb').write(mn)
    info = {'seed': seed, 'base': name, 'mutations': desc, 'kind': kind, 'detail': S,
            'inputs_hex': [i.hex() for i in inputs], 'min_len': len(mn), 'src_len': len(srcb),
            'replay': f'fuzz_arm.py {W} replay {seed}'}
    open(os.path.join(fd, 'info.json'), 'w').write(json.dumps(info, default=str, indent=1))
    print(f'MISMATCH kind={kind} seed={seed} base={name} src={len(srcb)}B min={len(mn)}B dir={fd}', flush=True)
    return fd


def main():
    build()
    if MODE == 'replay':
        seed = int(sys.argv[3])
        srcb, name, desc, inputs = make_case(seed)
        d = os.path.join(W, 'replay'); kind, S = check(srcb, inputs, d)
        print(f'seed={seed} base={name} mut={desc} kind={kind} detail={S}')
        return
    shard, nsh = map(int, MODE.split('/'))
    shard_dir = os.path.join(W, f'shard{shard}'); cd = os.path.join(shard_dir, 'case')
    os.makedirs(cd, exist_ok=True)
    cnt = dict(cases=0, accepted=0, rejected=0, programs=0, mismatches=0, hangs=0, crashes=0, translate=0, both_trap=0)
    t0 = last = time.time(); n = 0
    while MAX == 0 or n < MAX:
        seed = 1000003 * shard + n * nsh + shard
        srcb, name, desc, inputs = make_case(seed)
        kind, S = check(srcb, inputs, cd)
        n += 1; cnt['cases'] += 1
        if S.get('accepted'): cnt['accepted'] += 1; cnt['programs'] += 1
        elif kind is None: cnt['rejected'] += 1
        cnt['both_trap'] += S.get('both_trap', 0)
        if kind:
            cnt[{'compile': 'mismatches', 'program': 'mismatches', 'hang': 'hangs', 'crash': 'crashes',
                 'translate': 'translate'}[kind]] += 1
            report(seed, name, desc, kind, S, srcb, inputs, shard_dir)
        if time.time() - last >= STATUS_EVERY_S or (MAX and n == MAX):
            last = time.time()
            print(f'STATUS shard {shard}/{nsh} {time.strftime("%H:%M:%S")} elapsed {int(last - t0)}s {json.dumps(cnt)}',
                  flush=True)
    print(f'DONE shard {shard}/{nsh} {json.dumps(cnt)}', flush=True)


if __name__ == '__main__':
    main()
