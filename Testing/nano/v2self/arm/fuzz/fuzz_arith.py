#!/usr/bin/env python3
"""Differential fuzzer for UInt64 arithmetic in nano (UNPROVEN glue, report-only).

Random programs over + - * &&& ||| <<< >>> , literals up to 2^64-1, shift amounts 0..70 and variable shifts,
comparisons < == (and <=, != as swapped / negated forms the compiler accepts). Each program is checked three ways:
  model : a Python evaluator of the generated AST (UInt64, shifts mod 64, unsigned compare)
  rv    : B2 compiles it (nanorun), nanorun runs the RISC-V code
  arm   : rv2arm.sh with rv2arm_arm.bin under qemu-aarch64 (shim_arm), rv2arm.py must equal the same bytes
Output bytes and status must agree. Mismatches, crashes and hangs are minimized and written to FAILDIR.

usage: fuzz_arith.py WORKDIR SEED COUNT     (WORKDIR gets: nanorun, shim_arm, logs, fails/)
needs: cc, aarch64-linux-gnu-gcc, qemu-aarch64, python3; repo layout of Testing/nano/v2self/
"""
import json, os, random, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
V2 = os.path.abspath(os.path.join(HERE, '..', '..'))      # Testing/nano/v2self
ARM = os.path.join(V2, 'arm')
M = (1 << 64) - 1
QEMU = '/usr/bin/qemu-aarch64-static'
QEMU_RV = '/usr/bin/qemu-riscv64-static'
CONSTS = [0, 1, 2, 3, 5, 7, 8, 15, 16, 31, 32, 33, 63, 64, 65, 70, 127, 128, 255, 256, 2047, 2048, 4095, 4096,
          65535, 65536, 2**31 - 1, 2**31, 2**32 - 1, 2**32, 2**52, 2**63 - 1, 2**63, 2**64 - 2, 2**64 - 1]
SHIFT_AMTS = list(range(0, 71))
BIN = ['+', '-', '*', '&&&', '|||', '<<<', '>>>']


def rnd_const(r):
    return r.choice(CONSTS) if r.random() < 0.7 else r.getrandbits(64)


def gen_expr(r, depth, avail):
    if depth == 0 or r.random() < 0.2:
        if r.random() < 0.6:
            return ('var', r.choice(avail))
        return ('const', rnd_const(r))
    if r.random() < 0.25:
        cmp = r.choice(['lt', 'eq', 'le', 'ne'])
        return ('if', cmp, gen_expr(r, depth - 1, avail), gen_expr(r, depth - 1, avail),
                gen_expr(r, depth - 1, avail), gen_expr(r, depth - 1, avail))
    op = r.choice(BIN)
    if op in ('<<<', '>>>'):               # the compiler accepts only literal shift amounts
        return ('bin', op, gen_expr(r, depth - 1, avail), ('const', r.choice(SHIFT_AMTS)))
    return ('bin', op, gen_expr(r, depth - 1, avail), gen_expr(r, depth - 1, avail))


def ev(e, env):
    k = e[0]
    if k == 'var':
        return env[e[1]]
    if k == 'const':
        return e[1]
    if k == 'bin':
        a, b = ev(e[2], env), ev(e[3], env)
        op = e[1]
        return {'+': (a + b) & M, '-': (a - b) & M, '*': (a * b) & M, '&&&': a & b, '|||': a | b,
                '<<<': (a << (b % 64)) & M, '>>>': a >> (b % 64)}[op]
    a, b = ev(e[2], env), ev(e[3], env)
    t, f = ev(e[4], env), ev(e[5], env)
    if e[1] == 'lt':
        return t if a < b else f
    if e[1] == 'eq':
        return t if a == b else f
    if e[1] == 'le':                       # a <= b  is  not (b < a)
        return f if b < a else t
    return f if a == b else t              # ne: a != b  is  not (a == b)


def render(e):
    k = e[0]
    if k == 'var':
        return e[1]
    if k == 'const':
        return str(e[1])
    if k == 'bin':
        return '(%s %s %s)' % (render(e[2]), e[1], render(e[3]))
    a, b, t, f = (render(x) for x in e[2:])
    if e[1] == 'lt':
        return '(if %s < %s then %s else %s)' % (a, b, t, f)
    if e[1] == 'eq':
        return '(if %s == %s then %s else %s)' % (a, b, t, f)
    if e[1] == 'le':
        return '(if %s < %s then %s else %s)' % (b, a, f, t)
    return '(if %s == %s then %s else %s)' % (a, b, f, t)


def program_src(lets):
    def word(k):
        return ' ||| '.join(('(rd x %d <<< %d)' % (8 * k + i, 8 * i)) if i else 'rd x %d' % (8 * k) for i in range(8))
    def emit(o, v):                        # 8 bytes of v, lowest first; a helper def returning a list is rejected by B2
        for s in range(8):
            o = 'put (%s) %s' % (o, v if s == 0 else '(%s >>> %d)' % (v, 8 * s))
        return o
    body = ['  let w0 := %s;' % word(0), '  let w1 := %s;' % word(1)]
    body += ['  let t%d := %s;' % (i, render(e)) for i, e in enumerate(lets)]
    out = '[]'
    for i in range(len(lets)):
        out = emit(out, 't%d' % i)
    return 'def m (x : List UInt8) : List UInt8 :=\n' + '\n'.join(body) + '\n  ' + out + '\n'


def expected(lets, x):
    env = {'w0': int.from_bytes(x[0:8], 'little'), 'w1': int.from_bytes(x[8:16], 'little')}
    for i, e in enumerate(lets):
        env['t%d' % i] = ev(e, env)
    return b''.join(env['t%d' % i].to_bytes(8, 'little') for i in range(len(lets)))


def inputs(r):
    return [bytes(16), b'\xff' * 16, bytes(range(16)), b'\x80' * 16, b'\x01' * 16,
            bytes(r.getrandbits(8) for _ in range(16)), bytes(r.getrandbits(8) for _ in range(16))]


def run(cmd, timeout=60, stdin=None, out=None):
    try:
        p = subprocess.run(cmd, input=stdin, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'HANG', b'', ''
    return p.returncode, p.stdout, p.stderr.decode(errors='replace')


def check(lets, xs, W):
    """Return None if all three agree on every input, else a short failure label."""
    src = os.path.join(W, 'p.src'); rv = os.path.join(W, 'p.rv'); arm = os.path.join(W, 'p.arm')
    open(src, 'w').write(program_src(lets))
    rc, _, err = run([W + '/nanorun', os.path.join(V2, 'B2.bin'), src, rv])
    if rc == 'HANG':
        return 'HANG-compile'
    if not os.path.exists(rv) or os.path.getsize(rv) == 0:
        return 'B2-rejects'
    rc, out, err = run(['sh', '-c', 'RUN="%s %s/shim_arm %s/rv2arm_arm.bin" %s/rv2arm.sh %s > %s'
                        % (QEMU, W, ARM, ARM, rv, arm)], timeout=60)
    if rc == 'HANG':
        return 'HANG-translate'
    if rc != 0:
        return 'translate-error'
    orc, oout, _ = run(['python3', '-I', os.path.join(ARM, 'rv2arm.py'), rv])
    if open(arm, 'rb').read() != oout:
        return 'translator!=oracle'
    for x in xs:
        open(os.path.join(W, 'in.bin'), 'wb').write(x)
        rrc, rout, rerr = run([W + '/nanorun', rv, os.path.join(W, 'in.bin'), os.path.join(W, 'o.rv')])
        if rrc == 'HANG':
            return 'HANG-rv-run'
        o_rv = open(os.path.join(W, 'o.rv'), 'rb').read() if os.path.exists(os.path.join(W, 'o.rv')) else b''
        if 'a0 = ' not in rerr:
            return 'rv-trap'
        a0 = int(rerr.split('a0 = ')[1].split(' ')[0])
        arc, aout, aerr = run([QEMU, W + '/shim_arm', arm], stdin=x)
        if arc == 'HANG':
            return 'HANG-arm-run'
        if 'status ' not in aerr:
            return 'arm-no-status'
        st = aerr.split('status ')[1].split(',')[0]
        exp = expected(lets, x)
        if not (o_rv == aout == exp and str(a0) == st):
            return 'mismatch'
        src_rc, sout, serr = run([QEMU_RV, W + '/shim_rv', rv], stdin=x)   # RISC-V reference: shim_rv under qemu
        if src_rc == 'HANG':
            return 'HANG-shim_rv'
        if 'status ' not in serr or sout != exp or serr.split('status ')[1].split(',')[0] != str(a0):
            return 'shim_rv-mismatch'
    return None


def variants(e):
    yield ('const', 0)
    yield ('const', 1)
    if e[0] == 'bin':
        yield e[2]; yield e[3]
        for v in variants(e[2]): yield ('bin', e[1], v, e[3])
        for v in variants(e[3]): yield ('bin', e[1], e[2], v)
    if e[0] == 'if':
        yield e[4]; yield e[5]
        for i in (2, 3, 4, 5):
            for v in variants(e[i]):
                yield e[:i] + (v,) + e[i + 1:]


def shrink(lets, xs, W, label):
    progress = True
    while progress:
        progress = False
        for i in range(len(lets)):
            for v in variants(lets[i]):
                cand = lets[:i] + [v] + lets[i + 1:]
                if check(cand, xs, W) == label:
                    lets, progress = cand, True
                    break
            if progress:
                break
    return lets


def main():
    W, seed, count = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    os.makedirs(os.path.join(W, 'fails'), exist_ok=True)
    r = random.Random(seed)
    subprocess.run(['cc', '-O2', os.path.join(V2, 'run', 'nanorun.c'), '-o', W + '/nanorun'], check=True)
    subprocess.run(['aarch64-linux-gnu-gcc', '-O2', '-static', os.path.join(V2, 'run', 'shim', 'shim_arm.c'),
                    '-o', W + '/shim_arm'], check=True)
    subprocess.run(['riscv64-linux-gnu-gcc', '-O2', '-static', os.path.join(V2, 'run', 'shim', 'shim_rv.c'),
                    '-o', W + '/shim_rv'], check=True)
    stats = {'ok': 0, 'fail': 0}
    for n in range(count):
        k = r.randint(1, 4)
        lets = [gen_expr(r, r.randint(1, 4), ['w0', 'w1'] + ['t%d' % j for j in range(i)]) for i in range(k)]
        xs = inputs(r)
        label = check(lets, xs, W)
        if label is None:
            stats['ok'] += 1
        else:
            stats['fail'] += 1
            small = shrink(lets, xs, W, label)
            name = os.path.join(W, 'fails', '%d_%d_%s' % (seed, n, label))
            json.dump({'label': label, 'src': program_src(small), 'inputs': [x.hex() for x in xs],
                       'expected': [expected(small, x).hex() for x in xs]}, open(name + '.json', 'w'), indent=1)
            print('FAIL', label, name, flush=True)
        if (n + 1) % 50 == 0:
            print('progress seed=%d done=%d ok=%d fail=%d' % (seed, n + 1, stats['ok'], stats['fail']), flush=True)
    print('END seed=%d ok=%d fail=%d' % (seed, stats['ok'], stats['fail']), flush=True)


if __name__ == '__main__':
    main()
