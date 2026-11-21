#!/usr/bin/env python3
"""RELEASE fuzzer, native ARM by translation: B2 (RISC-V) vs N_arm (C with the JArm back end, native A64; must equal
jarm_rv(B2 output) byte for byte) on run outputs. Same families as fuzz_jarm.py; RVDIR keeps every 20th rv.
(was: Differential fuzzer for the J -> ARM TRANSLATOR (Nano/Codegen/JArm.lean).  PROTOTYPE, UNPROVEN glue.
usage: FAM=gen|arith|calls|big python3 fuzz_jarm.py SEED N WORKDIR [MUT]
Per case: B2 compiles the text (RISC-V bytes rv); the translator turns rv into A64 bytes ja (JA = its command, default
the RISC-V translator jarm_rv.bin under qemu-riscv64; JA_ARM=1: the native one jarm_arm.bin under qemu-aarch64);
GA_arm (GenArm, the oracle) compiles the text to ga.  Checks: the translator accepts every rv B2 emits, ga accepted
iff rv; every input: rv (RISC-V), ja and ga (A64) give the same status and output bytes (arith: also the Python model).
RVDIR=dir: also keep every accepted rv there (input for the spec comparison spec_cmp.lean).
Needs in $NA: shim_rv shim_arm GA_arm.bin jarm_rv.bin (JA_ARM: jarm_arm.bin)."""
import os, re, sys, random, shutil, subprocess, collections, concurrent.futures as cf
HERE = os.path.dirname(os.path.abspath(__file__)); V2 = os.path.abspath(os.path.join(HERE, '..'))
SEED, N, WORK = int(sys.argv[1]), int(sys.argv[2]), os.path.abspath(sys.argv[3])
MUT = float(sys.argv[4]) if len(sys.argv) > 4 else 0.5
NA = os.environ.get('NA', '/tmp/claude-0/na'); R = random.Random(SEED)
_argv = sys.argv; sys.argv = ['nanofuzz', '0', '0', WORK]; sys.path.insert(0, os.path.join(V2, 'fuzz'))
import nanofuzz as nf
sys.argv = _argv; nf.R = R
sys.path.insert(0, os.path.join(V2, 'arm/fuzz'))
import fuzz_arith as fa, gen as cg, nanobig as nb
FAM = os.environ.get('FAM', 'gen')
QR = ['qemu-riscv64', f'{NA}/shim_rv']; QA = ['qemu-aarch64', f'{NA}/shim_arm']

def run(cmd, inp, timeout=120):
    try: p = subprocess.run(cmd, input=inp, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired: return ('hang', b'')
    m = re.search(rb'status (-?\d+)', p.stderr)
    return (int(m.group(1)) if m else ('crash', p.returncode), p.stdout)

def inputs():
    ins = [b'', b'\x00', b'\xff', bytes([0xff] * 37), bytes(range(256)) * 2,
           bytes(R.randrange(256) for _ in range(R.choice([2, 3, 5, 8, 13, 40, 255])))]
    if R.random() < 0.1: ins.append(bytes(R.randrange(256) for _ in range(65536 + R.randrange(4096))))
    return ins

JA = QR + [f'{NA}/jarm_rv.bin']
def case(i, text, ins, want=None):
    src = text.encode()
    c1, rv = run(QR + [f'{V2}/B2.bin'], src); c2, a64 = run(QA + [f'{NA}/N_arm.bin'], src)
    if not all(isinstance(c, int) for c in (c1, c2)): return ('compiler_hang_or_crash', i, text, b'')
    if rv:
        c3, ja = run(JA, rv)
        if not isinstance(c3, int): return ('jarm_hang_or_crash', i, text, b'')
        if ja != a64: return ('N_arm!=jarm(B2)', i, text, b'')
        if os.environ.get('RVDIR') and i % 20 == 0: open(os.path.join(os.environ['RVDIR'], f'{FAM}{SEED}_{i}.rv'), 'wb').write(rv)
    if (len(rv) == 0) != (len(a64) == 0): return ('accept', i, text, b'')
    if not rv: return ('rejected', i, None, None)
    d = os.path.join(WORK, f'c{i}'); os.makedirs(d, exist_ok=True)
    open(f'{d}/rv', 'wb').write(rv); open(f'{d}/a64', 'wb').write(a64)
    for x in ins:
        r1 = run(QR + [f'{d}/rv'], x); r2 = run(QA + [f'{d}/a64'], x)
        if r1 != r2: return ('run', i, text, x)
        if not isinstance(r1[0], int): return ('hang_or_crash_both', i, text, x)
        if want is not None and r1 != (0 if want(x) else 1, want(x)): return ('model', i, text, x)
    shutil.rmtree(d)
    return ('ok', i, len(rv) // 4, len(a64) // 4)

def texts():
    if FAM == 'arith':
        for i in range(N):
            k = R.randint(1, 4)
            lets = [fa.gen_expr(R, R.randint(1, 4), ['w0', 'w1'] + ['t%d' % j for j in range(q)]) for q in range(k)]
            yield i, fa.program_src(lets), fa.inputs(R), (lambda x, l=lets: fa.expected(l, x))
        return
    if FAM == 'calls':
        for i in range(N): yield i, cg.gen(SEED * 1000003 + i), inputs(), None
        return
    if FAM == 'big':
        for i in range(N):
            ins = [b''] + [bytes(R.randrange(256) for _ in range(R.choice([1, 100, 5000, 30000, 65536]))) for _ in range(3)]
            yield i, nb.program(R), ins, None
        return
    gdir = os.path.join(WORK, 'gen')
    subprocess.run([sys.executable, os.path.join(V2, 'fuzz/nanogen.py'), str(SEED), str(N), gdir], check=True,
                   stdout=subprocess.DEVNULL)
    seeds = [open(os.path.join(V2, 'examples', f)).read() for f in sorted(os.listdir(os.path.join(V2, 'examples'))) if f.endswith('.lean')]
    seeds = ['\n'.join(l for l in s.split('\n') if not l.startswith('--')) for s in seeds]
    seeds.append(open(os.path.join(V2, 'self_S_input.txt')).read())
    for i, f in enumerate(sorted(os.listdir(gdir))[:N]):
        t = open(os.path.join(gdir, f)).read() if i % 8 else R.choice(seeds)
        yield i, (nf.mutate(t) if R.random() < MUT or i % 8 == 0 else t), inputs(), None

def main():
    os.makedirs(os.path.join(WORK, 'mismatch'), exist_ok=True); cnt = collections.Counter(); sz = [0, 0]
    with cf.ThreadPoolExecutor(int(os.environ.get('J', '4'))) as ex:
        for kind, i, a, b in ex.map(lambda c: case(*c), texts()):
            cnt[kind] += 1
            if kind == 'ok': sz[0] += a; sz[1] += b
            elif kind != 'rejected':
                open(os.path.join(WORK, 'mismatch', f'{i}.lean'), 'w').write(a); open(os.path.join(WORK, 'mismatch', f'{i}.in'), 'wb').write(b)
    print(f'{FAM} seed {SEED}: {dict(cnt)}; static words rv {sz[0]} a64 {sz[1]}')
    sys.exit(1 if set(cnt) - {'ok', 'rejected'} else 0)

if __name__ == '__main__': main()
