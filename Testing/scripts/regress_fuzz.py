#!/usr/bin/env python3
"""regress_fuzz.py: does a NEW compiler binary behave like an OLD one?  (code bytes may differ; RUN OUTPUTS may not)

usage: regress_fuzz.py [-n N] [--seed S] [--old-rv B2.bin] [--new-rv B2.bin] [--old-arm GA_arm.bin] [--new-arm GA_arm.bin]
  defaults: old = the file at origin/main (git show), new = the working tree:
    RISC-V compiler  Testing/nano/v2self/B2.bin                  (runs on qemu-riscv64, emits RISC-V code)
    native ARM       Testing/nano/v2self/native_arm/GA_arm.bin   (runs on qemu-aarch64, emits A64 code; skipped if the
                     old ref has none)
Programs: the examples, C's own source, and N fuzz programs rotating the families of native_arm/fuzz_native.py
(nanogen + mutation, UInt64 arithmetic, calls/recursion, big buffers). Per program and compiler pair: both accept or
both reject, and every run (several inputs) gives the same status and output bytes. Any difference, crash or hang is
printed loudly and saved in WORKDIR (default a temp dir); exit 1 if any. UNPROVEN test glue."""
import argparse, os, random, re, subprocess, sys, tempfile, collections
R = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
V2 = os.path.join(R, 'Testing/nano/v2self')
ap = argparse.ArgumentParser()
ap.add_argument('-n', type=int, default=400); ap.add_argument('--seed', type=int, default=1)
ap.add_argument('--old-rv'); ap.add_argument('--new-rv', default=os.path.join(V2, 'B2.bin'))
ap.add_argument('--old-arm'); ap.add_argument('--new-arm', default=os.path.join(V2, 'native_arm/GA_arm.bin'))
ap.add_argument('--ref', default='origin/main'); ap.add_argument('--work')
A = ap.parse_args()
W = A.work or tempfile.mkdtemp(prefix='regress_'); os.makedirs(W, exist_ok=True)
Rnd = random.Random(A.seed)

def git_file(path, out):
    p = subprocess.run(['git', '-C', R, 'show', f'{A.ref}:{path}'], capture_output=True)
    if p.returncode != 0: return None
    open(out, 'wb').write(p.stdout); return out
old_rv = A.old_rv or git_file('Testing/nano/v2self/B2.bin', f'{W}/old_B2.bin')
old_arm = A.old_arm or git_file('Testing/nano/v2self/native_arm/GA_arm.bin', f'{W}/old_GA_arm.bin')
assert old_rv, f'no old RISC-V compiler (give --old-rv or a ref with Testing/nano/v2self/B2.bin)'
for c, s in (('riscv64-linux-gnu-gcc', 'shim_rv'), ('aarch64-linux-gnu-gcc', 'shim_arm')):
    subprocess.run([c, '-O2', '-static', f'{V2}/run/shim/{s}.c', '-o', f'{W}/{s}'], check=True)
QR = ['qemu-riscv64', f'{W}/shim_rv']; QA = ['qemu-aarch64', f'{W}/shim_arm']
PAIRS = [('rv', QR, old_rv, A.new_rv)] + ([('arm', QA, old_arm, A.new_arm)] if old_arm else [])
if not old_arm: print(f'note: {A.ref} has no native_arm/GA_arm.bin: native ARM pair skipped')

def run(cmd, inp, timeout=120):
    try: p = subprocess.run(cmd, input=inp, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired: return ('hang', b'')
    m = re.search(rb'status (-?\d+)', p.stderr)
    return (int(m.group(1)) if m else ('crash', p.returncode), p.stdout)

sys.path[:0] = [os.path.join(V2, 'fuzz'), os.path.join(V2, 'arm/fuzz')]
_argv = sys.argv; sys.argv = ['nanofuzz', '0', '0', W]
import nanofuzz as nf, fuzz_arith as fa, gen as cg, nanobig as nb
sys.argv = _argv; nf.R = Rnd
def strip(t): return '\n'.join(l for l in t.split('\n') if not l.startswith('--'))
def ins_small(): return [b'', b'\x00', b'\xff' * 37, bytes(range(256)) * 2, bytes(Rnd.randrange(256) for _ in range(Rnd.choice([3, 13, 255])))]
def programs():
    seeds = [(f, strip(open(os.path.join(V2, 'examples', f)).read())) for f in sorted(os.listdir(os.path.join(V2, 'examples'))) if f.endswith('.lean')]
    selfsrc = open(os.path.join(V2, 'self_S_input.txt')).read()
    for f, t in seeds: yield f, t, ins_small()
    yield 'self_S_input', selfsrc, [selfsrc.encode()]
    gdir = os.path.join(W, 'gen'); subprocess.run([sys.executable, os.path.join(V2, 'fuzz/nanogen.py'), str(A.seed), str(A.n), gdir], check=True, stdout=subprocess.DEVNULL)
    gens = sorted(os.listdir(gdir))
    for i in range(A.n):
        k = i % 4
        if k == 0:
            t = open(os.path.join(gdir, gens[i])).read() if i % 16 else Rnd.choice([t for _, t in seeds] + [selfsrc])
            yield f'gen{i}', (nf.mutate(t) if Rnd.random() < 0.3 or i % 16 == 0 else t), ins_small()
        elif k == 1:
            lets = [fa.gen_expr(Rnd, Rnd.randint(1, 4), ['w0', 'w1'] + ['t%d' % j for j in range(q)]) for q in range(Rnd.randint(1, 4))]
            yield f'arith{i}', fa.program_src(lets), fa.inputs(Rnd)
        elif k == 2: yield f'calls{i}', cg.gen(A.seed * 1000003 + i), ins_small()
        else: yield f'big{i}', nb.program(Rnd), [b''] + [bytes(Rnd.randrange(256) for _ in range(Rnd.choice([100, 5000, 65536]))) for _ in range(2)]

bad = 0; cnt = collections.Counter()
def report(kind, name, text, detail, x=b''):
    global bad; bad += 1
    d = os.path.join(W, 'mismatch'); os.makedirs(d, exist_ok=True)
    open(f'{d}/{name}.lean', 'w').write(text); open(f'{d}/{name}.in', 'wb').write(x)
    print(f'*** REGRESSION {kind} {name}: {detail} (saved in {d})', flush=True)
for name, text, ins in programs():
    src = text.encode()
    for tag, Q, old, new in PAIRS:
        c1, o = run(Q + [old], src); c2, nw = run(Q + [new], src)
        if not (isinstance(c1, int) and isinstance(c2, int)): report(f'{tag}:compiler', name, text, f'old {c1} new {c2}'); continue
        if (len(o) == 0) != (len(nw) == 0): report(f'{tag}:accept', name, text, f'old {len(o)} bytes, new {len(nw)} bytes'); continue
        if not o: cnt[f'{tag} rejected'] += 1; continue
        open(f'{W}/o', 'wb').write(o); open(f'{W}/n', 'wb').write(nw)
        for x in ins:
            r1 = run(Q + [f'{W}/o'], x); r2 = run(Q + [f'{W}/n'], x)
            if r1 != r2 or not isinstance(r1[0], int):
                report(f'{tag}:run', name, text, f'old {r1[0]} {len(r1[1])}B, new {r2[0]} {len(r2[1])}B', x); break
        else: cnt[f'{tag} same'] += 1
print(f'regress_fuzz: {A.n} fuzz + {sum(f.endswith(".lean") for f in os.listdir(os.path.join(V2, "examples")))} examples + self; {dict(cnt)}; regressions {bad}; old {A.ref}; work {W}')
sys.exit(1 if bad else 0)
