#!/usr/bin/env python3
"""Differential fuzzer for the shims (UNPROVEN glue; see run/README.md, run/shim/SHIM_EXPLAINED.md).

For each program (an example, or a token-mutated example accepted by B2) and each input, nanorun (ASan+UBSan build)
is compared with shim_rv under qemu-riscv64 and with shim_arm under qemu-aarch64 (code translated by arm/rv2arm.sh).
Status, exit code and output bytes must agree. Mismatches go to WORK/found/<kind>-<seed>-<n>/.

usage: fuzz.py SELF_DIR WORK_DIR SECONDS SEED      (build WORK_DIR first with build.sh)
"""
import os, random, re, subprocess, sys, time
from collections import Counter
from pathlib import Path

V, W = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
END = time.time() + float(sys.argv[3])
SEED = int(sys.argv[4])
B2, RV2ARM, TRANSLATOR = V / 'B2.bin', V / 'arm' / 'rv2arm.sh', V / 'arm' / 'rv2arm_arm.bin'
CAP = 1 << 20
ENV = dict(os.environ, ASAN_OPTIONS='detect_leaks=0')
ARM_ENV = dict(ENV, RUN=' '.join(['qemu-aarch64-static', str(W / 'shim_arm'), str(TRANSLATOR)]))
NANORUN = [str(W / 'nanorun_asan')]
RV = ['qemu-riscv64-static', str(W / 'shim_rv')]
ARM = ['qemu-aarch64-static', str(W / 'shim_arm')]
FOUND, CASE = W / 'found', W / 'case'
CASE.mkdir(parents=True, exist_ok=True)
rng = random.Random(SEED)
stats = Counter()
ALPHA = 'abcdefghijklmnopqrstuvwxyz0123456789 +-*/()[]{}|=>:,._\n'
SIZES = [0, 1, 2, 3, 4, 7, 8, 9, 16, 31, 64, 255, 256, 1000, 4096, 65535]


def sh(cmd, inp=b'', env=ENV):
    p = subprocess.run(cmd, input=inp, capture_output=True, env=env, timeout=300)   # TimeoutExpired = hang finding
    err = p.stderr.decode(errors='replace')
    if 'Sanitizer' in err or 'runtime error' in err:           # ASan/UBSan report from nanorun or a shim
        d = FOUND / f'sanitizer-{SEED}-{time.time_ns()}'
        d.mkdir(parents=True)
        (d / 'stderr.txt').write_text(err)
        (d / 'cmd.txt').write_text(' '.join(map(str, cmd)))
        stats['sanitizer'] += 1
        print(f'MISMATCH sanitizer {d}', flush=True)
    return p.returncode, p.stdout, err


def status(err):
    m = re.search(r'(?:a0 = |status )(-?\d+)', err)
    return int(m.group(1)) if m else None


def shim(cmd, inp):
    rc, out, err = sh(cmd, inp)
    return rc, status(err), out


def nano(code, inp):
    (CASE / 'in.bin').write_bytes(inp)
    out = CASE / 'nr.out'
    out.unlink(missing_ok=True)
    rc, _, err = sh(NANORUN + [str(code), str(CASE / 'in.bin'), str(out)])
    st = status(err)
    return rc, st, out.read_bytes() if rc == 0 and st in (0, 1) else b''


def verdict(nr, sr, inp):
    (rc_n, st_n, out_n), (rc_s, st_s, out_s) = nr, sr
    if rc_n not in (0, 1):
        return 'nanorun-refused'                      # trap or assert in nanorun: no reference, not compared
    if rc_s == 2 and st_s is None and len(inp) == CAP:
        return 'known-input-2^20'                     # shim_rv.c:14 / shim_arm.c:24 refuse exactly 2^20 bytes
    if st_s != st_n:
        return 'status'
    if rc_s != rc_n:
        return 'exit'
    if out_s != out_n:
        return 'bytes'
    return 'ok'


def record(kind, src, code, arm, inp, nr, sr_rv, sr_arm):
    stats['recorded'] += 1
    d = FOUND / f'{kind}-{SEED}-{stats["recorded"]}'
    d.mkdir(parents=True)
    (d / 'prog.src').write_text(src)
    (d / 'code.rv').write_bytes(code)
    (d / 'code.arm').write_bytes(arm)
    (d / 'input.bin').write_bytes(inp)
    (d / 'verdict.txt').write_text(f'nanorun={nr!r:.300}\nshim_rv={sr_rv!r:.300}\nshim_arm={sr_arm!r:.300}\n')
    print(f'MISMATCH {kind} {d} in={len(inp)}B', flush=True)


def case(src, inputs):
    prog = CASE / 'prog.src'
    prog.write_text(src)
    code = CASE / 'code.rv'
    code.unlink(missing_ok=True)
    rc, _, err = sh(NANORUN + [str(B2), str(prog), str(code)])
    st = status(err)
    if rc != 0 or st != 0 or not code.exists() or code.stat().st_size == 0:
        stats['compile-rejected'] += 1
        return
    code_b = code.read_bytes()
    stats['compiled'] += 1
    rc_s, st_s, out_s = shim(RV + [str(B2)], src.encode())
    if (rc_s, st_s, out_s) != (0, 0, code_b):
        record('compile-mismatch', src, code_b, b'', b'', (rc, st, b''), (rc_s, st_s, out_s), None)
        return
    rc, out, err = sh(['sh', str(RV2ARM), str(code)], env=ARM_ENV)
    if rc != 0:
        record('translate-fail', src, code_b, b'', b'', (rc, None, out), (None, None, err.encode()), None)
        return
    arm = CASE / 'code.arm'
    arm.write_bytes(out)
    arm_b = out
    for inp in inputs:
        nr = nano(code, inp)
        sr_rv = shim(RV + [str(code)], inp)
        sr_arm = shim(ARM + [str(arm)], inp)
        for name, sr in (('rv', sr_rv), ('arm', sr_arm)):
            v = verdict(nr, sr, inp)
            stats[f'{name}:{v}'] += 1
            if v not in ('ok', 'nanorun-refused', 'known-input-2^20'):
                record(f'{name}-{v}', src, code_b, arm_b, inp, nr, sr_rv, sr_arm)


def mutate(s):
    t = list(s)
    for _ in range(rng.randint(1, 3)):
        i, r = rng.randrange(len(t)), rng.random()
        if r < 0.4:
            t[i] = rng.choice(ALPHA)
        elif r < 0.7:
            del t[i]
        else:
            t.insert(i, rng.choice(ALPHA))
    return ''.join(t)


def strip(text):
    return '\n'.join(l for l in text.splitlines() if not l.startswith('--'))


progs = {p.stem: strip(p.read_text()) for p in sorted((V / 'examples').glob('*.lean'))}
assert len(progs) >= 8, 'examples missing'
n = 0
while time.time() < END:
    n += 1
    if n % 50 == 0:                                   # exact-capacity output sizes (reverse: out = in)
        case(progs['reverse'], [rng.randbytes(s) for s in (CAP // 2 - 1, CAP // 2)])
    src = rng.choice(list(progs.values()))
    if rng.random() < 0.7:
        src = mutate(src)
    case(src, [rng.randbytes(rng.choice(SIZES)) for _ in range(3)])
    if n % 20 == 0:
        print(f'progress programs={n} {dict(sorted(stats.items()))}', flush=True)
print(f'done programs={n} {dict(sorted(stats.items()))}', flush=True)
