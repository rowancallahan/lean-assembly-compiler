#!/usr/bin/env python3
"""Buffer/memory differential fuzzer for the nano ARM path (UNPROVEN glue, test harness only).

Random nano programs (buffers, pushes, sets, gets, input indexing near bounds, output near the 524288 capacity),
each run three ways on the same input:
  B2 (checked-in ../../B2.bin, run by nanorun) -> RISC-V code -> nanorun              = reference
  RISC-V code -> rv2arm.sh with rv2arm_arm.bin under qemu                              = ARM translator
  ARM translator output == rv2arm.py (oracle), and shim_arm under qemu on the input   = must equal the reference
Status and output bytes must agree (output compared only for status 0/1, as nanorun writes none otherwise).

usage: bufdiff.py FIRST_SEED COUNT [OUTDIR]
  OUTDIR default: ./bufdiff_out (use the scratchpad). Writes OUTDIR/log.txt (one line per program) and
  OUTDIR/fail/<seed>/ (prog.lean, minimized input, report.txt) on any mismatch, crash, hang or rejection.
Needs: cc, aarch64-linux-gnu-gcc, qemu-aarch64-static (or qemu-aarch64) in PATH, python3.
"""
import os, random, re, shutil, subprocess, sys

V = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))   # .../v2self
ARM = os.path.join(V, 'arm')
QEMU = os.environ.get('QEMU') or shutil.which('qemu-aarch64-static') or shutil.which('qemu-aarch64')
TIMEOUT = 60
CAP = 524288
NANORUN = SHIM = SHIMRV = None   # set in main()
QRV = shutil.which('qemu-riscv64-static') or shutil.which('qemu-riscv64')

# ---------------------------------------------------------------- generator
NUMS = [0, 1, 2, 3, 7, 8, 15, 16, 127, 128, 255, 256, 257, 1000, 65535, 2**32 - 1, 2**63, 2**64 - 1]

def num(R):
    return str(R.choice(NUMS)) if R.random() < 0.85 else str(R.randrange(2**64))

def leaf(R, V_, B, X):
    k = R.random()
    if V_ and k < 0.4: return R.choice(V_)
    if X and k < 0.6: return f"(rd {X} ({R.choice(V_) if V_ and R.random() < 0.6 else num(R)}))"
    if B and k < 0.8: return f"(bget {R.choice(B)} ({R.choice(V_) if V_ and R.random() < 0.5 else num(R)}))"
    if B and k < 0.9: return f"(bsize {R.choice(B)})"
    return num(R)

def wexpr(R, d, V_, B, X):
    """A UInt64 operator expression; every compound form is parenthesised, so it is an atom."""
    if d <= 0 or R.random() < 0.3: return leaf(R, V_, B, X)
    if R.random() < 0.8:
        return f"({wexpr(R, d-1, V_, B, X)} {R.choice(['+', '-', '*', '&&&', '|||'])} {wexpr(R, d-1, V_, B, X)})"
    return f"({wexpr(R, d-1, V_, B, X)} {R.choice(['<<<', '>>>'])} {R.randrange(64)})"

def cond(R, V_, B, X):
    return f"({wexpr(R, 2, V_, B, X)}) {R.choice(['==', '<'])} ({wexpr(R, 2, V_, B, X)})"

def fam_copy(R):
    """copy the input forward/backward/strided, transform each byte, sometimes two puts per step."""
    step = R.choice(['(i + 1)', '(i - 1)', f'(i + {R.randrange(2, 5)})'])
    start = R.choice(['0', '(len x)', str(R.randrange(0, 4))])
    fuel = R.choice(["(len' x)", "(len' x)", str(R.choice([0, 1, 5, 1000, CAP, CAP + 1, 600000, R.randrange(3000)]))])
    idx = wexpr(R, 2, ['i'], [], 'x')
    w = wexpr(R, 2, ['i', 'c'], [], 'x')
    if R.random() < 0.3:
        body = f"    let o1 := (put o ({w}));\n    f n x {step} (put o1 c)"
    else:
        body = f"    f n x {step} (put o ({w}))"
    return (f"def f : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8\n"
            f"  | 0, x, i, o => o\n"
            f"  | n + 1, x, i, o =>\n"
            f"    let c := (rd x ({idx}));\n"
            f"{body}\n"
            f"def m (x : List UInt8) : List UInt8 := f {fuel} x {start} []\n")

def fam_build(R, cap=False):
    """build buffer b with pushes/sets from the input; optional patch loop with bset; emit b with bget."""
    fuel1 = str(R.choice([CAP - 1, CAP, CAP + 1, CAP + 2, R.randrange(CAP - 500, CAP + 500)])) if cap \
        else R.choice(["(len' x)", "(len' x)", str(R.randrange(0, 3000))])
    fuel2 = R.choice([str(CAP), str(CAP + 3), str(R.randrange(0, 2000)), "(len' x)", str(R.randrange(0, 600000))])
    start2 = R.choice(['0', '1', '(len x)'])
    if cap:
        st = f"(if {cond(R, ['i', 'c', 'v'], ['b'], 'x')} then (bpush b (v)) else b)"
    else:
        st = f"(if {cond(R, ['i', 'c', 'v'], ['b'], 'x')} then (bpush b (v)) else (bset b ({wexpr(R, 1, ['i'], ['b'], 'x')}) (v)))"
    g = (f"def g : Nat → List UInt8 → UInt64 → Buf → Buf\n"
         f"  | 0, x, i, b => b\n"
         f"  | n + 1, x, i, b =>\n"
         f"    let c := (rd x ({wexpr(R, 2, ['i'], [], 'x')}));\n"
         f"    let v := ({wexpr(R, 2, ['i', 'c'], ['b'], 'x')});\n"
         f"    let b2 := {st};\n"
         f"    g n x (i + 1) b2\n")
    p = ""
    if not cap and R.random() < 0.5:
        p = (f"def p : Nat → List UInt8 → Buf → UInt64 → Buf\n"
             f"  | 0, x, b, j => b\n"
             f"  | n + 1, x, b, j =>\n"
             f"    let b2 := (bset b ({wexpr(R, 2, ['j'], ['b'], 'x')}) ({wexpr(R, 2, ['j'], ['b'], 'x')}));\n"
             f"    p n x b2 (j + 1)\n")
        bsrc = f"(p {R.choice(["(len' x)", str(R.randrange(0, 50))])} x (g {fuel1} x 0 bnew) 0)"
    else:
        bsrc = f"(g {fuel1} x 0 bnew)"
    h = (f"def h : Nat → List UInt8 → Buf → UInt64 → List UInt8 → List UInt8\n"
         f"  | 0, x, b, j, o => o\n"
         f"  | n + 1, x, b, j, o =>\n"
         f"    let v := ({wexpr(R, 2, ['j'], ['b'], 'x')});\n"
         f"    h n x b (j + 1) (put o v)\n")
    return g + p + h + f"def m (x : List UInt8) : List UInt8 := h {fuel2} x {bsrc} {start2} []\n"

def fam_twobuf(R):
    """two live buffers: b built from input, c built from reads of b, output interleaves both."""
    g1 = (f"def g1 : Nat → List UInt8 → UInt64 → Buf → Buf\n"
          f"  | 0, x, i, b => b\n"
          f"  | n + 1, x, i, b =>\n"
          f"    let v := ({wexpr(R, 2, ['i'], [], 'x')});\n"
          f"    g1 n x (i + 1) (bpush b (v))\n")
    g2 = (f"def g2 : Nat → List UInt8 → Buf → UInt64 → Buf → Buf\n"
          f"  | 0, x, b, i, c => c\n"
          f"  | n + 1, x, b, i, c =>\n"
          f"    let v := ({wexpr(R, 2, ['i'], ['b'], 'x')});\n"
          f"    let c2 := (if {cond(R, ['i', 'v'], ['b', 'c'], 'x')} then (bpush c (v)) else (bset c (i) (v)));\n"
          f"    g2 n x b (i + 1) c2\n")
    h = (f"def h : Nat → List UInt8 → Buf → Buf → UInt64 → List UInt8 → List UInt8\n"
         f"  | 0, x, b, c, j, o => o\n"
         f"  | n + 1, x, b, c, j, o =>\n"
         f"    let v := ({wexpr(R, 2, ['j'], ['b', 'c'], 'x')});\n"
         f"    h n x b c (j + 1) (put o v)\n")
    f1 = R.choice(["(len' x)", str(R.randrange(0, 3000))])
    f2 = R.choice(["(len' x)", str(R.randrange(0, 3000))])
    f3 = R.choice([str(R.randrange(0, 4000)), "(len' x)", str(CAP)])
    return (g1 + g2 + h +
            f"def m (x : List UInt8) : List UInt8 :=\n"
            f"  let b := (g1 {f1} x 0 bnew);\n"
            f"  let c := (g2 {f2} x b 0 bnew);\n"
            f"  h {f3} x b c 0 []\n")

FAMILIES = [('copy', fam_copy), ('build', fam_build), ('cap', lambda R: fam_build(R, cap=True)), ('twobuf', fam_twobuf)]

def gen_input(R):
    k = R.random()
    if k < 0.08: n = 0
    elif k < 0.3: n = R.randrange(1, 16)
    elif k < 0.6: n = R.choice([63, 64, 65, 255, 256, 257, 1000, 4096])
    elif k < 0.9: n = R.randrange(1, 5000)
    else: n = R.choice([70000, 200000, 300000])
    style = R.random()
    if style < 0.5: return bytes(R.randrange(256) for _ in range(n))
    if style < 0.7: return bytes(R.choice([0, 255, 0x10, 0x7f, 0x80]) for _ in range(n))
    return bytes(R.choice([0x61, 0x62]) if R.random() < 0.8 else R.randrange(256) for _ in range(n))

# ---------------------------------------------------------------- running
def sh(cmd, inp=None, env=None, timeout=TIMEOUT):
    """returns (rc, stdout bytes, stderr text); rc None on timeout"""
    try:
        r = subprocess.run(cmd, input=inp, capture_output=True, timeout=timeout, env=env)
        return r.returncode, r.stdout, r.stderr.decode(errors='replace')
    except subprocess.TimeoutExpired:
        return None, b'', 'TIMEOUT'

def parse_nano(err):
    m = re.search(r'a0 = (-?\d+).*a1 = (\d+) output bytes', err)
    return (int(m.group(1)), int(m.group(2))) if m else (None, None)

def parse_shim(err, name):
    m = re.search(name + r': status (-?\d+), (\d+) output bytes', err)
    return (int(m.group(1)), int(m.group(2))) if m else (None, None)

def pipeline(T, prog, inputs, tag):
    """returns (kind, detail). Reference = qemu-riscv64 + shim_rv on the RISC-V code (B2 compiles via the same);
    ARM = rv2arm.sh (qemu-aarch64 + shim_arm) then shim_arm under qemu-aarch64; nanorun = third opinion."""
    rv = os.path.join(T, 'p.rv'); arm = os.path.join(T, 'p.arm')
    rc, code, err = sh([QRV, SHIMRV, os.path.join(V, 'B2.bin')], inp=prog.encode())
    if rc is None: return 'hang-compile', ''
    cs, _ = parse_shim(err, 'shim_rv')
    if cs is None: return 'crash-compile', err[-300:]
    if cs not in (0, 1): return 'compile-status', f'status {cs}'
    if not code: return 'rejected', ''
    open(rv, 'wb').write(code)
    # translator
    env = dict(os.environ, RUN=f"{QEMU} {SHIM} {os.path.join(ARM, 'rv2arm_arm.bin')}")
    rc, out, err = sh(['sh', os.path.join(ARM, 'rv2arm.sh'), rv], env=env)
    if rc is None: return 'hang-translate', ''
    if rc != 0: return 'translate-fail', err[-300:]
    open(arm, 'wb').write(out)
    rc, orc, _ = sh(['python3', os.path.join(ARM, 'rv2arm.py'), rv])
    if rc != 0 or orc != out: return 'translator-vs-oracle', f'rc={rc}'
    for k, inp in enumerate(inputs):
        # reference: RISC-V under qemu-riscv64
        rc, ref, rerr = sh([QRV, SHIMRV, rv], inp=inp)
        if rc is None: return 'hang-riscv', f'input {k}'
        rs, rn = parse_shim(rerr, 'shim_rv')
        if rs is None: return 'crash-riscv', f'input {k}: {rerr[-200:]}'
        if rs in (0, 1) and len(ref) != rn: return 'riscv-length', f'input {k}: a1={rn}, wrote {len(ref)}'
        # third opinion: nanorun on the same code
        ip = os.path.join(T, f'in{k}'); open(ip, 'wb').write(inp)
        op = os.path.join(T, f'o{k}')
        if os.path.exists(op): os.remove(op)
        rc, _, nerr = sh([NANORUN, rv, ip, op])
        if rc is None: return 'hang-nanorun', f'input {k}'
        ns, _ = parse_nano(nerr)
        if ns is None: return 'crash-nanorun', f'input {k}: {nerr[-200:]}'
        nout = open(op, 'rb').read() if os.path.exists(op) else b''
        if ns != rs or (rs in (0, 1) and nout != ref):
            return 'nanorun-vs-qemu', f'input {k}: qemu {rs} {len(ref)}B, nanorun {ns} {len(nout)}B'
        # ARM under qemu-aarch64
        rc, aout, aerr = sh([QEMU, SHIM, arm], inp=inp)
        if rc is None: return 'hang-arm', f'input {k}'
        as_, an = parse_shim(aerr, 'shim_arm')
        if as_ is None: return 'crash-arm', f'input {k}: {aerr[-200:]}'
        if as_ != rs: return 'status-mismatch', f'input {k}: riscv {rs}, arm {as_}'
        if rs in (0, 1):
            if aout != ref: return 'output-mismatch', f'input {k}: status {rs}, {len(ref)} vs {len(aout)} bytes'
        elif aout:
            return 'output-on-error-status', f'input {k}: status {rs}, arm wrote {len(aout)} bytes'
    return 'ok', ''

def minimize(T, prog, inp, kind):
    """shrink the input (chunk deletion) while the same failure kind persists"""
    best = inp
    chunk = max(1, len(best) // 2)
    tries = 0
    while chunk >= 1 and tries < 150:
        i = 0; progressed = False
        while i < len(best) and tries < 150:
            cand = best[:i] + best[i + chunk:]
            tries += 1
            if pipeline(T, prog, [cand], 'min')[0] == kind:
                best = cand; progressed = True
            else:
                i += chunk
        if not progressed: chunk //= 2
    return best

def main():
    first, count = int(sys.argv[1]), int(sys.argv[2])
    out = sys.argv[3] if len(sys.argv) > 3 else os.path.join(os.getcwd(), 'bufdiff_out')
    os.makedirs(os.path.join(out, 'fail'), exist_ok=True)
    assert QEMU, 'qemu-aarch64 not found'
    global NANORUN, SHIM, SHIMRV
    T = os.path.join(out, 'tools'); os.makedirs(T, exist_ok=True)
    NANORUN, SHIM, SHIMRV = (os.path.join(T, n) for n in ('nanorun', 'shim_arm', 'shim_rv'))
    sh(['cc', '-O2', os.path.join(V, 'run', 'nanorun.c'), '-o', NANORUN])
    sh(['aarch64-linux-gnu-gcc', '-O2', '-static', os.path.join(V, 'run', 'shim', 'shim_arm.c'), '-o', SHIM])
    sh(['riscv64-linux-gnu-gcc', '-O2', '-static', os.path.join(V, 'run', 'shim', 'shim_rv.c'), '-o', SHIMRV])
    assert all(os.path.exists(x) for x in (NANORUN, SHIM, SHIMRV)), 'tool build failed'
    assert QRV, 'qemu-riscv64 not found'
    counts = {}; log = open(os.path.join(out, 'log.txt'), 'a')
    for seed in range(first, first + count):
        R = random.Random(seed)
        fname, fam = FAMILIES[R.randrange(len(FAMILIES))]
        prog = fam(R)
        inputs = [gen_input(R) for _ in range(R.randrange(3, 6))]
        tdir = os.path.join(out, 'work'); os.makedirs(tdir, exist_ok=True)
        kind, detail = pipeline(tdir, prog, inputs, seed)
        counts[kind] = counts.get(kind, 0) + 1
        log.write(f"{seed} {fname} {kind} {detail.splitlines()[0] if detail else ''}\n"); log.flush()
        if kind != 'ok':
            fd = os.path.join(out, 'fail', str(seed)); os.makedirs(fd, exist_ok=True)
            open(os.path.join(fd, 'prog.lean'), 'w').write(prog)
            bad = [i for i in inputs if pipeline(tdir, prog, [i], seed)[0] == kind] or inputs[:1]
            mi = minimize(tdir, prog, bad[0], kind) if kind in ('output-mismatch', 'status-mismatch', 'output-on-error-status') else bad[0]
            open(os.path.join(fd, 'input.bin'), 'wb').write(mi)
            open(os.path.join(fd, 'report.txt'), 'w').write(f"seed {seed} family {fname}\nkind {kind}\n{detail}\n")
            print(f"FAIL seed={seed} kind={kind} {detail[:120]}", flush=True)
        if (seed - first + 1) % 50 == 0:
            print(f"progress {seed - first + 1}/{count} {counts}", flush=True)
    print(f"done {count} {counts}", flush=True)

if __name__ == '__main__':
    main()
