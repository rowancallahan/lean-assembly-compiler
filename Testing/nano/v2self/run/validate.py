#!/usr/bin/env python3
"""Validate nanorun (UNPROVEN glue): (1) self-compile: nanorun B2 on C's source must give B2 byte for byte;
(2) the qemu_regress programs: compile with nanorun B2, run with nanorun on 5 inputs, compare with the Python model of
the Lean semantics and, with QEMU=1, with qemu-system-riscv64 (cg_test.py);  (3) too little work memory gives a0 = -1;
(4) with SHIM="qemu-riscv64-static /tmp/shim_rv": the same through the native shim (shim/shim_rv.c).
usage (from the repository root):  python3 Testing/nano/v2self/run/validate.py [NANORUN]   (default: builds /tmp/nanorun)"""
import functools, hashlib, os, subprocess, sys, tempfile, time
V = "Testing/nano/v2self"; M = (1 << 64) - 1
NR = sys.argv[1] if len(sys.argv) > 1 else "/tmp/nanorun"
if len(sys.argv) == 1: subprocess.run(["cc", "-O2", f"{V}/run/nanorun.c", "-o", NR], check=True)
T = tempfile.mkdtemp()
def run(code, inp, out, work=None):
    t = time.time()
    r = subprocess.run([NR, code, inp, out] + ([str(work)] if work else []), capture_output=True, text=True)
    return r.returncode, r.stderr.strip(), time.time() - t
# (1) fixed point
rc, msg, dt = run(f"{V}/B2.bin", f"{V}/self_S_input.txt", f"{T}/B3.bin")
b2 = open(f"{V}/B2.bin", "rb").read()
assert rc == 0 and open(f"{T}/B3.bin", "rb").read() == b2, msg
assert hashlib.sha256(b2).hexdigest() == open(f"{V}/B2.sha256").read().split()[0]
print(f"self-compile: B3 == B2 ({len(b2)} bytes, sha256 {hashlib.sha256(b2).hexdigest()[:8]}…), {dt:.1f} s; {msg}")
# (3) out of memory is reported, not crashed
rc, msg, dt = run(f"{V}/B2.bin", f"{V}/self_S_input.txt", f"{T}/x.bin", 1)
assert rc == 1 and "a0 = -1" in msg, msg
print(f"self-compile with 1 MiB work: {msg}")
# (2) regression programs (the ones of boot/qemu_regress.py)
PROGS = {
 "loop2": ("def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64\n  | 0, x, i, a => a\n  | n + 1, x, i, a => f n x (i + 1) (a + rd x i)\n"
           "def m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0 0)\n", lambda xs: [sum(xs) & 255]),
 "loop3": ("def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64\n  | 0, x, i, a, b => a + b * 2\n  | n + 1, x, i, a, b => f n x (i + 1) (a + rd x i) (b + a)\n"
           "def m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0 0 0)\n",
           lambda xs: [(lambda st: (st[0] + st[1] * 2) & 255)(functools.reduce(lambda s, i: ((s[0] + xs[i]) & M, (s[1] + s[0]) & M), range(len(xs)), (0, 0)))]),
 "call2": ("def g (x : List UInt8) (a b : UInt64) : UInt64 := a * 3 + b + rd x 0\n"
           "def m (x : List UInt8) : List UInt8 := put [] (g x (len x) 5)\n", lambda xs: [(len(xs) * 3 + 5 + (xs[0] if xs else 0)) & 255]),
 "loop2out": ("def f : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8\n  | 0, x, i, o => o\n  | n + 1, x, i, o => f n x (i + 1) (put o (rd x i + 1))\n"
              "def m (x : List UInt8) : List UInt8 := f (len' x) x 0 []\n", lambda xs: [(v + 1) & 255 for v in xs]),
}
INS = [[], [1], [5, 7], [1, 2, 3, 4, 5], list(range(1, 30))]
for name, (src, model) in PROGS.items():
    open(f"{T}/{name}.lean", "w").write(src)
    rc, msg, dt = run(f"{V}/B2.bin", f"{T}/{name}.lean", f"{T}/{name}.bin")
    assert rc == 0, (name, msg)
    code = open(f"{T}/{name}.bin", "rb").read(); tq = 0.0
    for k, xs in enumerate(INS):
        open(f"{T}/in.bin", "wb").write(bytes(xs))
        rc, msg, _ = run(f"{T}/{name}.bin", f"{T}/in.bin", f"{T}/out.bin", 20)
        y = bytes(model(xs))
        assert rc == 0 and open(f"{T}/out.bin", "rb").read() == y and f"a0 = {0 if y else 1} " in msg, (name, xs, msg)
    if os.environ.get("QEMU"):
        # the same code on qemu-system-riscv64 through the usual harness (cg_test.py: words + cases, QEMU only)
        W = "Testing/asm/ir-words"; h = lambda b: "-" if not b else bytes(b).hex()
        open(f"{W}/nrun_{name}.words", "w").write(f"nrun_{name} 1\n" + "".join(f"{int.from_bytes(code[i:i+4], 'little'):08x}\n" for i in range(0, len(code), 4)))
        open(f"{W}/nrun_{name}.cases", "w").write("".join(f"{h(xs)} {0 if model(xs) else 1} {h(model(xs))}\n" for xs in INS))
        t = time.time()
        q = subprocess.run([sys.executable, f"{V}/cg_test.py", f"nrun_{name}"], env=dict(os.environ, BIG=str(20 << 20), NOSAIL="1"), capture_output=True, text=True)
        tq = time.time() - t
        os.remove(f"{W}/nrun_{name}.words"); os.remove(f"{W}/nrun_{name}.cases")
        assert q.returncode == 0, (name, (q.stdout + q.stderr)[-400:])
    print(f"{name}: compiled by nanorun B2 in {dt:.2f} s ({len(code)} bytes); {len(INS)} inputs agree with the model" +
          (f" and with QEMU ({tq:.0f} s)" if os.environ.get("QEMU") else ""))
# the native shim (shim/shim_rv.c), e.g. SHIM="qemu-riscv64-static /tmp/shim_rv" (or just the binary on a RISC-V machine)
if os.environ.get("SHIM"):
    sh = os.environ["SHIM"].split()
    t = time.time(); r = subprocess.run(sh + [f"{V}/B2.bin"], input=open(f"{V}/self_S_input.txt", "rb").read(), capture_output=True)
    assert r.returncode == 0 and r.stdout == b2, r.stderr
    print(f"shim self-compile: stdout == B2, {time.time() - t:.1f} s")
    for name, (src, model) in PROGS.items():
        code = subprocess.run(sh + [f"{V}/B2.bin"], input=src.encode(), capture_output=True, check=True).stdout
        assert code == open(f"{T}/{name}.bin", "rb").read(), name
        for xs in INS:
            r = subprocess.run(sh + [f"{T}/{name}.bin"], input=bytes(xs), capture_output=True)
            assert r.returncode == 0 and r.stdout == bytes(model(xs)), (name, xs, r.stderr)
        print(f"shim {name}: same code as nanorun; {len(INS)} inputs (stdin) agree with the model")
print("ALL OK")
