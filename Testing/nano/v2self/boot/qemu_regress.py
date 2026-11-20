#!/usr/bin/env python3
"""Regression: fuel loops with the implicit input + 2 and 3 state words, a call with the input + 2 args, compiled by B1 (lex -> Par1 -> g41) and RUN on QEMU
(cg_test.py harness) against a Python model of the Lean semantics.  usage: qemu_regress.py B1   (needs qemu-system-riscv64 + riscv64-linux-gnu-gcc)"""
import os, subprocess, sys
B1 = sys.argv[1]
M = (1 << 64) - 1
PROGS = {
 "loop2": ("def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64\n  | 0, x, i, a => a\n  | n + 1, x, i, a => f n x (i + 1) (a + rd x i)\n"
           "def m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0 0)\n",
           lambda xs: sum(xs) & 255),
 "loop3": ("def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64\n  | 0, x, i, a, b => a + b * 2\n  | n + 1, x, i, a, b => f n x (i + 1) (a + rd x i) (b + a)\n"
           "def m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0 0 0)\n",
           lambda xs: (lambda st: (st[0] + st[1] * 2) & 255)(
               __import__("functools").reduce(lambda s, i: ((s[0] + xs[i]) & M, (s[1] + s[0]) & M), range(len(xs)), (0, 0)))),
 "call2": ("def g (x : List UInt8) (a b : UInt64) : UInt64 := a * 3 + b + rd x 0\n"
           "def m (x : List UInt8) : List UInt8 := put [] (g x (len x) 5)\n",
           lambda xs: (len(xs) * 3 + 5 + (xs[0] if xs else 0)) & 255),
 "loop2out": ("def f : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8\n  | 0, x, i, o => o\n  | n + 1, x, i, o => f n x (i + 1) (put o (rd x i + 1))\n"
              "def m (x : List UInt8) : List UInt8 := f (len' x) x 0 []\n",
              None),
}
INS = [[], [1], [5, 7], [1, 2, 3, 4, 5], list(range(1, 30))]
D = "Testing/asm/ir-words"; os.makedirs(D, exist_ok=True)
fail = 0
for name, (src, model) in PROGS.items():
    code = subprocess.run([B1], input=src.encode(), capture_output=True).stdout
    if not code: print(f"{name}: B1 REJECTED a valid program"); fail += 1; continue
    assert len(code) % 4 == 0
    ws = [int.from_bytes(code[i:i + 4], "little") for i in range(0, len(code), 4)]
    open(f"{D}/bootreg_{name}.words", "w").write(f"bootreg_{name} 1\n" + "".join(f"{w:08x}\n" for w in ws))
    cases = ""
    for xs in INS:
        if model is None: y = [(v + 1) & 255 for v in xs]
        else: y = [model(xs)]
        h = lambda b: "-" if not b else bytes(b).hex()
        cases += f"{h(xs)} {0 if y else 1} {h(y)}\n"
    open(f"{D}/bootreg_{name}.cases", "w").write(cases)
    env = dict(os.environ, BIG=str(20 << 20), NOSAIL="1")
    r = subprocess.run([sys.executable, "Testing/nano/v2self/cg_test.py", f"bootreg_{name}"], env=env, capture_output=True, text=True)
    ok = r.returncode == 0
    print(f"{name}: code {len(ws)} words; QEMU vs model on {len(INS)} inputs: {'OK' if ok else 'FAIL'}", "" if ok else (r.stdout + r.stderr)[-400:])
    fail += not ok
sys.exit(1 if fail else 0)
