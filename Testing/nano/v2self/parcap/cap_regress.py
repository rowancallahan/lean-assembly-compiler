#!/usr/bin/env python3
"""WIDTH CAP regression, whole compiler: the k = 63 doubling program (slot count 2^64 - 1 before the cap) is rejected (empty
output) by B1 (Lean-compiled C) and by the self-compiled B2 on QEMU; a small k = 2 program is accepted by both with equal output.
usage: cap_regress.py B1 B2.bin WORKDIR"""
import os, subprocess, sys
B1, B2, W = sys.argv[1:4]
V = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
def src(k):
    lets = "".join(f"let a{i+1} := (a{i}, a{i}); " for i in range(k))
    return f"def f (a0 : UInt64) : UInt64 := {lets}a0\n\ndef m (x : List UInt8) : List UInt8 := put [] (f (rd x 0))\n".encode()
b = open(B2, "rb").read(); assert len(b) % 4 == 0
def b2(s):
    d = os.path.join(W, "b2run"); os.makedirs(d, exist_ok=True)
    open(f"{d}/P.words", "w").write("B2 code\n" + " ".join(f"{int.from_bytes(b[i:i+4], 'little'):08x}" for i in range(0, len(b), 4)) + "\n")
    open(f"{d}/src.txt", "wb").write(s)
    if os.path.exists(f"{d}/O.bin"): os.remove(f"{d}/O.bin")
    subprocess.run([sys.executable, os.path.join(V, "selfrun.py"), d, "80", "512"], check=True, capture_output=True)
    return open(f"{d}/O.bin", "rb").read() if os.path.exists(f"{d}/O.bin") else b""
fail = 0
for k, acc in ((2, True), (63, False)):
    o1 = subprocess.run([B1], input=src(k), capture_output=True).stdout
    o2 = b2(src(k))
    ok = (bool(o1) == acc) and (o1 == o2)
    print(f"k={k}: B1 {len(o1)} bytes, B2 {len(o2)} bytes, expected {'accept' if acc else 'reject'}: {'OK' if ok else 'FAIL'}")
    fail += not ok
sys.exit(1 if fail else 0)
