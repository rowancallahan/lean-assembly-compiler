#!/usr/bin/env python3
"""Lean ARM model (armrun) vs `expected` (Lean Exp.denote) vs AArch64 QEMU, for every input of a triple.txt.
usage: compare.py ARMRUN triple.txt WORKDIR.   QEMU part copied from asm/triple.py."""
import os, re, subprocess, sys, time
armrun, src, W = sys.argv[1:]; p = lambda f: os.path.join(W, f); os.makedirs(W, exist_ok=True)
sh = lambda c: subprocess.run(c, shell=True, check=True)
cases = []
for l in open(src):
    k, *r = l.split()
    if k == "case": cases.append({"name": r[0], "t": []})
    elif k in ("rv", "arm"): cases[-1][k] = r
    elif k == "exp": cases[-1]["exp"] = " ".join(r)
    else: assert k == "t" and len(r) == 5, l; cases[-1]["t"].append(r)
N = sum(len(c["t"]) for c in cases)
open(p("in.txt"), "w").write("".join(" ".join(t[:4] + c["arm"]) + "\n" for c in cases for t in c["t"]))
t0 = time.time(); out = subprocess.check_output([armrun, "run", p("in.txt")], text=True).split(); dt = time.time() - t0
assert len(out) == N
model = [int(x, 16) for x in out]
ARM = """.section .text.start
.globl _start
_start: ldr x19, =tab
  ldr x20, =res
  ldr x21, =%d
loop: ldp x0, x1, [x19]
  ldp x2, x3, [x19, #16]
  bl func
  str x0, [x20], #8
  add x19, x19, #32
  subs x21, x21, #1
  b.ne loop
halt: b halt
.ltorg
func:
%s.data
%s"""
def qemu(cmd, elf, n):
    syms = subprocess.check_output(f"aarch64-linux-gnu-nm {elf}", shell=True, text=True)
    halt, res = (int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16) for s in ("halt", "res"))
    q = subprocess.Popen(cmd, shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version"); t0 = time.time()
    while "PC=%016x" % halt not in hmp("info registers"):
        assert time.time() - t0 < 60, "QEMU did not reach halt"; time.sleep(0.01)
    hmp(f'pmemsave {res:#x} {8*n} "{p("o.bin")}"'); q.stdin.write("quit\n"); q.wait()
    b = open(p("o.bin"), "rb").read(); assert len(b) == 8 * n
    return [int.from_bytes(b[8*i:8*i+8], "little") for i in range(n)]
open(p("arm.ld"), "w").write("ENTRY(_start)\nSECTIONS { . = 0x40200000; .text : { *(.text.start) *(.text) } .data : { *(.data) } }\n")
bad, k = 0, 0
for c in cases:
    ts, n = c["t"], len(c["t"])
    data = "tab:\n" + "".join(f"  .quad {', '.join('0x' + a for a in t[:4])}\n" for t in ts) + f"res: .fill {n}, 8, 0x55\n"
    open(p("arm.S"), "w").write(ARM % (n, "".join(f"  .word 0x{w}\n" for w in c["arm"]), data))
    sh(f"aarch64-linux-gnu-gcc -nostdlib -static -Wl,-T,{p('arm.ld')} -Wl,--build-id=none {p('arm.S')} -o {p('arm.elf')}")
    q = qemu(f"qemu-system-aarch64 -machine virt -cpu cortex-a72 -m 1G -display none -serial none -monitor stdio -device loader,file={p('arm.elf')},cpu-num=0", p("arm.elf"), n)
    b = 0
    for i, t in enumerate(ts):
        e, m = int(t[4], 16), model[k + i]
        if not e == m == q[i]: b += 1; print(f"MISMATCH {c['name']} exp={c.get('exp')} words={' '.join(c['arm'])} inputs={t[:4]} expected={e:x} model={m:x} qemu={q[i]:x}")
    print(f"{c['name']}: {n} inputs, {len(c['arm'])} words, mismatches {b}"); bad += b; k += n
print(f"TOTAL {N} inputs, {len(cases)} cases, mismatches {bad}; model runner {dt:.2f} s = {N/dt:.0f} inputs/s (incl. startup and reset)")
assert bad == 0
