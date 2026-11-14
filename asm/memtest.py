#!/usr/bin/env python3
"""Test of `compileStore` (Proven/MemCompiler.lean). Input: output of memtest-data/memtest.lean.
For every case and input, the code is called with a0..a3 = inputs and s1 = &slot[i] (16-byte slots,
pre-filled with 0x55): Lean `e.denote` == the 8 bytes stored by the code on QEMU == on the Sail C emulator,
the 8 guard bytes after each slot stay 0x55 (QEMU), and the Sail emulator's only data writes are the slots.
usage: memtest.py ctest/memtest.txt"""
import os, re, subprocess, sys, time
D = os.path.dirname(os.path.abspath(__file__)); W = os.environ.get("WORK") or os.path.join(D, "ctest"); os.makedirs(W, exist_ok=True); p = lambda f: os.path.join(W, f)
SAIL = os.environ.get("SAIL", "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim")
sh = lambda c: subprocess.run(c, shell=True, check=True)
cases = []
for l in open(sys.argv[1]):
    k, *r = l.split()
    if k == "case": cases.append({"name": r[0], "t": []})
    elif k == "rv": cases[-1]["rv"] = [int(x, 16) for x in r]
    else: assert k == "t" and len(r) == 5, l; cases[-1]["t"].append([int(x, 16) for x in r])
words = lambda ws: "".join(f"  .word 0x{w:08x}\n" for w in ws)
data = lambda ts: "tab:\n" + "".join(f"  .quad {', '.join(hex(a) for a in t[:4])}\n" for t in ts) + f".align 4\nres: .rept {2*len(ts)}\n  .quad 0x5555555555555555\n.endr\n"
RV = """.section .text.start
.globl _start
_start: lla s0, tab
  lla s1, res
  li s2, %d
loop: ld a0, 0(s0)
  ld a1, 8(s0)
  ld a2, 16(s0)
  ld a3, 24(s0)
  jal ra, func
  addi s0, s0, 32
  addi s1, s1, 16
  addi s2, s2, -1
  bnez s2, loop
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
func:
%s.section .tohost,"aw"
.globl tohost
.globl fromhost
.align 6
tohost: .dword 0
fromhost: .dword 0
.data
%s"""
def qemu(elf, n):
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {elf}", shell=True, text=True)
    halt, res = (int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16) for s in ("halt", "res"))
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {elf} -display none -serial none -monitor stdio",
                         shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version"); t0 = time.time()
    while "pc       %016x" % halt not in hmp("info registers"):
        assert time.time() - t0 < 60, "QEMU did not reach halt"; time.sleep(0.01)
    hmp(f'pmemsave {res:#x} {16*n} "{p("o.bin")}"'); q.stdin.write("quit\n"); q.wait()
    b = open(p("o.bin"), "rb").read(); assert len(b) == 16 * n
    w = [int.from_bytes(b[8*i:8*i+8], "little") for i in range(2 * n)]
    return w[0::2], w[1::2], res
open(p("rv.ld"), "w").write("ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n")
total = 0
for c in cases:
    ts, n = c["t"], len(c["t"]); lean = [t[4] for t in ts]
    open(p("mem.S"), "w").write(RV % (n, words(c["rv"]), data(ts)))
    sh(f"riscv64-linux-gnu-gcc -march=rv64i -mabi=lp64 -nostdlib -static -Wl,-T,{p('rv.ld')} -Wl,--no-relax -Wl,--build-id=none {p('mem.S')} -o {p('mem.elf')}")
    rvq, guard, res = qemu(p("mem.elf"), n)
    r = subprocess.run(f"{SAIL} --inst-limit 100000000 --trace-mem --trace-output {p('sail.log')} {p('mem.elf')}", shell=True, capture_output=True, text=True)
    assert "SUCCESS" in r.stdout + r.stderr, (r.stdout + r.stderr)[-500:]
    sail = [None] * n
    for l in open(p("sail.log")):
        m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", l)
        if m and int(m.group(1), 16) >= 0x80200000:
            a = int(m.group(1), 16); assert res <= a < res + 16 * n and (a - res) % 16 == 0, l
            assert len(m.group(2)) == 16, l   # one 8-byte write
            sail[(a - res) // 16] = int(m.group(2), 16)
    for i in range(n):
        assert lean[i] == rvq[i] == sail[i] and guard[i] == 0x5555555555555555, (c["name"], ts[i], lean[i], rvq[i], sail[i], hex(guard[i]))
    total += n
    print(f"{c['name']}: {n} inputs, Lean == RV64 QEMU (stored bytes) == RV64 Sail emulator, guards intact ({len(c['rv'])} words)")
print(f"total {total} inputs")
