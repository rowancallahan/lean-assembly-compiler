#!/usr/bin/env python3
"""Triple comparison. Input: output of scratch/triple.lean (code for both backends + Lean-evaluated results).
For every case and input: Lean `Exp.denote` == RV64 code on QEMU == RV64 code on Sail C emulator == AArch64 code on QEMU.
usage: triple.py ctest/triple.txt"""
import os, re, subprocess, sys, time
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "ctest"); p = lambda f: os.path.join(W, f)
SAIL = os.environ.get("SAIL", "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim")
sh = lambda c: subprocess.run(c, shell=True, check=True)
cases = []
for l in open(sys.argv[1]):
    k, *r = l.split()
    if k == "case": cases.append({"name": r[0], "t": []})
    elif k == "exp": cases[-1]["exp"] = l.strip()
    elif k in ("rv", "arm"): cases[-1][k] = [int(x, 16) for x in r]
    else: assert k == "t" and len(r) == 5, l; cases[-1]["t"].append([int(x, 16) for x in r])
words = lambda ws: "".join(f"  .word 0x{w:08x}\n" for w in ws)
data = lambda ts: "tab:\n" + "".join(f"  .quad {', '.join(hex(a) for a in t[:4])}\n" for t in ts) + f"res: .fill {len(ts)}, 8, 0x55\n"
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
  sd a0, 0(s1)
  addi s0, s0, 32
  addi s1, s1, 8
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
def qemu(cmd, elf, nm, pcfmt, n):
    syms = subprocess.check_output(f"{nm} {elf}", shell=True, text=True)
    halt, res = (int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16) for s in ("halt", "res"))
    q = subprocess.Popen(cmd, shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version"); t0 = time.time()
    while pcfmt % halt not in hmp("info registers"):
        assert time.time() - t0 < 60, "QEMU did not reach halt"; time.sleep(0.01)
    hmp(f'pmemsave {res:#x} {8*n} "{p("o.bin")}"'); q.stdin.write("quit\n"); q.wait()
    b = open(p("o.bin"), "rb").read(); assert len(b) == 8 * n
    return [int.from_bytes(b[8*i:8*i+8], "little") for i in range(n)], res
open(p("rv.ld"), "w").write("ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80001000; .tohost : { *(.tohost) }\n . = 0x80002000; .data : { *(.data) } }\n")
open(p("arm.ld"), "w").write("ENTRY(_start)\nSECTIONS { . = 0x40200000; .text : { *(.text.start) *(.text) } .data : { *(.data) } }\n")
for c in cases:
    ts, n = c["t"], len(c["t"]); lean = [t[4] for t in ts]
    open(p("rv.S"), "w").write(RV % (n, words(c["rv"]), data(ts)))
    sh(f"riscv64-linux-gnu-gcc -march=rv64i -mabi=lp64 -nostdlib -static -Wl,-T,{p('rv.ld')} -Wl,--no-relax -Wl,--build-id=none {p('rv.S')} -o {p('rv.elf')}")
    rvq, res = qemu(f"qemu-system-riscv64 -machine virt -m 1G -bios {p('rv.elf')} -display none -serial none -monitor stdio",
                    p("rv.elf"), "riscv64-linux-gnu-nm", "pc       %016x", n)
    r = subprocess.run(f"{SAIL} --inst-limit 100000000 --trace-mem --trace-output {p('sail.log')} {p('rv.elf')}", shell=True, capture_output=True, text=True)
    assert "SUCCESS" in r.stdout + r.stderr, (r.stdout + r.stderr)[-500:]
    sail = [None] * n
    for l in open(p("sail.log")):
        m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", l)
        if m and res <= int(m.group(1), 16) < res + 8 * n: sail[(int(m.group(1), 16) - res) // 8] = int(m.group(2), 16)
    open(p("arm.S"), "w").write(ARM % (n, words(c["arm"]), data(ts)))
    sh(f"aarch64-linux-gnu-gcc -nostdlib -static -Wl,-T,{p('arm.ld')} -Wl,--build-id=none {p('arm.S')} -o {p('arm.elf')}")
    armq, _ = qemu(f"qemu-system-aarch64 -machine virt -cpu cortex-a72 -m 1G -display none -serial none -monitor stdio -device loader,file={p('arm.elf')},cpu-num=0",
                   p("arm.elf"), "aarch64-linux-gnu-nm", "PC=%016x", n)
    for i in range(n):
        assert lean[i] == rvq[i] == sail[i] == armq[i], (c["name"], c.get("exp"), ts[i], lean[i], rvq[i], sail[i], armq[i])
    print(f"{c['name']}: {n} inputs, Lean == RV64 QEMU == RV64 Sail emulator == AArch64 QEMU ({len(c['rv'])} / {len(c['arm'])} words)")
