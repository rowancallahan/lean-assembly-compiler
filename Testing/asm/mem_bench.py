#!/usr/bin/env python3
"""Run-time cost of the memory checks: instructions retired (minstret, QEMU) by one call of the inductive-path code
without checks (`Testing/asm/frontx-words/<name>.words`, the old theorem's static work bound) and with them
(`Testing/asm/mem-words/<name>.words`, work block = memoryNeeded), on the largest input of the first N cases.
usage: mem_bench.py N name..."""
import os, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__)); C = os.path.join(D, "ctest"); os.makedirs(C, exist_ok=True)
p = lambda f: os.path.join(C, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n"
unhex = lambda h: [] if h == "-" else list(bytes.fromhex(h))
def count(words, inp, wk, outlen):
    func = "".join(f"  .word 0x{w:08x}\n" for w in words)
    data = ",".join(str(b) for b in inp) or "0"
    src = f""".section .text.start
.globl _start
_start: lla a0, inp
  li a1, {len(inp)}
  lla a2, work
  lla a3, out
  li t0, {wk}
  add sp, a2, t0
  csrr s1, minstret
  jal ra, func
  csrr s2, minstret
  sub s3, s2, s1
  lla t0, res
  sd s3, 0(t0)
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
func:
{func}
.section .tohost,"aw"
.globl tohost
.align 6
tohost: .dword 0
fromhost: .dword 0
.data
.align 4
inp: .byte {data}
.align 4
out: .zero {max(outlen, 1)}
.align 3
res: .dword 0
.align 4
work: .zero {wk + 16}
"""
    open(p("b.S"), "w").write(src); open(p("b.ld"), "w").write(LD)
    sh(f"riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -nostdlib -static -Wl,-T,{p('b.ld')} -Wl,--no-relax "
       f"-Wl,--build-id=none {p('b.S')} -o {p('b.elf')}")
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {p('b.elf')}", shell=True, text=True)
    sym = lambda s: int([l for l in syms.split("\n") if l.endswith(" " + s)][0].split()[0], 16)
    halt, res = sym("halt"), sym("res")
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {p('b.elf')} -display none -serial none "
                         f"-monitor stdio", shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version")
    while "pc       %016x" % halt not in hmp("info registers"): pass
    hmp(f'pmemsave {res:#x} 8 "{p("b.res")}"'); q.stdin.write("quit\n"); q.wait()
    return int.from_bytes(open(p("b.res"), "rb").read(), "little")
N = int(sys.argv[1])
for name in sys.argv[2:]:
    old = [l for l in open(os.path.join(D, "frontx-words", name + ".words")) if l.strip()]
    new = [l for l in open(os.path.join(D, "mem-words", name + ".words")) if l.strip()]
    cases = [l.split() for l in open(os.path.join(D, "mem-words", name + ".cases")) if l.strip()][:N]
    oc = [l.split() for l in open(os.path.join(D, "frontx-words", name + ".cases")) if l.strip()][:N]
    i = max(range(len(cases)), key=lambda k: len(unhex(cases[k][0])))
    inp, outp, M = unhex(cases[i][0]), unhex(cases[i][1]), int(cases[i][2])
    hd = old[0].split()
    wk_old = int(hd[1]) + int(hd[2]) * len(inp) if hd[0] == "ind" else int(oc[i][2])
    a = count([int(w, 16) for w in old[1:]], inp, wk_old, len(outp))
    b = count([int(w, 16) for w in new[1:]], inp, M, len(outp))
    print(f"{name}: input {len(inp)} bytes: {a} instructions without checks (work {wk_old} bytes), {b} with "
          f"(work {M} bytes = memoryNeeded): +{100 * (b - a) / a:.0f}%; words {len(old) - 1} -> {len(new) - 1}")
