#!/usr/bin/env python3
"""Run P (words from selfcompile.lean) on QEMU with src.txt as input.  usage: selfrun.py DIR WORK_MB OUT_KB
Convention: a0 input, a1 length, a2 work base (8-aligned), a3 output, sp = work end.  Writes DIR/O.bin (output bytes), prints a0/a1/instructions-free timing.
FILL=0xa5: the work memory starts filled with that byte instead of zeros (checks no uninitialised reads)."""
import os, re, subprocess, sys, time
D, WK, OUT = sys.argv[1], int(sys.argv[2]) << 20, int(sys.argv[3]) << 10
x = open(f"{D}/src.txt", "rb").read()
words = [int(l, 16) for l in open(f"{D}/P.words").read().split()[2:]]
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80000000 + 0x%x; .tohost : { *(.tohost) }\n . = 0x80000000 + 0x%x; .data : { *(.data) } .bss : { *(.bss) } }\n"
tx = (len(words) * 4 + 0xfffff) // 0x100000 * 0x100000
LD = LD % (tx + 0x100000, tx + 0x200000)
S = f""".section .text.start
.globl _start
_start: lla s0, tab
  ld a0, 0(s0)
  ld a1, 8(s0)
  ld a2, 16(s0)
  ld a3, 24(s0)
  ld sp, 32(s0)
  jal ra, func
  sd sp, 56(s0)
  sd a1, 64(s0)
  sd a0, 72(s0)
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
func:
""" + "".join(f"  .word 0x{w:08x}\n" for w in words) + f""".section .tohost,"aw"
.globl tohost
.align 6
tohost: .dword 0
.data
.align 4
base:
.incbin "{D}/in.bin"
.align 3
tab: .quad base, {len(x)}, work, outb, work+{WK}, 0, 0, 0, 0, 0
.bss
.align 4
outb: .space {OUT}
""" + (f"""
.align 4
work: .space {WK}
""" if not os.environ.get("FILL") else f"""
.data
.align 4
work: .space {WK}, {os.environ["FILL"]}
""")
open(f"{D}/in.bin", "wb").write(x); open(f"{D}/t.S", "w").write(S); open(f"{D}/m.ld", "w").write(LD)
sh = lambda c: subprocess.run(c, shell=True, check=True)
sh(f"riscv64-linux-gnu-gcc -march=rv64im_zicsr -mabi=lp64 -nostdlib -static -Wl,-T,{D}/m.ld -Wl,--no-relax -Wl,--build-id=none {D}/t.S -o {D}/t.elf")
syms = subprocess.check_output(f"riscv64-linux-gnu-nm {D}/t.elf", shell=True, text=True)
sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
halt, tab, outb = sym("halt"), sym("tab"), sym("outb")
mem = (WK + OUT) >> 20
q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m {mem + 64 + (tx >> 20)}M -bios {D}/t.elf -display none -serial none -monitor stdio",
                     shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
def hmp(c):
    q.stdin.write(c + "\n"); buf = ""
    while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
    return buf
hmp("info version"); t = time.time()
while "pc       %016x" % halt not in hmp("info registers"):
    time.sleep(0.2)
    if time.time() - t > float(os.environ.get("TMO", "1200")): print("TIMEOUT"); print(hmp("info registers")[:1800]); q.kill(); sys.exit(2)
el = time.time() - t
hmp(f'pmemsave {tab:#x} 80 "{D}/tab.bin"'); hmp(f'pmemsave {outb:#x} {OUT} "{D}/out.bin"'); q.stdin.write("quit\n"); q.wait()
e = open(f"{D}/tab.bin", "rb").read(); g = lambda o: int.from_bytes(e[o:o + 8], "little")
a0, a1 = g(72), g(64)
print(f"QEMU time {el:.1f}s; a0 = {a0 if a0 < 2**63 else a0 - 2**64}, a1 (output bytes) = {a1}")
if a0 == 0: open(f"{D}/O.bin", "wb").write(open(f"{D}/out.bin", "rb").read()[:a1])
