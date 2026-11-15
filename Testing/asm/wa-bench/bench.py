# usage: python3 bench.py NAME CFUNC n...: instructions of one call (minstret, qemu -icount) of the words
# frontx-words/NAME.words (Implements1 convention) vs the C function CFUNC(inp, n) of crc.c (gcc -O2, rv64i)
import subprocess, sys, re, os
D = os.path.dirname(os.path.abspath(__file__)); C = os.path.join(D, "..", "ctest"); os.makedirs(C, exist_ok=True)
p = lambda f: os.path.join(C, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n"
def run(name, cfunc, n):
    lines = open(os.path.join(D, "..", "frontx-words", name + ".words")).read().split("\n")
    A, N, B, _ = map(int, lines[0].split()[1:])
    ws = [int(l, 16) for l in lines[1:] if l.strip()]
    func = "".join(f"  .word 0x{w:08x}\n" for w in ws)
    wk = 8 * (A + B * n) + 8 * (N + 1) + 7
    src = f""".section .text.start
.globl _start
_start: lla a0, inp
  li a1, {n}
  lla a2, work
  lla a3, out
  lla sp, wend
  csrr s1, minstret
  jal ra, func
  csrr s2, minstret
  sub s3, s2, s1
  lla t0, res
  sd s3, 0(t0)
  lla a0, inp
  li a1, {n}
  lla sp, wend
  csrr s1, minstret
  call {cfunc}
  csrr s2, minstret
  sub s3, s2, s1
  lla t0, res
  sd s3, 8(t0)
  sd a0, 16(t0)
halt: j halt
func:
{func}
.section .tohost,"aw"
.globl tohost
.globl fromhost
.align 6
tohost: .dword 0
fromhost: .dword 0
.data
.align 4
res: .dword 0, 0, 0
out: .dword 0
inp: .fill {n}, 1, 7
.align 4
work: .fill {wk + 64}, 1, 0
wend: .dword 0
"""
    open(p("b.S"), "w").write(src); open(p("m.ld"), "w").write(LD)
    sh(f"riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -O2 -ffreestanding -nostdlib -static -Wl,-T,{p('m.ld')} "
       f"-Wl,--no-relax -Wl,--build-id=none {p('b.S')} {os.path.join(D, 'crc.c')} -o {p('b.elf')}")
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {p('b.elf')}", shell=True, text=True)
    sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -icount shift=0 -bios {p('b.elf')} -display none "
                         f"-serial none -monitor stdio", shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version")
    while "pc       %016x" % sym("halt") not in hmp("info registers"): pass
    hmp(f'pmemsave {sym("res"):#x} 24 "{p("r.bin")}"'); q.stdin.write("quit\n"); q.wait()
    r = open(p("r.bin"), "rb").read()
    ours, theirs = int.from_bytes(r[0:8], "little"), int.from_bytes(r[8:16], "little")
    return ours, theirs, len(ws)
name, cfunc = sys.argv[1], sys.argv[2]
for n in map(int, sys.argv[3:]):
    o, t, w = run(name, cfunc, n)
    print(f"{name} n={n}: {o} instructions ({o / max(n, 1):.2f}/byte, {w} words) vs gcc -O2 {t} ({t / max(n, 1):.2f}/byte)")
