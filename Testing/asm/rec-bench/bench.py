# usage: python3 bench.py [n_sum] [n_fib]; instructions executed by one call (minstret, qemu -icount): frontx_rec words vs gcc -O2
import subprocess, sys, re, os
D = os.path.dirname(os.path.abspath(__file__)); C = os.path.join(D, "..", "ctest"); os.makedirs(C, exist_ok=True)
p = lambda f: os.path.join(C, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n"
def run(words_file, cfunc, n, cargs):
    ws = [int(l, 16) for l in open(words_file).read().split()[2:]]
    func = "".join(f"  .word 0x{w:08x}\n" for w in ws)
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
  {cargs}
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
work: .fill {200 * (n + 2)}, 1, 0
wend: .dword 0
"""
    open(p("b.S"), "w").write(src); open(p("m.ld"), "w").write(LD)
    sh(f"riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -O2 -ffreestanding -nostdlib -static -Wl,-T,{p('m.ld')} -Wl,--no-relax -Wl,--build-id=none {p('b.S')} {os.path.join(D, "rec.c")} -o {p('b.elf')}")
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {p('b.elf')}", shell=True, text=True)
    sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -icount shift=0 -bios {p('b.elf')} -display none -serial none -monitor stdio",
                         shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version")
    while "pc       %016x" % sym("halt") not in hmp("info registers"): pass
    hmp(f'pmemsave {sym("res"):#x} 32 "{p("r.bin")}"'); q.stdin.write("quit\n"); q.wait()
    r = open(p("r.bin"), "rb").read()
    v = [int.from_bytes(r[8*i:8*i+8], "little") for i in range(4)]
    print(f"{os.path.basename(words_file)} n={n}: ours {v[0]} instr, C -O2 {v[1]} instr (C result {v[2]}, our output word {v[3]})")
W = os.path.join(D, "..", "frontx-words") + "/"
for n in [int(a) for a in sys.argv[1:2]] or [100]:
    run(W + "nontailsumrec.words", "sumrec", n, "li a2, 0")
for n in [int(a) for a in sys.argv[2:3]] or [10]:
    run(W + "fiblen.words", "fib", n, "mv a0, a1")
