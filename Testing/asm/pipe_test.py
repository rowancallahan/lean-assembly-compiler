#!/usr/bin/env python3
"""Test of the `compile%` examples (`Riscv/Examples/PipeExamples.lean`; words and space tables printed by
`Testing/asm/emit_pipe.lean` into `Testing/asm/pipe-words/`) on QEMU and on the Sail C emulator.
For each input: a0 = &in (bytes xs), a1 = len xs, a2 = junk (scratch is unused), a3 = &out (128-byte slot
pre-filled with 0x55).  Checked against a Python model of the Lean function: the first |result| output bytes
are the result, the output bytes from `Pipe.space |xs|` on are untouched, the input slot is unchanged; on
Sail, every data write lands in out[0, space).
usage: pipe_test.py NAME NTESTS"""
import os, random, re, subprocess, sys, time
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "ctest"); os.makedirs(W, exist_ok=True)
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
p = lambda f: os.path.join(W, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
which, N = sys.argv[1], int(sys.argv[2])
words = [int(l, 16) for l in open(os.path.join(D, "pipe-words", which + ".words")) if l.strip()]
space = [int(x) for x in open(os.path.join(D, "pipe-words", which + ".space")).read().split()]
S = 128  # slot size
M64 = 2**64 - 1
def fold(f, a, xs):
    for x in xs: a = f(a, x)
    return a
le8 = lambda a: list(a.to_bytes(8, "little"))
MODEL = {
    "revinc5": lambda xs: [(x + 1) & 255 for x in xs[:5]][::-1],
    "mapsum": lambda xs: [sum((x ^ 0x20) if x < 10 else (x - 1) & 255 for x in xs) & 255],
    "revtake5": lambda xs: xs[::-1][:5],
    "mapsort": lambda xs: sorted(x & 0x7f for x in xs),
    "sort": lambda xs: sorted(xs),
    "sum64": lambda xs: le8(sum(xs)),
    "hash64": lambda xs: le8(fold(lambda a, x: ((a ^ x) + (a << 5)) & M64, 5381, xs)),
    "sortdesc": lambda xs: [x if x != 3 else 0 for x in sorted(xs)[::-1][2:]],
    "mid": lambda xs: sorted(xs)[1:4],
    "foldsorted": lambda xs: [fold(lambda a, x: ((a - x) & 255) ^ 1, 7, sorted(xs)[::-1][:4])],
    "twosort": lambda xs: sorted((x | 1) if x >= 0x80 else (0xff - x) for x in sorted(xs[3:])[:10][::-1]),
}
model = MODEL[which]
rng = random.Random(5)
def rand_case():
    L = rng.choice([0, 1, 2, 3, 4, 5, 6, rng.randrange(64), rng.randrange(64), 64])
    k = rng.randrange(4)
    xs = [rng.choice([0, 255, rng.randrange(256)]) if k == 0 else rng.randrange(256) if k == 1
          else rng.randrange(12) if k == 2 else (i * 37) % 256 for i in range(L)]
    if rng.random() < 0.2: xs.sort(reverse=rng.random() < 0.5)
    return xs
DRIVER = """.section .text.start
.globl _start
_start: lla s0, tab
  li s2, %d
1: ld a0, 0(s0)
  ld a1, 8(s0)
  ld a2, 16(s0)
  ld a3, 24(s0)
  jal ra, func
  addi s0, s0, 32
  addi s2, s2, -1
  bnez s2, 1b
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
.align 7
ins:
%s
outs: .fill %d, 1, 0x55
tab:
%s"""
open(p("pipe.ld"), "w").write("ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n")
cases0 = [[], [7], [0], [255], [3, 3], [9, 200]]  # always: empty and length-1 lists
B, done = 40, 0
while done < N:
    k = min(B, N - done)
    cases = [cases0.pop() if cases0 else rand_case() for _ in range(k)]
    ins = "\n".join(f"  .byte {', '.join(str(x) for x in xs + [0xAA] * (S - len(xs)))}" for xs in cases)
    tab = "\n".join(f"  .quad ins+{S*i}, {len(xs)}, {rng.getrandbits(64)}, outs+{S*i}" for i, xs in enumerate(cases))
    open(p("pipe.S"), "w").write(DRIVER % (k, "".join(f"  .word 0x{w:08x}\n" for w in words), ins, S * k, tab))
    sh(f"riscv64-linux-gnu-gcc -march=rv64i -mabi=lp64 -nostdlib -static -Wl,-T,{p('pipe.ld')} -Wl,--no-relax -Wl,--build-id=none {p('pipe.S')} -o {p('pipe.elf')}")
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {p('pipe.elf')}", shell=True, text=True)
    sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
    halt, ins_a, outs_a, tab_a = sym("halt"), sym("ins"), sym("outs"), sym("tab")
    size = tab_a - ins_a
    # QEMU
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {p('pipe.elf')} -display none -serial none -monitor stdio",
                         shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version"); t0 = time.time()
    while "pc       %016x" % halt not in hmp("info registers"):
        assert time.time() - t0 < 120, "QEMU did not reach halt"; time.sleep(0.01)
    hmp(f'pmemsave {ins_a:#x} {size} "{p("q.bin")}"'); q.stdin.write("quit\n"); q.wait()
    qmem = open(p("q.bin"), "rb").read()
    # Sail: replay the data writes on the initial image
    r = subprocess.run(f"{SAIL} --inst-limit 200000000 --trace-mem --trace-output {p('sail.log')} {p('pipe.elf')}",
                       shell=True, capture_output=True, text=True)
    assert "SUCCESS" in r.stdout + r.stderr, (r.stdout + r.stderr)[-500:]
    init = bytearray()
    for xs in cases: init += bytes(xs + [0xAA] * (S - len(xs)))
    init += bytes([0x55] * (S * k))
    allowed = set()
    for i, xs in enumerate(cases):
        assert len(model(xs)) <= space[len(xs)] <= S
        allowed |= set(range(outs_a + S * i, outs_a + S * i + space[len(xs)]))
    smem = bytearray(init)
    for l in open(p("sail.log")):
        m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", l)
        if not m: continue
        a, v = int(m.group(1), 16), m.group(2)
        if a < ins_a: continue
        nb = len(v) // 2
        for j in range(nb):
            assert a + j in allowed, f"unexpected Sail write {l.strip()}"
            smem[a + j - ins_a] = int(v[2 * (nb - 1 - j):2 * (nb - j)], 16)
    for name, mem in (("qemu", qmem), ("sail", smem)):
        for i, xs in enumerate(cases):
            out = model(xs); sp = space[len(xs)]
            got_in = list(mem[S * i:S * i + S]); got_out = list(mem[S * k + S * i:][:S])
            assert got_in == xs + [0xAA] * (S - len(xs)), (name, "input changed", xs)
            assert got_out[:len(out)] == out, (name, xs, got_out[:len(out) + 2], out)
            assert got_out[sp:] == [0x55] * (S - sp), (name, "write beyond space", xs, sp)
    done += k
    print(f"{which}: {done}/{N} ok (QEMU == Sail == model, {len(words)} words)", flush=True)
