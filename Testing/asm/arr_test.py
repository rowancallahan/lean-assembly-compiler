#!/usr/bin/env python3
"""Test of the byte-array compiler output (`Riscv/Examples/ArrExamples.lean`, `Riscv/Direct/SortIns.lean`; words printed by
`Testing/asm/emit_arr.lean` into `Testing/asm/arr-words/`) on QEMU and on the Sail C emulator.
For each input: a0 = &in (bytes xs), a1 = len xs, a2 = n, a3 = &out (128-byte slot pre-filled with 0x55);
after the call the driver stores a2.  Checked against a Python model: the whole output slot (result bytes,
then untouched 0x55 guard bytes), the input slot unchanged, a2 for `sum`; on Sail, every data write lands in
the expected output bytes (or the a2 result word).
usage: arr_test.py {sum,take,inc,sort} NTESTS"""
import os, random, re, subprocess, sys, time
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "ctest"); os.makedirs(W, exist_ok=True)
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
p = lambda f: os.path.join(W, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
which, N = sys.argv[1], int(sys.argv[2])
words = [int(l, 16) for l in open(os.path.join(D, "arr-words", which + ".words")) if l.strip()]
S = 128  # slot size
def model(xs, n):
    """(output bytes, a2 or None)"""
    if which == "sum": return [], sum(xs) % 2**64
    if which == "take": return xs[:n], None
    if which == "inc": return [(x + 1) & 255 for x in xs[:n]], None
    if which == "sort": return sorted(xs), None
rng = random.Random(3)
def rand_case():
    L = rng.choice([0, 1, 2, 3, 5, rng.randrange(64), rng.randrange(64), 64])
    k = rng.randrange(4)
    xs = [rng.choice([0, 255, rng.randrange(256)]) if k == 0 else rng.randrange(256) if k == 1
          else rng.randrange(3) if k == 2 else (i * 37) % 256 for i in range(L)]
    if rng.random() < 0.2: xs.sort(reverse=rng.random() < 0.5)
    n = rng.choice([0, 1, 5, L, L + 1, rng.randrange(80), 2**64 - 1, 2**63])
    return xs, n
DRIVER = """.section .text.start
.globl _start
_start: lla s0, tab
  li s2, %d
1: ld a0, 0(s0)
  ld a1, 8(s0)
  ld a2, 16(s0)
  ld a3, 24(s0)
  jal ra, func
  sd a2, 32(s0)
  addi s0, s0, 40
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
open(p("arr.ld"), "w").write("ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n")
B, done = 40, 0
while done < N:
    k = min(B, N - done)
    cases = [rand_case() for _ in range(k)]
    ins = "\n".join(f"  .byte {', '.join(str(x) for x in xs + [0xAA] * (S - len(xs)))}" for xs, _ in cases)
    syms0 = None
    # first link to learn addresses of ins/outs (the table holds absolute addresses: use symbol arithmetic)
    tab = "\n".join(f"  .quad ins+{S*i}, {len(xs)}, {n}, outs+{S*i}, 0" for i, (xs, n) in enumerate(cases))
    open(p("arr.S"), "w").write(DRIVER % (k, "".join(f"  .word 0x{w:08x}\n" for w in words), ins, S * k, tab))
    sh(f"riscv64-linux-gnu-gcc -march=rv64i -mabi=lp64 -nostdlib -static -Wl,-T,{p('arr.ld')} -Wl,--no-relax -Wl,--build-id=none {p('arr.S')} -o {p('arr.elf')}")
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {p('arr.elf')}", shell=True, text=True)
    sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
    halt, ins_a, outs_a, tab_a = sym("halt"), sym("ins"), sym("outs"), sym("tab")
    size = tab_a + 40 * k - ins_a
    # QEMU
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {p('arr.elf')} -display none -serial none -monitor stdio",
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
    r = subprocess.run(f"{SAIL} --inst-limit 200000000 --trace-mem --trace-output {p('sail.log')} {p('arr.elf')}",
                       shell=True, capture_output=True, text=True)
    assert "SUCCESS" in r.stdout + r.stderr, (r.stdout + r.stderr)[-500:]
    img = bytearray(qmem)  # overwritten below from the initial image
    init = bytearray()
    for xs, _ in cases: init += bytes(xs + [0xAA] * (S - len(xs)))
    init += bytes([0x55] * (S * k))
    allowed = set()
    for i, (xs, n) in enumerate(cases):
        out, _ = model(xs, n)
        allowed |= set(range(outs_a + S * i, outs_a + S * i + len(out)))
        allowed |= set(range(tab_a + 40 * i + 32, tab_a + 40 * i + 40))
    smem = bytearray(init + bytes(qmem[len(init):]))
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
        for i, (xs, n) in enumerate(cases):
            out, a2 = model(xs, n)
            got_in = list(mem[S * i:S * i + S]); got_out = list(mem[len(init) - S * k + S * i:][:S])
            assert got_in == xs + [0xAA] * (S - len(xs)), (name, "input changed", xs, n)
            assert got_out == out + [0x55] * (S - len(out)), (name, xs, n, got_out[:len(out) + 2], out)
            if a2 is not None:
                o = tab_a - ins_a + 40 * i + 32
                assert int.from_bytes(mem[o:o + 8], "little") == a2, (name, xs, a2)
    done += k
    print(f"{which}: {done}/{N} ok (QEMU == Sail == model, {len(words)} words)", flush=True)
