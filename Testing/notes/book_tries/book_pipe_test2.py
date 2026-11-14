#!/usr/bin/env python3
"""Test of the `compile%` examples (`Riscv/Examples/PipeExamples.lean`; words and space tables printed by
`Testing/asm/emit_pipe.lean` into `Testing/asm/pipe-words/`) on QEMU and on the Sail C emulator.
For each input: a0 = &in (bytes xs), a1 = len xs, a2 = junk (scratch is unused), a3 = &out (128-byte slot
pre-filled with 0x55).  Checked against a Python model of the Lean function: the first |result| output bytes
are the result, the output bytes from `Pipe.space |xs|` on are untouched, the input slot is unchanged; on
Sail, every data write lands in out[0, space).
usage: pipe_test.py NAME NTESTS"""
import itertools, os, random, re, subprocess, sys, time
D = os.environ.get("PIPEDIR") or os.path.dirname(os.path.abspath(__file__)); W = os.environ.get("WORK") or os.path.join(D, "ctest"); os.makedirs(W, exist_ok=True)
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
p = lambda f: os.path.join(W, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
which = sys.argv[1]
TAB = {}
ALL = []
for l in open(os.path.join(os.environ["PIPEDIR"], which + ".exp")):
    a, b = l.split(); f = lambda h: [] if h == "-" else list(bytes.fromhex(h)); ALL.append(f(a)); TAB[tuple(f(a))] = f(b)
N = len(ALL)
words = [int(l, 16) for l in open(os.path.join(D, which + ".words")) if l.strip()]
space = [int(x) for x in open(os.path.join(D, which + ".space")).read().split()]
sspace = [int(x) for x in open(os.path.join(D, which + ".sspace")).read().split()]
ST, MAGIC, E = 256, 0x1234567890ABCDEF, 56  # stack bytes per case, gp value, table entry size
S = 128  # slot size
M64 = 2**64 - 1
def fold(f, a, xs):
    for x in xs: a = f(a, x)
    return a
le8 = lambda a: list(a.to_bytes(8, "little"))
opt = lambda v: [0] if v is None else [1, v]
model = lambda xs: TAB[tuple(xs)]

rng = random.Random(5)
def rand_case():
    L = rng.choice([0, 1, 2, 3, 4, 5, 6, rng.randrange(64), rng.randrange(64), 64])
    k = rng.randrange(6)
    c = rng.choice([0, 3, 7, 200, rng.randrange(256)])
    xs = [rng.choice([0, 255, rng.randrange(256)]) if k == 0 else rng.randrange(256) if k == 1
          else rng.randrange(12) if k == 2 else (i * 37) % 256 if k == 3 else c if k == 4
          else rng.choice([0, 0, 0, 42, 3, 5, 7, 128, 201, rng.randrange(256)]) for i in range(L)]
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
  ld sp, 40(s0)
  li gp, %d
  jal ra, func
  sd a1, 32(s0)
  sd gp, 48(s0)
  addi s0, s0, 56
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
scrs: .fill %d, 1, 0x66
stks: .fill %d, 1, 0x77
tab:
%s
tabend:
"""
open(p("pipe.ld"), "w").write("ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n")
B, done = 40, 0
while done < N:
    k = min(B, N - done)
    cases = ALL[done:done + k]
    ins = "\n".join(f"  .byte {', '.join(str(x) for x in xs + [0xAA] * (S - len(xs)))}" for xs in cases)
    sps = [ST * i + ST - 8 - rng.randrange(8) for i in range(k)]
    tab = "\n".join(f"  .quad ins+{S*i}, {len(xs)}, scrs+{S*i}, outs+{S*i}, 0, stks+{sps[i]}, 0" for i, xs in enumerate(cases))
    open(p("pipe.S"), "w").write(DRIVER % (k, MAGIC, "".join(f"  .word 0x{w:08x}\n" for w in words), ins, S * k, S * k, ST * k, tab))
    sh(f"riscv64-linux-gnu-gcc -march=rv64i -mabi=lp64 -nostdlib -static -Wl,-T,{p('pipe.ld')} -Wl,--no-relax -Wl,--build-id=none {p('pipe.S')} -o {p('pipe.elf')}")
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {p('pipe.elf')}", shell=True, text=True)
    sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
    halt, ins_a, outs_a, tab_a, tabend = sym("halt"), sym("ins"), sym("outs"), sym("tab"), sym("tabend")
    scrs_a, stks_a = sym("scrs"), sym("stks")
    size = tabend - ins_a
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
    init += bytes([0x55] * (S * k)) + bytes([0x66] * (S * k)) + bytes([0x77] * (ST * k))
    tab0 = bytearray(qmem[tab_a - ins_a:])  # the table; the driver writes a1 and gp into words 4 and 6
    for i in range(k): tab0[E * i + 32:E * i + 40] = bytes(8); tab0[E * i + 48:E * i + 56] = bytes(8)
    init += tab0
    allowed = set(range(tab_a, tabend))
    for i, xs in enumerate(cases):
        assert len(model(xs)) <= space[len(xs)] <= S and sspace[len(xs)] <= S
        allowed |= set(range(outs_a + S * i, outs_a + S * i + space[len(xs)]))
        allowed |= set(range(scrs_a + S * i, scrs_a + S * i + sspace[len(xs)]))
        fp = (stks_a + sps[i]) // 8 * 8 - 64
        allowed |= set(range(fp, fp + 64))
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
            a1 = int.from_bytes(mem[tab_a - ins_a + E * i + 32:][:8], "little")
            assert a1 == len(out), (name, "a1 is not the result length", xs, a1, len(out))
            gp = int.from_bytes(mem[tab_a - ins_a + E * i + 48:][:8], "little")
            assert gp == MAGIC, (name, "gp not restored", hex(gp))
            ss = sspace[len(xs)]; got_scr = list(mem[2 * S * k + S * i:][:S])
            assert got_scr[ss:] == [0x66] * (S - ss), (name, "scratch write beyond sspace", xs, ss)
            stk = list(mem[3 * S * k + ST * i:][:ST]); fp = (stks_a + sps[i]) // 8 * 8 - 64 - stks_a - ST * i
            assert all(b == 0x77 for j, b in enumerate(stk) if not (fp <= j < fp + 64)), (name, "stack outside frame")
    done += k
    print(f"{which}: {done}/{N} ok (QEMU == Sail == model, {len(words)} words)", flush=True)
