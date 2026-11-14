#!/usr/bin/env python3
"""Tests of the call compiler's clients (`Riscv/Examples/CallExamples.lean`; words from `Testing/asm/emit_calls.lean`
in `Testing/asm/calls-words/`) on QEMU and on the Sail C emulator.

Each case: its own input bytes, 8-aligned 8-byte output, and a stack of exactly `space` bytes (the bound of the
theorem) with `sp` at a random misalignment, all separated by guard bytes; `gp` is set to a magic value.  Checked on
both: output = reference (8 bytes LE), input and guards unchanged, gp and sp restored, and (Sail trace) every data
write lands in the output word or in the case's stack block.
usage: calls_test.py [sumto|fib|even|tree ...]"""
import os, random, re, subprocess, sys
import types
D = os.path.dirname(os.path.abspath(__file__))
M = types.ModuleType("msort_test"); M.__file__ = os.path.join(D, "msort_test.py")   # its helpers, without its main
exec(open(M.__file__).read().split("\nif sys.argv[1]")[0], M.__dict__)
p, sh, G, E, MAGIC = M.p, M.sh, M.G, M.E, M.MAGIC
words = lambda n: [int(l, 16) for l in open(os.path.join(D, "calls-words", n + ".words")) if l.strip()]
MASK = 2 ** 64 - 1

def build(name, cases, func, ST):
    data, tab, lay, off = bytearray(), [], [], 0
    rng = random.Random(len(cases))
    for xs in cases:
        i0 = off; o0 = (i0 + len(xs) + G + 7) // 8 * 8; k0 = o0 + 8 + G + rng.randrange(8); top = k0 + ST
        off = (top + G + 7) // 8 * 8
        lay.append((i0, o0, k0, top))
        tab.append(f"  .quad base+{i0}, {len(xs)}, 0, base+{o0}, base+{top}, {MAGIC}, 0, 0, 0")
        blk = bytearray(b"\xAA" * (off - i0)); blk[0:len(xs)] = bytes(xs); blk[o0 - i0:o0 - i0 + 8] = b"\x55" * 8
        blk[k0 - i0:top - i0] = b"\x77" * ST; data += blk
    open(p(name + ".bin"), "wb").write(data)
    src = M.DRIVER % (len(cases), E, func) + f'.data\n.align 4\nbase:\n.incbin "{p(name + ".bin")}"\n.align 3\ntab:\n' + "\n".join(tab) + "\n"
    open(p(name + ".S"), "w").write(src); open(p("m.ld"), "w").write(M.LD)
    sh(f"riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -nostdlib -static -Wl,-T,{p('m.ld')} -Wl,--no-relax "
       f"-Wl,--build-id=none {p(name + '.S')} -o {p(name + '.elf')}")
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {p(name + '.elf')}", shell=True, text=True)
    sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
    return lay, sym("halt"), sym("base"), sym("tab"), off

def run(name, allc, ref, ST, B=64):
    func = "".join(f"  .word 0x{w:08x}\n" for w in words(name)); done = 0; deepest = 0
    while done < len(allc):
        cases = allc[done:done + B]
        lay, halt, base, tab, size = build("cl", cases, func, ST)
        qmem, _ = M.qemu("cl", halt, base, tab + E * len(cases) - base)
        r = subprocess.run(f"{M.SAIL} --inst-limit 2000000000 --trace-mem --trace-output {p('sail.log')} {p('cl.elf')}",
                           shell=True, capture_output=True, text=True)
        assert "SUCCESS" in r.stdout + r.stderr, (r.stdout + r.stderr)[-500:]
        init = bytearray(open(p("cl.bin"), "rb").read()) + bytearray(qmem[size:])
        allowed = set(range(tab, tab + E * len(cases)))
        for (i0, o0, k0, top) in lay:
            allowed |= set(range(base + o0, base + o0 + 8)) | set(range(base + k0, base + top))
        smem = bytearray(init)
        for l in open(p("sail.log")):
            m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", l)
            if not m: continue
            a, v = int(m.group(1), 16), m.group(2)
            if a < base: continue
            nb = len(v) // 2
            for j in range(nb):
                assert a + j in allowed, f"unexpected Sail write {l.strip()}"
                smem[a + j - base] = int(v[2 * (nb - 1 - j):2 * (nb - j)], 16)
        for nm, mem in (("qemu", qmem), ("sail", smem)):
            for c, ((i0, o0, k0, top), xs) in enumerate(zip(lay, cases)):
                assert list(mem[i0:i0 + len(xs)]) == list(xs), (nm, "input", xs)
                got = int.from_bytes(mem[o0:o0 + 8], "little")
                assert got == ref(xs) & MASK, (nm, "output", xs[:20], hex(got), hex(ref(xs) & MASK))
                assert all(b == 0xAA for b in mem[i0 + len(xs):o0] + mem[o0 + 8:k0] + mem[top:top + G]), (nm, "guard", xs[:20])
                e = tab - base + E * c
                gp, spo = (int.from_bytes(mem[e + o:e + o + 8], "little") for o in (48, 56))
                assert gp == MAGIC and spo == base + top, (nm, "gp/sp", hex(gp), spo)
                used = next((j for j, b in enumerate(mem[k0:top]) if b != 0x77), ST)
                deepest = max(deepest, ST - used)
        done += len(cases)
    print(f"{name}: {len(allc)} cases OK on QEMU and Sail (stack block {ST} bytes, deepest use {deepest})")

def fib(n):
    a, b = 0, 1
    for _ in range(n): a, b = b, a + b
    return a

if __name__ == "__main__":
    which = sys.argv[1:] or ["sumto", "fib", "even"]
    if "sumto" in which: run("sumto", [[n] for n in range(256)], lambda x: x[0] * (x[0] + 1) // 2, 16 + 24 + 24 * 255 + 24)
    if "fib" in which: run("fib", [[n] for n in range(25)], lambda x: fib(x[0]), 16 + 32 + 32 * 255 + 24)
    if "even" in which: run("even", [[n] for n in range(256)], lambda x: 1 - x[0] % 2, 16 + 24 + 24 * 255 + 24)
