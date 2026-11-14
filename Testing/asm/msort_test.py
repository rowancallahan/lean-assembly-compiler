#!/usr/bin/env python3
"""Tests of the compiled merge sort (`Riscv/Direct/SortMergeMachine.lean`, words from `Testing/asm/emit_arr2.lean` in
`Testing/asm/arr-words/msort.words`) on QEMU and on the Sail C emulator, and instruction counts.

check N: N random inputs (lengths 0..3, 2^k +- 1 up to 2^11 + 1, random up to 3000).  Each case gets its own
input / scratch / output slot (each followed by 16 guard bytes) and its own 256-byte stack with `sp` at a random
misalignment; the driver sets `gp` to a magic value before the call and stores `gp`, `sp` after it.  Checked on
QEMU and Sail: output = sorted(input), input and all guard bytes unchanged, gp and sp restored, and (Sail) every
data write lands in the case's scratch or output bytes or in its 64-byte frame below sp.
bench: instructions retired (QEMU -icount, minstret) for msort, the insertion sort and Testing/asm/sort.S at n = 1000
and n = 100000 (insertion sort at 100000 only if --ins100k).
usage: msort_test.py check N | msort_test.py bench [--ins100k]"""
import os, random, re, subprocess, sys, time
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "ctest"); os.makedirs(W, exist_ok=True)
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
p = lambda f: os.path.join(W, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
words = lambda n: [int(l, 16) for l in open(os.path.join(D, os.environ.get("WDIR", "arr-words"), n + ".words")) if l.strip()]
G, ST, E = 16, 256, 72        # guard bytes, stack per case, table entry size
MAGIC = 0x0123456789ABCDEF
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n"
TAIL = """.section .tohost,"aw"
.globl tohost
.globl fromhost
.align 6
tohost: .dword 0
fromhost: .dword 0
"""
# table entry: in, len, scr, out, sp, gp-in | gp-out, sp-out, instret
DRIVER = """.section .text.start
.globl _start
_start: lla s0, tab
  li s2, %d
1: ld a0, 0(s0)
  ld a1, 8(s0)
  ld a2, 16(s0)
  ld a3, 24(s0)
  ld sp, 32(s0)
  ld gp, 40(s0)
  csrr s3, minstret
  jal ra, func
  csrr s4, minstret
  sub s4, s4, s3
  sd gp, 48(s0)
  sd sp, 56(s0)
  sd s4, 64(s0)
  addi s0, s0, %d
  addi s2, s2, -1
  bnez s2, 1b
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
func:
%s""" + TAIL

def build(name, cases, func):
    """cases: list of xs; lay out [in | G][scr | G][out | G][stack ST] per case"""
    data, tab, off, lay = [], [], 0, []
    rng = random.Random(len(cases))
    for xs in cases:
        L = len(xs); i0 = off; s0 = i0 + L + G; o0 = s0 + L + G; k0 = o0 + L + G; off = k0 + ST
        mis = rng.randrange(8); sp = k0 + ST - 8 - mis
        lay.append((i0, s0, o0, k0, sp))
        tab.append(f"  .quad base+{i0}, {L}, base+{s0}, base+{o0}, base+{sp}, {MAGIC}, 0, 0, 0")
        data.append(bytes(xs) + b"\xAA" * G + b"\x33" * L + b"\xAA" * G + b"\x55" * L + b"\xAA" * G + b"\x77" * ST)
    open(p(name + ".bin"), "wb").write(b"".join(data))
    src = DRIVER % (len(cases), E, func) + f'.data\n.align 4\nbase:\n.incbin "{p(name + ".bin")}"\n.align 3\ntab:\n' + "\n".join(tab) + "\n"
    open(p(name + ".S"), "w").write(src); open(p("m.ld"), "w").write(LD)
    sh(f"riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -nostdlib -static -Wl,-T,{p('m.ld')} -Wl,--no-relax "
       f"-Wl,--build-id=none {p(name + '.S')} -o {p(name + '.elf')}")
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {p(name + '.elf')}", shell=True, text=True)
    sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
    return lay, sym("halt"), sym("base"), sym("tab"), off

def qemu(name, halt, a, n, icount=False, tmo=3600):
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {p(name + '.elf')} -display none -serial none "
                         f"-monitor stdio {'-icount shift=0' if icount else ''}",
                         shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version"); t0 = time.time()
    while "pc       %016x" % halt not in hmp("info registers"):
        assert time.time() - t0 < tmo, "QEMU did not reach halt"; time.sleep(0.01)
    dt = time.time() - t0
    hmp(f'pmemsave {a:#x} {n} "{p(name + ".q.bin")}"'); q.stdin.write("quit\n"); q.wait()
    return open(p(name + ".q.bin"), "rb").read(), dt

def check(N):
    rng = random.Random(7)
    fixed = [0, 1, 2, 3] + [2 ** k + d for k in range(1, 12) for d in (-1, 0, 1)]
    lens = (fixed + [rng.choice([rng.randrange(40), rng.randrange(300), rng.randrange(3000)]) for _ in range(N)])[:N]
    def gen(L):
        k = rng.randrange(5)
        xs = [rng.randrange(256) if k < 2 else rng.randrange(3) if k == 2 else rng.choice([0, 255]) if k == 3
              else (i * 37) % 256 for i in range(L)]
        if rng.random() < 0.2: xs.sort(reverse=rng.random() < 0.5)
        return xs
    allc = [gen(L) for L in lens]
    func = "".join(f"  .word 0x{w:08x}\n" for w in words("msort"))
    done, B = 0, 40
    while done < N:
        cases = allc[done:done + B]
        lay, halt, base, tab, size = build("ms", cases, func)
        qmem, _ = qemu("ms", halt, base, tab + E * len(cases) - base)
        r = subprocess.run(f"{SAIL} --inst-limit 2000000000 --trace-mem --trace-output {p('sail.log')} {p('ms.elf')}",
                           shell=True, capture_output=True, text=True)
        assert "SUCCESS" in r.stdout + r.stderr, (r.stdout + r.stderr)[-500:]
        init = bytearray(open(p("ms.bin"), "rb").read()) + bytearray(qmem[size:])  # table: as QEMU left it
        allowed = set()
        for (i0, s0, o0, k0, sp), xs in zip(lay, cases):
            L = len(xs); fp = sp // 8 * 8 - 64
            allowed |= set(range(base + s0, base + s0 + L)) | set(range(base + o0, base + o0 + L))
            allowed |= set(range(base + fp, base + fp + 64))
        allowed |= set(range(tab, tab + E * len(cases)))
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
            for c, ((i0, s0, o0, k0, sp), xs) in enumerate(zip(lay, cases)):
                L = len(xs); fp = sp // 8 * 8 - 64
                assert list(mem[i0:i0 + L + G]) == xs + [0xAA] * G, (nm, "input", L)
                assert list(mem[s0 + L:s0 + L + G]) == [0xAA] * G, (nm, "scratch guard", L)
                assert list(mem[o0:o0 + L]) == sorted(xs), (nm, "output", L)
                assert list(mem[o0 + L:o0 + L + G]) == [0xAA] * G, (nm, "output guard", L)
                st = mem[k0:k0 + ST]
                assert all(b == 0x77 for j, b in enumerate(st) if not (fp - k0 <= j < fp - k0 + 64)), (nm, "stack")
                e = tab - base + E * c
                gp, spo = (int.from_bytes(mem[e + o:e + o + 8], "little") for o in (48, 56))
                assert gp == MAGIC and spo == base + sp, (nm, "gp/sp", hex(gp), spo)
        done += len(cases)
        print(f"msort: {done}/{N} ok (QEMU == Sail == sorted; lengths up to {max(map(len, cases))})", flush=True)

def bench(ins100k):
    rng = random.Random(11)
    with open(os.path.join(D, "sort.S")) as f: hand = f.read().replace(".globl sort\nsort:", ".globl sort\nsort:", 1)
    progs = {"msort (proved)": "".join(f"  .word 0x{w:08x}\n" for w in words("msort")),
             "insertion (proved)": "".join(f"  .word 0x{w:08x}\n" for w in words("sort")),
             "sort.S (hand)": "  j sort\n" + hand + "\n.text\n"}
    for n in (1000, 100000):
        xs = [rng.randrange(256) for _ in range(n)]
        for nm, func in progs.items():
            if nm.startswith("insertion") and n == 100000 and not ins100k:
                print(f"n={n:6d} {nm:20s} skipped (O(n^2); run with --ins100k)"); continue
            lay, halt, base, tab, size = build("bench", [xs], func)
            mem, _ = qemu("bench", halt, base, tab + E - base, icount=True)
            _, dt = qemu("bench", halt, base, tab + E - base)
            (i0, s0, o0, k0, sp), L = lay[0], n
            assert list(mem[o0:o0 + L]) == sorted(xs), nm
            cnt = int.from_bytes(mem[tab - base + 64:tab - base + 72], "little")
            print(f"n={n:6d} {nm:20s} {cnt:12d} instructions  ({cnt / n:9.1f} per byte; QEMU wall {dt:6.2f} s)",
                  flush=True)

if sys.argv[1] == "check": check(int(sys.argv[2]))
else: bench("--ins100k" in sys.argv)
