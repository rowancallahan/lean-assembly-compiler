#!/usr/bin/env python3
"""Instruction-count benchmark: our compiled code vs hand-written vs gcc (RV64I -O0/-O2/-O3, AArch64 -O2) on QEMU.
Count = instructions retired between `jal/bl func` and return, measured with QEMU `-icount shift=0`:
RV64: csrr minstret before/after; AArch64: PMU INST_RETIRED (pmevcntr0) before/after. A call to an empty `ret` function is measured
and subtracted, so the number is "instructions executed inside the function" (including its final ret).
usage: bench.py [FUNC ...] [--sizes 100,1000,100000]   results appended to bench/results.json"""
import json, os, random, re, subprocess, sys, time
D = os.path.dirname(os.path.abspath(__file__)); R = os.path.dirname(D); W = os.path.join(D, "work"); os.makedirs(W, exist_ok=True)
p = lambda f: os.path.join(W, f)
sh = lambda c: subprocess.run(c, shell=True, check=True, capture_output=True, text=True)
M64 = 2**64 - 1
words = lambda path: [int(l, 16) for l in open(path) if l.strip()]
wfile = lambda sub, n: os.path.join(R, "Testing", "asm", sub, n + ".words")
le8 = lambda a: list((a & M64).to_bytes(8, "little"))
def fold(f, a, xs):
    for x in xs: a = f(a, x)
    return a
# ---- models: xs -> (expected output bytes or None, expected result or None)
MODEL = {
  "msort": lambda xs: (sorted(xs), None), "insertion": lambda xs: (sorted(xs), None),
  "sum": lambda xs: (None, sum(xs) & M64), "take": lambda xs: (xs, None), "inc": lambda xs: ([(x + 1) & 255 for x in xs], None),
  "revinc5": lambda xs: ([(x + 1) & 255 for x in xs[:5]][::-1], None),
  "mapsum": lambda xs: ([sum((x ^ 0x20) if x < 10 else (x - 1) & 255 for x in xs) & 255], None),
  "revtake5": lambda xs: (xs[::-1][:5], None), "mapsort": lambda xs: (sorted(x & 0x7f for x in xs), None),
  "sort": lambda xs: (sorted(xs), None), "sum64": lambda xs: (le8(sum(xs)), None),
  "hash64": lambda xs: (le8(fold(lambda a, x: ((a ^ x) + (a << 5)) & M64, 5381, xs)), None),
  "sortdesc": lambda xs: ([x if x != 3 else 0 for x in sorted(xs)[::-1][2:]], None), "mid": lambda xs: (sorted(xs)[1:4], None),
  "foldsorted": lambda xs: ([fold(lambda a, x: ((a - x) & 255) ^ 1, 7, sorted(xs)[::-1][:4])], None),
  "twosort": lambda xs: (sorted((x | 1) if x >= 0x80 else (0xff - x) for x in sorted(xs[3:])[:10][::-1]), None),
}
def sumdown(n, acc):
    return (acc + n * (n + 1) // 2) & M64
def gcd(a, b):
    while a and b:
        if a < b: b -= a
        else: a -= b
    return a or b
def demo(a, b, c, d): return (((a + b) ^ (c & 0xff)) - (d | 0x1234)) & M64
def s64(x): return x - 2**64 if x >> 63 else x
def demo2(a, b, c, d):
    if (int(a < b) ^ int(s64(a) < s64(c))) == 0: return ((a << (d & 63)) + (b >> (c & 63))) & M64
    return (int(c == d) - (s64(c) >> (a & 63))) & M64
NUM = {"gcd": (lambda a: gcd(a[0], a[1]), "gcd_sub"), "loopsum": (lambda a: sumdown(a[0], a[1]), "sumdown"),
       "demo": (lambda a: demo(*a), None), "demo2": (lambda a: demo2(*a), None)}
ARR = list(MODEL)
QUAD = {"insertion"}
# ---- what exists: ours words (RV), hand-written sources
OURS = {"msort": wfile("arr-words", "msort"), "insertion": wfile("arr-words", "sort"), "sum": wfile("arr-words", "sum"),
        "take": wfile("arr-words", "take"), "inc": wfile("arr-words", "inc"),
        "gcd": wfile("loop-words", "gcd"), "loopsum": wfile("loop-words", "sum")}
for n in ARR:
    if os.path.exists(wfile("pipe-words", n)) and n not in OURS: OURS[n] = wfile("pipe-words", n)
OURS["sort"] = wfile("pipe-words", "sort")
OURS_RES_A2 = {"sum"}            # our array sum returns in a2, everything else in a0
A2N = {"take", "inc"}            # a2 = count n for these (ours), scratch pointer for the rest
CNAME = {n: "c_" + n for n in ARR}; CNAME.update({"gcd": "c_gcd", "loopsum": "c_sumdown", "demo": "c_demo", "demo2": "c_demo2"})
HAND_RV = {"msort": os.path.join(R, "Testing", "asm", "sort.S")}; HAND_ARM = {"msort": os.path.join(R, "Testing", "asm-arm", "sort.S")}

TAIL = '.section .tohost,"aw"\n.globl tohost\n.globl fromhost\n.align 6\ntohost: .dword 0\nfromhost: .dword 0\n'
RVDRV = """.section .text.start
.globl _start
_start: lla s0, tab
  li s2, %d
1: ld a0, 0(s0)
  ld a1, 8(s0)
  ld a2, 16(s0)
  ld a3, 24(s0)
  ld sp, 32(s0)
  csrr s3, minstret
  jal ra, bench_fn
  csrr s4, minstret
  sub s4, s4, s3
  sd a0, 40(s0)
  sd a2, 48(s0)
  sd s4, 56(s0)
  addi s0, s0, 64
  addi s2, s2, -1
  bnez s2, 1b
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
""" + TAIL
ARMDRV = """.section .text.start
.globl _start
_start: ldr x19, =tab
  mov x21, #%d
  mov x2, #7
  msr pmcr_el0, x2
  mov x2, #1
  msr pmcntenset_el0, x2
  mov x2, #8
  msr pmevtyper0_el0, x2
  isb
1: ldp x0, x1, [x19]
  ldp x2, x3, [x19, #16]
  ldr x4, [x19, #32]
  mov sp, x4
  mrs x20, pmevcntr0_el0
  bl bench_fn
  mrs x22, pmevcntr0_el0
  sub x22, x22, x20
  stp x0, x2, [x19, #40]
  str x22, [x19, #56]
  add x19, x19, #64
  subs x21, x21, #1
  b.ne 1b
halt: b halt
.ltorg
"""
RVLD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n"
ARMLD = "ENTRY(_start)\nSECTIONS { . = 0x40200000; .text : { *(.text.start) *(.text) } . = 0x40400000; .data : { *(.data) } }\n"

def layout(func, cases):
    """cases: list of dicts {xs | args}. returns data blob, table lines, per-case info"""
    blob = bytearray(); lines = []; info = []
    def alloc(b, al=16):
        while len(blob) % al: blob.append(0)
        o = len(blob); blob.extend(b); return o
    for c in cases:
        if "xs" in c:
            n = len(c["xs"]); i0 = alloc(bytes(c["xs"]) + b"\xAA" * 64); s0 = alloc(b"\x33" * (3 * n + 256)); o0 = alloc(b"\x55" * (2 * n + 256)); k0 = alloc(b"\x77" * 8192)
            a2 = f"base+{i0 if False else (n if func in A2N else s0)}" if func not in A2N else str(n)
            a2 = str(n) if func in A2N else f"base+{s0}"
            lines.append(f"  .quad base+{i0}, {n}, {a2}, base+{o0}, base+{k0 + 8192 - 16}, 0, 0, 0")
            info.append((i0, o0, n))
        else:
            k0 = alloc(b"\x77" * 8192); a = c["args"]
            lines.append(f"  .quad {a[0]}, {a[1]}, {a[2]}, {a[3]}, base+{k0 + 8192 - 16}, 0, 0, 0"); info.append((0, 0, 0))
    return bytes(blob), lines, info

def build(isa, name, cases, variant, func):
    """variant: ('ours', wordsfile) | ('hand', src) | ('c', opt) | ('empty',). returns (elf, layout info)"""
    blob, lines, info = layout(func, cases)
    open(p(name + ".bin"), "wb").write(blob)
    rv = isa == "rv"
    drv = (RVDRV if rv else ARMDRV) % len(cases)
    drv += f'.data\n.align 4\n.globl base\nbase:\n.incbin "{p(name + ".bin")}"\n.align 4\n.globl tab\ntab:\n' + "\n".join(lines) + "\n"
    open(p(name + ".S"), "w").write(drv); open(p(isa + ".ld"), "w").write(RVLD if rv else ARMLD)
    cc = "riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -Wl,--no-relax" if rv else "aarch64-linux-gnu-gcc"
    extra, link = "", ""
    kind = variant[0]
    if kind == "empty":
        open(p(name + "_f.S"), "w").write(".text\n.globl bench_fn\nbench_fn: " + ("ret\n" if rv else "ret\n")); extra = p(name + "_f.S")
    elif kind == "ours":
        ws = "".join(f"  .word 0x{w:08x}\n" for w in words(variant[1]))
        open(p(name + "_f.S"), "w").write(".text\n.globl bench_fn\nbench_fn:\n" + ws); extra = p(name + "_f.S")
    elif kind == "hand":
        extra = variant[1]; link = "-Wl,--defsym=bench_fn=sort"
    else:
        opt = variant[1]
        flags = "-march=rv64i -mabi=lp64" if rv else ""
        o = p(name + "_c.o")
        sh(f"{'riscv64-linux-gnu-gcc' if rv else 'aarch64-linux-gnu-gcc'} {flags} -{opt} -ffreestanding -nostdlib -fno-tree-loop-distribute-patterns -c {D}/bench.c -o {o}")
        extra = o; link = f"-Wl,--defsym=bench_fn={CNAME[func]}"
    elf = p(name + ".elf")
    sh(f"{cc} -nostdlib -static -Wl,-T,{p(isa + '.ld')} -Wl,--build-id=none {link} {p(name + '.S')} {extra} -o {elf}")
    return elf, info

def run(isa, elf, n, tmo=3000):
    tool = "riscv64-linux-gnu-nm" if isa == "rv" else "aarch64-linux-gnu-nm"
    syms = sh(f"{tool} {elf}").stdout
    sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
    halt, base, tab = sym("halt"), sym("base"), sym("tab")
    cmd = (f"qemu-system-riscv64 -machine virt -m 1G -bios {elf}" if isa == "rv" else
           f"qemu-system-aarch64 -machine virt -cpu cortex-a72 -m 1G -device loader,file={elf},cpu-num=0") + " -display none -serial none -monitor stdio -icount shift=0"
    q = subprocess.Popen(cmd, shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version"); t0 = time.time()
    pat = ("pc       %016x" if isa == "rv" else "PC=%016x") % halt
    while pat not in hmp("info registers"):
        assert time.time() - t0 < tmo, "QEMU timeout"; time.sleep(0.05)
    size = tab + 64 * n - base
    hmp(f'pmemsave {base:#x} {size} "{p("dump.bin")}"'); q.stdin.write("quit\n"); q.wait()
    return open(p("dump.bin"), "rb").read(), tab - base

_over = {}
def overhead(isa):
    if isa not in _over:
        elf, _ = build(isa, f"empty_{isa}", [{"args": (0, 0, 0, 0)}], ("empty",), "demo")
        mem, to = run(isa, elf, 1); _over[isa] = int.from_bytes(mem[to + 56:to + 64], "little") - 1
    return _over[isa]

def measure(isa, func, variant, sizes, seed=1):
    """returns {n: (count, ok)} """
    rng = random.Random(seed); cases = []; exp = []
    if func in ARR:
        for n in sizes:
            xs = [rng.randrange(256) for _ in range(n)]; cases.append({"xs": xs}); exp.append(MODEL[func](xs))
    else:
        mdl = NUM[func][0]
        for a in sizes:
            cases.append({"args": a}); exp.append(mdl(a))
    tag = f"{func}_{isa}_{'_'.join(map(str, variant[1:2])) if variant[0]=='c' else variant[0]}".replace("/", "_")
    elf, info = build(isa, tag, cases, variant, func)
    mem, to = run(isa, elf, len(cases))
    res = {}; ov = overhead(isa)
    for i, c in enumerate(cases):
        e = to + 64 * i; a0, a2, cnt = (int.from_bytes(mem[e + o:e + o + 8], "little") for o in (40, 48, 56))
        ok = True
        if func in ARR:
            n = len(c["xs"]); outb, r = exp[i]; o0 = info[i][1]
            if outb is not None: ok &= list(mem[o0:o0 + len(outb)]) == outb
            if r is not None: ok &= ((a2 if (variant[0] == "ours" and func in OURS_RES_A2) else a0) == r)
            key = n
        else:
            ok = a0 == exp[i]; key = str(c["args"])
        res[key] = (cnt - ov, bool(ok))
    return res

def default_sizes(func):
    if func in ARR: return [100, 1000, 10000] if func in QUAD else [100, 1000, 100000]
    if func == "gcd": return [(832040, 514229, 0, 0), (100000, 3, 0, 0), (1000, 999, 0, 0)]
    if func == "loopsum": return [(100, 0, 0, 0), (1000, 0, 0, 0), (100000, 0, 0, 0)]
    rng = random.Random(9); return [tuple(rng.randrange(2**64) for _ in range(4)) for _ in range(4)]

if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]; funcs = args or (ARR + list(NUM))
    out = json.load(open(p("results.json"))) if os.path.exists(p("results.json")) else {}
    for f in funcs:
        sizes = default_sizes(f)
        variants = []
        if f in OURS: variants.append(("rv", "ours", ("ours", OURS[f])))
        if os.path.exists(wfile("opt-words", f)): variants.append(("rv", "ours-opt", ("ours", wfile("opt-words", f))))
        if "--opt-only" in sys.argv: variants = [v for v in variants if v[1] == "ours-opt"]
        if f in HAND_RV and "--opt-only" not in sys.argv: variants.append(("rv", "hand", ("hand", HAND_RV[f])))
        if f in ("demo", "demo2") and "--opt-only" not in sys.argv:
            for isa in ("rv", "arm"):
                for k in ("std", "fast"): variants.append((isa, "ours-" + k, ("ours", os.path.join(D, "exp-words", f"{f}-{isa}-{k}.words"))))
        if "--opt-only" not in sys.argv: variants += [("rv", f"c-{o}", ("c", o)) for o in ("O0", "O2", "O3")] + [("arm", "c-O2", ("c", "O2"))]
        if f in HAND_ARM and "--opt-only" not in sys.argv: variants.append(("arm", "hand", ("hand", HAND_ARM[f])))
        for isa, label, v in variants:
            t0 = time.time(); r = measure(isa, f, v, sizes)
            out.setdefault(f, {})[f"{isa}/{label}"] = {str(k): list(x) for k, x in r.items()}
            print(f"{f:10s} {isa}/{label:10s} " + "  ".join(f"{k}:{x[0]}{'' if x[1] else ' WRONG'}" for k, x in r.items()) + f"   ({time.time()-t0:.0f}s)", flush=True)
            json.dump(out, open(p("results.json"), "w"), indent=1)
