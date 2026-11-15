#!/usr/bin/env python3
"""Instruction counts of Frontx entry points: ours (frontx-words), ours-opt (opt-words, where the function exists),
gcc -O2 RV64 (bench.c) on QEMU (-icount shift=0, minstret around the call, empty-call overhead subtracted);
Lean's own compiled code (Bench.lean) and gcc -O2 on x86-64 under valgrind (callgrind Ir, per-call slope over reps).
usage: bench_frontx.py rv [FN...] | x86 [FN...]    -> results/<mode>.json"""
import json, os, re, subprocess, sys, time, zlib
D = os.path.dirname(os.path.abspath(__file__)); A = os.path.dirname(D); W = os.path.join(D, "work"); os.makedirs(W, exist_ok=True)
os.makedirs(os.path.join(D, "results"), exist_ok=True)
p = lambda f: os.path.join(W, f)
def sh(c): return subprocess.run(c, shell=True, check=True, capture_output=True, text=True).stdout
SIZES = [1024, 65536, 1048576]
M = 2**64 - 1
def gen(n, kind):
    s, xs = 88172645463325252, bytearray()
    for _ in range(n):
        s ^= (s << 13) & M; s ^= s >> 7; s ^= (s << 17) & M
        xs.append(((s >> 33) & 255) & (3 if kind == "scan" else 255))
    return bytes(xs)
def d64(c): return c-65 if 65<=c<=90 else c-71 if 97<=c<=122 else c+4 if 48<=c<=57 else 62 if c==43 else 63 if c==47 else 64
opt = lambda v: bytes([0, 0]) if v is None else bytes([1, v])
# name -> (kind, model: xs -> (bytes, is_list))
FN = {
 "crcraw": ("rand", lambda x: (zlib.crc32(x).__xor__(0xFFFFFFFF).to_bytes(4, "little"), 0)),
 "b64all": ("rand", lambda x: ((sum(map(d64, x)) % 2**32).to_bytes(4, "little"), 0)),
 "findnl": ("scan", lambda x: ((x.find(10) if 10 in x else len(x)).to_bytes(8, "little"), 0)),
 "be32at0": ("rand", lambda x: (int.from_bytes(x[:4].ljust(4, b"\0"), "big").to_bytes(8, "little"), 0)),
 "tailsum": ("rand", lambda x: (sum(x).to_bytes(8, "little"), 0)),
 "nontailsum": ("rand", lambda x: (sum(x).to_bytes(8, "little"), 0)),
 "taillength": ("rand", lambda x: (len(x).to_bytes(8, "little"), 0)),
 "booklength": ("rand", lambda x: (len(x).to_bytes(8, "little"), 0)),
 "take5": ("rand", lambda x: (x[:5], 1)), "drop5": ("rand", lambda x: (x[5:], 1)),
 "filterall": ("rand", lambda x: (bytes(b for b in x if b > 3), 1)),
 "inceach": ("rand", lambda x: (bytes((b + 1) & 255 for b in x), 1)),
 "twice": ("rand", lambda x: (x + x, 1)),
 "headof": ("rand", lambda x: (opt(x[0] if x else None), 0)),
 "finalof": ("rand", lambda x: (opt(x[-1] if x else None), 0)),
 "findfirstgt3": ("scan", lambda x: (opt(next((b for b in x if b > 3), None)), 0)),
}
# hand-written optimised-path code (opt-words, AStmt/compileAFO) for the same function: conv a2/a3
OPTW = {"tailsum": "sum", "inceach": "inc"}
MAGIC = 0x0123456789ABCDEF
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n"
DRV = """.section .text.start
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
  sd a0, 48(s0)
  sd a1, 56(s0)
  sd a2, 64(s0)
  sd s4, 72(s0)
  sd gp, 80(s0)
  addi s0, s0, 88
  addi s2, s2, -1
  bnez s2, 1b
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
.section .tohost,"aw"
.globl tohost
.globl fromhost
.align 6
tohost: .dword 0
fromhost: .dword 0
"""
def build(name, cases, kind, src):
    """cases: list of (xs, outlen); kind ours|opt|c|empty; src = words file | opt name"""
    blob, rows = bytearray(), []
    def alloc(b):
        while len(blob) % 16: blob.append(0)
        o = len(blob); blob.extend(b); return o
    slots = int(open(src).readline()) if kind == "ours" else 0
    WK = 8 * (slots + 1) + 7
    for xs, R in cases:
        n = len(xs); i0 = alloc(xs + b"\xAA" * 64); o0 = alloc(b"\x55" * (R + 64)); w0 = alloc(b"\x77" * (max(WK, 64) + 64))
        top = f"base+{w0 + max(WK, 64)}"
        if kind == "ours": rows.append(f"  .quad base+{i0}, {n}, base+{w0}, base+{o0}, {top}, {MAGIC}")
        elif kind == "c": rows.append(f"  .quad base+{i0}, {n}, base+{o0}, 0, {top}, {MAGIC}")
        elif kind == "opt": rows.append(f"  .quad base+{i0}, {n}, " + (f"base+{w0}" if src.endswith("sum.words") else str(n)) + f", base+{o0}, {top}, {MAGIC}")
        else: rows.append(f"  .quad 0, 0, 0, 0, {top}, {MAGIC}")
    open(p(name + ".bin"), "wb").write(blob)
    if kind in ("ours", "opt"):
        ws = [l.strip() for l in open(src) if l.strip()][1 if kind == "ours" else 0:]
        body = "".join(f"  .word 0x{w}\n" for w in ws)
    elif kind == "empty": body = "  ret\n"
    else: body = "  j c_entry\n"
    s = DRV % len(cases) + "func:\n" + (body if kind != "c" else "  j c_" + name.split("__")[0] + "\n") + f'.data\n.align 4\n.globl base\nbase:\n.incbin "{p(name + ".bin")}"\n.align 3\n.globl tab\ntab:\n' + "\n".join(
        r + ", 0, 0, 0, 0, 0" for r in rows) + "\n"
    open(p(name + ".S"), "w").write(s); open(p("rv.ld"), "w").write(LD)
    objs = ""
    if kind == "c":
        sh(f"riscv64-linux-gnu-gcc -march=rv64i -mabi=lp64 -O2 -ffreestanding -nostdlib -fno-tree-loop-distribute-patterns -c {D}/bench.c -o {p('c.o')}"); objs = p("c.o")
    sh(f"riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -nostdlib -static -Wl,--no-relax -Wl,-T,{p('rv.ld')} -Wl,--build-id=none {p(name + '.S')} {objs} -o {p(name + '.elf')}")
    return p(name + ".elf")
def run(elf, ncases):
    syms = sh(f"riscv64-linux-gnu-nm {elf}")
    sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
    halt, base, tab = sym("halt"), sym("base"), sym("tab")
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {elf} -display none -serial none -monitor stdio -icount shift=0",
                         shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version"); t0 = time.time()
    while "pc       %016x" % halt not in hmp("info registers"):
        assert time.time() - t0 < 3000, "timeout"; time.sleep(0.2)
    size = tab + 88 * ncases - base
    hmp(f'pmemsave {base:#x} {size} "{p("dump.bin")}"'); q.stdin.write("quit\n"); q.wait()
    return open(p("dump.bin"), "rb").read(), tab - base
_over = []
def overhead():
    if not _over:
        e = build("empty", [(b"", 0)], "empty", None); mem, to = run(e, 1)
        _over.append(int.from_bytes(mem[to + 72:to + 80], "little") - 1)  # a lone `ret`: 1 instruction inside
    return _over[0]
def measure(fn, kind, src):
    k, model = FN[fn]; cases = []; exp = []
    for n in SIZES:
        xs = gen(n, k); y, lst = model(xs); cases.append((xs, len(y))); exp.append((y, lst))
    elf = build(f"{fn}__{kind}", cases, kind, src); mem, to = run(elf, len(cases)); res = {}
    off = 0
    for (xs, R), (y, lst), n in zip(cases, exp, SIZES):
        # layout offsets as in build()
        pass
    # recompute offsets exactly as build() did
    blobo = 0
    def al(o): return (o + 15) // 16 * 16
    WK = (8 * (int(open(src).readline()) + 1) + 7) if kind == "ours" else 0
    for c, ((xs, R), (y, lst), n) in enumerate(zip(cases, exp, SIZES)):
        i0 = al(blobo); blobo = i0 + len(xs) + 64; o0 = al(blobo); blobo = o0 + R + 64; w0 = al(blobo); blobo = w0 + max(WK, 64) + 64
        e = to + 88 * c; g = lambda j: int.from_bytes(mem[e + 8 * j:e + 8 * j + 8], "little")
        assert bytes(mem[o0:o0 + R]) == y or (kind == "opt" and fn == "tailsum" and g(8) == int.from_bytes(y, "little")), (fn, kind, n, bytes(mem[o0:o0 + 16]).hex(), y[:16].hex())
        if kind == "ours": assert g(10) == MAGIC
        if kind != "opt" and lst: assert g(7) == R or g(6) == R, (fn, kind, g(6), g(7), R)
        res[n] = g(9) - overhead()
    return res
def rv(names):
    out = json.load(open(p("rv.json"))) if os.path.exists(p("rv.json")) else {}
    for fn in names:
        r = {"ours": measure(fn, "ours", os.path.join(A, "frontx-words", fn + ".words")), "c": measure(fn, "c", None)}
        if fn in OPTW: r["opt"] = measure(fn, "opt", os.path.join(A, "opt-words", OPTW[fn] + ".words"))
        out[fn] = r; json.dump(out, open(p("rv.json"), "w"), indent=1); print(fn, r, flush=True)
def ir(cmd):
    o = subprocess.run(f"ulimit -s unlimited; valgrind --tool=callgrind --callgrind-out-file=/dev/null --main-stacksize=1000000000 {cmd}", shell=True, capture_output=True, text=True).stderr
    return int(re.search(r"Collected : (\d+)", o).group(1))
def x86(names):
    out = {}
    for fn in names:
        k = FN[fn][0]; r = {}
        for tool, exe in (("lean", f"{D}/build/bench_lean"), ("gcc86", f"{D}/build/bench_c86")):
            r[tool] = {}
            for n in SIZES:
                # per-call slope (3 reps - 1 rep)/2 removes startup and input construction
                a, b = ir(f"{exe} {fn} {n} 1 {k}"), ir(f"{exe} {fn} {n} 3 {k}")
                r[tool][n] = (b - a) / 2
        out[fn] = r; print(fn, r, flush=True)
    json.dump(out, open(p("x86.json"), "w"), indent=1)
mode, names = sys.argv[1], sys.argv[2:] or list(FN)
{"rv": rv, "x86": x86}[mode](names)
