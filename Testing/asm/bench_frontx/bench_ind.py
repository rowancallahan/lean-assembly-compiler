#!/usr/bin/env python3
"""Instruction counts of the frontx_ind words (ours: decode + function + encode of the byte format) vs gcc -O2 C on linked
structures (core = the function alone on a built structure; e2e = decode + function + encode, as ours), QEMU -icount shift=0, minstret.
usage: bench_ind.py [FN...] -> results/ind.json"""
import json, os, random, re, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__)); A = os.path.dirname(D); W = os.path.join(D, "work"); os.makedirs(W, exist_ok=True)
p = lambda f: os.path.join(W, f)
def sh(c): return subprocess.run(c, shell=True, check=True, capture_output=True, text=True).stdout
M = 2**64 - 1; MAGIC = 0x0123456789ABCDEF
IN, WORK, OUT, OUT2, HEAP, STK = 0x81000000, 0x82000000, 0x8a000000, 0x8b000000, 0x90000000, 0xBFF00000
le = lambda v: (v & M).to_bytes(8, "little")
# trees as python values: None | (l, x, r); lists as python lists; levels None-free: ('z',) ('s',u) ('m',u,v) ('i',u,v) ('p',)
def tree(n, rnd):
    if n == 0: return None
    k = rnd.randrange(n); return (tree(k, rnd), rnd.randrange(2**64), tree(n - 1 - k, rnd))
def balanced(n, rnd):
    if n == 0: return None
    k = (n - 1) // 2; return (balanced(k, rnd), rnd.randrange(2**64), balanced(n - 1 - k, rnd))
def et(t): return b"\0" if t is None else b"\1" + et(t[0]) + le(t[1]) + et(t[2])
def mir(t): return None if t is None else (mir(t[2]), t[1], mir(t[0]))
def cnt(t): return 0 if t is None else 1 + cnt(t[0]) + cnt(t[2])
el = lambda xs: b"".join(b"\1" + le(x) for x in xs) + b"\0"
def lv(n, rnd):  # n internal nodes, leaves all zero
    if n == 0: return b"\0"
    k = rnd.randrange(n); t = rnd.choice([1, 2, 3])
    return b"\1" + lv(n - 1, rnd) if t == 1 else bytes([t]) + lv(k, rnd) + lv(n - 1 - k, rnd)
def gen(fn, n, rnd):
    """-> (input bytes, expected output bytes, nodes)"""
    if fn in ("count", "mirror"):
        t = balanced(n, rnd); return et(t), (le(cnt(t)) if fn == "count" else et(mir(t))), n
    xs = [rnd.randrange(2**64) for _ in range(n)]
    if fn == "nontail": return el(xs), le(sum(xs)), n
    if fn == "reverse": return el(xs), el(xs[::-1]), n
    if fn == "append": ys = [rnd.randrange(2**64) for _ in range(n)]; return el(xs) + el(ys), el(xs + ys), 2 * n
    if fn == "hasparam": b = lv(n, rnd); return b, b"\0", n
WORDS = {"count": "bt_count", "mirror": "bt_mirror", "nontail": "nontail_sum_ln", "reverse": "tail_reverse_ln", "append": "list_append_ln", "hasparam": "level_hasparam"}
SIZES = tuple(int(x) for x in os.environ.get("SZ", "500,2000").split(","))
LD = f"ENTRY(_start)\nSECTIONS {{ . = 0x80000000; .text : {{ *(.text.start) *(.text) }}\n . = 0x80100000; .tohost : {{ *(.tohost) }}\n . = 0x80200000; .data : {{ *(.data) }}\n . = {HEAP:#x}; .heap : {{ heap = .; }} }}\n"
def harness(call, setup, after=""):
    return f"""  {setup}
  lla t1, tmp
  csrr t0, minstret
  sd t0, 0(t1)
  {call}
  csrr t2, minstret
  {after}
  lla t1, tmp
  ld t0, 0(t1)
  sub t2, t2, t0
  lla t3, resp
  ld t4, 0(t3)
  sd t2, 0(t4)
  addi t4, t4, 8
  sd t4, 0(t3)
"""
def build(fn, inp, R):
    ws = [l.strip() for l in open(os.path.join(A, "frontx-words", WORDS[fn] + ".words")) if l.strip()]
    hdr = ws[0].split(); assert hdr[0] == "ind"; A0, B0 = int(hdr[1]), int(hdr[2]); words = ws[1:]
    n = len(inp); wk = A0 + B0 * n; wk += -wk % 8
    open(p("in.bin"), "wb").write(inp)
    S = f""".section .text.start
.globl _start
_start: li sp, {STK}
  lla t0, res
  lla t1, resp
  sd t0, 0(t1)
  li gp, {MAGIC}
"""
    S += harness("jal ra, emp", "")
    # ours: sp switched to the work end around the call
    S += harness("jal ra, func", f"""li a0, {IN}
  li a1, {n}
  li a2, {WORK}
  li a3, {OUT}
  lla t5, mainsp
  sd sp, 0(t5)
  li sp, {WORK + wk}""", f"""lla t5, mainsp
  ld sp, 0(t5)
  lla t5, post
  sd a1, 0(t5)
  sd gp, 8(t5)""")
    S += f"  li gp, 0\n"
    S += f"  li a0, {IN}\n  jal ra, reset\n  li a0, {IN}\n  jal ra, build_{fn}\n  lla t5, post\n  sd a0, 16(t5)\n  li a0, {IN}\n  jal ra, build_{'append2' if fn == 'append' else fn}\n  lla t5, post\n  ld a1, 16(t5)\n  sd a0, 24(t5)\n"
    # core: a0 = root, a1 = root2
    S += harness(f"jal ra, core_{fn}", "lla t5, post\n  ld a0, 16(t5)\n  ld a1, 24(t5)", "lla t5, post\n  sd a0, 32(t5)")
    S += f"  jal ra, reset\n"
    S += harness(f"jal ra, e2e_{fn}", f"li a0, {IN}\n  li a1, {n}\n  li a2, {OUT2}", "lla t5, post\n  sd a0, 40(t5)")
    S += f"""  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
emp: ret
func:
""" + "".join(f"  .word 0x{w}\n" for w in words) + f""".section .tohost,"aw"
.globl tohost
.globl fromhost
.align 6
tohost: .dword 0
fromhost: .dword 0
.data
.align 4
.globl res
res: .fill 8, 8, 0
resp: .dword 0
tmp: .dword 0
mainsp: .dword 0
.globl post
post: .fill 8, 8, 0
.org {IN - 0x80200000}
.incbin "{p('in.bin')}"
"""
    open(p("ind.S"), "w").write(S); open(p("ind.ld"), "w").write(LD)
    sh(f"riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -O2 -ffreestanding -nostdlib -static -fno-tree-loop-distribute-patterns -Wl,--no-relax -Wl,--build-id=none -Wl,-T,{p('ind.ld')} {p('ind.S')} {D}/ind.c -o {p('ind.elf')}")
    return wk
def run(fn, inp, exp):
    wk = build(fn, inp, len(exp)); syms = sh(f"riscv64-linux-gnu-nm {p('ind.elf')}")
    sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {p('ind.elf')} -display none -serial none -monitor stdio -icount shift=0",
                         shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version")
    import time; t0 = time.time()
    while "pc       %016x" % sym("halt") not in hmp("info registers"):
        assert time.time() - t0 < 1500; time.sleep(0.3)
    hmp(f'pmemsave {sym("res"):#x} 32 "{p("r.bin")}"'); hmp(f'pmemsave {sym("post"):#x} 64 "{p("post.bin")}"')
    hmp(f'pmemsave {OUT:#x} {len(exp) + 8} "{p("o1.bin")}"'); hmp(f'pmemsave {OUT2:#x} {len(exp) + 8} "{p("o2.bin")}"'); q.stdin.write("quit\n"); q.wait()
    g = lambda f, i: int.from_bytes(open(p(f), "rb").read()[8 * i:8 * i + 8], "little")
    emp, ours, core, e2e = (g("r.bin", i) for i in range(4)); ov = emp - 1
    o1, o2 = open(p("o1.bin"), "rb").read()[:len(exp)], open(p("o2.bin"), "rb").read()[:len(exp)]
    assert g("post.bin", 1) == MAGIC, "gp not restored"
    if fn != "hasparam":   # hasparam's expected byte is checked below (levels have no python model: compare ours with C)
        assert o1 == exp, (fn, "ours", o1[:24].hex(), exp[:24].hex()); assert o2 == exp, (fn, "gcc e2e")
        if exp[:1] and fn in ("mirror", "reverse", "append"): assert g("post.bin", 0) == len(exp), (fn, g("post.bin", 0), len(exp))
        assert g("post.bin", 5) == len(exp)
    else: assert o1[:1] == o2[:1], ("hasparam", o1[:1], o2[:1])
    return ours - ov, core - ov, e2e - ov
out = {}
for fn in sys.argv[1:] or list(WORDS):
    rnd = random.Random(7); r = {}
    for n in ((511, 4095) if fn in ("count", "mirror") else SIZES):
        inp, exp, nodes = gen(fn, n, rnd); r[nodes] = run(fn, inp, exp); print(fn, n, nodes, len(inp), r[nodes], flush=True)
    out[fn] = r; json.dump(out, open(os.path.join(D, "results", "ind.json"), "w"), indent=1)
