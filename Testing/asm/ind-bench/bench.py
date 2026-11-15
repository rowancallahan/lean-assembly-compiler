# usage: python3 bench.py; instructions executed by one call (minstret, qemu -icount) of the `frontx_ind` words
# (Testing/asm/frontx-words) vs gcc -O2 (rv64i) on the same input bytes (ind.c: decode, run, encode)
import subprocess, os, re, sys
D = os.path.dirname(os.path.abspath(__file__)); C = os.path.join(D, "..", "ctest"); os.makedirs(C, exist_ok=True)
p = lambda f: os.path.join(C, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n"
def run(name, cfunc, inp, desc):
    lines = open(os.path.join(D, "..", "frontx-words", name + ".words")).read().split("\n")
    hd = lines[0].split()
    # `indw` (programs of several functions): a work block of 4 MiB (the theorem's bound is per input)
    A, B = (int(hd[1]), int(hd[2])) if hd[0] == "ind" else (1 << 22, 0) if hd[0] == "indw" else (8 * (int(hd[0]) + 1) + 7, 0)
    ws = [int(l, 16) for l in lines[1:] if l.strip()]
    func = "".join(f"  .word 0x{w:08x}\n" for w in ws)
    n = len(inp); wk = A + B * n
    OUT = max(2 * n + 16, 1 << 16)
    data = ",".join(str(b) for b in inp) or "0"
    src = f""".section .text.start
.globl _start
_start: lla a0, inp
  li a1, {n}
  lla a2, work
  lla a3, out
  li t0, {wk}
  add sp, a2, t0
  csrr s1, minstret
  jal ra, func
  csrr s2, minstret
  sub s3, s2, s1
  lla t0, res
  sd s3, 0(t0)
  lla a0, inp
  li a1, {n}
  lla a2, work
  lla a3, out2
  li t0, {wk}
  add sp, a2, t0
  csrr s1, minstret
  call {cfunc}
  csrr s2, minstret
  sub s3, s2, s1
  lla t0, res
  sd s3, 8(t0)
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
inp: .byte {data}
.align 4
out: .fill {OUT}, 1, 0
out2: .fill {OUT}, 1, 0
.align 4
work: .fill {wk + 16}, 1, 0
"""
    open(p("b.S"), "w").write(src); open(p("m.ld"), "w").write(LD)
    sh(f"riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -O2 -ffreestanding -nostdlib -static -Wl,-T,{p('m.ld')} -Wl,--no-relax -Wl,--build-id=none {p('b.S')} {os.path.join(D, 'ind.c')} -o {p('b.elf')}")
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
    hmp(f'pmemsave {sym("res"):#x} 16 "{p("r.bin")}"')
    hmp(f'pmemsave {sym("out"):#x} {OUT} "{p("o1.bin")}"'); hmp(f'pmemsave {sym("out2"):#x} {OUT} "{p("o2.bin")}"')
    q.stdin.write("quit\n"); q.wait()
    r = open(p("r.bin"), "rb").read(); v = [int.from_bytes(r[8*i:8*i+8], "little") for i in range(2)]
    same = open(p("o1.bin"), "rb").read() == open(p("o2.bin"), "rb").read()
    print(f"{name} ({desc}, {n} input bytes): ours {v[0]} instr, gcc -O2 {v[1]} instr, ratio {v[0]/v[1]:.1f}, outputs equal: {same}")
le8 = lambda k: list(k.to_bytes(8, "little"))
def bst(keys):  # balanced BST over sorted keys, encoded
    if not keys: return [0]
    m = len(keys) // 2
    return [1] + bst(keys[:m]) + le8(keys[m]) + bst(keys[m+1:])
lst = lambda xs: sum(([1] + le8(x) for x in xs), []) + [0]
ONLY = sys.argv[1:]
_run = run
def run(name, *a):
    if not ONLY or name in ONLY: _run(name, *a)
keys = [2 * i for i in range(1, 256)]  # 255 keys, 5 absent
run("tree_contains5", "c_contains5", bst(keys), "balanced BST, 255 keys")
run("tree_insert5", "c_insert5", bst(keys), "balanced BST, 255 keys")
xs = [i + 10 for i in range(200)] + [5]
run("list_elem5", "c_elem5", lst(xs), "201 elements, 5 last")
run("list_erase5", "c_erase5", lst(xs), "201 elements, 5 last")
w = list((0x123456789ABCDEF0).to_bytes(8, "little"))
run("satprede", "c_satpred", w, "satPred, one word")
run("bvarofdatae", "c_bvarofdata", w, "bvarOfData, one word")
run("packdatae", "c_packdata", w, "packData, four bytes")
pos = lambda n: [1] * (n - 1) + [0]
run("pos_mul", "c_posmul", pos(30) + pos(30), "Pos.mul 30 * 30")
xs = [i + 10 for i in range(100)]
run("nontail_reverse_ln", "c_reverse", lst(xs), "NonTail.reverse, 100 elements")
def lv(d, s):  # a level of depth d: max / imax / succ / zero / param
    if d == 0: return [0] if s % 2 == 0 else [4]
    k = (s * 2654435761 + d) % 7
    if k < 2: return [1] + lv(d - 1, s + 1)
    if k < 4: return [2] + lv(d - 1, 2 * s) + lv(d - 1, 2 * s + 1)
    return [3] + lv(d - 1, 2 * s + 3) + lv(d - 1, 2 * s + 1)
run("level_simplify", "c_simplify", lv(9, 1), "Level.simplify, depth 9")
