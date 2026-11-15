#!/usr/bin/env python3
"""Run the emitted ARM words of Apc/Emit2.lean (test/words2.txt) on AArch64 QEMU (system mode, virt, cortex-a72).
Per test the stub sets x0 = input, x1 = length, x2 = scratch / table block, x3 = output, sp = top of a 64 KiB work
block, x28 = a magic value, then `bl func`; afterwards it records sp and x28.  Checks: the output (sorted input /
CRC-32 / the word result), input unchanged, guard bytes around the output, sp and x28 restored.
usage: ext_test.py KIND WORKDIR [N=300]   KIND in msort msortO crc crcO sumTo fib isEven tree"""
import os, random, re, subprocess, sys, time, zlib
K, W = sys.argv[1], sys.argv[2]; N = int(sys.argv[3]) if len(sys.argv) > 3 else 300
os.makedirs(W, exist_ok=True); p = lambda f: os.path.join(W, f)
words = dict(l.split(None, 1) for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "words2.txt")))[K].split()
r = random.Random(7); M64 = (1 << 64) - 1
def tree(d):                                   # random tree, its encoding (Spec/Tree.lean) and value
    if d == 0 or r.random() < 0.3:
        v = r.randrange(256); return [0, v], v
    op = r.choice([1, 2, 3]); ea, va = tree(d - 1); eb, vb = tree(d - 1)
    return [op] + ea + eb, ((va + vb) if op == 1 else (va - vb) if op == 2 else (va ^ vb)) & M64
def fib(n):
    a, b = 0, 1
    for _ in range(n): a, b = b, a + b
    return a & M64
tests = []                                     # (input bytes, expected output bytes)
for i in range(N):
    if K in ("msort", "msortO"):
        n = r.choice([0, 1, 2, 3]) if i % 6 == 0 else r.randrange(0, 200)
        k = r.choice([1, 2, 4, 256]); t = bytes(r.randrange(256) % k if i % 4 == 0 else r.randrange(256) for _ in range(n))
        tests.append((t, bytes(sorted(t))))
    elif K in ("crc", "crcO"):
        t = bytes(r.randrange(256) for _ in range(r.randrange(0, 300))); tests.append((t, zlib.crc32(t).to_bytes(4, "little")))
    elif K == "sumTo":
        n = r.randrange(256); tests.append((bytes([n]), (n * (n + 1) // 2).to_bytes(8, "little")))
    elif K == "fib":
        n = r.randrange(23); tests.append((bytes([n]), fib(n).to_bytes(8, "little")))
    elif K == "isEven":
        n = r.randrange(256); tests.append((bytes([n]), (1 if n % 2 == 0 else 0).to_bytes(8, "little")))
    elif K == "tree":
        e, v = tree(r.randrange(0, 7)); tests.append((bytes(e), v.to_bytes(8, "little")))
G = 8
S = """.section .text.start
.globl _start
_start: ldr x19, =tab
  ldr x21, =%d
  ldr x28, =0x2828282828282828
loop: ldp x0, x1, [x19]
  ldp x2, x3, [x19, #16]
  ldr x9, [x19, #32]
  mov sp, x9
  bl func
  mov x9, sp
  str x9, [x19, #40]
  str x28, [x19, #48]
  add x19, x19, #56
  subs x21, x21, #1
  b.ne loop
halt: b halt
.ltorg
func:
%s.data
.balign 16
dstart:
%s.balign 16
stk: .fill 65536, 1, 0
stktop:
tab:
%sdend:
"""
blocks = "".join(f".balign 8\nin{i}: .byte {', '.join(map(str, t)) or '0'}\n.balign 8\nsc{i}: .fill {max(len(t), 2048)}, 1, 0x33\n"
                 f".balign 8\ng{i}: .fill {G}, 1, 0xAA\nout{i}: .fill {max(len(e), len(t), 1)}, 1, 0x55\nh{i}: .fill {G}, 1, 0xBB\n"
                 for i, (t, e) in enumerate(tests))
tab = "".join(f"  .quad in{i}, {len(t)}, sc{i}, out{i}, stktop, 0, 0\n" for i, (t, e) in enumerate(tests))
open(p("s.S"), "w").write(S % (N, "".join(f"  .word 0x{w}\n" for w in words), blocks, tab))
open(p("s.ld"), "w").write("ENTRY(_start)\nSECTIONS { . = 0x40200000; .text : { *(.text.start) *(.text) } .data : { *(.data) } }\n")
subprocess.run(f"aarch64-linux-gnu-gcc -nostdlib -static -Wl,-T,{p('s.ld')} -Wl,--build-id=none {p('s.S')} -o {p('s.elf')} 2>&1 | grep -v RWX; true", shell=True, check=True)
sym = {m.group(2): int(m.group(1), 16) for m in re.finditer(r"(\w+) \w (\w+)\n", subprocess.check_output(f"aarch64-linux-gnu-nm {p('s.elf')}", shell=True, text=True))}
q = subprocess.Popen(f"qemu-system-aarch64 -machine virt -cpu cortex-a72 -m 1G -display none -serial none -monitor stdio -device loader,file={p('s.elf')},cpu-num=0",
                     shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
def hmp(c):
    q.stdin.write(c + "\n"); b = ""
    while not b.endswith("(qemu) ") or c not in b: b += q.stdout.read(1)
    return b
hmp("info version"); t0 = time.time()
while "PC=%016x" % sym["halt"] not in hmp("info registers"):
    assert time.time() - t0 < 300, "QEMU did not reach halt"; time.sleep(0.05)
n = sym["dend"] - sym["dstart"]; hmp(f'pmemsave {sym["dstart"]:#x} {n} "{p("o.bin")}"'); q.stdin.write("quit\n"); q.wait()
d = open(p("o.bin"), "rb").read(); assert len(d) == n
g = lambda s, k: d[sym[s] - sym["dstart"]:sym[s] - sym["dstart"] + k]
bad = 0
for i, (t, e) in enumerate(tests):
    row = g("tab", 56 * N)[56 * i:56 * i + 56]
    sp, x28 = int.from_bytes(row[40:48], "little"), int.from_bytes(row[48:56], "little")
    ok = (g(f"out{i}", len(e)) == e and g(f"in{i}", len(t)) == t and g(f"g{i}", G) == b"\xaa" * G and
          g(f"h{i}", G) == b"\xbb" * G and sp == sym["stktop"] and x28 == 0x2828282828282828)
    if not ok: bad += 1; print(f"MISMATCH {K} test {i} in={t.hex()} out={g(f'out{i}', len(e)).hex()} want={e.hex()} sp={sp:#x} x28={x28:#x}")
print(f"{K}: {N} inputs, {len(words)} words, mismatches {bad}")
assert bad == 0
