#!/usr/bin/env python3
"""Insertion-sort code of apc/test/words.txt on AArch64 QEMU (system mode, virt, cortex-a72): x0 = input, x1 = length,
x3 = output block.  Checks: output = sorted(input), input unchanged, guard bytes around the output unchanged.
usage: sort_test.py WORKDIR [N=300]"""
import os, random, re, subprocess, sys, time
W = sys.argv[1]; N = int(sys.argv[2]) if len(sys.argv) > 2 else 300
os.makedirs(W, exist_ok=True); p = lambda f: os.path.join(W, f)
words = dict(l.split(None, 1) for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "words.txt")))["sort"].split()
r = random.Random(2); tests = []
for i in range(N):
    n = r.choice([0, 1, 2, 3]) if i % 6 == 0 else r.randrange(0, 80)
    k = r.choice([1, 2, 4, 256]); tests.append(bytes(r.randrange(256) % k if i % 4 == 0 else r.randrange(256) for _ in range(n)))
G = 8  # guard bytes on both sides of every output block
S = """.section .text.start
.globl _start
_start: ldr x19, =tab
  ldr x21, =%d
loop: ldp x0, x1, [x19]
  ldr x3, [x19, #16]
  bl func
  add x19, x19, #24
  subs x21, x21, #1
  b.ne loop
halt: b halt
.ltorg
func:
%s.data
dstart:
%stab:
%sdend:
"""
blocks = "".join(f"in{i}: .byte {', '.join(map(str, t)) or '0'}\ng{i}: .fill {G}, 1, 0xAA\nout{i}: .fill {max(len(t), 1)}, 1, 0x55\nh{i}: .fill {G}, 1, 0xBB\n" for i, t in enumerate(tests))
tab = "".join(f"  .quad in{i}, {len(t)}, out{i}\n" for i, t in enumerate(tests))
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
    assert time.time() - t0 < 120, "QEMU did not reach halt"; time.sleep(0.02)
n = sym["tab"] - sym["dstart"]; hmp(f'pmemsave {sym["dstart"]:#x} {n} "{p("o.bin")}"'); q.stdin.write("quit\n"); q.wait()
d = open(p("o.bin"), "rb").read(); assert len(d) == n
bad = 0
for i, t in enumerate(tests):
    g = lambda s, k: d[sym[s] - sym["dstart"]:sym[s] - sym["dstart"] + k]
    ok = g(f"out{i}", len(t)) == bytes(sorted(t)) and g(f"in{i}", len(t)) == t and g(f"g{i}", G) == b"\xaa" * G and g(f"h{i}", G) == b"\xbb" * G
    if not ok: bad += 1; print(f"MISMATCH test {i} in={t.hex()} out={g(f'out{i}', len(t)).hex()} guards={g(f'g{i}', G).hex()} {g(f'h{i}', G).hex()}")
print(f"sort: {N} inputs (lengths 0..79), {len(words)} words, mismatches {bad}")
assert bad == 0
