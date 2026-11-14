#!/usr/bin/env python3
"""Run loop-compiler output (`compileF sumProg` / `compileF gcdProg`, words printed by scratch/emit_loops.lean)
on QEMU and on the Sail C emulator, many inputs per ELF (a driver loop calls the function once per input;
it keeps its pointers in s0..s2, which the function provably preserves).
usage: loop_test.py WORDS_FILE {sum,gcd} NTESTS
Checks a0 after each call against the Python model of `sumDown a0 a1` / `gcdSub a0 a1`."""
import os, random, re, subprocess, sys, time
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "ctest")
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
M = 2**64

def sumDown(n, acc):
    while n: n, acc = n - 1, (acc + n) % M
    return acc

def gcdSub(a, b):
    while a and b:
        if a < b: b -= a
        else: a -= b
    return b if a == 0 else a

words = [int(l, 16) for l in open(sys.argv[1]) if l.strip()]
which, N = sys.argv[2], int(sys.argv[3])
rng = random.Random(2)
fib = [1, 2]
while fib[-1] < M: fib.append(fib[-1] + fib[-2])
fib = [f for f in fib if f < M]
def rand_input():
    junk = [rng.randrange(M) for _ in range(2)]   # a2, a3: ignored by sum, a2 clobbered by gcd
    if which == "sum":
        n = rng.choice([0, 1, 2, 3, rng.randrange(50), rng.randrange(400)])
        acc = rng.choice([0, 0, M - 1, rng.randrange(M)])
        return [n, acc] + junk
    k = rng.randrange(6)
    if k == 0: a, b = rng.randrange(400), rng.randrange(400)
    elif k == 1:  # big multiples of a big gcd: few iterations, 64-bit values
        g = rng.randrange(1, M // 64); a, b = g * rng.randrange(1, 40), g * rng.randrange(1, 40)
    elif k == 2: i = rng.randrange(1, len(fib) - 1); a, b = fib[i], fib[i - 1]   # worst case for Euclid
    elif k == 3: a, b = rng.choice([0, rng.randrange(M)]), 0
    elif k == 4: a, b = 0, rng.randrange(M)
    else: a = rng.randrange(M); b = a
    if rng.random() < 0.5: a, b = b, a
    return [a, b] + junk
ref = (lambda a: sumDown(a[0], a[1])) if which == "sum" else (lambda a: gcdSub(a[0], a[1]))
p = lambda f: os.path.join(W, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
os.makedirs(W, exist_ok=True)
open(p("link.ld"), "w").write("""ENTRY(_start)
SECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }
  . = 0x80010000; .tohost : { *(.tohost) }
  . = 0x80020000; .data : { *(.data) } }
""")
B = 50   # inputs per ELF
done = 0
while done < N:
    k = min(B, N - done)
    args = [rand_input() for _ in range(k)]
    src = f""".section .text.start
.globl _start
_start:
  lla s0, args
  lla s1, results
  li s2, {k}
1:
  ld a0, 0(s0)
  ld a1, 8(s0)
  ld a2, 16(s0)
  ld a3, 24(s0)
  jal ra, func
  sd a0, 0(s1)
  addi s0, s0, 32
  addi s1, s1, 8
  addi s2, s2, -1
  bnez s2, 1b
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
.text
func:
""" + "".join(f"  .word 0x{w:08x}\n" for w in words) + """
.section .tohost,"aw"
.globl tohost
.globl fromhost
.align 6
tohost: .dword 0
fromhost: .dword 0
.data
args:
""" + "".join(f"  .dword {', '.join(hex(x) for x in a)}\n" for a in args) + f"""results: .fill {k}, 8, 0x5555555555555555
"""
    open(p("l.S"), "w").write(src)
    sh(f"riscv64-linux-gnu-gcc -march=rv64i -mabi=lp64 -nostdlib -static -Wl,-T,{p('link.ld')} -Wl,--no-relax -Wl,--build-id=none {p('l.S')} -o {p('l.elf')}")
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {p('l.elf')}", shell=True, text=True)
    halt = int(re.search(r"(\w+) t halt", syms).group(1), 16)
    res = int(re.search(r"(\w+) d results", syms).group(1), 16)
    # QEMU
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {p('l.elf')} -display none -serial none -monitor stdio",
                         shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(cmd):
        q.stdin.write(cmd + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or cmd not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version")
    t0 = time.time()
    while f"pc       {halt:016x}" not in hmp("info registers"):
        assert time.time() - t0 < 60, "QEMU did not reach halt"
        time.sleep(0.01)
    hmp(f"pmemsave {res:#x} {8 * k} \"{p('q.bin')}\""); q.stdin.write("quit\n"); q.wait()
    qb = open(p("q.bin"), "rb").read()
    qv = [int.from_bytes(qb[8 * i:8 * i + 8], "little") for i in range(k)]
    # Sail
    r = subprocess.run(f"{SAIL} --inst-limit 20000000 --trace-mem --trace-output {p('sail.log')} {p('l.elf')}",
                       shell=True, capture_output=True, text=True)
    assert "SUCCESS" in r.stdout + r.stderr, (r.stdout + r.stderr)[-500:]
    sv = [None] * k
    for line in open(p("sail.log")):
        m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", line)
        if m and res <= int(m.group(1), 16) < res + 8 * k: sv[(int(m.group(1), 16) - res) // 8] = int(m.group(2), 16)
    for a, x, y in zip(args, qv, sv):
        want = ref(a)
        assert x == want and y == want, f"args {[hex(v) for v in a]}: want {want:#x} qemu {x:#x} sail {y}"
    done += k
    print(f"{which}: {done}/{N} ok", flush=True)
