#!/usr/bin/env python3
"""Run compiler output (`compile demoE`, words from Lean) on QEMU and on the Sail C emulator.
usage: compile_test.py WORDS_FILE NTESTS
WORDS_FILE: one hex word per line (printed by scratch/emit.lean).  Checks a0 after return against
demo(a0..a3) = ((a0 + a1) ^ (a2 & 0xff)) - (a3 | 0x1234) mod 2^64 on random inputs."""
import os, random, re, subprocess, sys, time
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "ctest")
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
M = 2**64
demo = lambda a, b, c, d: (((a + b) % M ^ (c & 0xff)) - (d | 0x1234)) % M
words = [int(l, 16) for l in open(sys.argv[1]) if l.strip()]
N = int(sys.argv[2])
p = lambda f: os.path.join(W, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
open(p("link.ld"), "w").write("""ENTRY(_start)
SECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }
  . = 0x80001000; .tohost : { *(.tohost) }
  . = 0x80002000; .data : { *(.data) } }
""")
rng = random.Random(1)
special = [0, 1, M - 1, 0x8000000000000000, 0xff, 0x1234]
for t in range(N):
    args = [rng.choice(special) if rng.random() < 0.3 else rng.randrange(M) for _ in range(4)]
    want = demo(*args)
    src = f""".section .text.start
.globl _start
_start:
  lla t6, args
  ld a0, 0(t6)
  ld a1, 8(t6)
  ld a2, 16(t6)
  ld a3, 24(t6)
  jal ra, func
  lla t6, result
  sd a0, 0(t6)
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
.text
func:
""" + "".join(f"  .word 0x{w:08x}\n" for w in words) + f"""
.section .tohost,"aw"
.globl tohost
.globl fromhost
.align 6
tohost: .dword 0
fromhost: .dword 0
.data
args: .dword {", ".join(hex(a) for a in args)}
result: .dword 0x5555555555555555
"""
    open(p("t.S"), "w").write(src)
    sh(f"riscv64-linux-gnu-gcc -march=rv64i -mabi=lp64 -nostdlib -static -Wl,-T,{p('link.ld')} -Wl,--no-relax -Wl,--build-id=none {p('t.S')} -o {p('t.elf')}")
    syms = subprocess.check_output(f"riscv64-linux-gnu-nm {p('t.elf')}", shell=True, text=True)
    halt = int(re.search(r"(\w+) t halt", syms).group(1), 16)
    res = int(re.search(r"(\w+) d result", syms).group(1), 16)
    # QEMU
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {p('t.elf')} -display none -serial none -monitor stdio",
                         shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(cmd):
        q.stdin.write(cmd + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or cmd not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version")
    t0 = time.time()
    while f"pc       {halt:016x}" not in hmp("info registers"):
        assert time.time() - t0 < 10, "QEMU did not reach halt"
        time.sleep(0.005)
    hmp(f"pmemsave {res:#x} 8 \"{p('q.bin')}\""); q.stdin.write("quit\n"); q.wait()
    qv = int.from_bytes(open(p("q.bin"), "rb").read(), "little")
    # Sail
    r = subprocess.run(f"{SAIL} --inst-limit 100000 --trace-mem --trace-output {p('sail.log')} {p('t.elf')}",
                       shell=True, capture_output=True, text=True)
    assert "SUCCESS" in r.stdout + r.stderr, (r.stdout + r.stderr)[-500:]
    sv = None
    for line in open(p("sail.log")):
        m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", line)
        if m and int(m.group(1), 16) == res: sv = int(m.group(2), 16)
    assert qv == want and sv == want, f"args {[hex(a) for a in args]}: want {want:#x} qemu {qv:#x} sail {sv}"
print(f"{N} random inputs: QEMU == Sail == demo(a0..a3) for {len(words)}-word compiled code")
