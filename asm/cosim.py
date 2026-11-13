#!/usr/bin/env python3
"""Run sort.elf on QEMU and on the Sail C emulator; compare PC trace, register writes, output bytes.
usage: cosim.py N [seed] [--notrace]"""
import os, random, re, subprocess, sys, time
N = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 0
TRACE = "--notrace" not in sys.argv
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "work"); os.makedirs(W, exist_ok=True)
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
IN, OUT = 0x80100000, 0x88000000
data = bytes(random.Random(seed).randrange(256) for _ in range(N)); want = bytes(sorted(data))
blob = N.to_bytes(8, "little") + data
p = lambda f: os.path.join(W, f)
open(p("in.bin"), "wb").write(blob)
sh = lambda c: subprocess.run(c, shell=True, check=True)
sh(f"riscv64-linux-gnu-objcopy -I binary -O elf64-littleriscv --change-section-address .data={IN-8:#x} {p('in.bin')} {p('in.o')}")
sh(f"riscv64-linux-gnu-ld -Ttext=0 --section-start=.data={IN-8:#x} -e 0 {p('in.o')} -o {p('in.elf')}")
syms = subprocess.check_output(f"riscv64-linux-gnu-nm {D}/sort.elf", shell=True, text=True)
halt = int(re.search(r"(\w+) t halt", syms).group(1), 16)

# ---- QEMU
q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {D}/sort.elf -display none -serial none -monitor stdio "
                     f"-device loader,file={p('in.bin')},addr={IN-8:#x} "
                     + (f"-accel tcg,one-insn-per-tb=on -d exec,cpu,nochain -D {p('qemu.log')}" if TRACE else ""),
                     shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
t0 = time.time()
def hmp(cmd):
    q.stdin.write(cmd + "\n"); buf = ""
    while not buf.endswith("(qemu) ") or cmd not in buf: buf += q.stdout.read(1)
    return buf
hmp("info version")
while f"pc       {halt:016x}" not in hmp("info registers"): time.sleep(0.005)
qemu_secs = time.time() - t0
hmp(f"pmemsave {OUT:#x} {max(N,1)} \"{p('qemu_out.bin')}\""); q.stdin.write("quit\n"); q.wait()
qemu_out = open(p("qemu_out.bin"), "rb").read()[:N]
assert qemu_out == want, "QEMU output != sorted input"

# ---- Sail
open(p("sig.ld"), "w").write("")
t0 = time.time()
r = subprocess.run(f"{SAIL} --inst-limit 4000000000 " + (f"--trace-instr --trace-reg --trace-mem --trace-output {p('sail.log')} " if TRACE else "")
                   + f"{D}/sort.elf {p('in.elf')}", shell=True, capture_output=True, text=True)
sail_secs = time.time() - t0
assert "SUCCESS" in r.stdout + r.stderr, r.stdout[-500:] + r.stderr[-500:]
m = re.search(r"Instructions:\s*(\d+)", r.stdout + r.stderr)
print(f"N={N} seed={seed}: QEMU ok ({qemu_secs:.3f}s wall incl. startup), Sail ok ({sail_secs:.2f}s)")
if not TRACE: sys.exit(0)

# ---- compare traces from PC=0x80000000 until halt
sail_mem = {}
sail_steps = []  # (pc, [(reg, val)])
for line in open(p("sail.log")):
    m = re.match(r"\[\d+\] \[M\]: 0x([0-9A-F]+) ", line)
    if m: sail_steps.append((int(m.group(1), 16), [])); continue
    m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", line)
    if m:
        a, v = int(m.group(1), 16), bytes.fromhex(m.group(2))[::-1]
        for k, b in enumerate(v): sail_mem[a + k] = b
    m = re.match(r"x(\d+) <- 0x([0-9A-F]+)", line)
    if m and sail_steps: sail_steps[-1][1].append((int(m.group(1)), int(m.group(2), 16)))
qemu_steps = []  # (pc, regs-before)
names = "zero ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6".split()
cur = None
for line in open(p("qemu.log")):
    m = re.match(r" pc\s+([0-9a-f]{16})", line)
    if m: cur = (int(m.group(1), 16), {}); qemu_steps.append(cur); continue
    if cur and line.startswith(" x"):
        for r_, v in re.findall(r"x\d+/(\w+)\s+([0-9a-f]{16})", line): cur[1][r_] = int(v, 16)
cut = lambda s: s[next(i for i, x in enumerate(s) if x[0] == 0x80000000):]
S, Q = cut(sail_steps), cut(qemu_steps)
Q = Q[:len(S)]
assert len(Q) == len(S), (len(Q), len(S))
nw = 0
for i, ((spc, writes), (qpc, _)) in enumerate(zip(S, Q)):
    assert spc == qpc, f"step {i}: PC sail {spc:#x} qemu {qpc:#x}"
    if i + 1 < len(Q):
        for reg, val in writes:
            nw += 1; assert Q[i + 1][1][names[reg]] == val, f"step {i} pc {spc:#x}: x{reg} sail {val:#x} qemu {Q[i+1][1][names[reg]]:#x}"
assert bytes(sail_mem[OUT + i] for i in range(N)) == qemu_out, "Sail output bytes != QEMU output bytes"
print(f"  trace match: {len(S)} instructions, {nw} register writes identical, Sail out == QEMU out == sorted(input)")
