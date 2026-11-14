#!/usr/bin/env python3
"""Three-way test, list class: book function run by Lean (expected output in the input file written by
book_pipe.lean) == RV64 machine code on QEMU == on Sail C emulator. Adapted from Testing/asm/pipe_test.py.
usage: book_pipe_test.py book_pipe.txt   (env WORK = scratch dir)"""
import os, random, re, subprocess, sys, time
D = os.path.dirname(os.path.abspath(__file__)); W = os.environ.get("WORK") or os.path.join(D, "ctest"); os.makedirs(W, exist_ok=True)
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
p = lambda f: os.path.join(W, f)
sh = lambda c: subprocess.run(c, shell=True, check=True)
unhex = lambda t: [] if t == "-" else list(bytes.fromhex(t))
CASES = []
for l in open(sys.argv[1]):
    k, *r = l.split()
    if k == "case": CASES.append({"name": r[0], "t": []})
    elif k == "words": CASES[-1]["words"] = [int(x, 16) for x in r]
    elif k == "space": CASES[-1]["space"] = [int(x) for x in r]
    else: assert k == "t"; CASES[-1]["t"].append((unhex(r[0]), unhex(r[1])))
S = 128
DRIVER = """.section .text.start
.globl _start
_start: lla s0, tab
  li s2, %d
1: ld a0, 0(s0)
  ld a1, 8(s0)
  ld a2, 16(s0)
  ld a3, 24(s0)
  jal ra, func
  addi s0, s0, 32
  addi s2, s2, -1
  bnez s2, 1b
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
func:
%s.section .tohost,"aw"
.globl tohost
.globl fromhost
.align 6
tohost: .dword 0
fromhost: .dword 0
.data
.align 7
ins:
%s
outs: .fill %d, 1, 0x55
tab:
%s"""
open(p("pipe.ld"), "w").write("ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n")
for C in CASES:
    which, words, space, tests = C["name"], C["words"], C["space"], C["t"]
    rng = random.Random(5)
    B, done = 40, 0
    N = len(tests)
    while done < N:
        k = min(B, N - done)
        chunk = tests[done:done + k]; cases = [x for x, _ in chunk]
        ins = "\n".join(f"  .byte {', '.join(str(x) for x in xs + [0xAA] * (S - len(xs)))}" for xs in cases)
        tab = "\n".join(f"  .quad ins+{S*i}, {len(xs)}, {rng.getrandbits(64)}, outs+{S*i}" for i, xs in enumerate(cases))
        open(p("pipe.S"), "w").write(DRIVER % (k, "".join(f"  .word 0x{w:08x}\n" for w in words), ins, S * k, tab))
        sh(f"riscv64-linux-gnu-gcc -march=rv64i -mabi=lp64 -nostdlib -static -Wl,-T,{p('pipe.ld')} -Wl,--no-relax -Wl,--build-id=none {p('pipe.S')} -o {p('pipe.elf')}")
        syms = subprocess.check_output(f"riscv64-linux-gnu-nm {p('pipe.elf')}", shell=True, text=True)
        sym = lambda s: int(re.search(rf"(\w+) \w {s}\n", syms).group(1), 16)
        halt, ins_a, outs_a, tab_a = sym("halt"), sym("ins"), sym("outs"), sym("tab")
        size = tab_a - ins_a
        # QEMU
        q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {p('pipe.elf')} -display none -serial none -monitor stdio",
                             shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
        def hmp(c):
            q.stdin.write(c + "\n"); buf = ""
            while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
            return buf
        hmp("info version"); t0 = time.time()
        while "pc       %016x" % halt not in hmp("info registers"):
            assert time.time() - t0 < 120, "QEMU did not reach halt"; time.sleep(0.01)
        hmp(f'pmemsave {ins_a:#x} {size} "{p("q.bin")}"'); q.stdin.write("quit\n"); q.wait()
        qmem = open(p("q.bin"), "rb").read()
        # Sail: replay the data writes on the initial image
        r = subprocess.run(f"{SAIL} --inst-limit 200000000 --trace-mem --trace-output {p('sail.log')} {p('pipe.elf')}",
                           shell=True, capture_output=True, text=True)
        assert "SUCCESS" in r.stdout + r.stderr, (r.stdout + r.stderr)[-500:]
        init = bytearray()
        for xs in cases: init += bytes(xs + [0xAA] * (S - len(xs)))
        init += bytes([0x55] * (S * k))
        allowed = set()
        for i, xs in enumerate(cases):
            assert len(chunk[i][1]) <= space[len(xs)] <= S
            allowed |= set(range(outs_a + S * i, outs_a + S * i + space[len(xs)]))
        smem = bytearray(init)
        for l in open(p("sail.log")):
            m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", l)
            if not m: continue
            a, v = int(m.group(1), 16), m.group(2)
            if a < ins_a: continue
            nb = len(v) // 2
            for j in range(nb):
                assert a + j in allowed, f"unexpected Sail write {l.strip()}"
                smem[a + j - ins_a] = int(v[2 * (nb - 1 - j):2 * (nb - j)], 16)
        for name, mem in (("qemu", qmem), ("sail", smem)):
            for i, xs in enumerate(cases):
                out = chunk[i][1]; sp = space[len(xs)]
                got_in = list(mem[S * i:S * i + S]); got_out = list(mem[S * k + S * i:][:S])
                assert got_in == xs + [0xAA] * (S - len(xs)), (name, "input changed", xs)
                assert got_out[:len(out)] == out, (name, xs, got_out[:len(out) + 2], out)
                assert got_out[sp:] == [0x55] * (S - sp), (name, "write beyond space", xs, sp)
        done += k


    print(f"{which}: {N} inputs, Lean(book) == RV64 QEMU == RV64 Sail ({len(words)} words)", flush=True)
