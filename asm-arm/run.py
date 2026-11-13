#!/usr/bin/env python3
"""Run sort.elf on qemu-system-aarch64 (virt, cortex-a72); check output == sorted(input); report time.
usage: run.py N [seed]"""
import os, random, re, subprocess, sys, time
N = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
D = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(D, "work"); os.makedirs(W, exist_ok=True)
IN, OUT = 0x40300000, 0x48000000
data = bytes(random.Random(seed).randrange(256) for _ in range(N)); want = bytes(sorted(data))
open(f"{W}/in.bin", "wb").write(N.to_bytes(8, "little") + data)
halt = int(re.search(r"(\w+) t halt", subprocess.check_output(f"aarch64-linux-gnu-nm {D}/sort.elf", shell=True, text=True)).group(1), 16)
q = subprocess.Popen(f"qemu-system-aarch64 -machine virt -cpu cortex-a72 -m 1G -display none -serial none -monitor stdio "
                     f"-device loader,file={D}/sort.elf,cpu-num=0 -device loader,file={W}/in.bin,addr={IN-8:#x},force-raw=on",
                     shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
t0 = time.time()
def hmp(cmd):
    q.stdin.write(cmd + "\n"); buf = ""
    while not buf.endswith("(qemu) ") or cmd not in buf: buf += q.stdout.read(1)
    return buf
hmp("info version")
while f"PC={halt:016x}" not in hmp("info registers"):
    assert time.time() - t0 < 120, "timeout"; time.sleep(0.005)
secs = time.time() - t0
hmp(f'pmemsave {OUT:#x} {max(N,1)} "{W}/out.bin"'); q.stdin.write("quit\n"); q.wait()
assert open(f"{W}/out.bin", "rb").read()[:N] == want, "QEMU output != sorted input"
print(f"N={N} seed={seed}: aarch64 QEMU output == sorted(input), {secs:.3f}s wall incl. startup")
