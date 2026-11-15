#!/usr/bin/env python3
"""Bare-metal test of the boot stub (`Riscv/Back/Boot.lean`, words from `Testing/asm/emit_boot.lean`) on
`qemu-system-riscv64 -M virt -bios none` (reset ROM jumps to 0x80000000).
Image: stub at 0x80000000, code at 0x80001000, input length (8 bytes LE) at 0x80100000, input at 0x80200000;
output and work blocks pre-filled with 0x55 (the stub must zero them).  Checked: pc = 0x80000050 (halt),
output = model(input), the rest of the output block zero (the stub zeroed it).
usage: boot_test.py NAME NTESTS   (NAME: revinc5 | inc)"""
import os, random, socket, struct, subprocess, sys, tempfile, time
D = os.path.dirname(os.path.abspath(__file__))
MODEL = {"revinc5": lambda xs: [(x + 1) & 255 for x in xs[:5]][::-1], "inc": lambda xs: [(x + 1) & 255 for x in xs]}
words = lambda n: [int(l, 16) for l in open(os.path.join(D, "boot-words", n + ".words")) if l.strip()]
wb = lambda ws: b"".join(struct.pack("<I", w) for w in ws)
OUT, WORK, TOP = 0x80300000, 0x80400000, 0x81000000

def monitor(sock, cmd):
    sock.sendall((cmd + "\n").encode()); time.sleep(0.3); data = b""
    sock.settimeout(1.0)
    try:
        while True:
            chunk = sock.recv(1 << 20)
            if not chunk: break
            data += chunk
    except socket.timeout: pass
    return data.decode(errors="replace")

def run_qemu(tmp, code, xs):
    files = {"stub.bin": (wb(words("stub")), 0x80000000), "code.bin": (wb(code), 0x80001000),
             "len.bin": (struct.pack("<Q", len(xs)), 0x80100000), "in.bin": (bytes(xs), 0x80200000),
             "junk.bin": (b"\x55" * (TOP - OUT), OUT)}
    args = ["qemu-system-riscv64", "-M", "virt", "-bios", "none", "-m", "128M", "-display", "none",
            "-serial", "none", "-monitor", f"unix:{tmp}/mon,server,nowait"]
    for f, (data, addr) in files.items():
        open(os.path.join(tmp, f), "wb").write(data)
        args += ["-device", f"loader,file={tmp}/{f},addr={addr:#x}"]
    q = subprocess.Popen(args)
    try:
        time.sleep(2.0)
        s = socket.socket(socket.AF_UNIX); s.connect(f"{tmp}/mon"); monitor(s, "")
        monitor(s, "stop")
        regs = monitor(s, "info registers")
        pc = int(regs.split("pc")[1].split()[0], 16)
        monitor(s, f"pmemsave {OUT:#x} {TOP - OUT:#x} \"{tmp}/dump.bin\""); time.sleep(0.5)
        monitor(s, "quit")
    finally:
        q.wait(timeout=10)
    dump = open(f"{tmp}/dump.bin", "rb").read()
    return pc, dump

def main():
    name, n = sys.argv[1], int(sys.argv[2])
    code, model = words(name), MODEL[name]
    rng = random.Random(1)
    with tempfile.TemporaryDirectory() as tmp:
        for t in range(n):
            xs = [rng.randrange(256) for _ in range(rng.randrange(0 if t else 3, 40))] if t else [3, 1, 2]
            want = model(xs)
            pc, dump = run_qemu(tmp, code, xs)
            ok = pc == 0x80000050 and list(dump[:len(want)]) == want and not any(dump[len(want):WORK - OUT])
            print(f"qemu {name} {xs[:8]}{'...' if len(xs) > 8 else ''} -> {list(dump[:len(want)])} pc={pc:#x} "
                  f"{'ok' if ok else 'FAIL'}")
            if not ok: sys.exit(1)
    print(f"ALL {n} OK")

main()
