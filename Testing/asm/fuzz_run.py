#!/usr/bin/env python3
"""Generic differential runner for compiled byte-block / variable programs on QEMU and the Sail C emulator.
usage: fuzz_run.py CASES.txt [JOBS]   (JOBS parallel processes, programs round-robin)   exit 1 on any mismatch (prints it)
Case file: `prog NAME` starts a program; then `kind blk|var8`, `words HEX...`, kind params, and one `in ...` line per input.
 kind blk  (pipes, sorts): a0=&in a1=len a2=<scr|n|junk> a3=&out, sp/gp set (gp magic restored), params `a2 scr|n|junk`, `frame 0|64`
   `in i=HEX e=HEX sp=SPACE ss=SCRSPACE mis=K`: out[0:len e] == e, out[SPACE:] and scratch[SSPACE:] untouched, input unchanged,
   stack untouched outside the 64-byte frame window below sp (frame 64), sp/gp restored; Sail: every write inside those windows.
 kind var8 (loops, array statements): a0..a7 = vars, block b base in var bv[b]; `bv I J K`; `rw 0 1 1` writable flags per block
   `in v=V0,..,V7 b=HEX:HEX:.. ev=E0,..,E7 eb=HEX:HEX:..`: '?' = unchecked var (base vars are never checked); finals: vars, blocks;
   guard bytes after each block untouched; read-only blocks unchanged; Sail: every write inside writable blocks.
Count of checked inputs is printed as `OK <inputs> inputs <programs> programs`."""
import os, re, subprocess, sys, tempfile, time
D = os.path.dirname(os.path.abspath(__file__))
SAIL = os.environ.get("SAIL", "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim")
BASE = 0x80200000; G = 16; ST = 512; MAGIC = 0x0123456789ABCDEF
sh = lambda c: subprocess.run(c, shell=True, check=True, capture_output=True, text=True)
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n"
DRIVER = """.section .text.start
.globl _start
_start: lla s0, tab
  li s2, %d
1: ld a0, 0(s0)
  ld a1, 8(s0)
  ld a2, 16(s0)
  ld a3, 24(s0)
  ld a4, 32(s0)
  ld a5, 40(s0)
  ld a6, 48(s0)
  ld a7, 56(s0)
  ld sp, 64(s0)
  ld gp, 72(s0)
  jal ra, func
  sd a0, 80(s0)
  sd a1, 88(s0)
  sd a2, 96(s0)
  sd a3, 104(s0)
  sd a4, 112(s0)
  sd a5, 120(s0)
  sd a6, 128(s0)
  sd a7, 136(s0)
  sd sp, 144(s0)
  sd gp, 152(s0)
  addi s0, s0, 160
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
.align 4
"""
E = 160

def parse(path):
    progs = []; cur = None
    for l in open(path):
        k, _, r = l.strip().partition(" ")
        if not k or k.startswith("#"): continue
        if k == "prog": cur = {"name": r, "kind": "blk", "ins": [], "a2": "scr", "frame": 0, "bv": [], "rw": []}; progs.append(cur)
        elif k == "words": cur["words"] = [int(x, 16) for x in r.split()]
        elif k in ("kind", "a2"): cur[k] = r
        elif k == "frame": cur["frame"] = int(r)
        elif k in ("bv", "rw"): cur[k] = [int(x) for x in r.split()]
        elif k == "in": cur["ins"].append(dict(t.split("=", 1) for t in r.split()))
        else: raise ValueError(l)
    return progs
hx = lambda s: b"" if s in ("-", "") else bytes.fromhex(s)

def build(pg, d):
    blob = bytearray(); lay = []
    def alloc(b):
        while len(blob) % 16: blob.append(0)
        o = len(blob); blob.extend(b); return o
    tab = []   # per input: dict(regs init, sp, expectations)
    for t in pg["ins"]:
        e = {"t": t}
        if pg["kind"] == "blk":
            xs = hx(t["i"]); L = len(xs); exp = hx(t["e"]); sp = int(t["sp"]); ss = int(t["ss"]); mis = int(t.get("mis", 0))
            i0 = alloc(xs + b"\xAA" * G); s0 = alloc(b"\x33" * L + b"\xAA" * G); ocap = max(sp, len(exp)) + 16; o0 = alloc(b"\x55" * ocap + b"\xAA" * G)
            k0 = alloc(b"\x77" * ST); spv = BASE + k0 + ST - 8 - mis
            a2 = {"scr": BASE + s0, "n": L, "junk": 0xDEADBEEF}[pg["a2"]]
            e.update(i0=i0, s0=s0, o0=o0, k0=k0, L=L, exp=exp, ocap=ocap, ss=ss, sp=spv, regs=[BASE + i0, L, a2, BASE + o0, 0, 0, 0, 0])
        else:
            bs = [hx(x) for x in t["b"].split(":")] if "b" in t else []
            v = [int(x) if x != "?" else 0x1111111111111111 for x in t["v"].split(",")]
            offs = [alloc(b + b"\xAA" * G) for b in bs]; k0 = alloc(b"\x77" * ST)
            for b, (bi, o) in enumerate(zip(pg["bv"], offs)): v[bi] = BASE + o
            e.update(offs=offs, bs=bs, k0=k0, sp=BASE + k0 + ST - 8, regs=v)
        tab.append(e)
    while len(blob) % 16: blob.append(0)
    tb = len(blob)
    for e in tab: blob.extend(b"".join(x.to_bytes(8, "little") for x in e["regs"] + [e["sp"], MAGIC] + [0] * 10))
    open(f"{d}/data.bin", "wb").write(blob)
    src = DRIVER % (len(tab), "".join(f"  .word 0x{w:08x}\n" for w in pg["words"])) + f'.incbin "{d}/data.bin"\n.globl tab\n.set tab, {BASE + tb}\n'
    open(f"{d}/p.S", "w").write(src); open(f"{d}/p.ld", "w").write(LD)
    sh(f"riscv64-linux-gnu-gcc -march=rv64i_zicsr -mabi=lp64 -nostdlib -static -Wl,-T,{d}/p.ld -Wl,--no-relax -Wl,--build-id=none {d}/p.S -o {d}/p.elf")
    syms = sh(f"riscv64-linux-gnu-nm {d}/p.elf").stdout
    halt = int(re.search(r"(\w+) \w halt\n", syms).group(1), 16)
    return tab, bytes(blob), tb, halt

def qemu(d, halt, size):
    q = subprocess.Popen(f"qemu-system-riscv64 -machine virt -m 1G -bios {d}/p.elf -display none -serial none -monitor stdio",
                         shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); buf = ""
        while not buf.endswith("(qemu) ") or c not in buf: buf += q.stdout.read(1)
        return buf
    hmp("info version"); t0 = time.time()
    while "pc       %016x" % halt not in hmp("info registers"):
        assert time.time() - t0 < float(os.environ.get("FUZZ_TMO", "600")), "QEMU did not reach halt (program hangs or crashes)"; time.sleep(0.01)
    hmp(f'pmemsave {BASE:#x} {size} "{d}/q.bin"'); q.stdin.write("quit\n"); q.wait()
    return bytearray(open(f"{d}/q.bin", "rb").read())

def sail(d, init, size):
    r = subprocess.run(f"{SAIL} --inst-limit 4000000000 --trace-mem --trace-output {d}/sail.log {d}/p.elf", shell=True, capture_output=True, text=True)
    assert "SUCCESS" in r.stdout + r.stderr, (r.stdout + r.stderr)[-300:]
    mem = bytearray(init); writes = []
    for l in open(f"{d}/sail.log"):
        m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", l)
        if not m: continue
        a, v = int(m.group(1), 16), m.group(2)
        if a < BASE or a >= BASE + size: continue      # tohost etc.
        nb = len(v) // 2
        for j in range(nb):
            mem[a + j - BASE] = int(v[2 * (nb - 1 - j):2 * (nb - j)], 16); writes.append(a + j - BASE)
    return mem, writes

def check(pg, tab, tb, init, mem, writes, who):
    errs = []
    def err(i, msg): errs.append(f"{pg['name']} input {i} [{who}]: {msg}")
    allowed = None
    if who == "sail":
        allowed = set(range(tb, tb + E * len(tab)))
    for i, e in enumerate(tab):
        te = tb + E * i; res = [int.from_bytes(mem[te + 80 + 8 * j:te + 88 + 8 * j], "little") for j in range(10)]
        if pg["kind"] == "blk":
            L, o0, ocap, exp, sp = e["L"], e["o0"], e["ocap"], e["exp"], int(e["t"]["sp"])
            if mem[o0:o0 + len(exp)] != exp: err(i, f"output {bytes(mem[o0:o0 + len(exp)]).hex()} != expected {exp.hex()} (input {e['t']['i']})")
            if mem[o0 + sp:o0 + ocap] != init[o0 + sp:o0 + ocap]: err(i, "output bytes beyond space modified")
            if mem[o0 + ocap:o0 + ocap + G] != b"\xAA" * G: err(i, "output guard modified")
            if mem[e["i0"]:e["i0"] + L + G] != init[e["i0"]:e["i0"] + L + G]: err(i, "input block modified")
            ss = e["ss"]
            if mem[e["s0"] + ss:e["s0"] + L + G] != init[e["s0"] + ss:e["s0"] + L + G]: err(i, "scratch beyond sspace / guard modified")
            fp = e["sp"] // 8 * 8 - pg["frame"]
            ok = lambda j: pg["frame"] and fp - BASE <= e["k0"] + j < fp - BASE + pg["frame"]
            if any(mem[e["k0"] + j] != 0x77 for j in range(ST) if not ok(j)): err(i, "stack modified outside frame")
            if res[8] != e["sp"] or res[9] != MAGIC: err(i, f"sp/gp not restored {res[8]:#x} {res[9]:#x}")
            if allowed is not None:
                allowed |= set(range(o0, o0 + sp)) | set(range(e["s0"], e["s0"] + ss))
                if pg["frame"]: allowed |= set(range(fp - BASE, fp - BASE + pg["frame"]))
        else:
            t = e["t"]; ev = t.get("ev", "").split(","); eb = [hx(x) for x in t["eb"].split(":")] if "eb" in t else []
            for j, x in enumerate(ev):
                if x != "?" and j not in pg["bv"] and res[j] != int(x): err(i, f"a{j} = {res[j]} != expected {int(x)} (init vars {t['v']})")
            for b, (o, ib) in enumerate(zip(e["offs"], e["bs"])):
                n = len(ib)
                if b < len(eb) and mem[o:o + n] != eb[b]: err(i, f"block {b} = {bytes(mem[o:o + n]).hex()} != expected {eb[b].hex()}")
                if mem[o + n:o + n + G] != b"\xAA" * G: err(i, f"guard after block {b} modified")
                if not pg["rw"][b] and mem[o:o + n] != ib: err(i, f"read-only block {b} modified")
                if allowed is not None and pg["rw"][b]: allowed |= set(range(o, o + n))
            if any(mem[e["k0"] + j] != 0x77 for j in range(ST)): err(i, "stack modified")
            if res[8] != e["sp"] or res[9] != MAGIC: err(i, "sp/gp not restored")
    if allowed is not None:
        bad = [w for w in writes if w not in allowed]
        if bad: errs.append(f"{pg['name']} [sail]: write outside allowed regions at {BASE + bad[0]:#x} ({len(bad)} bytes)")
    return errs

def run_progs(progs):
    errs = []; n = 0
    for pg in progs:
        with tempfile.TemporaryDirectory() as d:
            tab, init, tb, halt = build(pg, d)
            size = tb + E * len(tab)
            q = qemu(d, halt, size); s, w = sail(d, init, size)
            errs += check(pg, tab, tb, init, q, [], "qemu") + check(pg, tab, tb, init, s, w, "sail")
            n += len(tab)
    return n, errs

if __name__ == "__main__":
    progs = parse(sys.argv[1]); J = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    if J == 1: n, errs = run_progs(progs)
    else:
        from concurrent.futures import ProcessPoolExecutor
        parts = [progs[i::J] for i in range(J)]
        with ProcessPoolExecutor(J) as ex: rs = list(ex.map(run_progs, parts))
        n = sum(r[0] for r in rs); errs = [e for r in rs for e in r[1]]
    for e in errs[:20]: print("MISMATCH", e)
    print(("FAIL" if errs else "OK"), n, "inputs", len(progs), "programs", len(errs), "errors")
    sys.exit(1 if errs else 0)
