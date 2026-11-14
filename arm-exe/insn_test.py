#!/usr/bin/env python3
"""Instruction-level differential test: ONE instruction from a random register/flag/memory state,
AArch64 QEMU (system mode, virt, cortex-a72, EL1) vs the runnable Lean ARM model (`armrun step`, one `step_model`).
Compared: x0..x30, NZCV, PC (via a taken/not-taken marker on QEMU), and a 64-byte memory buffer.
usage: insn_test.py ARMRUN WORKDIR [N per form=1000] [SEED=1] [form ...]"""
import os, random, re, subprocess, sys, time
armrun, W = sys.argv[1:3]; N = int(sys.argv[3]) if len(sys.argv) > 3 else 1000; SEED = int(sys.argv[4]) if len(sys.argv) > 4 else 1
os.makedirs(W, exist_ok=True); p = lambda f: os.path.join(W, f)
M64 = 2**64 - 1
EDGE = [0, 1, 2, 3, 2**63, 2**63 - 1, M64, M64 - 1, 2**32, 2**32 - 1, 0xFF, 0xFFF, 0x800, 0x7FF, 2**63 + 1, 63, 64, 65, 127, 128, 31, 32, 2**31, 2**31 - 1]
TEXT, DATA, BUFS = 0x40200000, 0x42000000, 0x44000000   # code, in/out tables, memory buffers
INSZ, OUTSZ, BUFSZ = 256, 272, 64

def val(r): return r.choice(EDGE) if r.randrange(3) == 0 else r.getrandbits(64)
def reg(r): return r.randrange(32)          # 31 = xzr in the forms that use this
def reg31(r): return r.randrange(31)        # forms where 31 would mean sp, or must hold an address
# Each form: f(r) -> (word, fix) ; fix(regs, A, buf) may overwrite register values (branch targets, base addresses)
def dp(base, shifts):
    return lambda r: (base | r.randrange(shifts) << 22 | reg(r) << 16 | r.choice([0, 0, r.randrange(64)]) << 10 | reg(r) << 5 | reg(r), None)
def shv(op): return lambda r: (0x9ac02000 | op << 10 | reg(r) << 16 | reg(r) << 5 | reg(r), None)
def imm(base, rd): return lambda r: (base | r.randrange(2) << 22 | r.choice([0, 1, 0xfff, r.randrange(4096)]) << 10 | reg31(r) << 5 | rd(r), None)
def csel(base, conds): return lambda r: (base | reg(r) << 16 | r.choice(conds) << 12 | reg(r) << 5 | reg(r), None)
def cset(conds): return lambda r: (0x9a9f07e0 | (r.choice(conds) ^ 1) << 12 | reg(r), None)
def mov(base): return lambda r: (base | r.randrange(4) << 21 | r.choice([0, 1, 0xffff, r.getrandbits(16)]) << 5 | reg(r), None)
def bfm(base, f): return lambda r: (base | (lambda s: f(s, r))(r.randrange(64)) | reg(r) << 5 | reg(r), None)
def cb(base):
    def f(r):
        rt = reg(r); z = r.randrange(2)
        return base | 2 << 5 | rt, (lambda x, A, buf: x.__setitem__(rt, 0) if z and rt < 31 else None)
    return f
def ret(r):
    rn = reg31(r); return 0xd65f0000 | rn << 5, lambda x, A, buf: x.__setitem__(rn, A + 8)
def mem(base, scale, size, unaligned=False):
    def f(r):
        rn, rt = reg31(r), reg(r); i = r.choice([0, 0, r.randrange((BUFSZ - size) // scale + 1)]); off = r.randrange(BUFSZ - size - i * scale + 1)
        if scale > 1: off = (off & ~7) + (1 + r.randrange(7) if unaligned else 0); off -= 8 * (off + i * scale + size > BUFSZ)
        return base | i << 10 | rn << 5 | rt, lambda x, A, buf: x.__setitem__(rn, buf + off)
    return f
ALL = list(range(16)); C = {"eq": 0, "ne": 1, "hs": 2, "lo": 3, "ge": 10, "lt": 11}
FORMS = {
  "add_shifted": dp(0x8b000000, 3), "sub_shifted": dp(0xcb000000, 3), "and_shifted": dp(0x8a000000, 4),
  "orr_shifted": dp(0xaa000000, 4), "eor_shifted": dp(0xca000000, 4), "subs_shifted": dp(0xeb000000, 3),
  "cmp_shifted": lambda r: (dp(0xeb000000, 3)(r)[0] | 31, None),
  "mov_orr_xzr": lambda r: (0xaa0003e0 | reg(r) << 16 | reg(r), None),
  "lslv": shv(0), "lsrv": shv(1), "asrv": shv(2),
  "cmp_imm": imm(0xf1000000, lambda r: 31), "subs_imm": imm(0xf1000000, reg), "add_imm": imm(0x91000000, reg31), "sub_imm": imm(0xd1000000, reg31),
  "csinc_lo_lt_eq": csel(0x9a800400, [3, 11, 0]), "cset_lo_lt_eq": cset([3, 11, 0]), "csel_ne": csel(0x9a800000, [1]),
  "csel_allcond": csel(0x9a800000, ALL), "csinc_allcond": csel(0x9a800400, ALL),
  "movz": mov(0xd2800000), "movk": mov(0xf2800000), "movn": mov(0x92800000),
  "ret": ret, "b": lambda r: (0x14000002, None), "cbz": cb(0xb4000000), "cbnz": cb(0xb5000000),
  **{f"b.{n}": (lambda c: lambda r: (0x54000040 | c, None))(c) for n, c in C.items()},
  "b.cond_all": lambda r: (0x54000040 | r.randrange(16), None),
  "ldr_x": mem(0xf9400000, 8, 8), "str_x": mem(0xf9000000, 8, 8), "ldrb": mem(0x39400000, 1, 1),
  # MMU is off: the model treats data memory as Device and raises an Alignment fault on unaligned access; QEMU performs the access.
  # For these two forms the check is: the model takes the fault (PC = 0x200, registers and memory unchanged). QEMU is not compared.
  "ldr_x_unaligned": mem(0xf9400000, 8, 8, True), "str_x_unaligned": mem(0xf9000000, 8, 8, True), "strb": mem(0x39000000, 1, 1),
  "lsl_imm": bfm(0xd3400000, lambda s, r: ((64 - s) % 64) << 16 | (63 - s) << 10), "lsr_imm": bfm(0xd3400000, lambda s, r: s << 16 | 63 << 10),
  "asr_imm": bfm(0x93400000, lambda s, r: s << 16 | 63 << 10),
  "ubfm_any": bfm(0xd3400000, lambda s, r: s << 16 | r.randrange(64) << 10), "sbfm_any": bfm(0x93400000, lambda s, r: s << 16 | r.randrange(64) << 10),
  "madd": lambda r: (0x9b000000 | reg(r) << 16 | reg(r) << 10 | reg(r) << 5 | reg(r), None),
  "msub": lambda r: (0x9b008000 | reg(r) << 16 | reg(r) << 10 | reg(r) << 5 | reg(r), None),
}
names = sys.argv[5:] or list(FORMS)
BLOCK = """  ldr x0, =%#x
  mov sp, x0
  ldr x0, [sp, #248]
  msr nzcv, x0
%s  ldr x30, [sp, #240]
t%d: .word %#x
  b 1f
  add sp, sp, #256
  stp x0, x1, [sp]
  mov x0, #1
  b 2f
1: add sp, sp, #256
  stp x0, x1, [sp]
  mov x0, #0
2: str x0, [sp, #256]
%s  str x30, [sp, #240]
  mrs x0, nzcv
  str x0, [sp, #248]
"""
LD = "".join(f"  ldp x{i}, x{i+1}, [sp, #{8*i}]\n" for i in range(0, 30, 2)); ST = "".join(f"  stp x{i}, x{i+1}, [sp, #{8*i}]\n" for i in range(2, 30, 2))
open(p("t.ld"), "w").write(f"ENTRY(_start)\nSECTIONS {{ . = {TEXT:#x}; .text : {{ *(.text.start) *(.text) }} }}\n")
MODE = os.environ.get("MODE", "step"); log = open(p("mismatch.txt"), "w")
q8 = lambda b, i: int.from_bytes(b[8*i:8*i+8], "little")
total = bad = 0
for name in names:
    r = random.Random(f"{SEED}/{name}"); tests = []
    for i in range(N):
        w, fix = FORMS[name](r)
        tests.append((w, fix, [val(r) for _ in range(31)], r.randrange(16), r.getrandbits(8 * BUFSZ).to_bytes(BUFSZ, "little")))
    S = ".section .text.start\n.globl _start\n_start:\n" + "".join(BLOCK % (DATA + i * (INSZ + OUTSZ), LD, i, t[0], ST) + (".ltorg\n" if i % 100 == 99 else "") for i, t in enumerate(tests))
    S = S.replace(".ltorg\n", "  b 9f\n.ltorg\n9:\n") + "halt: b halt\n.ltorg\n"
    open(p("t.S"), "w").write(S)
    subprocess.run(f"aarch64-linux-gnu-gcc -nostdlib -static -Wl,-T,{p('t.ld')} -Wl,--build-id=none {p('t.S')} -o {p('t.elf')} 2>&1 | grep -v RWX; true", shell=True, check=True)
    sym = {m.group(2): int(m.group(1), 16) for m in re.finditer(r"(\w+) \w (\w+)\n", subprocess.check_output(f"aarch64-linux-gnu-nm {p('t.elf')}", shell=True, text=True))}
    data = b""; lines = []
    for i, (w, fix, x, nzcv, mb) in enumerate(tests):
        A, buf = sym[f"t{i}"], BUFS + i * BUFSZ
        if fix: fix(x, A, buf)
        data += b"".join(v.to_bytes(8, "little") for v in x) + (nzcv << 28).to_bytes(8, "little") + bytes(OUTSZ)
        lines.append(" ".join(f"{v:x}" for v in [A, nzcv] + x + [w, buf]) + " " + mb.hex())
    open(p("data.bin"), "wb").write(data); open(p("bufs.bin"), "wb").write(b"".join(t[4] for t in tests)); open(p("in.txt"), "w").write("\n".join(lines) + "\n")
    q = subprocess.Popen(f"qemu-system-aarch64 -machine virt -cpu cortex-a72 -m 1G -display none -serial none -monitor stdio -device loader,file={p('t.elf')},cpu-num=0 "
                         f"-device loader,file={p('data.bin')},addr={DATA:#x},force-raw=on -device loader,file={p('bufs.bin')},addr={BUFS:#x},force-raw=on",
                         shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=0)
    def hmp(c):
        q.stdin.write(c + "\n"); b = ""
        while not b.endswith("(qemu) ") or c not in b: b += q.stdout.read(1)
        return b
    hmp("info version"); t0 = time.time()
    while "PC=%016x" % sym["halt"] not in hmp("info registers"):
        assert time.time() - t0 < 120, f"{name}: QEMU did not reach halt"; time.sleep(0.02)
    hmp(f'pmemsave {DATA:#x} {len(data)} "{p("o.bin")}"'); qd = open(p("o.bin"), "rb").read()
    hmp(f'pmemsave {BUFS:#x} {N * BUFSZ} "{p("b.bin")}"'); qb = open(p("b.bin"), "rb").read(); q.stdin.write("quit\n"); q.wait()
    assert len(qd) == len(data) and len(qb) == N * BUFSZ
    model = subprocess.check_output([armrun, MODE, p("in.txt")], text=True).splitlines(); assert len(model) == N
    b = 0
    for i, (w, fix, x, nzcv, mb) in enumerate(tests):
        o = qd[i * (INSZ + OUTSZ) + INSZ:(i + 1) * (INSZ + OUTSZ)]; A = sym[f"t{i}"]
        assert qd[i * (INSZ + OUTSZ):i * (INSZ + OUTSZ) + INSZ] == data[i * (INSZ + OUTSZ):i * (INSZ + OUTSZ) + INSZ], "input table was overwritten"
        qs = " ".join(f"{v:x}" for v in [A + 4 + 4 * q8(o, 32), q8(o, 31) >> 28] + [q8(o, j) for j in range(31)]) + " " + qb[i * BUFSZ:(i + 1) * BUFSZ].hex()
        assert q8(o, 32) in (0, 1) and q8(o, 31) & ~(15 << 28) == 0
        if name.endswith("_unaligned"): qs = " ".join(["200"] + lines[i].split()[1:33] + [lines[i].split()[35]])
        if qs != model[i]:
            b += 1; log.write(f"MISMATCH {name} word={w:08x} pc={A:x} nzcv={nzcv:x}\n  in    {lines[i]}\n  qemu  {qs}\n  model {model[i]}\n")
    mp = sum(m.split()[0] != f"{sym[f't{i}']+4:x}" and m.split()[0] != f"{sym[f't{i}']+8:x}" for i, m in enumerate(model))
    print(f"{name}: {N} states, mismatches {b}, model PC outside insn+4/+8: {mp}", flush=True); log.flush(); total += N; bad += b
print(f"TOTAL {len(names)} forms, {total} states, mismatches {bad}")
assert bad == 0
