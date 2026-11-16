#!/usr/bin/env python3
"""FULL-CHAIN test, mirroring Nano/Chain.lean (`nano_chain`, `nano_chain_int`) stage by stage, for UInt64 and Int64 sources
(corpus + random + adversarial edge cases, accepted and rejected):
 L  Lean's REAL elaborator: every source as its own root-level file + `#eval` of the entry on the inputs (plain `lean`).
 E  `nanoElabT` (the spec, run in Lean; no compiled binary of it exists yet): accept => Lean accepts, same type, same
    values (exact-subset rule).
 P  proved route `nanoCompile` (code computed in Lean: no compiled binary of `Ir.compileW` exists): the code on QEMU and
    on Sail in the real `StartCorrect` convention, at `memoryNeeded` (output == Lean's real value) and at
    `memoryNeeded - 1` (OOM flag), writes only in output + work (Testing/asm/ir_test.py).
 S  stack route `nanoCompileS = asm ∘ genR`, its largest self-hosted prefix: `genR` in Lean, then `asm` as OUR compiler's
    RISC-V binary (`Nano.Self.nanoAsm`, machine theorem `implements1`) on QEMU and Sail (frontx_test: == Lean `asm`),
    its output code (taken from the QEMU run) run on qemu-riscv64 and on Sail (nano convention) == Lean's real value.
usage: chain_test.py [R random programs per type] [seed]"""
import os, random, re, shutil, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(D, "..", "..")); A = os.path.join(ROOT, "Testing", "asm")
sys.path.insert(0, D)
from nanolib import *
R = int(sys.argv[1]) if len(sys.argv) > 1 else 8
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 4)
W = os.path.join(D, "work", "chain"); shutil.rmtree(W, ignore_errors=True); os.makedirs(W)
SAIL = "/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim"
lean_env = f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH"
EDGE_SRC = [  # adversarial (owner list): accepted or rejected, judged on both sides
    "def f (x : Int64) : Int64 := -5", "def f (x : Int64) : Int64 := (-5)",
    "def g (x : Int64) : Int64 := x\ndef f (x : Int64) : Int64 := g -5", "def f (x : Int64) : Int64 := - -5",
    "def f (x y : Int64) : Int64 := x - -y", "def f (x : Int64) : Int64 := 9223372036854775808 + x",
    "def f (x : Int64) : Int64 := 18446744073709551621 * x", "def f (x : Int64) : Int64 := 0 - -9223372036854775808",
    "def f (x : Int64) : Int64 := -9223372036854775808 * -1", "def f (x : Int64) : UInt64 := x",
    "def f (x : UInt64) (y : Int64) : Int64 := y", "def f (x : UInt64) : UInt64 := x * -1",
    "def f (x : UInt64) : UInt64 := g 0x10", "def id (x : UInt64) : UInt64 := x", "def f (x : UInt64) : UInt64 :=\tx",
    "def g (a b : Int64) : Int64 := a - b\ndef f (x y : Int64) : Int64 := g (x)y",
    "def k : Int64 := -1\ndef f (x : Int64) : Int64 := k -1", "def f (x : Int64) : Int64 := x --5",
]
gu, gi = GI(rng, "UInt64"), GI(rng, "Int64")
srcs = list(CORPUS) + list(INT_CORPUS) + EDGE_SRC + [gu.program() for _ in range(R)] + [gi.program() for _ in range(R)]
def entry(s):
    ds = re.findall(r"^def\s+(\w+)((?:\s*\([^)]*\))*)\s*:", s, re.M)
    if not ds: return None, 0
    name, ps = ds[-1]; return name, sum(len(g.split(":")[0].split()) for g in re.findall(r"\(([^)]*)\)", ps))
progs = []
for s in srcs:
    name, k = entry(s); st = bool(re.search(r"\bInt64\b", s)) and not re.search(r"\bUInt64\b", s)
    progs.append((s, name, k, st, inputs_i(rng, k, 4) if st else inputs(rng, k, 4)))
# ---- L: Lean's real elaborator
def lean_run(i):
    s, name, k, st, ins = progs[i]; T = "Int64" if st else "UInt64"
    ev = "".join(f"\n#eval ({name} " + " ".join(f"({x} : {T})" for x in a) + ")" for a in ins) if name else ""
    open(f"{W}/l{i}.lean", "wb").write(s.encode() + ev.encode() + b"\n")
    r = subprocess.run(f"PATH=$HOME/.elan/bin:$PATH lean {W}/l{i}.lean", shell=True, capture_output=True, text=True, cwd=W)
    outs = [int(l) % M for l in r.stdout.split("\n") if re.fullmatch(r"-?\d+", l.strip())]
    return r.returncode == 0 and len(outs) == len(ins), outs
with ThreadPoolExecutor(4) as ex: L = list(ex.map(lean_run, range(len(progs))))
# ---- E: nanoElabT
lst = []
for i, (s, name, k, st, ins) in enumerate(progs):
    open(f"{W}/p{i:03}.nano", "wb").write(s.encode())
    for a in ins: lst.append(f"{W}/p{i:03}.nano " + " ".join(str(x % M) for x in a))
open(f"{W}/list.txt", "w").write("\n".join(lst) + "\n")
J = subprocess.run(f"{lean_env} lake env lean --run Testing/nano/judge.lean {W}/list.txt", shell=True, check=True,
                   capture_output=True, text=True).stdout.split("\n")
acc, pos, bad = [], 0, []
for i, (s, name, k, st, ins) in enumerate(progs):
    nv = J[pos:pos + len(ins)]; pos += len(ins)
    if nv[0] == "NONE": continue
    if not L[i][0]: bad.append(("E: nano accepts, Lean rejects", s)); continue
    if any(v.split()[0] != ("I" if st else "U") for v in nv): bad.append(("E: type", s)); continue
    if [int(v.split()[1]) for v in nv] != L[i][1]: bad.append(("E: meaning", s, nv, L[i][1])); continue
    acc.append(i)
nL = sum(ok for ok, _ in L)
print(f"L: {len(progs)} sources, Lean accepts {nL}; E: nanoElab accepts {len(acc)}, all == Lean (type, {sum(len(progs[i][4]) for i in acc)} values); "
      f"nano rejects / Lean accepts {nL - len(acc)}; mismatches {len(bad)}")
for b in bad: print("FAIL", b)
assert not bad
# ---- P: proved route on QEMU + Sail (StartCorrect convention), expected = Lean's real values
lit = lambda s: '"' + s.replace("\\", "\\\\").replace("\n", "\\n").replace("\t", "\\t").replace("\r", "\\r") + '"'
E = ["import Nano.ProofTop", "import Nano.Elab", "import Nano.Gen", "open Proven (leN)", "open Proven.Ir Proven.Top.Alloc Nano",
     "def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then \"0\" ++ s else s",
     "def hx (xs : List UInt8) : String := if xs.isEmpty then \"-\" else String.join (xs.map hex2)",
     "def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); \"\".pushn '0' (8 - s.length) ++ s",
     "def mainSlots (Q : Proven.Ir.Prog Nat) : Nat := ((Q.funcs[Q.main]?).map (·.slots)).getD 0",
     "def peakF (E : List MemEvent) : Nat :=",
     "  (E.reverse.foldl (fun (c, m) e => match e with",
     "    | .alloc n => (c + n, max m (c + n)) | .free n => (c - n, max m (c - n))) (0, 0)).2",
     "def emitC (name src : String) (cases : List (List Nat × Nat)) : IO Unit := do",
     "  let some p := nanoElab src.toUTF8.toList | throw (IO.userError s!\"{name}: rejected\")",
     "  let some (ws, Q) := compileW (lower p) | throw (IO.userError s!\"{name}: compile failed\")",
     "  unless Proven.Top.wordBytes ws == nanoGen p do throw (IO.userError s!\"{name}: words != nanoGen\")",
     "  IO.FS.writeFile s!\"Testing/asm/ir-words/{name}.words\" (String.intercalate \"\\n\" (s!\"{name} 0\" :: ws.map hex8) ++ \"\\n\")",
     "  let mut s := \"\"",
     "  for (args, want) in cases do",
     "    let x := (args.map fun a => leN 8 a).flatten",
     "    let y := leN 8 want",
     "    let some (o, ev) := interp Q 100000000 x | throw (IO.userError s!\"{name}: interp\")",
     "    unless nanoRun p x == some y && o == y do throw (IO.userError s!\"{name}: nanoRun/interp != Lean's value\")",
     "    s := s ++ s!\"{hx x} {hx y} {8 * peakF (ev ++ [.alloc (mainSlots Q + 3)])}\\n\"",
     "  IO.FS.writeFile s!\"Testing/asm/ir-words/{name}.cases\" s",
     "#eval show IO Unit from do"]
for i in acc:
    s, name, k, st, ins = progs[i]
    E.append(f"  emitC \"chain_{i:03}\" {lit(s)} {[([x % M for x in a], v) for a, v in zip(ins, L[i][1])]}")
src = "\n".join(E) + "\n"
open(f"{W}/emit_chain.lean", "w").write(src)
os.makedirs(f"{A}/ir-words", exist_ok=True)
subprocess.run(f"{lean_env} lake env lean {W}/emit_chain.lean", shell=True, check=True)
nP = 0
try:
    for i in acc:
        subprocess.run(f"{lean_env} python3 Testing/asm/ir_test.py check {len(progs[i][4])} chain_{i:03} > /dev/null", shell=True, check=True)
        nP += len(progs[i][4])
finally:
    shutil.rmtree(f"{A}/ctest", ignore_errors=True)
    for f in os.listdir(f"{A}/ir-words"):
        if f.startswith("chain_"): os.remove(f"{A}/ir-words/{f}")
print(f"P (proved nanoCompile, code from Lean): {len(acc)} programs, {nP} (program, input) pairs on QEMU and Sail == Lean's real "
      f"elaborator at memoryNeeded; OOM flag at memoryNeeded - 1; writes only in output + work")
# ---- S: stack route, `asm` stage as our compiler's binary
S = os.path.join(W, "sel"); os.makedirs(S)
for i in acc: shutil.copy(f"{W}/p{i:03}.nano", f"{S}/p{i:03}.nano")
bak = {f: open(f"{A}/frontx-words/{f}", "rb").read() for f in ("nanoasm.cases", "nanoasm.words")}
try:
    subprocess.run(f"{lean_env} NANO_DIR={S} lake env lean --tstack=400000 Testing/nano/emit_nano.lean > /dev/null", shell=True, check=True)
    cwd = os.getcwd(); os.chdir(A); sys.path.insert(0, A)
    sys.argv = ["frontx_test.py", "-", "0", "nanoasm"]
    import frontx_test as F
    F.LISTS.add("nanoasm")
    F.check(len(F.CASES))  # the binary on QEMU and Sail == Lean `asm`
    rows = [l.split() for l in open(f"{S}/index.txt")]
    unhex = lambda h: b"" if h == "-" else bytes.fromhex(h)
    cases = [(list(unhex(r[1])), [0] * (len(unhex(r[1])) + 8)) for r in rows]
    lay, halt, base, tab, size = F.build(cases, "".join(f"  .word 0x{w:08x}\n" for w in F.words))
    mem = F.qemu(halt, base, tab + F.E * len(cases) - base)
    os.chdir(cwd)
finally:
    for f, b in bak.items(): open(f"{A}/frontx-words/{f}", "wb").write(b)
    shutil.rmtree(f"{A}/ctest", ignore_errors=True)
subprocess.run(f"riscv64-linux-gnu-gcc -O1 -static -march=rv64g -mabi=lp64d {D}/driver.c -o {W}/driver", shell=True, check=True)
runs = []  # (code, args, want)
for c, (r, (i0, o0, w0)) in enumerate(zip(rows, lay)):
    a1 = int.from_bytes(mem[tab - base + F.E * c + 64:][:8], "little")
    code = bytes(mem[o0:o0 + a1]); assert code == unhex(r[2]), ("binary asm != Lean nanoGenS", r[0])
    i = int(re.search(r"p(\d+)\.nano", r[0]).group(1))
    for a, v in zip(progs[i][4], L[i][1]): runs.append((code, [x % M for x in a], v))
for code, args, want in runs:
    open(f"{W}/code.bin", "wb").write(code); open(f"{W}/args.bin", "wb").write(b"".join(a.to_bytes(8, "little") for a in args) or b"\0")
    got = int.from_bytes(subprocess.run(f"qemu-riscv64 {W}/driver {W}/code.bin {W}/args.bin", shell=True, check=True, capture_output=True).stdout, "little")
    assert got == want, ("S QEMU", args, got, want)
# Sail: one bare-metal ELF, per run: code | args | out word | stack
LD = "ENTRY(_start)\nSECTIONS { . = 0x80000000; .text : { *(.text.start) *(.text) }\n . = 0x80100000; .tohost : { *(.tohost) }\n . = 0x80200000; .data : { *(.data) } }\n"
data = b""; tabl = []; ST = 8192; outs = []
for code, args, want in runs:
    o = len(data); code = code + b"\0" * (-len(code) % 8); a0 = o + len(code); out = a0 + 8 * len(args); stk = out + 8
    tabl.append(f"  .quad base+{o}, base+{a0}, base+{out}, base+{stk + ST}, 0, 0"); outs.append((out, stk))
    data += code + b"".join(a.to_bytes(8, "little") for a in args) + b"\x55" * 8 + b"\0" * ST
open(f"{W}/s.bin", "wb").write(data)
open(f"{W}/s.S", "w").write(f""".section .text.start
.globl _start
_start: lla s0, tab
  li s2, {len(runs)}
1: ld t3, 0(s0)
  ld a0, 8(s0)
  ld a1, 16(s0)
  ld sp, 24(s0)
  jalr ra, t3, 0
  sd sp, 32(s0)
  addi s0, s0, 48
  addi s2, s2, -1
  bnez s2, 1b
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
.section .tohost,"aw"
.globl tohost
.align 6
tohost: .dword 0
.data
.align 4
base:
.incbin "{W}/s.bin"
.align 3
tab:
""" + "\n".join(tabl) + "\n"); open(f"{W}/m.ld", "w").write(LD)
subprocess.run(f"riscv64-linux-gnu-gcc -march=rv64im_zicsr -mabi=lp64 -nostdlib -static -Wl,-T,{W}/m.ld -Wl,--no-relax -Wl,--build-id=none {W}/s.S -o {W}/s.elf", shell=True, check=True)
syms = subprocess.check_output(f"riscv64-linux-gnu-nm {W}/s.elf", shell=True, text=True)
sym = lambda x: int(re.search(rf"(\w+) \w {x}\n", syms).group(1), 16)
sbase, stab = sym("base"), sym("tab")
subprocess.run(f"set -o pipefail; {SAIL} --inst-limit 2000000000 --trace-mem --trace-output /dev/stdout {W}/s.elf 2>&1 | grep -E 'mem\\[W|SUCCESS|FAIL|limit' > {W}/sail.log", shell=True, executable="/bin/bash")
log = open(f"{W}/sail.log").read(); assert "SUCCESS" in log, log[-300:]
smem = {}
for l in log.splitlines():
    m = re.match(r"mem\[(?:W,)?0x([0-9A-F]+)\] <- 0x([0-9A-F]+)", l)
    if m:
        a, v = int(m.group(1), 16), m.group(2)
        for j in range(len(v) // 2): smem[a + j] = int(v[2 * (len(v) // 2 - 1 - j):2 * (len(v) // 2 - j)], 16)
for c, ((code, args, want), (out, stk)) in enumerate(zip(runs, outs)):
    got = int.from_bytes(bytes(smem[sbase + out + j] for j in range(8)), "little"); assert got == want, ("S Sail", args, got, want)
    sp = int.from_bytes(bytes(smem[stab + 48 * c + 32 + j] for j in range(8)), "little"); assert sp == sbase + stk + ST, ("S Sail sp", sp)
print(f"S (genR in Lean, asm = our compiler's binary on QEMU + Sail == Lean asm): {len(rows)} programs, code == Lean nanoGenS; "
      f"{len(runs)} (program, input) pairs on qemu-riscv64 and on Sail == Lean's real elaborator")
