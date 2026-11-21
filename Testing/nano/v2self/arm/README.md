# rv2arm: run nano programs natively on AArch64 (Apple Silicon) — UNPROVEN GLUE

**Nothing here is proved.** The correctness theorem covers the compiler's RISC-V output on the Sail RISC-V model.
`rv2arm.lean` translates that RISC-V output to AArch64. It is written in **nano**, so B2 compiles it and the result
runs anywhere B2's output runs. If it has a bug, results are wrong and no proof notices. `PROOF_NOTES.md` is the
plan for a proved version (`armTarget`, `Testing/notes/NANO_V2_ARM.md`).

| file | what |
|---|---|
| `rv2arm.lean` | the translator (nano subset, also valid Lean: `cat ../../../../Nano/Main/Prelude.lean rv2arm.lean` + `#eval m …`) |
| `rv2arm.sh` | driver: runs the translator once per chunk of CHUNK_WORDS RV words (see Chunking) and concatenates |
| `rv2arm_rv.bin` | `rv2arm.lean` compiled by B2 (RISC-V) |
| `rv2arm_arm.bin` | `rv2arm_rv.bin` translated by itself (AArch64). It translates itself to itself |
| `B2_arm.bin` | the compiler `../B2.bin` translated (AArch64). It compiles the compiler's source to `B2.bin` |
| `rv2arm.py` | test oracle only (same bytes as the nano translator) |
| `test_arm.sh` | the Linux/qemu test below |
| `synth_rv.py` | a synthetic RV program of rare forms (translator vs oracle) |
| `SHA256SUMS` | of the three binaries |
| `PROOF_NOTES.md` | per-block proof plan, lemma map (AL1–AL6), register-31 gaps |
| `ArmBlock.lean` | DRAFT Lean statement of block correctness (`BlockOK`), no proofs, not in the lake build |
| `gen_check.py`, `check_lean.sh` | Lean check: `ArmBlock.lean` elaborates, and its `blockJ` = the oracle on 13,539 J instructions |

## Use on a Mac (Apple Silicon), from this directory

Quick start (all on ARM; Mac native, Linux via qemu-aarch64):
```
./compile.sh prog.lean > prog.arm          # compile a Lean program to ARM code
./run.sh prog.arm input.txt output.txt     # run it (prog.lean also works: compiles first)
./try_arm.sh                               # self-check + all examples
./cross_check.sh                           # Linux: RISC-V and ARM (QEMU) build each other's compiler; all = self-compile
./try_arm.sh prog.lean input.txt           # compile + run, print the output as hex and as text
```
`output.txt` from `run.sh` is the raw output bytes, so `cat output.txt` shows text output directly; `xxd output.txt`
shows hex, and `xxd -r -p hex.txt > bytes` turns hex back into bytes.

```
cc -O2 ../run/shim/shim_arm.c -o shim_arm
grep -v '^--' prog.lean > prog.src                     # the compiler accepts no comments
./shim_arm B2_arm.bin < prog.src > prog_rv.bin         # compile: source in, RISC-V code out
./rv2arm.sh prog_rv.bin > prog_arm.bin                 # translate (runs ./shim_arm rv2arm_arm.bin)
./shim_arm prog_arm.bin < input > output               # run natively
```

`shim_arm` prints `status S, N output bytes` on stderr (0 ok, 1 ok with empty output, −1 out of work memory,
−2 buffer capacity) and exits 1 on −1/−2. A program the compiler rejects gives 0 bytes of code. `rv2arm.sh` exits 1
if a chunk fails, e.g. when the input is not compiler output.
Not yet run on a real Mac (none here). `shim_arm.c` uses `MAP_JIT` + `pthread_jit_write_protect_np` there. If macOS
refuses the mapping, the binary may need the `com.apple.security.cs.allow-jit` entitlement (`codesign`).

Rebuild the binaries without Python, from the checked-in `B2.bin` alone. The RISC-V code runs on QEMU's RISC-V
model. On Linux (x86-64), with `gcc-riscv64-linux-gnu gcc-aarch64-linux-gnu qemu-user-static`:
```
riscv64-linux-gnu-gcc -O2 -static ../run/shim/shim_rv.c -o shim_rv
aarch64-linux-gnu-gcc -O2 -static ../run/shim/shim_arm.c -o shim_arm      # rv2arm.sh runs it under qemu-aarch64
grep -v '^--' rv2arm.lean > rv2arm.src && qemu-riscv64-static ./shim_rv ../B2.bin < rv2arm.src > rv2arm_rv.bin
RUN="qemu-riscv64-static ./shim_rv rv2arm_rv.bin" ./rv2arm.sh rv2arm_rv.bin > rv2arm_arm.bin   # bootstrap
./rv2arm.sh ../B2.bin > B2_arm.bin                                                      # ARM translator from now on
```
(`qemu-riscv64` where the non-static build is installed.) This reproduces `SHA256SUMS` (checked 2026-11-20).
On a Mac there is no RISC-V machine (qemu-riscv64 user mode is Linux-only). Use the checked-in `rv2arm_arm.bin`.
Or, as a fallback only, bootstrap with the interpreter:
`RUN="./nanorun rv2arm_rv.bin /dev/stdin /dev/stdout"` (`cc -O2 ../run/nanorun.c -o nanorun`).
Default runs need no nanorun: `test_arm.sh` uses qemu-riscv64/qemu-aarch64, and `NANORUN=1` adds nanorun as a
cross-check of every RISC-V run.

## Chunking

A nano `List` holds fewer than 2^19 elements; a larger one stops the program with status −2. The translator emits 16
bytes per RV word, so one call can translate at most 2^19 / 16 = 32,768 words. B2 alone is 84,464 words (1.35 MB of
ARM code). So the input to one call is `[4-byte chunk index c][RV code]`, and the call emits the blocks of RV words
`CHUNK_WORDS·c … CHUNK_WORDS·(c+1) − 1`. `CHUNK_WORDS` is `def z0 : UInt64 := 32000` at the top of `rv2arm.lean`
(32,000 leaves a margin below 32,768); `rv2arm.sh` reads it from there and concatenates the chunks.
Every call validates the WHOLE program first (an invalid program gives the empty output in every call). So the
translation work per call is one full pass plus one chunk, and B2 costs 3 validation passes.
Removing the chunking needs a larger list capacity in C: a compiler change, not done.

## Translation (details and per-block proof notes: `PROOF_NOTES.md`)

Each RV word is decoded back to its J instruction (`Nano/Run/Call.lean`, encoded by
`RvEnc.encJX`) and becomes a fixed block of **4** A64 words, padded with `add x16, x16, #0`. J index pc ↦ A64 byte
offset 16·pc. A first pass validates the whole program; any other word, register or out-of-range branch gives the
empty output.

Registers (RV → A64): x0 → none (read from x17 after `movz x17, #0`), x1 (ra) → x30, x2 (RV sp) → x4, x10..x13 → x0..x3,
x28 → x12, x29 → x13, x30 → x10, x31 → x11, x5..x8, x14, x15 → the same number. Scratch: x16, x17.
Never touched: sp, x18, x19..x29.
Convention (mirrors RV): x0 input, x1 length, x2 work base, x3 output, **x4 = work top** (RV sp), return via x30;
status in x0, length in x1. `../run/shim/shim_arm.c` passes the work top in x4, and also still sets sp to it.
Emitted instructions follow `NANO_V2_ARM.md` §0-min, the set the proof will cover:
* movz/movk, add/sub (imm, reg), subs (Rd = x16), and/orr/eor, lslv/lsrv, madd, b.cond, cbz, b, bl, br, ldr/str
  (unsigned offset), ldrb/strb;
* no register field is ever 31: no xzr, wzr or sp. No ldur/stur. `test_arm.sh` checks this with objdump.

| J | A64 block (then padding) |
|---|---|
| `addi rd rs imm` | `add/sub d, s, #abs`; rs = x0: `movz d, #imm`, or (imm < 0) `movz d, #(65536+imm); movk d, #0xFFFF, lsl 16/32/48` |
| `ld` / `sd` | `ldr`/`str [s, #off]` (off ∈ 8ℕ, < 32768), else `add/sub x16, s, #abs` + `[x16]` |
| `lbu` / `sb` | `ldrb`/`strb [s, #off]` (0 ≤ off < 4096), else via x16 |
| x0 as an operand or stored value | `movz x17, #0` first, then x17 |
| `alu op rd a b` | `add/sub/and/orr/lslv/lsrv/eor d, a, b`; mul = `movz x17, #0; madd d, a, b, x17` |
| `slli/srli rd rs sh` | `movz x16, #sh; lslv/lsrv d, s, x16` |
| `beq a x0` (either side) | `cbz a, 4·o` |
| `beq/bne/bltu/bgeu a b o` | `subs x16, a, b; b.eq/ne/lo/hs 4·o − 1` (− 2 after a `movz x17, #0`) |
| `jal x0 o` / `jal x1 o` | `b 4·o` / `pad; pad; pad; bl 4·o − 3` (x30 = the next block) |
| `jalr x0 r` | `br r` |
| rd = x0 (no-op) | 4 × padding |

## Tests (Linux x86-64, qemu-riscv64 + qemu-aarch64, 2026-11-20): `test_arm.sh`, 74/74 OK (also with `NANORUN=1`)

* Every RISC-V run is on qemu-riscv64 (`shim_rv`), every ARM run on qemu-aarch64 (`shim_arm`). `NANORUN=1`
  also runs each RISC-V program with nanorun and requires the same status and output: all agree.
* B2 compiles `rv2arm.lean`, and the result translates itself (RISC-V, qemu) to give `rv2arm_arm.bin`. Under qemu,
  `rv2arm_arm.bin` translates its own RISC-V code to itself (fixpoint). Both translators equal the Python oracle.
* All 8 examples: compiled by B2, translated by the ARM translator (= oracle), run with a static `shim_arm` under
  qemu on 6 inputs (empty, 1 byte, text, edge bytes, 3000 random bytes, 0x14). Output and status equal the RISC-V run's:
  **48/48**.
* B2 translated by the ARM translator = `B2_arm.bin`. ARM-B2 on `../self_S_input.txt` = `B2.bin` byte for byte
  (337,856 bytes, sha256 `bb5558a5…`; since perf-names 340,296 bytes, `24759aa0…`, checked with nanorun only), 1.3 s under qemu-aarch64. The RISC-V B2 under qemu-riscv64 gives the same
  bytes (0.9 s; nanorun: 11.8 s). Translating B2: 0.5 s under qemu.
* The instruction set of `B2_arm.bin` and `rv2arm_arm.bin` is §0-min's (objdump check).
* `synth_rv.py`'s program of rare forms (x0/x2 operands, mul, far offsets, x0 stores): translator = oracle.
* Refused: an `ecall` word, an odd-sized file, and 4 FZ-T cases (unmapped source with rd = x0 ×3, `jalr` through x0).
  Also 9 range cases: branch/jal targets past the end or before 0, misaligned offsets, a shift field with bit 26,
  srai, and `jal x5`. The in-range edge cases are accepted (= oracle).
* `arm/fuzz/fuzz.py`, 40 seeds: 120 runs agree with nanorun.
* Semantic certificate (by G, `Nano/SelfHost/CertArm`, lake-built, no sorry): `CertArm.sem_rv2arm`, i.e. the nano
  semantics of `rv2arm.lean`'s text equals the Lean function `RA.m` (unless a buffer hits the cap). It says nothing
  about the ARM code being right. `test_arm.sh` fails if the certificate is about an older `rv2arm.lean`; after any
  edit, regenerate it with the 4 commands in `../cert/gen_cert.py` (target `arm`).
* `check_lean.sh`: `ArmBlock.lean` elaborates, and `blockJ` = the oracle on 13,539 distinct J instructions.
