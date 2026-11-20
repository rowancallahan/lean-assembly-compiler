# rv2arm: run nano programs natively on AArch64 (Apple Silicon) — UNPROVEN GLUE

**Nothing here is proved.** The correctness theorem covers the compiler's RISC-V output on the Sail RISC-V model.
`rv2arm.lean` translates that RISC-V output to AArch64. It is written in **nano**, so B2 compiles it and the result
runs anywhere B2's output runs. If it has a bug, results are wrong and no proof notices. `PROOF_NOTES.md` is the
plan for a proved version (`armTarget`, `Testing/notes/NANO_V2_ARM.md`).

| file | what |
|---|---|
| `rv2arm.lean` | the translator (nano subset, also valid Lean: `cat ../../../../Nano/V2Self/Prelude.lean rv2arm.lean` + `#eval m …`) |
| `rv2arm.sh` | driver: runs the translator once per 32000-word chunk (a nano list holds < 2^19 bytes) and concatenates |
| `rv2arm_rv.bin` | `rv2arm.lean` compiled by B2 (RISC-V) |
| `rv2arm_arm.bin` | `rv2arm_rv.bin` translated by itself (AArch64). It translates itself to itself |
| `B2_arm.bin` | the compiler `../B2.bin` translated (AArch64). It compiles the compiler's source to `B2.bin` |
| `rv2arm.py` | test oracle only (same bytes as the nano translator) |
| `test_arm.sh` | the Linux/qemu test below |
| `SHA256SUMS` | of the three binaries |

## Use on a Mac (Apple Silicon), from this directory

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

Rebuild the binaries without Python, using only the checked-in `B2.bin` and the portable interpreter:
```
cc -O2 ../run/nanorun.c -o nanorun
grep -v '^--' rv2arm.lean > rv2arm.src && ./nanorun ../B2.bin rv2arm.src rv2arm_rv.bin
RUN="./nanorun rv2arm_rv.bin /dev/stdin /dev/stdout" ./rv2arm.sh rv2arm_rv.bin > rv2arm_arm.bin
./rv2arm.sh ../B2.bin > B2_arm.bin
```

## Translation (details and per-block proof notes: `PROOF_NOTES.md`)

Each RV word is decoded back to its J instruction (`Nano/V2Self/Proof/Machine/Call.lean`, encoded by
`RvEnc.encJX`) and becomes a fixed block of **4** A64 words, padded with `add x16, x16, #0`. J index pc ↦ A64 byte
offset 16·pc. A first pass validates the whole program; any other word, register or out-of-range branch gives the
empty output.

Registers (RV → A64): x0 → xzr, x1 (ra) → x30, x2 (sp) → sp, x10..x13 → x0..x3, x28 → x12, x29 → x13, x30 → x10,
x31 → x11, x5..x8, x14, x15 → the same number. Scratch: x16, x17. Never touched: x18, x19..x29.
Convention (mirrors RV): x0 input, x1 length, x2 work base, x3 output, sp = work top, return via x30;
status in x0, length in x1. Only the minimal instruction set of `NANO_V2_ARM.md` is emitted: movz, add/sub (imm,
reg), and/orr/eor, lslv/lsrv, madd, cmp (subs), b.cond, b, bl, br, ldr/str/ldur/stur, ldrb/strb.

| J | A64 block (then padding) |
|---|---|
| `addi rd rs imm` | `add/sub d, s, #abs`; rs = x0: `movz d, #imm`, or (imm < 0) `movz x16, #abs; sub d, xzr, x16` |
| `ld` / `sd` | `ldr`/`str [s, #off]` (off ∈ 8ℕ, < 32768), else `ldur`/`stur` (−256 ≤ off < 256), else `add/sub x16, s, #abs` + `[x16]` |
| `lbu` / `sb` | `ldrb`/`strb [s, #off]` (0 ≤ off < 4096), else via x16 |
| `alu op rd a b` | `add/sub/mul/and/orr/lslv/lsrv/eor d, a, b` |
| `slli/srli rd rs sh` | `movz x16, #sh; lslv/lsrv d, s, x16` |
| `beq/bne/bltu/bgeu a b o` | `cmp a, b; b.eq/ne/lo/hs 4·o − 1` |
| `jal x0 o` / `jal x1 o` | `b 4·o` / `pad; pad; pad; bl 4·o − 3` (x30 = the next block) |
| `jalr x0 r` | `br r` |
| rd = x0 (no-op) | 4 × padding |

An sp operand of a register-form instruction is first copied with `add x16/x17, sp, #0`, and branch offsets shift
by the number of copies.

## Tests (Linux x86-64, qemu-aarch64, 2026-11-20): `test_arm.sh`, all OK

* B2 compiles `rv2arm.lean`, and nanorun runs the result on itself to give `rv2arm_arm.bin`. Under qemu,
  `rv2arm_arm.bin` translates its own RISC-V code to itself (fixpoint). Both translators equal the Python oracle.
* All 8 examples: compiled by B2, translated by the ARM translator (= oracle), run with a static `shim_arm` under
  qemu on 6 inputs (empty, 1 byte, text, edge bytes, 3000 random bytes, 0x14). Output and status equal nanorun's:
  **48/48**.
* B2 translated by the ARM translator = `B2_arm.bin`. ARM-B2 on `../self_S_input.txt` = `B2.bin` byte for byte
  (337,856 bytes, sha256 `bb5558a5…`), 1.3 s under qemu (nanorun: 11.8 s). Translating B2: 0.5 s under qemu.
* An `ecall` word and an odd-sized file are refused.
