# rv2arm: run nano programs natively on AArch64 (Apple Silicon) — UNPROVEN GLUE

**Nothing here is proved.** The correctness theorem is about the compiler's RISC-V output on the Sail RISC-V model.
`rv2arm.py` is a hand-written translator from that RISC-V output to AArch64; `B2_arm.bin` is `rv2arm.py B2.bin`.
If either has a bug, results are wrong and no proof notices. (A proved Lean version is planned, see
`Testing/notes/NANO_V2_ARM.md`.)

## Use on a Mac (Apple Silicon)

```
cc -O2 ../run/shim/shim_arm.c -o shim_arm
grep -v '^--' prog.lean > prog.src                     # the compiler accepts no comments
./shim_arm B2_arm.bin < prog.src > prog_rv.bin         # compile: source in, RISC-V code out
python3 rv2arm.py prog_rv.bin > prog_arm.bin           # translate to AArch64
./shim_arm prog_arm.bin < input > output               # run natively
```

`shim_arm` prints `status S, N output bytes` on stderr (0 ok, 1 ok with empty output, −1 out of work memory,
−2 buffer capacity) and exits 1 on −1/−2. A rejected program gives 0 bytes of code (status 1). Not yet run on a real
Mac (none here); `shim_arm.c` uses `MAP_JIT` + `pthread_jit_write_protect_np` there. If macOS refuses the mapping,
the binary may need the `com.apple.security.cs.allow-jit` entitlement (`codesign`).

## Translation

Each RV word is decoded back to its J instruction (`Nano/V2Self/Proof/Machine/Call.lean`, encoded by
`RvEnc.encJX`; any other word fails an assert) and becomes a fixed block of **K = 4** A64 words, padded with
`add x16, x16, #0`. J index pc ↦ A64 byte offset 16·pc; branch offsets are relocated ×4.

Registers (RV → A64): x0 → xzr, x1 (ra) → x30, x2 (sp) → sp, x10..x13 → x0..x3, x28 → x12, x29 → x13, x30 → x10,
x31 → x11, x5..x8, x14, x15 → same number. Scratch: x16, x17. Never touched: x18, x19..x29.
Convention (mirrors RV): x0 input, x1 length, x2 work base, x3 output, sp = work top, return via x30;
status in x0, length in x1.

| J | A64 block (then padding) |
|---|---|
| `addi rd rs imm` | `add/sub xd, xs, #abs`; rs = x0: `movz xd, #imm`, or (imm < 0) `movz x16, #-imm; sub xd, xzr, x16`; rd = x0: padding only |
| `ld rd rs off` | `ldr xd, [xs, #off]` (off ∈ 8ℕ, < 32768), else `ldur` (−256 ≤ off < 256), else `add/sub x16, xs, #abs; ldr xd, [x16]` |
| `sd rs2 rs1 off` | as `ld`, with `str`/`stur` (x0 stores xzr) |
| `lbu` / `sb` | `ldrb`/`strb wd, [xs, #off]` (0 ≤ off < 4096), else via x16 |
| `alu op rd a b` | `add/sub/mul(madd ..,xzr)/and/orr/lslv/lsrv/eor xd, xa, xb` |
| `slli/srli rd rs sh` | `movz x16, #sh; lslv/lsrv xd, xs, x16` |
| `beq/bne/bltu/bgeu a b o` | `cmp xa, xb; b.eq/ne/lo/hs 4·o − 1` |
| `jal x0 o` | `b 4·o` |
| `jal x1 o` | `pad; pad; pad; bl 4·o − 3` (the LAST word, so x30 = the next block: link width W = 16) |
| `jalr x0 r` | `br xr` (host return = `br x30`) |

A register-form operand that is RV x2 (sp) is first copied with `add x16/x17, sp, #0`. Only the instructions of the
minimal set in `NANO_V2_ARM.md` are emitted (objdump shows aliases: mov, neg, lsl, lsr, cmp).

## Tests (Linux, 2026-11-19)

`test_arm.sh` (needs `gcc-aarch64-linux-gnu`, `qemu-user-static`): every example compiled by `B2.bin` (nanorun),
translated, run with a static `shim_arm` under `qemu-aarch64` on 6 inputs (empty, 1 byte, text, edge bytes,
3000 random bytes, 0x14); output and status equal nanorun's. **Result: 8 × 6 = 48 OK.**

Self-compile: `qemu-aarch64 shim_arm B2_arm.bin < ../self_S_input.txt` = `B2.bin` byte for byte
(337,856 bytes, sha256 `bb5558a5…`), status 0, 1.3 s under qemu (nanorun: 11.8 s). So `B2_arm.bin` is an
ARM-hosted compiler (it still emits RISC-V; translate its output with `rv2arm.py`).
`B2_arm.bin` sha256 is in `B2_arm.sha256`; rebuild with `python3 rv2arm.py ../B2.bin > B2_arm.bin`.
