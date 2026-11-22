# nanorun — run the nano compiler on a machine without RISC-V

**Optional cross-check, not the default run path.** By default, code runs on QEMU's machine models:
* RISC-V: `qemu-riscv64` + `shim/shim_rv.c`, built with `riscv64-linux-gnu-gcc -static`;
* ARM: `qemu-aarch64` + `shim/shim_arm.c`, or natively on Apple Silicon (see `../arm/README.md`).

The scripts `../examples/run_examples.sh` and `../arm/test_arm.sh` take `NANORUN=1` to use or add nanorun.

**Unproven glue.** Nothing here is part of the correctness theorem. The theorem is about the compiler's RISC-V code on
the Sail RISC-V model; `nanorun` is a small interpreter written by hand so that code can be run on a Mac or any other
host. If `nanorun` has a bug, results are wrong and no proof notices.

## Use

```
cc -O2 nanorun.c -o nanorun            # C99 + __int128 (clang and gcc), no dependencies; macOS and Linux
nanorun CODE.bin INPUT OUTPUT [work_MB]
```

- `CODE.bin`: raw little-endian 32-bit RISC-V instruction words.
- `INPUT`: the bytes given to the code (at most 2^20 bytes, the limit of the compiler's contract).
- `OUTPUT`: written when the code reports success.
- `work_MB`: work memory in MiB, default 80 (what the self-compile needs is below that; small programs need about 5).

It prints `a0` (0 ok, 1 ok with empty output, −1 out of work memory, −2 a buffer reached its capacity), `a1` (output
length) and the number of instructions executed. Exit status 0 on success, 1 when the code reported −1/−2, 3 on a trap.

Two steps (`make demo` does both):

```
nanorun ../B2.bin prog.lean prog.bin    # (a) compile: the compiler is itself such a code file
nanorun prog.bin in.bin out.bin         # (b) run the compiled program
```

`B2.bin` is the compiler compiled by itself. It is checked in next to this directory
(`Testing/nano/v2self/B2.bin`, sha256 in `B2.sha256`) and is produced by `Testing/nano/v2self/boot/fixpoint.sh`
(builds the trusted Lean-compiled `B1`, runs it on the compiler's source `self_S_input.txt` to get `B2`, then checks on
QEMU that `B2` compiles the source to `B2` again). `make selfcheck` repeats that last check with `nanorun`.

## Memory layout

One block of host memory stands for guest addresses from `0x80000000` (the RAM start of the proved machine); everything
stays below 4 GiB.

| guest address | content |
|---|---|
| `0x80000000` | 4 bytes never executed: the return address given to the code (`ra`). Reaching it ends the run. |
| `0x80001000` | the code |
| after the code, 16-aligned | the input (`a0` = its address, `a1` = its length) |
| next, 16-aligned | the output block, 2 MiB (`a3`) |
| next, 16-aligned | the work block (`a2` = base, `sp` = its end). Zero-filled. |

The code keeps its stack and its buffers in the work block and never asks the host for anything: no system calls.
`nanorun` traps with a message on a load or store outside the block, a store into the code or the input, a jump outside
the code, and on any instruction outside RV64IM integer instructions (no CSR, `ecall`, atomics, floating point,
compressed). The compiler's own code uses only: `ld lbu addi slli srli sb sd add sub mul sll srl or and beq bne bltu
bgeu jal jalr`.

## Validation (`validate.py`, run from the repository root)

- self-compile: `nanorun B2.bin self_S_input.txt` gives `B2.bin` byte for byte (sha256 `395f0b9d…` since exp-syntax; `24759aa0…` with the hashed def table; before it: `bb5558a5…`);
- the four programs of `boot/qemu_regress.py`, compiled with `nanorun B2.bin` and run on five inputs each: outputs equal
  the Python model of the Lean semantics, and (with `QEMU=1`) the outputs of `qemu-system-riscv64`;
- with 1 MiB of work memory the self-compile returns −1 (out of memory) instead of crashing.

Measured on the Linux build box (x86-64, `cc -O2`), 2026-11-19:

| run | time | instructions |
|---|---|---|
| self-compile (87,286-byte source → 340,296 bytes of code; branch perf-names, 2026-11-20) | 7.2 s | 641,996,759 |
| self-compile (exp-syntax: lexer trivia; → 348,904 bytes of code, 2026-11-20) | — | 664,861,123 |
| self-compile before the hashed def table (86,725 B → 337,856 B) | 13.5 s | 1,454,349,112 |
| compiling a 4-line program | 0.07 s | 6.5 million |
| running a compiled 4-line program on 5 bytes | < 0.01 s | 441 |
| the same 4 programs × 5 inputs on `qemu-system-riscv64` (for comparison) | 28 s per program | |

About 107 million interpreted instructions per second. Not yet run on macOS (no Mac here): the code uses only C99,
`__int128` and stdio, and asserts a little-endian host.

## How a native loader would differ

`nanorun` interprets RISC-V. To run natively on Apple Silicon the compiler would first need an AArch64 code generator
(it has none). Given one, the loader would:

- allocate the code with `mmap(..., MAP_JIT)`, write it with `pthread_jit_write_protect_np(0)`, switch back with
  `pthread_jit_write_protect_np(1)` and call `sys_icache_invalidate` (macOS forbids writable+executable pages otherwise;
  a signed binary also needs the `com.apple.security.cs.allow-jit` entitlement);
- place input, output and work blocks anywhere (the 4 GiB limit above is a property of the proved RISC-V machine);
- call the code as a C function following the convention above mapped to AArch64 registers
  (`x0` input, `x1` length, `x2` work base, `x3` output, `sp` work top, `x30` return), on a separate stack = the work block;
- have no bounds checks: a wrong program would corrupt the process instead of trapping.

## Native shim (`shim/`): run the code as an ordinary process

`nanorun` interprets. `shim/shim_rv.c` (31 lines) loads the code into executable memory and jumps to it, on a RISC-V
Linux machine or under user-mode QEMU. Also unproven glue.

```
riscv64-linux-gnu-gcc -O2 -static shim/shim_rv.c -o shim_rv
./shim_rv B2.bin < prog.lean > prog.bin      # compile: the code file is the only argument
./shim_rv prog.bin < input.bin > out.bin     # run the compiled program
```

On a machine that is not RISC-V: `qemu-riscv64-static ./shim_rv …` (Debian/Ubuntu package `qemu-user-static`).
Input comes from stdin, the output bytes go to stdout, the status line to stderr; exit status 0 on success (status 0 or
1), 1 when the code reported −1 (out of work memory) or −2 (buffer capacity), 2 on a usage error.
Fixed sizes: code up to 4 MiB, input 1 MiB, output 2 MiB, work memory 1 GiB.

What it does: `mmap` a read-write-execute block for the code, read the input into a static buffer, flush the
instruction cache, then one line of inline assembly: park the host stack pointer in `s1`, set `sp` to the top of the
work block, `jalr` to the code with `a0..a3` set, restore the host stack. It relies on the code keeping `sp` and
`s0..s11` (part of the proved contract). It exits with status 2 and a message when the code file or the input fills
its buffer (instead of truncating) or executable memory is refused, and refuses an output length above 2 MiB. Unlike
`nanorun` it has no memory bounds checks: wrong code corrupts or crashes the process.

Tested here under `qemu-riscv64-static` 8.2 (`SHIM="qemu-riscv64-static /tmp/shim_rv" python3 …/validate.py`):
self-compile output equals `B2.bin` byte for byte in 1.1 s (nanorun: 13.5 s); the four regress programs give the same
code as through nanorun and the model's outputs on five inputs each. Not run on real RISC-V hardware.

`shim/shim_arm.c` is the same for AArch64 (`x0..x3`, `sp`, `x30`; on macOS `MAP_JIT`, `pthread_jit_write_protect_np`,
`sys_icache_invalidate`). It is **for the future ARM back end and untested**: the compiler emits RISC-V only, so there
is no code it could run, and it has not been compiled here (no AArch64 toolchain on this box).
