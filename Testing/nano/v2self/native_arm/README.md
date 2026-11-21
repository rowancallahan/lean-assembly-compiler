# native_arm: a native AArch64 back end for C — PROTOTYPE, UNPROVEN

**Nothing here is proved and nothing here is wired into the proven compiler.** `C/Gen.lean`, B2, `rv2arm` and every
proof file are unchanged. The proof plan is `Testing/notes/NATIVE_ARM_PROOF_PLAN.md`.

| file | what |
|---|---|
| `Nano/Codegen/GenArm.lean` | the back end: `a31` (= `g41` with A64 output). Nano subset, same style as `Gen.lean`; plain defs, no proofs |
| `build_self_A.py` | writes `self_A.lean` / `self_A_input.txt`: Base + Lex2 + Par1 + Own + Gen + GenArm + driver `m = a31 …` (generated, not committed) |
| `compile.sh`, `run.sh` | **use it**: `./compile.sh prog.lean > prog.a64`, `./run.sh prog.lean input output` (native on ARM64, else qemu-aarch64) |
| `GA_arm.bin`, `SHA256SUMS` | the native-ARM compiler (C with the GenArm back end) as native A64 code; it compiles itself to itself |
| `test_native.sh` | builds everything with B2 and runs the checks below |
| `cross_native.sh` | cross-hosting matrix: RISC-V-hosted vs rv2arm-hosted vs native-hosted builds of both compilers |
| `bench.sh` | instruction counts and qemu wall time, RISC-V vs rv2arm vs native |
| `diff_run.sh` | one program, one input: RISC-V (B2) vs native A64, status + output bytes |
| `fuzz_native.py` | differential fuzzer, families `FAM=gen` (nanogen + mutation + mutated examples / C's source), `arith` (UInt64 expressions + Python model), `calls` (helper DAGs, recursion), `big` (big buffers, inputs to 64 KB) |
| `dyn_count.sh` | dynamic instruction count of generated code under QEMU (exec log, one instruction per TB) |
| `edge/` | targeted programs: large constants (movz/movn/movk paths), frames past the ldur range, OOM (−1), capacity (−2) |

## How it fits
`a31 c x` takes the same input as `g41` (the AST from `o41 (y16 (s10 x))`) and runs the same machine: one fuel loop
over the same work items (`g36`/`g37` ↔ `a24`/`a25`), the same width pre-pass (`g53`, reused), the same frame layout,
calling convention (`armMapping`), heap/buffer layout, word 0 = jump to start, words 1–5 out-of-memory stub, 6–10
capacity stub. Only the emitted words differ: each template is written directly as A64. Reused from Gen unchanged:
`g14 g15 g16 g17 g18 g24 g27 g33 g40 g43 g53 g55`. Because the structure is Gen's, the later proof can reuse the
generic J-run proof and needs one lemma per template on the A64 side (see the proof plan).

## Design decisions
* **Registers** = rv2arm's map (RV t0 t1 t2 s0 a4 a5 → x5 x6 x7 x8 x14 x15, t3/t4 → x12/x13, heap top t5 → x10,
  stack t6 → x11, ra → x30, a0–a3 → x0–x3, sp → x4). Same shim, same `armMapping`; x9, x18–x29 never touched.
* **No register field 31** (no xzr, no sp), as for rv2arm: compares are `subs x16, a, b`, zero comes from
  `movz x17, #0` where needed (mul addend, a stored zero). Keeps the instruction set inside what both ARM models
  are known to handle; avoids the sp/xzr ambiguity.
* **Small instruction vocabulary** (27 forms): add/sub imm; add/sub/and/orr/eor/lslv/lsrv/madd reg; `subs x16`
  always directly followed by its `b.cond`; add with lsl #3; movz/movk/movn; ldr/str (scaled uimm), ldur/stur, ldp;
  ldrb (register offset, RD only), strb (start loop only); b, bl, cbz, cbnz, br (the return is `br x30`). No pre/post-index, no csel: every
  extra form is an extra lemma per ARM model.
* **Better than translation where A64 allows it**: constants by movz/movn + movk only for the chunks that need it
  (≤ 4 words, RV `li` is up to 17); real offsets (`ldr [x8, #off]`, `ldur` for −256..−1); `ldp` for pops;
  `add x16, buf, idx, lsl #3` + `ldr [x16, #16]` for buffer access; IF = compare + one inverted `b.cond` straight to
  the else branch (RV: branch over a `jal`); LOOP head = `ldr` + `cbnz` (RV: `ld; beq; jal`); `bl`/`br`/`ret`.
* **Labels**: placeholders are the branch word with offset 0 (`b`, `b.cond`, `cbnz`); `a18` patches by opcode
  (imm26 or imm19). The ±1 MiB range check is Gen's `g14`, so every branch form is always in range.
* **Accept set**: the same checks as Gen, but the 2^18-word code limit applies to A64 words. Native code is smaller on
  every test, so in practice it accepts whatever B2 accepts; a pathological program could differ (not seen).

## Per template (words: RISC-V / native A64; rv2arm = 4 × RISC-V)
| template | RV | A64 |
|---|---|---|
| push | 4 (3 run) | 4 (4 run: A64 has no register-register compare-and-branch) |
| const v | 1–17 + push | 1–4 + push |
| binop | 5 (mul 5) | 4 (mul 5) |
| IF compare | 5 | 4 |
| LOOP head | 3 | 2 |
| BGET / BSET / BPUSH | 10 / 9 / 12 | 9 / 8 / 9 |

## Results (2026-11-20, QEMU 8.2.2)
* B2 compiles `self_A` (C with the native back end). Fixpoint: GA_arm (native A64) compiles `self_A` to its own bytes.
* GA_arm compiles C's RISC-V source to B2_na (B2 as native A64, 311 KB; rv2arm's B2_arm: 1361 KB; B2: 340 KB);
  B2_na compiles C's source to **B2.bin exactly**.
* examples + edge, 5 inputs each: identical status and output. Fuzz (`fuzz_native.py`, final version): 4000 cases (1763 accepted and run on 6–7 inputs each, 2237 rejected by both), 0 mismatches; earlier version 6000 cases, 0 real mismatches.
* Big fuzz (2026-11-21, GenArm d6db803): 21,000 cases, **0 mismatches**: gen 6000 (3265 accepted and run, 2735
  rejected by both), arith 6000 (all also equal to the Python UInt64 model), calls 6000, big 3000 (inputs to 64 KB).
* `cross_native.sh`: 14 sources × 3 host builds × 2 compilers byte-identical; both fixpoints hold.
* Static code words: native A64 = 0.74–0.96 × RISC-V (rv2arm 4.0 ×). Dynamic, examples: native 1.00–1.06 × RISC-V
  (rv2arm 3.6 ×); B2 compiling rle.lean: RISC-V 7.77 M, rv2arm 27.9 M, native 7.70 M instructions.

| example | static RV / rv2arm / native | dynamic RV / rv2arm / native |
|---|---|---|
| fib | 311 / 1244 / 271 | 1159 / 4171 / 1175 |
| hex | 327 / 1308 / 283 | 9177 / 33134 / 9684 |
| rle | 412 / 1648 / 365 | 10059 / 36275 / 10585 |
| upper | 274 / 1096 / 235 | 6692 / 23816 / 7072 |

## Benchmarks (`bench.sh`, QEMU 8.2.2 user mode; dynamic = generated code only, 300-byte input)

| example | static RV / rv2arm / native | dynamic RV / rv2arm / native | wall s (400 KB in) RV / rv2arm / native |
|---|---|---|---|
| count | 123 / 492 / 91 | 103 / 372 / 76 | 0.02 / 0.02 / 0.02 |
| fib | 311 / 1244 / 271 | 2435 / 8769 / 2517 | 0.02 / 0.03 / 0.03 |
| hex | 327 / 1308 / 283 | 61913 / 223598 / 65492 | 0.02 / 0.04 / 0.03 |
| maxbyte | 246 / 984 / 209 | 14550 / 52442 / 15131 | 0.02 / 0.02 / 0.02 |
| reverse | 206 / 824 / 170 | 19912 / 73294 / 19891 | 0.03 / 0.03 / 0.03 |
| rle | 412 / 1648 / 365 | 52536 / 189785 / 55172 | 0.02 / 0.03 / 0.03 |
| sum | 207 / 828 / 171 | 13335 / 49079 / 13613 | 0.02 / 0.02 / 0.03 |
| upper | 274 / 1096 / 235 | 33111 / 117923 / 35067 | 0.02 / 0.02 / 0.03 |

Example wall times are QEMU start-up (~0.02 s).

| C compiling C's source | wall s (3 runs, QEMU) | dynamic instructions |
|---|---|---|
| RISC-V B2 | 0.55 0.53 0.58 | 642 M |
| rv2arm B2_arm | 0.90 0.87 0.91 | ≈ 3.6 × (not counted: the exec log needs > 30 min) |
| native B2_na | 0.80 0.78 0.92 | ≈ 1.0 × (B2 compiling rle.lean: RV 7.77 M, rv2arm 27.9 M, native 7.70 M) |

QEMU wall time is not a CPU measure: it translates RV and A64 at different costs and rv2arm's PAD words are cheap, so
the 3.6× instruction gap shows as only ≈ 1.15× in QEMU time. Real ARM hardware (not available here) is the test for speed.

## Uniform (U) vs variable (V) blocks: what the non-uniform proof buys
The proof's layout layer assumes one fixed-size block per J instruction. GenArm is V (variable, per template).
`uniform_est.py` models U: rv2arm's per-J-instruction A64 sequences padded to K words, weighted by the RISC-V run's
per-PC counts (a model, not an implemented back end). Every J instruction fits in 2 words except 4 stub/start-code
blocks (`addi a0, x0, −1`: 1 word with movn), so K = 2 is the best uniform choice.

| (fib / hex / rle / upper) | static × RISC-V | dynamic × RISC-V |
|---|---|---|
| rv2arm (U, K = 4), measured | 4.00 | 3.60 |
| U, K = 2 (model) | 2.00 | 1.94–1.95 |
| V = GenArm, measured | 0.86–0.89 | 1.01–1.06 |

So V is ≈ 2.3× smaller and ≈ 1.9× faster than the best uniform layout, and ≈ 3.5× faster than rv2arm.

## Use
```
./compile.sh prog.lean > prog.a64          # compile on ARM (the compiler itself is native A64)
./run.sh prog.a64 input.txt output.txt     # run (prog.lean also works: compiles first)
```
On x86-64 Linux both run under qemu-aarch64 (`apt install qemu-user gcc-aarch64-linux-gnu`; the shim is built on first
use). On an ARM64 Mac/Linux they run natively (the shim is `cc`-built; on macOS it may need the JIT entitlement, as
`arm/README.md` says; not tried on a Mac). Rebuild `GA_arm.bin` from `B2.bin` alone: `./test_native.sh DIR`, then
`DIR/GA_arm.bin` (it must equal the checked-in one: `sha256sum -c SHA256SUMS`).

Tests: `./test_native.sh` (build, fixpoints, examples + edge), `./cross_native.sh`, `FAM=… python3 fuzz_native.py SEED N
WORKDIR [MUT]`, `./bench.sh [DIR] [selfdyn]`.

## Known limits
* Unproven. The proven compiler is RISC-V (`C_correctLO`) and ARM via rv2arm (`C_correct_armDM`, `C_correct_armSail`).
* Accept set: the 2^18-word code limit is checked on A64 words (native code is smaller, so in practice a superset of
  B2's; never seen to differ).
* Dynamic count ≈ RISC-V (+0–6%): a checked push is 4 A64 instructions vs 3 RV (no register-register compare-and-branch).
* No register 31, small instruction vocabulary (27 forms): chosen for provability, not peak speed (no csel,
  pre/post-index, register allocation; still the stack machine of Gen).
* Same memory/heap limits as RISC-V: work memory from the shim (1 GiB), buffer capacity 2^19 words (−2 beyond).
