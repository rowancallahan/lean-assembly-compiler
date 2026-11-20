# Benchmarks: exact instruction counts (baseline B1, main @ 935c0ac1)

Scripts and raw results: `Testing/nano/v2self/bench/` (`results/riscv.csv`, `results/scaling.csv`, `results/self_S_regions.txt`).
All RISC-V numbers are **exact executed-instruction counts** from `run/nanorun.c` (one count per interpreted instruction;
deterministic). The self-compile count reproduces B1 (1,454,349,112) both in the plain and in the profiling build.
ARM counts are **not available** (see "ARM: blocked").

## Method

- `run_bench.sh`: compile each example with B2 (`nanorun B2.bin src`), then run the compiled program on four inputs:
  10 B, 1 KiB, 100 KiB, 1 MiB (`make_inputs.py`: uniform random bytes, seed 1). Status 1 (empty output) and -2 (buffer capacity)
  are reported, not hidden. The examples' own `-- expect` lines are not rechecked here (`run_examples.sh` does that).
- `profile_self.sh`: the self-compile with `bench/nanorun_prof.c`, a copy of `run/nanorun.c` that writes an execution count per
  code word to the file named in `NANORUN_PROF` (unset: identical behaviour). `profile_regions.py` groups the counts by function.
- `synth_scaling.py`: synthetic programs to measure compile cost against the number of defs and of expression terms.
- Function regions: every `jal ra` target in B2 starts with the prologue `addi x31,x31,-8`; 229 such targets exist, 226 are
  executed. A word belongs to the last target at or below it. Names are not resolved (see "Function names").

## Baseline table (B1)

Self-compile: 86,725 B source -> 337,856 B code: **1,454,349,112 instructions** (about 16,800 per source byte; 11.5 s in
`nanorun` here, 13.5 s in the README run).

| program | src B | compile instr | code B | 10 B | 1 KiB | 100 KiB | 1 MiB |
|---|---:|---:|---:|---:|---:|---:|---:|
| count | 54 | 5,623,980 | 492 | 101 | 101 | 101 | 101 |
| fib | 347 | 7,363,302 | 1,244 | 14,787 | 14,787 | 14,787 | 14,787 |
| hex | 330 | 7,482,090 | 1,308 | 2,171 | 211,055 | 21,094,511 | -2 (stopped at 50.3 M) |
| maxbyte | 230 | 6,855,630 | 984 | 618 | 49,300 | 4,915,348 | 50,331,796 |
| reverse | 210 | 6,508,446 | 824 | 770 | 67,694 | 6,758,510 | -2 (stopped at 30.9 M) |
| rle | 429 | 8,267,595 | 1,648 | 1,871 | 183,290 | 18,317,965 | -2 (stopped at 43.4 M) |
| sum | 194 | 6,456,967 | 828 | 573 | 45,189 | 4,505,733 | 46,137,477 |
| upper | 285 | 6,993,914 | 1,096 | 1,121 | 102,456 | 10,236,996 | -2 (stopped at 48.8 M) |

Run instructions per input byte (from the table, excluding fixed cost):

| program | 10 B | 1 KiB | 100 KiB | 1 MiB | comment |
|---|---:|---:|---:|---:|---|
| count | - | - | - | - | constant 101 |
| fib | - | - | - | - | constant 14,787: reads the first byte only |
| hex | 217 | 206 | 206 | - | linear |
| maxbyte | 62 | 48 | 48 | 48 | linear |
| reverse | 77 | 66 | 66 | - | linear |
| rle | 187 | 179 | 179 | - | linear |
| sum | 57 | 44 | 44 | 44 | linear |
| upper | 112 | 100 | 100 | - | linear |

**No superlinear growth in the run costs.** Status -2 at 1 MiB is the nano `List` limit (fewer than 2^19 elements, README
"Chunking"): the list-based programs stop; their counts are the work done before the stop, not a time for 1 MiB.

## Compile cost: superlinear in the number of defs (flagged)

`scaling.csv` (compile instructions):

| K | flat_K (K independent defs, summed by `m`) | chain_K (each def calls the previous) | expr_K (one sum of K byte reads) |
|---:|---:|---:|---:|
| 10 | 10,671,943 | 8,814,342 | 6,738,649 |
| 20 | 16,861,498 | 12,634,253 | 7,939,659 |
| 40 | 31,829,308 | 21,849,975 | 10,341,679 |
| 80 | 72,119,728 | 46,585,019 | 15,145,719 |
| 160 | 201,564,928 | 125,203,318 | 24,753,799 |
| 320 | 641,852,048 | 391,281,136 | 43,969,959 |

- `expr_K` is linear: a fixed 6.7 M plus 0.12 M per term.
- `flat_K` and `chain_K` grow like K^2: the cost added per extra def rises linearly with K (flat: about 0.6 M at K=15, 2.8 M
  at K=240). Output size is linear in both (about 143 B of code per chain def). This points at work per def or per call site
  that scans all defs (e.g. name lookup without an index). That is a hypothesis; the compiler code was not read for it.
- Relevance: the self-compile (234 defs, 86.7 KB) is about 1.45 G instructions; part of that may be this quadratic term.
  Compile of 640 chain defs (43 KB) was rejected (0 bytes out, status 1): a capacity limit, not investigated.

## Self-compile: where the instructions go (RISC-V, B2 compiles self_S_input.txt)

Top 20 function regions (`results/self_S_regions.txt`, top 25 there). Share = share of all 1,454 M instructions.

| # | entry word | size (words) | calls | share | guess at why it is hot |
|---:|---:|---:|---:|---:|---|
| 1 | 8055 | 442 | 360,370 | 6.8% | Largest per-call body in the hot set: a 24-byte frame, reads frame fields at +32/+40 and branches on them (30% loads). Most likely a per-node/state dispatch of the code generator. Not named. |
| 2 | 6073 | 40 | 2,582,858 | 6.4% | Small frame-pop/return stub: saves ra and x8, reloads continuation and frame pointers, `jalr` to the continuation. Called once per generated call/return. |
| 3 | 6139 | 40 | 2,526,959 | 6.3% | Same stub shape as 6073. |
| 4 | 6205 | 40 | 2,200,901 | 5.5% | Same shape. |
| 5 | 6271 | 40 | 1,849,759 | 4.6% | Same shape. |
| 6 | 6337 | 40 | 1,808,159 | 4.5% | Same shape. |
| 7 | 14382 | 298 | 3,698 | 4.1% | Few calls, 19% stores, 23% loads: a loop per call over a buffer (copying or emitting words). Guess. |
| 8 | 6113 | 26 | 2,582,858 | 4.1% | Return stub, 26-word variant. |
| 9 | 6179 | 26 | 2,511,617 | 4.0% | Return stub, 26-word variant. |
| 10 | 6049 | 24 | 2,831,838 | 3.9% | Return stub, 24-word variant (the first one decoded: `addi x5,x0,64` then the frame pop). |
| 11 | 45541 | 94 | 603,643 | 3.5% | Small helper with 26% loads, called 0.6 M times. Guess: buffer/list access helper. |
| 12 | 6245 | 26 | 2,200,901 | 3.5% | Return stub, 26-word variant. |
| 13 | 42037 | 1,515 | 124,490 | 2.9% | Large body, 23% branches, 124 K calls (about 1.4 per source byte): probably the per-character step of the lexer. Guess. |
| 14 | 6311 | 26 | 1,849,759 | 2.9% | Return stub, 26-word variant. |
| 15 | 6377 | 26 | 1,808,159 | 2.9% | Return stub, 26-word variant. |
| 16 | 43552 | 335 | 1 | 2.0% | Called once, 28.8 M instructions: a top-level loop (the driver over all defs or AST items). Guess. |
| 17 | 12535 | 275 | 124,490 | 1.9% | Same call count as #13: a helper of the per-character step. Guess. |
| 18 | 51906 | 770 | 9,415 | 1.7% | About 9 K calls, 16% branches: per-definition or per-token processing. Guess. |
| 19 | 60831 | 231 | 655 | 1.5% | Called 655 times: per-definition work. Guess. |
| 20 | 58872 | 1,803 | 63,575 | 1.1% | Large body with 63 K calls: probably instruction encoding/emission (B2 emits 84,464 words). Guess. |

Summary: the 11 return stubs (entries 6049–6377, 24–40 words, 1.8–2.8 M calls each) add up to about **48% of all
instructions**. They are generic glue, so the cost is in the number of calls the compiler makes, not in any one function.
The next largest single items are the dispatch (#1) and the per-character step (#13, #17).

**Function names: not resolved.** Attempts, so nobody repeats them:
- Lean 4.29 was installed (elan) and `cg_map.lean` (def -> word offset table of a copy of `C.g39`) ran: 192 entries. Only the
  first 57 (indices 0-56) start with the function prologue seen in B2; from index 57 on most do not (index 57 is at word
  12054, which is not a function start). So this table does not describe B2's code layout. Reason not found.
- Source order of the 190 functions with arguments in `self_S.lean` does not match the call graph (`s8` calls `q0`, but the
  code calls region 5, not region 0).
- The fix is to find the generator's own def-entry bookkeeping (`g54`, which `g39` calls) and run the same code path as
  `g42` on `self_S_ast.bin`, or to add a def-name section to the compiler (not done: the compiler is not to be changed).

## ARM: blocked

- No `qemu-aarch64` / `qemu-user` and no `aarch64-linux-gnu-gcc` on this machine. `apt-get install qemu-user-static
  gcc-aarch64-linux-gnu` was refused by the session's permission check, so it was not retried.
- Without them: no shim_arm, no plugin, no `-d exec` trace. Not done: `libinsn.so`, `-d exec,nochain`, or a small AArch64
  interpreter for the translator's instruction subset (it would need to reproduce `B2_arm.bin`'s output as its check).
- To finish: install `qemu-user-static` and `gcc-aarch64-linux-gnu` (or build qemu-user with `--enable-plugins`), then
  count the code region only (PC outside the static shim's ELF segments) for the self-compile and the 8 examples at 10 B.

## Reproduce

```
Testing/nano/v2self/bench/run_bench.sh        # riscv.csv, scaling.csv (about 2 min)
Testing/nano/v2self/bench/profile_self.sh     # self_S_regions.txt (about 15 s)
```
Needs a C compiler (no QEMU). Inputs are generated, not stored.

## Follow-up 1: which parts grow as K^2 (flat defs, K = 80 vs 320)

`results/flat_growth_80_320.txt` (made by `bench/profile_growth.py`; profiles by `NANORUN_PROF`, total 72.1 M -> 641.9 M,
factor 8.9 for K x4, so quadratic in total). Factor = instructions at K=320 / K=80. "~16x" = K^2, "~4x" = linear.

- **Grow about K^2** (factor 11.7-16.4; call counts grow 12-15x, instructions per call constant for the stubs):
  - entry 8055, 442 words (words 8055-8496): calls 10,200 -> 156,000, factor 16.4. Per call 412 -> 440 instructions.
  - the 11 return stubs: 6049 (24 w), 6073 (40 w), 6113 (26 w), 6139 (40 w), 6179 (26 w), 6205 (40 w), 6245 (26 w),
    6271 (40 w), 6311 (26 w), 6337 (40 w), 6377 (26 w). Calls grow 11.7-14.9x; instructions per call stay 36 (40-word
    stubs), 23 (26-word), 20 (24-word). So the K^2 comes from the number of calls, not from the stubs getting longer.
  - entry 14382, 298 words: calls 241 -> 961 (4x) but instructions per call 7,440 -> 29,280 (4x): a loop whose trip count
    grows with K, run a number of times that also grows with K, so its total is K^2. Factor 15.7.
- **Grow linearly** (factor 4.0): 42037 (1515 w, 7,231 -> 28,831 calls, 372 instr/call), 45541 (94 w), 43552 (335 w, once),
  12535 (275 w), 60831 (231 w), 3494 (942 w), 4436 (711 w), 58872 (1803 w), 130, 322, 79722 (211 w, once). Per call constant.
- Totals: the K^2 entries together are about 70% of the large run's instructions (the 11 stubs alone about 48%).
  So the K^2 part of the compile cost is the call count times a per-call cost, and the call count is the number of call
  sites that the generated code runs. The compiler's own `m` makes K calls and the per-def work is paid once per call.

## Follow-up 2: chain-640 rejection: the limit is 512 defs

Bisection on `chain_K` (each def calls the previous): K=480 ok, 511 ok, **512 rejected** (status 1, 0 bytes). Confirmed with
other families (not only chains): the same cut-off at exactly 512 for:
- `unused_K`: K defs with 2 args, bodies not called, `m` calls only `h0`: 511 ok, 512 rejected, 600 rejected, 1000 rejected.
- `one_K` (1 arg) and `three_K` (3 args): 511 ok, 512 rejected. So it does not depend on the parameter count.
- `flat_nocall_K`: 511 ok, 512 rejected.

Source of the constant: `Testing/nano/v2self/self_S.lean` line 919: `if (bget h 12) < 512 then` guards `v86` (the def
registration; `h[12]` counts defs). The same file uses id 512 + j for the j-th def (`v1 h 45 (512 + j)`, lines 413-414) and
`if a < 512` to separate builtin ids from def ids (lines 396-400). So names live in a 10-bit id space: 0-511 builtins and
locals, 512-1023 defs. The def table itself has room for 1024 entries (`d14 := 1024`, line 153), so the binding limit is
the id space, not the table size.

Checked and not the limit: the node cap (`d13 = 16384`, Par1: `bget h 9 < d13`) and the output buffer (`g_999 = 524288`,
`262143 < bsize o`): the failure is the same for tiny and for large bodies at exactly 512 defs, and the 512-def program
has far fewer nodes than 16384 in all the tests above. The `d12` (tasks, 4096), `d15` (8192) and `d13` limits were not
measured separately. Whether constant defs (`def k : UInt64 := ...`) also count toward the 512 was not tested.

Practical consequence: the self-compile (234 defs) is well under the cap, but any program with more than 511 defs is rejected
silently (empty output, no error message).

Reproduce: `Testing/nano/v2self/bench/synth_scaling.py` (chain/flat/expr families); bisect by hand with `nanorun B2.bin src`.
