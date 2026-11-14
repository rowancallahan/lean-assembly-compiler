# arm-exe: building the ARM Lean model as a runnable program (second machine)

Box: 4 cores, 15 GB RAM, no swap (the `swapon` step was refused by this session's permission layer), 30 GB disk free.
Input: `arm-exe-gen/armv9/` from branch `arm-exe-gen` (commit f6cdd89), unmodified. `lake-manifest.json` there
lists no packages, so `lake build` says `missing manifest`; copied the one from `armv9-lean/` (lean-sail e4745c8).
Build script: `arm-exe/build.sh <Module>...` (logs in `arm-exe/logs/`, peak RSS sampled every 5 s with `ps`).

## Step 1: toolchain
Lean 4.34.1 from the GitHub release tarball, elan from its GitHub release: OK.
opam 2.1.5 (apt), OCaml 5.1.1 switch: OK. `opam.ocaml.org` reachable.

## Step 3: early modules
`lake build Armv9.Prelude Armv9.Builtins Armv9.MonoRewrites Armv9.Common Armv9.Option Armv9.ReverseEndianness Armv9.Flow`:
25 jobs, 0 errors, 1m44s wall (Defs 85 s). Lean accepts these as computable; nothing missing so far.

## Observations before the full build
- `cycle_count` / `get_cycle_count` are provided by lean-sail (`Sail/ArchSem.lean`); no stub needed.
- `__GetVerbosity` is generated in `Prelude.lean`.
- Generated `main` is `main_of_sail_main default (sail_model_init >=> sail_main)`: initial memory is EMPTY
  (no ELF loader anywhere), a read of an unmapped byte throws `OutOfMemoryRange`, and `sailOutput` is only
  printed when the run ends. So the generated `main` cannot run a program as is; a hand-written driver that
  preloads `mem` is needed (to be listed here when written).

## Step 4: full build, one module at a time (`arm-exe/logs/summary.txt`)
| Module | result | wall | peak RSS |
|---|---|---|---|
| V8Base | built (same `sorry` warning as checked build, `Reduce__1`) | 1874 s | 13.8 GB |
| Stubs, Interrupts, Devices, Interface, Impdefs | built | 1-17 s each | <= 1.5 GB |
| SysregsAutogen | **FAILED: `error: Lean exited with code 137`** (kernel OOM kill) | 498 s | >= 13.4 GB at kill |

SysregsAutogen detail (second run, RSS every 10 s, `logs/SysregsAutogen.profile.rss`): RSS grows slowly
1.8 -> 5.0 GB over the first 480 s, then 5.0 -> 8.3 -> 13.2 GB within 20 s and is killed. So one definition
blows up. Largest definitions in the file (bytes of text): `AArch64_AutoGen_SysRegRead` 6.5 MB (line 65666 of
215157, the first of the big ones), `AArch64_AutoGen_SysRegWrite` 3.7 MB, `AArch32_AutoGen_SysRegWrite32` 1.4 MB,
`AArch32_AutoGen_SysRegRead32` 1.4 MB. Their if/else chains are under the 1000-level cut threshold
(`if_chain_min`) so they are emitted unsplit.
Blocked behind it: Sysregs, Reset, Instrs32, Instrs64, DecodeEnd, Fetch, Elfmain, Armv9 (the exe).

## Hand-written files (nothing generated is edited)
- `arm-exe/Run.lean`: driver. `armrun <x0> <hexword>...` builds an initial state with the words at address 0
  (reset vector, `CFG_RVBAR = 0`), runs `sail_model_init`, `__InitSystem`, sets `R0`, calls the model's own
  `step_model` once per word, prints `R0`. Needed because the generated `main` starts with empty memory.
  NOT yet compiled (blocked on SysregsAutogen).
- `arm-exe/mkmodel.sh`: makes `ArmRun/Model.lean` = generated `Armv9.lean` minus its last 2 lines (`def main`),
  because a second `main` cannot be declared in a module that imports the generated one. Equivalent to
  generating without `--lean-executable` (that flag only adds `main` and the `lean_exe` lakefile entry).
- `arm-exe/lakefile.toml`: separate package requiring `../arm-exe-gen/armv9` by path.
- No stubs for C primitives were needed so far: `cycle_count`, `get_cycle_count` come from lean-sail,
  `__GetVerbosity` is generated. There is no ELF loader; `Run.lean` replaces it.

More step-4 numbers (unmodified `arm-exe-gen/armv9`):
| MapClauses | built | 5 s | 1.8 GB |
| Instrs64Sme | built | 147 s | 3.4 GB |
| Instrs64Sve | built | 473 s | 5.2 GB |

Confirmed culprit: the first 65665 lines of `SysregsAutogen.lean` (everything before
`AArch64_AutoGen_SysRegRead`) compile alone in 483 s at 4.2 GB peak. The full file is killed ~15 s later.

## EXPERIMENT (not the pinned generator): `if_chain_min = 100`
Coordinator approved, runnable variant only. Generator = pinned Sail + repo patch + one constant changed
(`if_chain_min` 1000 -> 100; full diff vs upstream: `arm-exe/gen100/sail-if_chain_min-100.patch`). Sail sources
unchanged. Flags as for `arm-exe-gen` (`--lean-executable`, no `-lean-noncomputable`, `src/elfmain.sail` added).
Generation: rc=0, 1248 s, Sail peak RSS 8.6 GB.
Files that differ from `arm-exe-gen/armv9`: exactly 4. `_tailK` helper definitions per file (threshold 100 / 1000):
DecodeEnd 32 / 11, SysregsAutogen 25 / 0, V8Base 3 / 0, MapClauses 1 / 0.
SysregsAutogen helpers by function: SysRegRead 8, SysRegWrite 6, AArch32 SysRegRead32 4, SysRegWrite32 4,
SysOpsWrite 2, SysOpsWrite128 1.
Build tree for the experiment: a copy of `arm-exe-gen/armv9` with ONLY `Armv9/SysregsAutogen.lean` replaced by
`arm-exe/gen100/SysregsAutogen.lean` (V8Base and MapClauses kept from the threshold-1000 output, already built).
Logs: `arm-exe/logs100/`.

### Experiment results: Lean stage (tree = arm-exe-gen/armv9 + threshold-100 SysregsAutogen.lean)
| Module | result | wall | peak RSS |
|---|---|---|---|
| SysregsAutogen (split, 25 helpers) | built | 1527 s | 11.9 GB |
| Sysregs | built | 19 s | 1.9 GB |
| Reset | built | 1 s | - |
| Instrs32 | built | 243 s | 3.6 GB |
| Instrs64 | built | 221 s | 3.2 GB |
| DecodeEnd (threshold-1000 file, unchanged) | built | 1467 s | 11.8 GB |
| Fetch, Elfmain | built | 6 s, 3 s | 1.8 GB |
| Armv9 (root, has `main`) | built | 227 s | 3.8 GB |
Every Lean module of the runnable model is accepted as computable; 0 errors; only warning is the known
`sorry` in `Reduce__1` (V8Base). No `--lean-noncomputable-function` needed.
`arm-exe/Run.lean` + `ArmRun/Model.lean` also compile (Model 230 s).
Note: the model uses lean-sail's `ConcurrencyInterfaceV1` (`SailM` = `EStateM` over a state with `regs`, `mem`).

### C stage (lake `:o` facet, clang -O3 from the Lean toolchain, one module at a time)
Generated C sizes: SysregsAutogen.c 225 MB, V8Base.c 87 MB, DecodeEnd.c 60 MB, Instrs64Sve.c 49 MB,
Instrs32.c 28 MB, Instrs64.c 22 MB, Instrs64Sme.c 22 MB, Defs.c 12 MB.
New error class: `V8Base.c:168754:1: fatal error: bracket nesting level exceeded maximum of 500`.
The generated lakefile passes `-fbracket-depth=500`. EDIT TO GENERATED OUTPUT (recorded in
`arm-exe/gen100/lakefile-bracket-depth.patch`): 500 -> 100000 in `lakefile.toml`. No generator flag sets this.
Second edit in the same patch: `-O0` appended. Reason: clang on `DecodeEnd.c` did not finish at `-O3`
(stopped by hand after ~2300 s) nor at `-O1` (stopped after ~700 s); it has single C functions of ~300,000
lines (`__DecodeT32`, `__DecodeA64_SME`, `__DecodeA64_DataProcFPSIMD`). At `-O0` it takes 45 s.
`arm-exe/gen100/lakefile.patch` is the whole edit: `["-fbracket-depth=500"]` -> `["-fbracket-depth=100000", "-O0"]`.

| C file | level | result | wall | clang peak RSS |
|---|---|---|---|---|
| V8Base.c | -O3, depth 500 | FAILED bracket depth | 2 s | - |
| V8Base.c | -O3 | built | 665 s | 2.5 GB |
| Instrs64.c / Instrs32.c / Instrs64Sme.c / Instrs64Sve.c | -O3 | built | 112 / 148 / 141 / 350 s | 0.7 / 0.9 / 0.8 / 1.7 GB |
| DecodeEnd.c | -O3, -O1 | not finished (stopped) | >2300 s, >700 s | 2.2 GB |
| DecodeEnd.c | -O0 | built | 45 s | 3.5 GB |
| SysregsAutogen.c | -O0 | built | 123 s | 7.3 GB |
| V8Base.c | -O0 | built | 47 s | 2.7 GB |
`SysregsAutogen.c` at -O3 was never attempted. The linked executable is all `-O0`.

## Step 5: RESULT
Executable `armrun` linked (461 MB; link + remaining C files 40 s). Tree: `arm-exe-gen/armv9` + threshold-100
`SysregsAutogen.lean` + `lakefile.patch`, driver `arm-exe/Run.lean`. Reproduce: `arm-exe/build-exe100.sh`
(written after the fact from the commands used; the script itself has not been run end to end).

    $ armrun 21 aa0003e9 aa0003ea 8b0a0129 aa0903e0 d65f03c0
    x0 = 42                                  (0.08 s wall, exit 0)
    $ armrun 5 aa0003e9 aa0003ea 8b0a0129 aa0903e0 d65f03c0      -> x0 = 10
    $ armrun 1000000007 <same 5 words>                           -> x0 = 2000000014
    $ armrun 5 aa0003e9 aa0003ea 8b0a0129                        -> x0 = 5   (stops before `mov x0,x9`)
    $ armrun 5                                                   -> x0 = 5   (reset only)

What ran: `sail_model_init`, `__InitSystem` (cold reset; CPU at EL3 AArch64, PC = 0), `R0 := arg`, then the
model's `step_model` 5 times, i.e. full fetch/decode/execute through `__TopLevel`, then read `R0`.
NOT done: comparison against QEMU on this box (no qemu installed here); `ret` jumps to x30 = reset value 0.

The generated `main` (exe `run`, unmodified entry point `sail_model_init >=> sail_main`) also links and runs:
    $ run
    Error while running the sail program!: 0 Out of Memory Range        (exit 1)
i.e. reset succeeds and the first instruction fetch at address 0 fails because memory is empty. `sail_main`
itself has no way to receive a program in the Lean build (the C emulator's ELF loader has no Lean counterpart).

## Summary for the owner
- Runnable: yes, with (a) generator constant `if_chain_min` 1000 -> 100 for `SysregsAutogen` only,
  (b) lakefile `-fbracket-depth` raised and `-O0`, (c) a 22-line hand-written driver. No `.sail` change,
  no stubs, no hand edit of any generated `.lean` file.
- With the pinned generator (threshold 1000) on 15 GB without swap: fails at one definition,
  `AArch64_AutoGen_SysRegRead` in `SysregsAutogen`, RSS > 13.2 GB when killed. Whether a bigger machine alone
  suffices is not known from this box.
- Peak memory seen (Lean): V8Base 13.8 GB, SysregsAutogen (split) 11.9 GB, DecodeEnd 11.8 GB; all else <= 5.2 GB.
- Sum of wall times for a from-scratch build as done here: about 1 h 55 min on 4 cores (Lean modules ~1 h 46, driver model 4 min, C at -O0 ~5 min).

## Elaborator or code generator? (unsplit SysregsAutogen, threshold 1000)
Same file with `noncomputable section` inserted after the imports (scratch copy, compiled against the runnable
build's dependencies, no `-c`): `rc=137` (OOM kill) at 491 s, last RSS sample 10.7 GB (5 s sampling).
The computable run died at 498 s. So on this box (15 GB, no swap) the kill happens at the same point with code
generation off: the elaboration of `AArch64_AutoGen_SysRegRead` alone exceeds available memory here. Whether
code generation adds memory on top cannot be measured on this box. (Coordinator reports the unsplit file passes
the checked build on a box with 12 GB swap.)

## Batch runner and comparison against QEMU
`Run.lean` is now a batch runner: `armrun FILE`, one line per input `x0 x1 x2 x3 word...` (hex), prints x0 (hex).
(The single-shot `armrun 21 <words>` form shown above was the earlier version, commit 1a7290d.)
- The trailing `ret` IS executed: x30 is set to 0x100000 and `step_model` is called until PC = 0x100000
  (bound 1,000,000 steps). Nothing is fetched from that address.
- Reset (`sail_model_init`, `__InitSystem`) is run ONCE; its resulting state value is reused for every line with
  that line's memory, x0..x3 and x30. Sound because the state is an immutable Lean value and reset is
  deterministic (no input); the runner asserts reset left memory empty.

`arm-exe/compare.py ARMRUN triple.txt WORKDIR` (QEMU half copied from `asm/triple.py`), run on
`asm/triple-data/triple.txt` from main (14fbd02), qemu-system-aarch64 8.2.2 (-machine virt -cpu cortex-a72):

    TOTAL 17099 inputs, 18 cases, mismatches 0
    Lean ARM model == expected (Lean Exp.denote) == AArch64 QEMU on this box, for every input.

Per case (inputs, words): all 18 cases report `mismatches 0`; largest are deep_ite (589 inputs, 316 words) and
chain9_depth10 (589, 115). Instructions exercised are only what the corpus contains (mov/orr, add, sub, and, eor,
movz, lslv/lsrv/asrv, subs/cmp, cset/csel/csinc, ret); this says nothing about the rest of the model.
RV64 half of triple.py was not run here.

Throughput of the model runner (executable compiled at -O0, one core): 17099 inputs in 177.5 s = 96 inputs/s,
= 2,185 model steps/s (387,920 instructions incl. `ret`), including process start and the one reset.

## ALL deviations from the checked model on main needed for the runnable build
1. Generator flags: `-lean-noncomputable` dropped, `--lean-executable` added, `src/elfmain.sail` added (coordinator's `arm-exe-gen`).
2. `lake-manifest.json` in `arm-exe-gen/armv9` replaced by the one from `armv9-lean` (generated one lists no packages).
3. Generator constant `if_chain_min` 1000 -> 100, used for ONE file: `Armv9/SysregsAutogen.lean` (25 `_tailK` helpers). `arm-exe/gen100/`.
4. Generated `lakefile.toml`: `-fbracket-depth=500` -> `100000`, and `-O0` added. `arm-exe/gen100/lakefile.patch`.
5. Hand-written: `arm-exe/Run.lean` (driver), `arm-exe/mkmodel.sh` (copies generated `Armv9.lean` without its 2-line `def main`), `arm-exe/lakefile.toml`.
6. NOT applied here: main's newer `--lean-partial-function Reduce__1`; this build's V8Base still has the `sorry`-terminated `Reduce__1`.
No `.sail` change, no stub for any C primitive, no hand edit of a generated `.lean` file.

## Heavy testing round (2026-11-14)
Model variant that ran: the SAME build as above (threshold-100 SysregsAutogen, V8Base from `arm-exe-gen` f6cdd89, i.e. it
predates main's `--lean-partial-function Reduce__1`). Runner binary: `arm-exe/o3.sh` relink, same generated C, every file at
clang -O3 except `DecodeEnd.c` and `SysregsAutogen.c` (-O0 objects reused). Output of the -O0 and -O3 binaries is identical
on the one sample compared (300 lines, md5 equal); -O3 is about 3x faster.
`Run.lean` modes now: `run` (as before), `step` / `stepA0` / `stepdbg` (ONE `step_model` from a full state), `reset`.

### 2. Instruction-level differential test (`arm-exe/insn_test.py`, log `logs-test/insn_seed1_n1000.txt`)
One instruction, random state, QEMU 8.2.2 (virt, cortex-a72, EL1, MMU off) vs model (EL3 after reset, MMU off), same PC,
same x0..x30, same NZCV, same 64-byte memory buffer at the same address. Compared after the instruction: x0..x30, NZCV,
PC, the 64 buffer bytes. Values: 1/3 edge list, 2/3 uniform 64-bit; NZCV uniform 0..15; registers uniform incl. 31 (xzr)
where 31 is xzr; shift amounts / immediates biased to edges. Seed 1, 1000 states per form.

    TOTAL 47 forms, 47000 states, mismatches 0        (42 s wall, -O0 binary)

Forms (1000 states each, 0 mismatches each): `add_shifted` `sub_shifted` `and_shifted` `orr_shifted` `eor_shifted` `subs_shifted` `cmp_shifted` `mov_orr_xzr` `lslv` `lsrv` `asrv` `cmp_imm` `subs_imm` `add_imm` `sub_imm` `csinc_lo_lt_eq` `cset_lo_lt_eq` `csel_ne` `csel_allcond` `csinc_allcond` `movz` `movk` `movn` `ret` `b` `cbz` `cbnz` `b.eq` `b.ne` `b.hs` `b.lo` `b.ge` `b.lt` `b.cond_all` `ldr_x` `str_x` `ldrb` `ldr_x_unaligned` `str_x_unaligned` `strb` `lsl_imm` `lsr_imm` `asr_imm` `ubfm_any` `sbfm_any` `madd` `msub`

Limits of this test:
- PC on QEMU is observed as taken / not taken (branch targets are always insn+8), not read directly.
- `ret`: target register holds insn+8. `cbz`/`cbnz`: register forced to 0 in half the states.
- `add_imm`/`sub_imm`/`subs_imm`/`cmp_imm` and load/store bases never use register 31 (sp is the harness's table pointer).
- Load/store: base register points into the buffer; unsigned-offset forms only (imm12), no writeback forms, 64-bit and byte only.
- 64-bit (sf=1) forms only; no 32-bit W forms.

FINDING (model vs QEMU; the two `_unaligned` forms above check the model's behaviour only, QEMU is not compared there):
unaligned 8-byte `ldr`/`str`. With the MMU off the model gives data accesses memory type Device, and
`AArch64_S1HasAlignmentFault` returns `memtype == Device && !aligned`, so the model takes a Data Abort
(ESR_EL3 = 0x96000021 = alignment fault, PC = 0x200, FAR = the address; registers and memory unchanged) although
SCTLR_EL3.A = 0 (SCTLR_EL3 after reset = 0x30850030; clearing bit 1 changes nothing). QEMU performs the access.
`ldr_x_unaligned` / `str_x_unaligned` check that the model faults with state unchanged: 1000/1000 each.
On the first smoke run (unaligned not yet separated) these were the only mismatches of any form: ldr 9/20, str 6/20, all with
address % 8 != 0. Consequence for the next layers: `ldr`/`str` on this model with the MMU off need 8-byte-aligned addresses
(or an enabled MMU mapping Normal memory); byte accesses are unaffected.
