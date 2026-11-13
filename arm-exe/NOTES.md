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
