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
