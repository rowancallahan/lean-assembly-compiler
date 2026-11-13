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
