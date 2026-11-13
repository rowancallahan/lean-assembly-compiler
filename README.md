# lean-assembly-compiler

Machine code proved correct against Sail-generated CPU models in Lean 4. Work in progress.

## What is kernel-checked today (RISC-V, Sail model `opencompl/sail-riscv-lean`, unmodified)

- `Proven.compile_ok` (`Proven/Compiler.lean`): for every expression `e` over `+ - &&& ||| ^^^`, 64-bit constants
  and up to four arguments, with `e.depth < 5`, the code `compile e` placed anywhere in RAM runs on the Sail model
  with no trap and no model error, returns to `ra`, leaves `a0 = e.denote (a0, a1, a2, a3)`, leaves memory unchanged,
  keeps callee-saved registers and the control state `Cfg`.
- `Proven.demo_ok` (`Proven/Reify.lean`): the same for a Lean function `demo`, reified by `reify%`.
- Axioms used (from `#print axioms`): `propext`, `Classical.choice`, `Quot.sound`, plus opaque externs declared by the
  generated model (`cancel_reservation`, `get_16_random_bits`, `load_reservation`, `match_reservation`,
  `plat_term_write`, `sys_enable_experimental_extensions`, `valid_reservation`). No `sorryAx`.
- Empirical check: `compile demoE` (47 words) on 200 random inputs: QEMU == Sail C emulator == reference
  (`asm/compile_test.py`).

## Not proved

- `Proven.sort_ok` (`Proven/Sort.lean`): stated with `sorry`.
- `Proven/SortSteps.lean`: per-instruction lemmas for the sort; 5 of them currently fail with
  `(kernel) deep recursion detected`.
- Nothing is proved against the ARM model yet.

## Layout

- `Proven/Spec.lean` — the specification (`Cfg`, `Retires`, `runsTo`, `Implements`, ...). Read this first.
- `Proven/SailEval.lean` — `sail_eval`, a call-by-value symbolic executor tactic for Sail models.
- `Proven/Regs.lean`, `Proven/Step.lean` — register facts and per-instruction step lemmas for `try_step`.
- `Proven/Compiler.lean`, `Proven/Reify.lean` — the compiler, its proof, and `reify%`.
- `asm/` — RV64I merge sort, QEMU vs Sail C emulator co-simulation (`cosim.py`), compiler test.
- `asm-arm/` — AArch64 merge sort and QEMU harness.
- `arm-gen/` — `regen.sh` regenerates the ARM Lean model from pinned upstream commits; `DIFFS.md` lists every
  diff from upstream.
- `armv9-lean/` — generated ARM v9.4-A Lean model (do not edit by hand).

## Build

Lean 4.29.0 for `Proven/` (needs the RISC-V model checked out at `../deps/sail-riscv-lean`), Lean 4.34.1 for
`armv9-lean/`.
