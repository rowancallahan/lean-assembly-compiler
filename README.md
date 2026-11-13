# lean-assembly-compiler

Work in progress: machine code proved correct against Sail-generated CPU models in Lean 4.

- `asm/` — RV64I merge sort, bare-metal harness, QEMU vs Sail C emulator co-simulation (`cosim.py`).
- `asm-arm/` — AArch64 merge sort and QEMU harness (`run.py`).
- `Proven/` — Lean: `SailEval.lean` (symbolic executor tactic for Sail models); RISC-V step lemmas, spec, compiler (in progress).
- `arm-gen/` — `regen.sh` regenerates the ARM Lean model from pinned upstream commits; `DIFFS.md` lists every diff from upstream (currently none).
- `armv9-lean/` — generated ARM v9.4-A Lean model (output of `arm-gen/regen.sh`; do not edit by hand).

Status: nothing in `Proven/` is claimed proved until stated in this file. The ARM model's Lean build has not yet completed.
