# Session summary (dated log, newest last)

Append one short entry per session: date, what changed, what was proved/tested, what failed.

## Up to 2026-11-14 (seeded from the READMEs and `ROADMAP.md`)

Proved (RISC-V, axioms = Lean's three + the Sail model's declared externs; middle layer = Lean's three only):
- `compile_ok` (expressions, depth < 11), `demo_ok`/`demo2_ok` via `reify%`.
- `compileS_ok`, `compileF_ok`, `sum_ok`, `gcd_ok` (loops); `compileStore_ok` (8-byte store).
- `compileA_ok`, `compileAF_ok` (byte arrays), `sumCode_ok`, `takeCode_ok`, `incCode_ok`.
- `sortCode_implements` (insertion sort = `List.mergeSort`), `compileBF_ok` (spill slots),
  `msortCode_implements` (bottom-up merge sort = `List.mergeSort`).
- `compileP_ok`, `compile%` examples (`Riscv/Examples/PipeExamples.lean`).
- Middle layer `Proven.Mach`: `compAF_ok` etc., RISC-V theorems re-derived through the interface (`Riscv/Back/`).
- ARM: `compile_ok_exec` (decode+execute of `gen e 0 ++ [iRes]`), `ret_word` (partial).

Tested only: `Arm/CompilerArm.lean` on QEMU (`triple.py`); all RISC-V examples on QEMU == Sail C emulator.

Not proved: `Riscv/Legacy/Sort.lean` (`sorry`), `Riscv/Legacy/SortSteps.lean` (kernel deep recursion; fix known,
see `DETAILS.md` "Memory"). ARM fetch / full step / chaining `ret`.

Far future (noted, not planned): self-hosting; multi-core with read-only shared blocks; con-leche / con-ron
compiled to proved ARM and RISC-V code; lean-svg's `render` as a large client; a tiny RTOS on RISC-V.

## 2026-11-14: repository reorganisation

- Layout `Spec/`, `Compiler/`, `Riscv/`, `Arm/`, `Testing/` (moves with `git mv`; module names follow folders;
  namespaces unchanged; only import lines edited, plus the header comments of the five generated `*Words.lean`
  files, regenerated from their updated generators). Lakefile uses `globs`, no root files.
- The repo is now the working directory; `/home/user/proven` is retired.
- `Arm/proofs/check.sh` stages `Spec/Code.lean` / `Arm/CompilerArm.lean` instead of keeping copies.
- New `Testing/scripts/check.sh` (build, axioms vs `expected-axioms.txt`, forbidden-word grep).
