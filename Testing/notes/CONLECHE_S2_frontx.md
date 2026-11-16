# CONLECHE_S2: con-leche batch functions with `number % 4 == 2` through `frontx_ind`

Status: **not completed.** No function has a gate result or a compile result. No tests were added.

## Setup (done)

- Toolchain leanprover/lean4:v4.29.0 (elan). Build cache restored to `../deps/sail-riscv-lean` from `origin/build-cache`.
- `lake build Frontx` on main `f37e21b`: completed, 301 jobs, no errors.
- Test harness blocked: `Testing/asm/frontx_test.py` needs the Sail simulator at `/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim` and asserts `SUCCESS` from it. That binary is not in this environment and the GitHub release download is refused by the proxy (403). QEMU (`qemu-system-riscv64`) and `riscv64-linux-gnu-gcc`/`nm` were installed via apt. `ctest` was never created, so nothing to delete.

## Inputs

- `batchA.lean`: not on `origin/conleche-batch-b`. Used `origin/conleche-batch-b2` (883 lines, later fix-up commit that adds 5 missing definitions). `origin/conleche-batch-a` (840 lines) is the earlier version.
- `batchB.lean`: `origin/conleche-batch-b`.
- Numbering: the 257 `-- frontx_ind` markers, batch A first (27), then batch B (230), 1-based in file order. Numbers with `n % 4 == 2` give 64 targets: 2, 6, 10, …, 254 (A: `Expr.bvarBRaw`, `Expr.probeHit`, `Expr.beqGoX`, `Expr.hasFvar`, `Expr.abstract1`, `Expr.binderPair?`, `Expr.piResult`; B: from `Expr.piSortTeleLen?` through `Cached.classReadMinorC`).

## Why the port stops

Assembling `Riscv/Frontx/ConLecheS2.lean` as batch A body + batch B body, after `import Riscv.Frontx.ExprExamples`, gives about 101 elaboration errors (the compiler hit its 100-error limit). Causes:

1. **Missing instances.** The batch copies leave out non-function declarations they depend on. `Expr.beq` (batch A line 19) uses `decide (a = b)`, but no `DecidableEq Expr` exists in the copy. The source (`origin/conleche-depth`, `Testing/conleche-depth/out/F2.lean.txt`) has `instance : DecidableEq Expr := Expr.decEq` at line 1696, plus `DecidableEq Name` (157), `DecidableEq Level` (553) and `DecidableEq Literal` (604). Those depend on the memoized `decEq` / `decEqPtr` machinery (`withPtrEqDecEq`, `csimp` lemmas), which the batches do not contain. Any target that uses equality on these types fails.
2. **Duplicates with imports.** `ConLeche.satRange`, `bvarOfData`, `fvarOfData`, `lpOfData` are defined by `ScalarExamples` (imported by `ExprExamples`) and by the batch copies. `instantiate1`, `hasFvar`, `piResult`, `getAppFn`, `fvarTypeD` are defined by `ExprExamples.lean` and by batch A. `piResult` (#26) is already compiled with `frontx_ind` in `ExprExamples.lean:247`.
3. **Batch A and batch B clash.** Both define `bvarOfData`, `fvarOfData`, `lpOfData` (A: lines 62-70; B: lines 1354, 3780, 5260). They cannot be concatenated verbatim into one file.

No target was gated, so the gate and compile columns are empty for all 64. The draft (does not elaborate) is `Testing/conleche-batches/ConLecheS2.draft.lean`, outside `Riscv.Frontx` so the `Frontx` lake glob does not pick it up.

## Options to finish

- Add the `DecidableEq` chain for `Name`, `Level`, `Literal`, `Expr` verbatim from F2 (lines ~82–160, 479–605, 1696–1725 and their helpers). This pulls in the pointer-equality machinery and is the bulk of the work.
- Or restrict the batch to targets that do not use equality on these types, and drop the duplicate blocks from B, with a note of each removal.
- Provide the Sail simulator (path above) or a way to install it, so `frontx_test.py check` can run.
