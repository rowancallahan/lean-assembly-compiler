# CONLECHE_S2 status

## Setup

| Step | Result |
|---|---|
| 1. `git fetch origin build-cache main` | done |
| 2. `git show origin/build-cache:sail-riscv-lean.tar.zst \| zstd -dc \| tar xf - -C ../deps` | **FAILED** |
| 3. sailsim extraction to /home/user/deps | not attempted (stopped at step 2 failure) |
| 4. `git merge origin/main` | not attempted |
| 5. elan install + `lake build Frontx` | not attempted |

Exact error (step 2; step 3 fails identically):

```
/bin/bash: line 1: zstd: command not found
tar: This does not look like a tar archive
tar: Exiting with failure status due to previous errors
```

`which zstd` returns nothing in this container. The downloaded archive `/tmp/s.tar.zst` was not decompressed.

## Targets

Not started. No functions were gated, compiled, emitted, or tested.

## Resume attempt

Parent session said to run `apt-get install -y zstd` and redo setup from step 2. The install was **denied** by the auto-mode permission classifier (`Bash` apt-get install), so no zstd was installed. Steps 2–5 remain blocked. Also not attempted: `git merge origin/main`, restoring `repo-build.tar.zst.part-*`, `qemu-system-misc`, and all target work.

To unblock: allow `apt-get install -y zstd` (or pre-install zstd in the container), then rerun from step 2.

## Session update (resume, gzip cache)

Setup, now complete:

| Step | Result |
|---|---|
| 1. fetch build-cache, main | done |
| 2. sail-riscv-lean (`.tar.gz`, gzip copy) | done |
| 3. sailsim (`.tar.gz`) | done; `sail_riscv_sim --help` runs |
| 4. `git merge origin/main` | done (main caa4cee-era, fast) |
| 5. elan installed; `lake build Frontx` | done, "Build completed successfully (311 jobs)" |
| repo-build parts (`.tar.gz`) | extracted; `.lake/build` present |
| `apt-get install -y zstd` | not needed after switch to gzip; the earlier install was denied and not retried |

Batch inputs: `batchA.lean` is on `origin/conleche-batch-a` (840 lines, 27 targets). `batchB.lean` is on `origin/conleche-batch-b` (230 targets). Numbering used: 1-based, A then B, 257 targets; slice = numbers ≡ 2 (mod 4), 64 targets (2, 6, …, 254).

Port state (not advanced this session):

- `Testing/conleche-batches/ConLecheS2.draft.lean` elaborated with `lake env lean` on the merged main: **101 errors** (hit the 100-error limit). Same blockers as the earlier note: missing `DecidableEq` chain (Expr, Name, Level, Literal) from F2; duplicate `satRange`, `bvarOfData`, `fvarOfData`, `lpOfData` (already in `ScalarExamples`); A/B duplicate definitions; `hasFvar`, `piResult`, `getAppFn`, `fvarTypeD` already in `ExprExamples`.
- Gate (`frontx_ind_gate`): **not run**, because the file does not elaborate, so the gate has no context to run in.
- Compile, emit, and `frontx_test.py check 50`: **not run**.

Next step: build `Riscv/Frontx/ConLecheS2.lean` on `import Riscv.Frontx.ExprExamples` with the verbatim `DecidableEq` chain from `origin/conleche-depth` `Testing/conleche-depth/out/F2.lean.txt` (~lines 82–160, 479–605, 1696–1725), removing the duplicate defs, then gate the 64 targets.

## Port attempt 2 (fresh ConLecheS2.lean)

- `Riscv/Frontx/ConLecheS2.lean` now imports `ExprExamples` (reuses Expr/Name/Level/Literal, satRange, bvarOfData, etc.). Only one block so far: batch B #3 `Expr.piSortTeleLen?`, verbatim, body shortened to its definition (doc comment removed).
- Gate: `frontx_ind_gate ConLeche.Expr.piSortTeleLen? on TExpr` → **gate FAIL: frontx_ind: unsupported result type `Option Nat`**. Not compiled, no emit, no test.
- Full batch B (230 blocks, slice 2 lines un-commented, rest commented out, imports as above) elaborates with **101 errors**. Causes:
  1. Gate names are written without the `ConLeche.` prefix once the namespace has closed (`Unknown constant Expr.piSortTeleLen?`). Every slice target needs its full name.
  2. `ConLeche.Expr.numArgs` duplicates the one in `ExprExamples`.
  3. Callees missing from the slice are not defined in the file: `pi`, `cnst`, `piA` (BasisDSL / Builder), `quotName`, `quotSoundName`, `natZeroName`, `listNilName`, `charOfNatName`, `eqRecMotive`, `quotRel`, `lamProj?`. The note's "callees" column does not list all of these, so it cannot be used as the dependency closure.
  4. Batch A's targets (A is a separate file, not included here) and the `DecidableEq` chain are not in the file, so the Expr-equality targets are not testable yet.
- Leaf-only probe (no-callee targets alone): all failed at unknown names of the same kind; no gate passed or ran.
- Status: 0 of 64 targets gated successfully, 0 compiled, 0 tested. Remaining work is (a) build the full dependency closure of each slice target verbatim (following real references, not the note's callee column), (b) add the `DecidableEq`/`beqMemo` chain from F2 (lines 1166–1730, plus `ptrDecEq` at F2:37), (c) qualify gate names.

## Slice 2 result (narrowed run, 90-minute budget)

Slice 2 = batch numbers ≡ 2 (mod 4) over A (27) then B (230), 257 total, 64 targets. Filter applied per parent: fully qualified gate names, skip names on main, self-contained only, skip `Option` results.

Self-contained candidates (not on main, no missing callees): 13 gated. Results:

| # | Function | Gate | Compiled | Tests |
|---|---|---|---|---|
| 2 | `ConLeche.Expr.bvarBRaw` | ok; arms FAIL: "equation has no constructor pattern" | no | pending |
| 18 | `ConLeche.Expr.abstract1` | FAIL: more than one scalar parameter | no | pending |
| 22 | `ConLeche.Expr.binderPair?` | FAIL: unsupported result type (Option/pair) | no | pending |
| 34 | `ConLeche.lamProj?` | FAIL: unsupported result type (Option) | no | pending |
| 42 | `ConLeche.quotName` | FAIL: no argument of a declared type (a constant) | no | pending |
| 74 | `ConLeche.sameConstHeads` | ok; arms FAIL: pattern on another argument | no | pending |
| 98 | `ConLeche.natOpName` | ok; arms FAIL: no constructor pattern; also unknown `natOpNames`, `natDivModNames` (needs closure) | no | pending |
| 106 | `ConLeche.etaProjs` | ok; arms FAIL: no constructor pattern | no | pending |
| 110 | `ConLeche.openPisAtFvars` | FAIL: more than one scalar parameter | no | pending |
| 130 | `ConLeche.structProjArgP` | ok; arms ok | FAIL: `ConLeche.Expr.proj has no equations` | pending |
| 186 | `ConLeche.Expr.isCompound` | ok; arms ok | **yes** | pending (see below) |
| 198 | `ConLeche.Expr.isCompoundF` | ok; arms ok | **yes** | pending (see below) |
| 230 | `ConLeche.Cached.sameConstHeadsC` | ok; arms FAIL: pattern on another argument | no | pending |

Compiled targets (2): `Riscv/Frontx/ConLecheS2.lean` builds (`lake build Riscv.Frontx.ConLecheS2`, exit 0). Verbatim blocks, provenance `batchB.lean` lines for each; no duplicates on main.

Cases emitted: `Testing/asm/emit_conleche_s2.lean` (imports `ConLecheS2`, helpers copied from `emit_expr.lean` lines 1–78) → `Testing/asm/frontx-words/conleche_iscompound.{words,cases}` and `conleche_iscompoundf.{words,cases}`, 60 cases each.

Tests: **pending**. `frontx_test.py check 50 conleche_iscompound` and `…conleche_iscompoundf` fail while building the test driver: `riscv64-linux-gnu-gcc` is not installed (`which` finds no gcc/QEMU), and installing it is denied. The Sail simulator is present (`sail_riscv_sim --help` runs), but the harness builds the RISC-V driver first, so the Sail half cannot run either. `Testing/asm/ctest` deleted after each run.

Needs closure (not attempted; not self-contained): the remaining slice targets, for example `Expr.beqGoX`, `Expr.probeHit`, all `Expr` equality users (main has no `DecidableEq Expr`), the `natName`/`quotName` naming chain, the `Cached.*` functions with CheckCM/CState callees, and the `BasisDSL` ones (`trueName`, `reduceBoolName`, `quotRel`, `eqRecMotive`).
