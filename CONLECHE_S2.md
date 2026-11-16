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
