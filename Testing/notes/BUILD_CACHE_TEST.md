# Build cache test

Branch: `build-cache-test`. Toolchain: `leanprover/lean4:v4.29.0`. Target: `lake build Frontx`.

## Setup

- elan installed from `raw.githubusercontent.com/leanprover/elan`; `zstd` installed via apt.
- Restored `origin/build-cache:sail-riscv-lean.tar.zst` into `../deps` (0.3 s). Result: `../deps/sail-riscv-lean` with `.lake/build` (LeanRV64D oleans) and `.lake/packages/Sail` (git checkout at `079463134b9c50450b8393e1566a09fc492a34d9`).
- No `Riscv.Steps.Gen` module exists; used `lake build Frontx`.

## Results

- Exit code 0. Wall time **15m 1s** (user 36m 15s, 4 cores).
- Jobs: 100 modules built (`✔`), 32 warnings, 0 errors.
- Built by package: Riscv 58, Compiler 29, Sail (lean-sail) 8, Spec 5.
- **`Lean_RV64D` / `LeanRV64D` was NOT rebuilt.** No line in the build log mentions it.
- The Sail package was rebuilt: lake printed `Sail: cloning https://github.com/rems-project/lean-sail` and built 8 `Sail.*` modules (~1–2 s each).
- Re-running `lake build Frontx` immediately afterwards: no-op, 0.5 s.

### 10 slowest modules (from the log)

| # | Module | Time |
|---|---|---|
| 1 | Riscv.Steps.GenMem | 139 s |
| 2 | Riscv.Steps.GenALU | 79 s |
| 3 | Riscv.Steps.GenBranch | 52 s |
| 4 | Riscv.Steps.Regs | 34 s |
| 5 | Riscv.Steps.GenMul | 30 s |
| 6 | Riscv.Steps.Step | 27 s |
| 7 | Riscv.Back.Implements1 | 19 s |
| 8 | Riscv.Steps.GenTac | 16 s |
| 9 | Compiler.CStmt | 14 s |
| 10 | Riscv.Frontx.IndCmd | 12 s |

## Why the dependency was not rebuilt

- `Lean_RV64D` is a path requirement (`../deps/sail-riscv-lean`), and its build output in `../deps/sail-riscv-lean/.lake/build` was reused. The restore is what avoided the rebuild.
- The transitive `Sail` requirement was **not** reused from the cache. Lake resolves it into the root workspace at `.lake/packages/Sail` (absent after restore), so it cloned from GitHub and rebuilt. The copy at `../deps/sail-riscv-lean/.lake/packages/Sail` is ignored by the root workspace.
- The bulk of the 15 minutes is this repo's own modules (100 of 100 built). The tarball does not contain root `.lake/build`, so that is expected.

## What the cache must contain for a full skip

1. `../deps/sail-riscv-lean/.lake/build` (present; reused).
2. `.lake/packages/Sail` at the repo root, including `.lake/build` for lean-sail at rev `079463134b9c50450b8393e1566a09fc492a34d9` (absent; only 8 small modules, so the cost is minor).
3. Optional: root `.lake/build` for Spec/Compiler/Riscv (absent; this is where ~all the 15 minutes go).

Restoring item 2 requires the root-level path, not the dependency-level one. Tarballs written from `../deps/sail-riscv-lean` alone do not satisfy it. The README's claim that the cache rebuilds "only this repo's own modules" holds for `LeanRV64D`, but the transitive Sail package still gets rebuilt.

## Not verified

- Whether restoring item 2 alone would stop the Sail rebuild. Not tested.
- Whether the `Spec.Riscv` rebuild stems from the root build being empty or from a changed LeanRV64D trace. The log cannot distinguish these; `LeanRV64D` was not rebuilt, so the first reason is more likely.
