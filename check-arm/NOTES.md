# check-arm notes

## Task 1: independent build of committed armv9-lean (Lean 4.34.1, lean-sail v10)
Lean installed from the GitHub release tarball (elan from GitHub, toolchain extracted manually). 15 GB RAM + 12 GB swap.

- `lake build`: rc=0, 2436 s wall. 0 errors.
- `lake build Armv9.<M>` for all 34 `Armv9/*.lean`: all rc=0, 0 errors. Only `DecodeEnd` was not built by the default target (not imported by `Armv9.lean`): built in 1501 s per lake's own timer (3716 s wall for that command in my script; machine was otherwise idle apart from lake).
- Largest modules (lake timers): V8Base 2083 s, SysregsAutogen 1923 s, DecodeEnd 1501 s, Instrs64Sve 560 s, Instrs32 265 s, Instrs64 238 s, Instrs64Sme 237 s, Defs 96 s, Sysregs 22 s; all others < 6 s.
- `sorry` warnings: exactly one definition, `Armv9/V8Base.lean:72881:0` and `:72882:4` (the same declaration, `Reduce__1`; see below). No other `sorry` warnings in any module log.
- Olean check: 34 `.lean` files, 0 missing `.olean` under `.lake/build/lib/lean/Armv9/`.
- Result matches expectation (34 modules, 0 errors, one sorry).
