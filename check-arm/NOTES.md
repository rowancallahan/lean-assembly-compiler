# check-arm notes

## Task 1: independent build of committed armv9-lean (Lean 4.34.1, lean-sail v10)
Lean installed from the GitHub release tarball (elan from GitHub, toolchain extracted manually). 15 GB RAM + 12 GB swap.

- `lake build`: rc=0, 2436 s wall. 0 errors.
- `lake build Armv9.<M>` for all 34 `Armv9/*.lean`: all rc=0, 0 errors. Only `DecodeEnd` was not built by the default target (not imported by `Armv9.lean`): built in 1501 s per lake's own timer (3716 s wall for that command in my script; machine was otherwise idle apart from lake).
- Largest modules (lake timers): V8Base 2083 s, SysregsAutogen 1923 s, DecodeEnd 1501 s, Instrs64Sve 560 s, Instrs32 265 s, Instrs64 238 s, Instrs64Sme 237 s, Defs 96 s, Sysregs 22 s; all others < 6 s.
- `sorry` warnings: exactly one definition, `Armv9/V8Base.lean:72881:0` and `:72882:4` (the same declaration, `Reduce__1`; see below). No other `sorry` warnings in any module log.
- Olean check: 34 `.lean` files, 0 missing `.olean` under `.lake/build/lib/lean/Armv9/`.
- Result matches expectation (34 modules, 0 errors, one sorry).

## Task 2: regeneration reproducibility
Setup: apt `opam z3 libgmp-dev bubblewrap`; `opam init --bare --disable-sandboxing`; `opam switch create sail 5.1.1`; sail at ef5dca5ac + the patch (`git apply` clean); `opam install . --deps-only` + `make install` (4m21s); sail-arm at 5416ef6. `make gen_lean VERBOSE_FLAG=` run twice from fresh copies of the sail-arm tree (cold: 1336 s and 1277 s, both rc=0), each copied to its own directory.

- run1 vs run2: `diff -rq` empty; sha256 of sorted per-file sha256 list identical (`f0ad4151999e636689be75438ca1e80adad718d34835cd3e2e0566b5fe58fd0c`, 39 files incl. lakefile/toolchain/Armv9.lean).
- run1 vs committed `armv9-lean/` (excluding `.lake`, `lake-manifest.json`): identical. Same for run2. Same aggregate hash for committed tree.
- Result: regeneration is byte-identical.

regen.sh changes: the patch loop failed on re-run (`git apply` of an already applied patch, with `-e`); made it idempotent (`apply --reverse --check || apply`). Also note `eval $(opam env)` uses the current opam switch; I used a switch named `sail` (`opam env --switch=sail`). regen.sh was not run end to end (my gen.sh ran the same make steps); the idempotency edit is only syntax-checked (`sh -n`).

## Task 3: unpatched Sail comparison
Same sail commit (ef5dca5ac) with the patch reversed (`git status` clean), `make install`, then the same `make gen_lean` on sail-arm 5416ef6 (1321 s, rc=0). Compared with run1 (patched == committed).

Files that differ (11 of 39): `Builtins, DecodeEnd, Fetch, Instrs32, Instrs64, Instrs64Sme, Instrs64Sve, Prelude, Sysregs, SysregsAutogen, V8Base` (all under `Armv9/`). Identical: the other 23 `Armv9/*.lean` plus `Armv9.lean`, lakefile, toolchain.

The claim "only DecodeEnd.lean differs structurally" holds, but "small typing fixes" touch 10 other files, and DecodeEnd also carries them (so more than "small" by line count: ~67k differing diff-lines total, mostly DecodeEnd and SysregsAutogen):
- Two textual classes, mechanical:
  1. patched `(sailThrow (X) : SailM Unit)` vs unpatched `sailThrow (X)` (type ascription added).
  2. patched `let x ← (( do (E) ) : T )` / `(( do` + newline vs unpatched `let x ← (( (E) ) : T )` / `((`.
- Check: after normalising both classes with sed (`\(sailThrow (.*) : SailM Unit\)` -> `sailThrow \1`, `\(\( do \(` -> `(( (`), residual diffs are 0 in Builtins, Fetch, Instrs64Sme, Instrs64Sve, Prelude, Sysregs, SysregsAutogen, V8Base; 8 lines in Instrs32 and 4 in Instrs64 remain, which for Instrs64 I inspected: they are class 2 with `(( do` at end of line (`let fltval ← (( do` vs `let fltval ← ((`). Instrs32 residual was not inspected.
- DecodeEnd.lean structural: patched has 22 `_tail` identifiers (helper defs split out of `__DecodeA64_SVE`); unpatched has 0 (single large function; the diff spans ~29k lines). The unpatched DecodeEnd was not compiled by me, so I do not know whether it type-checks.
- Counts per file (differing diff lines): Builtins 2, DecodeEnd 29495, Fetch 10, Instrs32 4046, Instrs64 2962, Instrs64Sme 1260, Instrs64Sve 3004, Prelude 4, Sysregs 48, SysregsAutogen 26470, V8Base 160.
