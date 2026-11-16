# HARVEST

Branch `harvest` = `origin/main` + the pieces below. `lake build Frontx` succeeds (no errors, no `sorry`). No tests were run (no QEMU here); the test status column is what each source branch recorded.

## Included

| File | Functions | Source branch | Test files | Test status (per source branch) |
|---|---|---|---|---|
| `Riscv/Frontx/MixHash.lean` | `MixHashPort.mixHashLean`, `Proven.WA.MixHash.fuzzRun`, `mixHashE` | `mixhash-port` (merged) | `Testing/asm/emit_wa.lean` entry, `frontx-words/wa_mixhash.{words,cases}` | not run here |
| `Riscv/Frontx/BookExtra.lean` | `MoreClear.Tail.sumHelper` (book text), `Tail.sumHelper` with `frontx_compile` invariant | `book-hints2` (merged) | none | not run here |
| `Riscv/Frontx/ConLecheS1.lean` | `Expr.beqIsApp`, `Cached.whnfCoreEasy` | `conleche-s1` | `Testing/asm/emit_conleche_s1.lean`, `frontx-words/expr_beqisapp.*`, `cached_whnfcoreeasy.*` | QEMU 50/50 each; Sail not run |
| `Riscv/Frontx/ConLecheS2.lean` | `Expr.isCompound`, `Expr.isCompoundF` | `conleche-s2` | `Testing/asm/emit_conleche_s2.lean`, `frontx-words/conleche_iscompound.*`, `conleche_iscompoundf.*` | cases emitted, **not run** (branch: no RISC-V gcc / Sail) |
| `Riscv/Frontx/ConLecheS3.lean` | `classBinder`, `Cached.whnfEasy` | `conleche-s3` | `Testing/asm/emit_conleche_s3.lean`, `frontx-words/s3_classbinder.*`, `s3_whnfeasy.*` | `check 50` passed on QEMU and Sail (branch note) |
| `Riscv/Frontx/BookS1.lean` | `Finite.isSingleton` (namespace `Proven.Frontx.BookS1.R320`) | `book-s1` | `Testing/asm/emit_books1.lean`, `frontx-words/finite_issingleton.*` (11 cases) | **pending**, not run |
| `Testing/scripts/axioms_harvest.lean` | `#print axioms` for the 7 `implements1` theorems of ConLecheS1/S2/S3 and BookS1 | new | — | all 7 print with no `sorryAx`; only the project's usual Sail extern axioms, `propext`, and the Lean core axioms |

`ConLecheS2` and `BookS1` also contain `frontx_ind` probe lines; `BookS1` also keeps two probe lines (`#eval IO.println "@@MARK@@"`, `#check`) from the branch.

## Left out

- **`conleche-s0` (8 functions: `beqRecursive`, `hasFvar`, `piResult`, `numArgs`, `isLit`, `depth`, `isCompound`, `whnfCoreKeyC`)**: not produced. The branch file is a 22k-line dump of the whole con-leche development (`Testing/conleche-depth`), with 44 elaboration errors in the dump region, and `Riscv/Frontx/ConLecheS0.lean` on that branch breaks `lake build Frontx`. I tried extracting a dependency closure of the 8 targets: `ConLeche.Expr` has computed fields and its `BeqSt`/`Display`/`Level` machinery reaches about 1,200 declarations (~17k lines). That closure still fails with unknown names from `open`-style unqualified use (`uN`, `pi`, `rule`, ...) and with missing instances, and it hits the dump's own errors. Making it error-free means editing con-leche code, which the rules forbid. Not included: the S0 `.words`/`.cases` files, `teleArityOk` (compiled, but no test) and all other S0 entries.
- **`conleche-s0` isCompound vs `conleche-s2` isCompound**: different types. S0's `ConLeche.Expr` (dump) is not `ConLeche.Expr` of `ExprExamples`. Same name, different type, so they can't be merged. Only the S2 version is in harvest. Any module importing both `ExprExamples` and a dump-based S0 file would clash.
- **`book-s2` (`BookS2.lean`: `EarlyReturn.Non.List.find?`, `EarlyReturn.List.find?`, `findHelper`, `Array.find`, entries `nonFindGt3`, `findGt3`, `arrFindGt3`)**: dropped as a duplicate. `Riscv/Frontx/HofExamples.lean` on main already defines the same code (namespace `Proven.Frontx.Hof`), with `frontx_hof_entry` and the `hof_nonfindgt3`, `hof_findgt3`, `hof_arrfindgt3` tests. Keeping both would duplicate definitions. Its `results_s2.json` and the notes stay on `book-s2`.
- **`conleche-s1` / `conleche-s3` / `conleche-s2` / `book-s1` notes, diagnostic logs, `make_*.py`, `.draft.lean`, probe dumps**: not included. Only Lean files and the test emitters, words and cases.
- **`mixhash-port` `MIXHASH_PORT.md`**, **`book-hints2` `BOOK_HINTS2.md`**: included with their merges (docs only).

## Notes for the parent

- `Testing/scripts/check.sh`: add `axioms_harvest.lean`.
- The emitters write into `Testing/asm/frontx-words/`; `frontx_test.py check 50 <name>` for each new case set (`conleche_iscompound`, `conleche_iscompoundf`, `s3_*`, `expr_beqisapp`, `cached_whnfcoreeasy`, `finite_issingleton`, `wa_mixhash`).
- Each emitter runs with `lake env lean <file>` (their headers say so).
