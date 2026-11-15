# Book hints 2: directives for blocked fp-lean functions

Source: `leanprover/fp-lean` @0abeea5 (`examples/Examples/`), fetched shallow into the session scratchpad. Input: `BOOK_HINTS.md` §3 and `BOOK_SURVEY3.md` / `book_survey3.csv` on `origin/booksurvey3`.
Toolchain: Lean 4.29.0 (`lean-toolchain`). Build: `lake build Frontx` succeeded (exit 0). Sail model cloned to `../deps/sail-riscv-lean` (commit 51c635c).

## Result

| book row (file:line) | compiled | error without the directive (default command) |
|---|---|---|
| `ProgramsProofs/TCO.lean:33` `MoreClear.Tail.sumHelper` | **yes**, with `with` invariant in `Riscv/Frontx/BookExtra.lean` | `frontx: could not prove B[i].toNat + soFar < 2 ^ 64` (reproduced) |
| `Intro.lean:925` `evenLoops` | no, not attempted | n/a: the book's `#check_msgs` shows this failure on purpose |
| `Intro.lean:1009` `div` | no, not attempted | n/a: see below |
| `Intro.lean:1813` `sameLength` | no, not attempted | n/a: the book's `#check_msgs` shows this failure on purpose |

## Notes per row

**TCO.lean:33 (compiled).** The obligation is a running-sum bound, so the directive is a `with` invariant, not a `requires` clause as `BOOK_HINTS.md` §3 suggested. The directive is the one `ListExamples.lean:71-72` already uses for the same shape. Book text is `Examples/ProgramsProofs/TCO.lean:33-35` verbatim, with `soFar + 0` kept, inside `namespace Tail` (required by `frontx_view`). Compiled with the directive: `lake env lean Riscv/Frontx/BookExtra.lean` exit 0, no `sorry`, frontx success lines printed. Re-check of `TCO.lean:33`: confirmed as the `MoreClear` text, and the directive discharges the obligation.

**Intro.lean:925 `evenLoops`.** Not a missing directive. The book's body is `not (evenLoops n)` (no decreasing argument), and the book's `#check_msgs` block records the structural-recursion failure as the intended output. No directive keeps the book's meaning.

**Intro.lean:1009 `div`.** Not a clean directive. The book's own text is non-terminating at `k = 0`, so a `termination_by` or `with` measure needs a `0 < k` precondition, which changes the book's function. Not attempted.

**Intro.lean:1813 `sameLength`.** Not a missing directive. The first version is the book's deliberate failure (`#check_msgs`). The working versions are separate texts at `Intro.lean:1822` onward (`Both.sameLength`) and need no hint.

## Count

Qualifying functions (only a missing directive): 1 of the 4 candidates in `BOOK_HINTS.md` §3. Compiled: 1.

## Not changed

No existing compiler source was modified. The only new file is `Riscv/Frontx/BookExtra.lean`.
