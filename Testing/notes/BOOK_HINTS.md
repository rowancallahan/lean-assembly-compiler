# Book hints: text-only findings from BOOK_SURVEY3

Input: `Testing/notes/BOOK_SURVEY3.md` and `book_survey3.csv` on `origin/booksurvey3` (6f14285).
Status: text-only. No Lean run was made: this container has no Lean 4.29.0 toolchain, and a probe of the toolchain host was denied by the permission check. So `Riscv/Frontx/BookExtra.lean` is not created and no directive is verified.

## 1. The four rows that no longer compile

Survey 2 listed 38 rows as compiled (15 machine-thm, 23 source-thm). Survey 3 compiles 34. Missing:

| book row | survey 3 result (CSV, truncated) | verdict |
|---|---|---|
| `Intro.lean:1009` `div` (source-thm) | not run: `fail to show termination for Proven.Frontx.Run.div ... Not considering parameter k` | Harness difference. Lean rejects the verbatim book text before the compiler runs. The compiler's own `div` (`BookExamples.lean:85-93`) is a different text (`termination_by n`, `decreasing_by omega`). |
| `Intro.lean:2081` `Match.Oops.halve` (source-thm) | not run: `Invalid pattern(s): n is an explicit pattern variable, but it only occurs in positions that are inaccessible` | Harness difference. Lean elaboration error in the verbatim text (book's `Oops` example). Not a compiler failure. |
| `Intro.lean:2489` `Oops.List.findFirst?` (machine-thm) | not run: `expected token` | Harness difference. Parse error on a one-line range (2489-2489), which suggests the extractor cut the def short. Check the extracted text before reading anything into it. |
| `ProgramsProofs/TCO.lean:33` `MoreClear.Tail.sumHelper` (machine-thm) | blocked: `could not prove B[i].toNat + soFar < 2 ^ 64` | Not a Lean issue: the compiler's own proof obligation fails. The CSV puts it in the "Array of non-bytes" bucket, which is wrong. The missing piece is a precondition bounding the running sum (a `requires` clause), see §3. `MoreClear` appears nowhere in `ce989e1` or `main`. The nearest committed def is `ListExamples.lean:65-71` (`sumHelper`, `frontx_view` with a `measure`, at `ce989e1`), which is a different text. Survey 2's "compiled" is therefore not backed by a committed directive. Treat as unverified, not as a confirmed compiler regression. |

Net: no confirmed compiler regression among the four. Three are verbatim book text Lean rejects, and one is a precondition failure whose survey-2 evidence is not in the tree.

## 2. Survey baseline is not current `main`

- Survey 3 ran against `ce989e1`. That commit is not an ancestor of `origin/main` (42a74eb).
- `origin/main` has no `Riscv/Frontx/` directory. `ce989e1` has 41 files there; `git diff ce989e1 origin/main -- Riscv/Frontx` shows 41 deleted files, 15 003 lines.
- Consequence: the 29 "compiled on main (hand directive)" rows cannot be checked against current `main`. Their directives live in files that are gone from `main`.

## 3. Blocked rows whose failure is only a missing hint

Ranked smallest first (by line span in the book file). Each row is blocked or not run because a termination or proof obligation needs a hint. None of them needs a missing language feature.

| rank | book row (file:line) | span | missing hint | survey 3 message |
|---|---|---|---|---|
| 1 | `ProgramsProofs/TCO.lean:33` `MoreClear.Tail.sumHelper` | 3 lines | `requires` bound on the running sum (the sum of byte values can exceed `2^64` once `soFar` is unbounded) | `could not prove B[i].toNat + soFar < 2 ^ 64` |
| 2 | `Intro.lean:925` `evenLoops` | 4 lines | `with` measure, or a `termination_by`-style hint | `fail to show termination ... Not considering parameter n` |
| 3 | `Intro.lean:1009` `div` | 4 lines | `with` measure. Note: as written it is not terminating (`k` may be `0`), so a hint changes the book's meaning; this is not a verbatim compile | `fail to show termination ... Not considering parameter k` |
| 4 | `Intro.lean:1813` `sameLength` | 5 lines | `with` measure on the list length; the book's `sameLength` takes two lists with a polymorphic `α`, `β` | `fail to show termination ... Not considering parameter α` |

Not counted (the message does not show a missing hint):

- `ProgramsProofs/Inequalities.lean:15` `merge`: `frontx_view: cannot reduce match`. Could be a view or wrapper issue; not decided from the message.
- `ProgramsProofs/Inequalities.lean:767` `mergeSort`: `frontx_view: the body is not a match`. Could be a wrapper entry; not decided from the message.

Compiler-side reference for the `requires` shape: `BookExamples.lean:152` (`divAt requires fun _ i => i + 8 < 2 ^ 64`) at `ce989e1`. It is not in `main`.

## 4. Directive attempts

Not run. Four rows qualify (§3), so the "up to 10" limit is not reached. Each attempt needs Lean 4.29.0 and the Sail model build, which this container does not have. Outcome: unknown for all four.

## Reproduce / next step

With a Lean toolchain and `fp-lean` at 0abeea5: add the directive for each §3 row in `Riscv/Frontx/BookExtra.lean` against the verbatim book text (cited by file:line), then `lake env lean` on the file. Accept only if the compiler's success line prints with no `sorry`.
