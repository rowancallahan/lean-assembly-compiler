# Book survey: "Functional Programming in Lean" against the compiler

Source: `github.com/leanprover/fp-lean`, directory `examples/` (37 Lean files; book text not copied). Theorem Proving in Lean 4 was not taken
(priority was the FP book). Data: `book_survey.csv` (one row per definition), scripts and tests in `Testing/notes/book_tries/`.
Compiler state: branch `booksurvey` = `main` merged at the "PIPE.md: standard-library functions table" commit (has filter, find?, head?, ...).
Rows marked "before main pull" were first tried on the older `main`.

## Method and what to trust

1. `extract.py`: regex over `examples/**/*.lean`: every top-level `def/abbrev/instance` (1 821 declarations in total, 664 `def`); comments
   stripped; the same name repeated in several `ANCHOR` blocks is collapsed (column `variants`). 588 rows remain after dropping IO/monad-transformer
   definitions (`pure=false`, not in the CSV).
2. `classify.py` / `verdict.py` / `finalize.py`: signature + body regexes give types, recursion kind (none / structural / wf / mutual / fold-map / `Id.run` loop),
   allocation, strings, Float. **This classifier is heuristic.** Spot checks showed it over-counts "tagged data" and "higher-order" for monad-style
   definitions (`State`, `Reader`, ... are plain functions in the book) and mislabels some zero-argument definitions. Verdict **B and D rows marked
   `basis=curated` were checked by hand and tried**; all C rows come from the classifier alone and are an upper-bound reading
   ("some feature is missing"), not individually verified.
3. Verdict codes: A compiles as is; B compiles after restatement; C needs a roadmap feature (`needs` column); D Float/IO;
   X not a function (type, proposition, proof, Lean meta-code, non-terminating book example); K constant value with no input.
4. Pure only: IO and effects excluded (D or dropped). `Id.run do` counts as pure.

## Counts per verdict per chapter (rows of the CSV)

| chapter | A | B | C | D | K | X | total |
|---|---|---|---|---|---|---|---|
| 1 Getting to Know Lean | 0 | 31 | 47 | 6 | 7 | 5 | 96 |
| 2 Hello, World! | 0 | 0 | 3 | 0 | 4 | 0 | 7 |
| 3 Propositions, Proofs, Indexing | 0 | 0 | 6 | 0 | 4 | 5 | 15 |
| 4 Overloading and Type Classes | 0 | 0 | 113 | 0 | 2 | 2 | 117 |
| 5 Monads | 0 | 0 | 101 | 0 | 1 | 9 | 111 |
| 6 Functor, Applicative, Monad | 0 | 0 | 49 | 0 | 2 | 9 | 60 |
| 7 Monad Transformers | 0 | 0 | 35 | 0 | 5 | 3 | 43 |
| 8 Dependent Types | 0 | 0 | 84 | 0 | 0 | 8 | 92 |
| 9 Programming, Proving, Performance | 0 | 14 | 25 | 0 | 1 | 1 | 41 |
| support files | 0 | 0 | 0 | 0 | 0 | 6 | 6 |
| **total** | **0** | **45** | **463** | **6** | **26** | **48** | **588** |

Of the 463 C rows, 98 are `instance`s and 356 are `def`s. B rows are many *variants* of ~25 distinct functions (the book re-states `length`, `halve`,
`unzip`, ... in several namespaces).

**A = 0.** Every book function is over `Nat`/`Int`/`List α`/`String`/user types; none is over `BitVec 64`/`UInt8`/`List UInt8`, which are the types the front ends accept.

## Verdict B: what was tried (compiler output, first line)

`reify%` (expressions on `BitVec 64`), `compile%` (`List UInt8`), loops as hand-written `Stmt` with a source-level proof. `OK` = accepted; the machine
theorem comes from the compiler. Files `book_tries/r_*.lean`, `c_*.lean`, `l_*.lean`; runner `run_tries.sh`.

| book function | natural restatement | accepted? | mechanical restatement that works / bounds |
|---|---|---|---|
| `add1`, `Nat.double`, `triple`, `quadruple`, `plus` | `n + 1`, `x + x`, ... on `BitVec 64` | OK (`Nat` as is: `reify%: not a BitVec 64`) | same; all values `< 2^64`, no overflow |
| `timesTwelve` | `x * 12` | rejected: `unsupported subterm x * 12` | `(x <<< 3) + (x <<< 2)` written with `(k : BitVec 64).toNat % 64` shift amounts |
| `volume` (3 products) | `a * b * c` | rejected: `unsupported subterm` | none: needs multiply (C) |
| `maximum`, `minus` | `if a < b then b else a` | rejected: `unsupported subterm` | `if (if a < b then 1 else 0 : BitVec 64) = 0 then a else b` |
| `isZero` | `n == 0 : Bool` | rejected: `not a BitVec 64` | Bool as word: `if n = 0 then 1 else 0` |
| `pred`, `even` (`n &&& 1`), `halve` | `n >>> 1` | `halve` rejected (`unsupported subterm`) | `n >>> ((1:BitVec 64).toNat % 64)`; even/halve/plus/minus: the book definitions recurse on `Nat`, equality with the closed form is a lemma (not proved here, tested instead) |
| `times`, `div` (repeated subtraction) | `Stmt` loop | OK, **proved** (`l_times.lean`: `timesProg_exec`, `timesDown_eq`, `times_ok`; `l_div.lean`: `divProg_exec`) | `times`: `n * k < 2^64`, `a2 = 0` on entry; `div`: `k > 0`, `a2 = 0` on entry |
| `Tail.sum`, `NonTail.sum` (`List Nat`) | `xs.foldl (· + ·) 0` over `List Nat` | rejected: `unsupported result type Nat` | `List UInt8` input (elements < 256), `BitVec 64` accumulator, 8-byte result (`sum64`) |
| `Tail.length`, `NonTail.length`, `length` | `xs.length` | rejected on both mains: `unsupported result type Nat` | `BitVec.ofNat 64 xs.length` OK (`c_length_bv`) |
| `reverse`, `Tail/NonTail.reverse`, `take n`, `drop n` | library `List.*` with `α := UInt8`, `n` literal | OK; the book's own recursion is not accepted (`unsupported list expression`) | equality book def = `List.*` is a lemma (tested, not proved) |
| `Tail.filter`, `NonTail.filter` | `xs.filter (· > 3)` | rejected before the pull; **OK after** | predicate must be a literal lambda |
| `List.head?`, `final?` (`getLast?`), `findFirst?` (`find?`) | Option result | rejected before the pull (`a result of type Option UInt8 must be a List.foldl`); **OK after** | `Option UInt8` = `[0]` or `[1, v]` |
| `mergeSort` (book), `insertionSort` (book, `Array`) | `xs.mergeSort` | OK | `α = UInt8`, `Ord` = `≤`; book def equals `List.mergeSort` by uniqueness of the stable sort (lemma not proved); `Array` result type itself is rejected (`c_insertionSort_array`) |
| `append` (`xs ++ xs`), `zip`, `Array.map` | | rejected: `++ is supported with one constant side only`; `unsupported result type List (UInt8 × UInt8)`; `unsupported result type Array UInt8` | C |

## Three-way comparison (owner's addition)

For every curated B function: the ORIGINAL book definition executed by Lean (`#eval`; `partial`/`termination` proofs dropped only for `merge`/`mergeSort`/`insertionSortLoop`)
== RV64 code on QEMU == RV64 code on the Sail C emulator, and for the expression class also == AArch64 code on QEMU (`Arm.compile`).
Harnesses: `book_triple.lean` + `Testing/asm/triple.py` (expressions); `book_pipe2.lean` + `book_pipe_test2.py` (adapted `pipe_test.py`, new calling
convention: length in `a1`, scratch block, stack, checks that nothing outside the output/scratch/frame is written); `book_loops.lean` +
`book_triple_test.py` (`triple.py` with the AArch64 leg optional). Inputs include empty list, 0, 1, 255, `2^63`, `2^64-1` (clipped to the stated bounds), all-equal,
sorted, reversed, 64-element lists, random.

| function (book) | inputs | RV64 QEMU | RV64 Sail | AArch64 QEMU | mismatches |
|---|---|---|---|---|---|
| add1 / double / triple / quadruple / timesTwelve | 784 / 661 / 624 / 589 / 589 | = | = | = | 0 |
| maximum / isZero / pred | 829 each | = | = | = | 0 |
| even (recursive book def on ≤2000; `% 2` spec on full range) | 12 829 | = | = | = | 0 |
| halve (same split) | 12 829 | = | = | = | 0 |
| plus / minus (book def on small args; `+`/`-` spec on full range) | 4 261 / 4 429 | = | = | = | 0 |
| times (`btimes`: recursion on `k`) | 672 | = | = | no ARM generator yet | 0 |
| div (book `Div.lean` shape) | 557 | = | = | no ARM generator yet | 0 |
| sum64 vs `Tail.sum`, `NonTail.sum` | 310 each | = | = | no ARM generator yet | 0 |
| reverse vs `Tail.reverse`, `NonTail.reverse` | 310 each | = | = | no ARM generator yet | 0 |
| take 5 / drop 5 vs book `take`/`drop` | 310 each | = | = | no ARM generator yet | 0 |
| sort vs book `mergeSort`, book `insertionSort` (Array) | 310 each | = | = | no ARM generator yet | 0 |
| length vs `Tail.length`, `NonTail.length` | 310 each | = | = | no ARM generator yet | 0 |
| filter (`> 3`) vs `Tail.filter`, `NonTail.filter` | 310 each | = | = | no ARM generator yet | 0 |
| head? / final? / findFirst? (`> 3`) | 310 each | = | = | no ARM generator yet | 0 |

No real mismatch. One failure during development was an error in my test input (the loop programs read their accumulator `a2`, which must be 0; I had passed junk);
fixed in `book_loops.lean`, the counted runs are after the fix. Not covered: `Tail.factorial`, `volume` (multiply), everything C.
`Testing/notes/book_tries/pipe-words/` and `ctest` outputs are generated (words, spaces, expected outputs).

## Missing features, ranked by number of C rows that list them

("any" = row lists the feature among its gaps; "only" = it is the single gap. Heuristic, see method.)

| # | feature | any | only |
|---|---|---|---|
| 1 | tagged data / user structures and inductives (incl. Option/Prod/Sum encodings: 114 rows) | 314 | 87 (+3) |
| 2 | polymorphism by monomorphisation (`α`, `[Ord α]`) | 171 | 12 |
| 3 | higher-order by specialisation (monad-style, predicates, `map f`) | 135 | 3 |
| 4 | strings (`String`, `Char`) | 110 | 30 |
| 5 | calls + stack / non-tail recursion | 107 | 4 |
| 6 | allocator (new data in memory) | 79 | 0 |
| 7 | dependent types (Vect, Row, Fin n): not on the roadmap | 50 | 4 |
| 8 | big numbers (`Int`, unbounded `Nat`) | 36 | 1 |
| 9 | multiply-divide | 22 | 4 |
| 10 | two list inputs | 15 | 0 |

Most of 1/3 comes from the monad chapters (5-7): `State`/`Reader`/`Except` as function types. If those chapters are set aside, strings, polymorphism, calls+stack
and Option/Prod encodings dominate.

## The 20 closest functions (smallest gap)

| function (chapter) | what exactly it needs |
|---|---|
| `Tail.length`/`NonTail.length`/`length` (1, 9) | already B via `BitVec.ofNat 64 xs.length`; plain `Nat` result: output encoding of `Nat` as a word |
| `Tail.sum` on `List Nat` (9) | already B for bytes; `List Nat` input needs word arrays (8-byte elements) |
| `reverse`, `take`, `drop` on `List α` (1) | monomorphisation done by hand; book's own recursion not recognised by `compile%` (needs the equality lemma or recursion recognition) |
| `Tail.filter p` (9) | B; generic `p` needs specialisation |
| `List.head?`/`final?`/`findFirst?` (1) | B for `UInt8`; generic `α` needs monomorphisation |
| `Prod.switch` (1) | `Prod` result encoding (two words) |
| `fromOption` (1) | `Option` as an *input* encoding |
| `volume a b c` (1) | multiply in `reify%` (rejected: `unsupported subterm`) |
| `Tail.factorial` / `factHelper` (9) | multiply; loop shape already available (`times` proved) |
| `NonTail.factorial` (9) | multiply + non-tail recursion (calls + stack) |
| `sameLength`, `zip` (1) | two list inputs; `sameLength` returns Bool, `zip` a list of pairs |
| `unzip` (1) | list-of-pairs input, pair-of-lists output |
| `Array.find`/`findHelper` (9) | `Option (Nat × α)` result, `Array` input |
| `TailRec.Array.map` (9) | `Array` result type in `compile%` (`List` version accepted) |
| `merge`, `splitList` (9) | two list inputs (merge) / pair output (splitList) |
| `Weekday.isWeekend` (5) | enum inductive as a byte (smallest "tagged data") |
| `Pos`/`Even` `plus`/`add` (4) | structure around `Nat` (newtype) |
| `divOption` (5) | `Option Int` result, signed division |
| `spaceBetween`, `joinStringsWith` (1) | strings as byte lists, append |
| `BinTree.count` (3) | recursion on an inductive: calls + stack, tagged nodes |

## Good next clients (pure, small, one new feature each)

1. `sameLength` / `List.zip` — two list inputs (one feature; Bool result already supported).
2. `volume` / `Tail.factorial` — multiply in `reify%`/`AExp`; loop proof pattern exists (`l_times.lean`).
3. `Weekday.isWeekend` — first enum (tag = byte), no allocation.
4. `Prod.switch`, `fromOption` — pair / Option input encodings.
5. `merge` (book, `Ord UInt8`) — two sorted lists in, one out; exercises the second input block.
6. `NonTail.sum` / `NonTail.reverse` as written — non-tail recursion (calls + stack), depth bounded by the input.
7. `BinTree.count`/`mirror` on a prefix-encoded tree — recursion over an inductive (stack), matches the roadmap's tree evaluator.
8. `spaceBetween` — strings as bytes + append.
9. `Array.find` — `Option (Nat × UInt8)` result.
10. `div` with unbounded `Nat` — big numbers after the multiply/divide step.

## Findings about the compiler (from the tries)

- `reify%` only matches the exact operator forms listed in `Reify.lean`: `if a < b then 1 else 0`, `if c = 0 then y else x`, shifts by `b.toNat % 64`.
  Natural `if a < b then b else a`, `n >>> 1`, `n == 0`, `x * 12` are rejected with `unsupported subterm` (or `not a BitVec 64` for `Nat`/`Bool`); a rewriting pass
  over these forms would make most arithmetic book functions "A after restating types only".
- `compile%` does not accept `Nat` results (`unsupported result type Nat`); `BitVec.ofNat 64 xs.length` is the workaround.
- `compile%` does not recognise user-written recursion: book definitions need to be restated with library functions (equality lemmas are the missing piece, not code generation).
- No wrong code found: every accepted case agrees with the executed original on all inputs tried.
