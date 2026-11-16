# BOOK_S1: first third of the survey's blocked rows, retried on current `main`

Source: `Testing/notes/book_survey3.csv` (branch `booksurvey3`), book `fp-lean` @0abeea5. Base: `book-s1` = `origin/main` merged in
(main has `frontx_hof`, `frontx_monad`, NOTES §25–§29). Prebuilt `repo-build` restored; `lake build Frontx` succeeds.

Files:
- `Riscv/Frontx/BookS1.lean`: the rows that compile (1 row, `Finite.isSingleton`). Only this file is in the `Frontx` glob, so it is the only one built.
- `Testing/notes/book_s1/BookS1.lean`: all 67 rows (verbatim, one namespace block each), not built: 66 of them fail, and a failing block would break `lake build Frontx`.

## Population and result

- Sorted example files: 33 (`Examples.lean`, `Examples/*.lean`). First third = the first 11.
- Blocked rows in them: 67. Compile on current main: **1** (`Finite.isSingleton`, `frontx_ind`).
- Tried per row: the signature's command (`frontx_ind` / `frontx_view`+`frontx_compile` / `wa_compile` / `frontx_compile`), plus `frontx_hof` and `frontx_monad` where the signature fits.
- `frontx_hof` on a generic row (`foldMap`, `Vect.*`, `flatMap`, `seq`, …) fails with "universe polymorphic" or "no call with a known function argument". Those rows need a hand-written entry (`frontx_hof_entry` as in `HofExamples.lean`), which is not a verbatim retry, so I did not write one.
- Not run: `frontx_test.py check 50 Finite.isSingleton`. QEMU is not installed (`apt-get install qemu-system-misc` was denied by the auto-mode classifier), so no test cases were added and `Testing/asm/ctest` was not created.

## Per-row result

| row | file:line | command | first error (or result) |
|---|---|---|---|
| Argh.posToString | Examples/Classes.lean:240 | frontx_ind | frontx_ind: unsupported result type |
| addNatPos | Examples/Classes.lean:757 | frontx_ind | frontx_ind: Nat.brecOn has no argument of a declared type (also tried hof) |
| addPosNat | Examples/Classes.lean:761 | frontx_ind | frontx_ind: Nat.brecOn has no argument of a declared type (also tried hof) |
| NonEmptyList.toList | Examples/Classes.lean:961 | frontx_ind | frontx_ind: List.cons has no equations |
| NonEmptyList.get? | Examples/Classes.lean:989 | frontx_ind | frontx_ind: unsupported result type (also tried hof, monad) |
| UseList.NonEmptyList.get? | Examples/Classes.lean:997 | frontx_ind | frontx_ind: Proven.Frontx.Run.UseList.NonEmptyList.get?.match_1 has no equations (also tried hof, monad) |
| NonEmptyList.inBounds | Examples/Classes.lean:1004 | frontx_ind | frontx_ind: unsupported result type |
| NonEmptyList.get | Examples/Classes.lean:1010 | frontx_ind | frontx_ind: Proven.Frontx.Run.NonEmptyList.get.match_1 has no equations |
| hashPos | Examples/Classes.lean:1245 | frontx_ind | frontx_ind: unsupported term (also tried hof) |
| hashBinTree | Examples/Classes.lean:1270 | frontx_ind | frontx_ind: unsupported term (also tried hof) |
| concat | Examples/Classes.lean:1442 | frontx_ind | frontx_ind: unsupported parameter type |
| String.separate | Examples/Classes.lean:1636 | frontx_view + frontx_compile | frontx_view: unsupported element type |
| dropDecimals | Examples/Classes.lean:1671 | frontx_compile | unknown free variable `_fvar.1453` |
| listMonoid | Examples/Classes.lean:1737 | frontx_ind | frontx_ind: Proven.Frontx.Run.Monoid.mk has no equations |
| MMM.foldMap | Examples/Classes.lean:1743 | frontx_ind | frontx_ind: unsupported parameter type (also tried hof) |
| foldMap | Examples/Classes.lean:1759 | frontx_ind | frontx_ind: unsupported parameter type (also tried hof) |
| Even.Even.mul | Examples/Classes/Even.lean:32 | frontx_ind | frontx_ind: nested patterns are not supported (Proven.Frontx.Run.Even.Even.mul.eq_2) (also tried hof) |
| Other.Even.add | Examples/Classes/Even.lean:96 | frontx_ind | Type mismatch (also tried hof) |
| natOrStringThree | Examples/DependentTypes.lean:6 | frontx_compile | frontx: unsupported result type |
| Vect.replicate | Examples/DependentTypes.lean:228 | frontx_ind | type expected, got |
| Extras.List.replicate | Examples/DependentTypes.lean:237 | frontx_view + frontx_compile | frontx_view: no list parameter |
| Vect.zip | Examples/DependentTypes.lean:274 | frontx_ind | type expected, got (also tried hof) |
| Details.Vect.zip | Examples/DependentTypes.lean:329 | frontx_ind | type expected, got (also tried hof) |
| Vect.map | Examples/DependentTypes.lean:347 | frontx_ind | type expected, got (also tried hof) |
| Vect.zipWith | Examples/DependentTypes.lean:351 | frontx_ind | type expected, got (also tried hof) |
| Vect.unzip | Examples/DependentTypes.lean:355 | frontx_ind | type expected, got (also tried hof) |
| Vect.push | Examples/DependentTypes.lean:362 | frontx_ind | type expected, got (also tried hof) |
| Vect.drop | Examples/DependentTypes.lean:366 | frontx_ind | type expected, got (also tried hof) |
| Vect.reverse | Examples/DependentTypes.lean:370 | frontx_ind | type expected, got (also tried hof) |
| Vect.take | Examples/DependentTypes.lean:375 | frontx_ind | type expected, got (also tried hof) |
| DBType.asType | Examples/DependentTypes/DB.lean:10 | frontx_ind | frontx_ind: unsupported result type (also tried hof) |
| DBType.beq | Examples/DependentTypes/DB.lean:39 | frontx_ind | frontx_ind: unsupported parameter type |
| Row | Examples/DependentTypes/DB.lean:84 | frontx_compile | frontx: unsupported result type (also tried hof) |
| Table | Examples/DependentTypes/DB.lean:104 | frontx_compile | frontx: unsupported result type |
| Row.bEq | Examples/DependentTypes/DB.lean:167 | frontx_compile | frontx: unsupported parameter type |
| Row.get | Examples/DependentTypes/DB.lean:193 | frontx_ind | type expected, got |
| Subschema.addColumn | Examples/DependentTypes/DB.lean:314 | frontx_ind | type expected, got (also tried hof) |
| addVal | Examples/DependentTypes/DB.lean:330 | frontx_compile | frontx: unsupported result type |
| Row.project | Examples/DependentTypes/DB.lean:337 | frontx_ind | type expected, got (also tried hof) |
| DBExpr.evaluate | Examples/DependentTypes/DB.lean:372 | frontx_ind | Application type mismatch: The argument (also tried hof) |
| disjoint | Examples/DependentTypes/DB.lean:412 | frontx_view + frontx_compile | frontx_view: the body is not a `match` |
| Schema.renameColumn | Examples/DependentTypes/DB.lean:418 | frontx_ind | type expected, got (also tried hof) |
| Row.append | Examples/DependentTypes/DB.lean:448 | frontx_compile | frontx: unsupported result type |
| Mine.List.flatMap | Examples/DependentTypes/DB.lean:458 | frontx_view + frontx_compile | frontx: unsupported parameter type (also tried hof) |
| Table.cartesianProduct | Examples/DependentTypes/DB.lean:465 | frontx_compile | frontx: unsupported result type |
| OrElse.Table.cartesianProduct | Examples/DependentTypes/DB.lean:472 | frontx_compile | frontx: unsupported result type (also tried monad) |
| List.without | Examples/DependentTypes/DB.lean:493 | frontx_view + frontx_compile | frontx_view: the body is not a `match` |
| Row.rename | Examples/DependentTypes/DB.lean:499 | frontx_ind | type expected, got |
| prefixRow | Examples/DependentTypes/DB.lean:509 | frontx_compile | frontx: unsupported result type |
| NDBType.asType | Examples/DependentTypes/DB.lean:657 | frontx_ind | frontx_ind: equation ite.eq_1 has no constructor pattern (also tried monad) |
| NatOrBool.asType | Examples/DependentTypes/Finite.lean:20 | frontx_ind | frontx_ind: unsupported result type |
| decode | Examples/DependentTypes/Finite.lean:32 | frontx_ind | frontx_ind: unsupported parameter type (also tried monad) |
| NestedPairs.asType | Examples/DependentTypes/Finite.lean:48 | frontx_ind | frontx_ind: unsupported result type (also tried hof) |
| NestedPairs.beq | Examples/DependentTypes/Finite.lean:68 | frontx_ind | frontx_ind: unsupported parameter type |
| Finite.asType | Examples/DependentTypes/Finite.lean:88 | frontx_ind | frontx_ind: unsupported result type (also tried hof) |
| Finite.count | Examples/DependentTypes/Finite.lean:95 | frontx_ind | frontx_ind: unsupported term (also tried hof) |
| List.product | Examples/DependentTypes/Finite.lean:103 | frontx_view + frontx_compile | frontx_view: the body is not a `match` (also tried monad) |
| ListExtras.List.foldr | Examples/DependentTypes/Finite.lean:118 | frontx_view + frontx_compile | Tactic `rewrite` failed: motive is not type correct: (also tried hof) |
| Finite.isSingleton | Examples/DependentTypes/Finite.lean:215 | frontx_ind | **compiles** |
| Nat.plusL | Examples/DependentTypes/Pitfalls.lean:8 | frontx_compile | frontx: unsupported match (also tried hof) |
| Nat.plusR | Examples/DependentTypes/Pitfalls.lean:15 | frontx_compile | frontx: unsupported match (also tried hof) |
| ApplicativeToFunctor.map | Examples/FunctorApplicativeMonad.lean:557 | frontx_compile | frontx: unsupported result type (also tried hof) |
| MonadApplicative.seq | Examples/FunctorApplicativeMonad.lean:592 | frontx_compile | frontx: unsupported result type (also tried hof, monad) |
| MonadApplicativeDesugar.seq | Examples/FunctorApplicativeMonad.lean:602 | frontx_compile | frontx: unsupported result type (also tried hof, monad) |
| Many.orElse | Examples/FunctorApplicativeMonad.lean:1501 | frontx_ind | frontx_ind: unsupported parameter type (also tried hof) |
| report | Examples/FunctorApplicativeMonad.lean:1588 | frontx_ind | Unknown identifier `TreeError` (also tried hof) |
| simpleConst | Examples/FunctorApplicativeMonad/ActualDefs.lean:29 | frontx_compile | frontx: unsupported result type |

## Test vectors and entry wrappers (update)

- Test vectors: `Testing/asm/emit_books1.lean` writes `Testing/asm/frontx-words/finite_issingleton.{words,cases}` (11 cases; the emitter runs without error). Test: **pending (run by parent at merge)**: `python3 Testing/asm/frontx_test.py check 50 finite_issingleton`. QEMU is not installed here, and the install was denied, so the test was not run.
- `frontx_hof_entry` wrappers: **0 added**. The rows that failed with "no call with a known function argument" mostly take no function argument at all (`addNatPos`, `Nat.plusL`, `Finite.count`, `hashPos`, …), so `frontx_hof` has nothing to specialise, and a wrapper would only add a call the book does not make. The one row with a function-typed parameter, `Many.orElse : Many α → (Unit → Many α) → Many α`, returns `Many α`, which has a `Unit → Many α` field. I did not write a wrapper for it; I expect frontx cannot hold that field, but I did not test this.
