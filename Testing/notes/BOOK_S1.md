# BOOK_S1: first third of the survey's blocked rows, retried on `main`

Source: `Testing/notes/book_survey3.csv` (branch `booksurvey3`), book `fp-lean` @0abeea5, base `main` @4a79eeb.
File: `Riscv/Frontx/BookS1.lean` (one namespace block per row: book context, the verbatim def with `-- TARGET file:line-end`, the command).

## Premise check (differs from the task)

- `main` @4a79eeb has no `frontx_hof`, no `Riscv/Frontx/HofExamples.lean`, and NOTES stop at §23. No fetched ref contains `frontx_hof`. A remote branch `feat-hof` exists (not fetched, not merged here; it is not on `main`).
- So the three higher-order rows (`listMonoid`, `MMM.foldMap`, `foldMap`) are retried with `frontx_ind` only, and fail there. They were not retried with `frontx_hof`.

## Population and result

- Sorted example files: 33 (`Examples.lean`, `Examples/*.lean`). First third = the first 11 (`Examples.lean` … `Examples/FunctorApplicativeMonad/ActualDefs.lean`).
- Blocked rows in them: 67. Compiled on `main`: **0**. Test cases added: none, so `frontx_test.py check 50` was not run and `Testing/asm/ctest` was not created.
- Command per row: `frontx_ind` if a user inductive is in the signature, `frontx_view` + `frontx_compile` if a `List` is, `wa_compile` if an `Array` is, else `frontx_compile`. The first error below is from the standalone run of that row (one file per row, same closure as the survey harness). Rows whose first error is an unknown name, a missing instance or a tactic failure (`Plus`, `TreeError`, `ToString`, `Type mismatch`, `_fvar`, `rewrite`) look like context gaps in the closure, not compiler verdicts; I did not check them further.
- Harness check: the same procedure compiles `Intro.lean:179 add1`, `Intro.lean:239 maximum` and `Classes.lean:181 Pos.plus` on `main`, so the failures are not from the harness.

## Per-row first error

| Argh.posToString | Examples/Classes.lean:240 | frontx_ind | frontx_ind: unsupported result type |
| addNatPos | Examples/Classes.lean:757 | frontx_ind | frontx_ind: Nat.brecOn has no argument of a declared type |
| addPosNat | Examples/Classes.lean:761 | frontx_ind | frontx_ind: Nat.brecOn has no argument of a declared type |
| NonEmptyList.toList | Examples/Classes.lean:961 | frontx_ind | frontx_ind: List.cons has no equations |
| NonEmptyList.get? | Examples/Classes.lean:989 | frontx_ind | frontx_ind: unsupported result type |
| UseList.NonEmptyList.get? | Examples/Classes.lean:997 | frontx_ind | frontx_ind: Proven.Frontx.Run.UseList.NonEmptyList.get?.match_1 has no equations |
| NonEmptyList.inBounds | Examples/Classes.lean:1004 | frontx_ind | frontx_ind: unsupported result type |
| NonEmptyList.get | Examples/Classes.lean:1010 | frontx_ind | frontx_ind: Proven.Frontx.Run.NonEmptyList.get.match_1 has no equations |
| hashPos | Examples/Classes.lean:1245 | frontx_ind | frontx_ind: unsupported term |
| hashBinTree | Examples/Classes.lean:1270 | frontx_ind | frontx_ind: unsupported term |
| concat | Examples/Classes.lean:1442 | frontx_ind | frontx_ind: unsupported parameter type |
| String.separate | Examples/Classes.lean:1636 | frontx_view + frontx_compile | frontx_view: unsupported element type |
| dropDecimals | Examples/Classes.lean:1671 | frontx_compile | unknown free variable `_fvar.1453` |
| listMonoid | Examples/Classes.lean:1737 | frontx_ind | frontx_ind: Proven.Frontx.Run.Monoid.mk has no equations |
| MMM.foldMap | Examples/Classes.lean:1743 | frontx_ind | frontx_ind: unsupported parameter type |
| foldMap | Examples/Classes.lean:1759 | frontx_ind | frontx_ind: unsupported parameter type |
| Even.Even.mul | Examples/Classes/Even.lean:32 | frontx_ind | frontx_ind: nested patterns are not supported (Proven.Frontx.Run.Even.Even.mul.eq_2) |
| Other.Even.add | Examples/Classes/Even.lean:96 | frontx_ind | Application type mismatch: The argument |
| natOrStringThree | Examples/DependentTypes.lean:6 | frontx_compile | frontx: unsupported result type |
| Vect.replicate | Examples/DependentTypes.lean:228 | frontx_ind | type expected, got |
| Extras.List.replicate | Examples/DependentTypes.lean:237 | frontx_view + frontx_compile | frontx_view: no list parameter |
| Vect.zip | Examples/DependentTypes.lean:274 | frontx_ind | type expected, got |
| Details.Vect.zip | Examples/DependentTypes.lean:329 | frontx_ind | type expected, got |
| Vect.map | Examples/DependentTypes.lean:347 | frontx_ind | type expected, got |
| Vect.zipWith | Examples/DependentTypes.lean:351 | frontx_ind | type expected, got |
| Vect.unzip | Examples/DependentTypes.lean:355 | frontx_ind | type expected, got |
| Vect.push | Examples/DependentTypes.lean:362 | frontx_ind | type expected, got |
| Vect.drop | Examples/DependentTypes.lean:366 | frontx_ind | type expected, got |
| Vect.reverse | Examples/DependentTypes.lean:370 | frontx_ind | type expected, got |
| Vect.take | Examples/DependentTypes.lean:375 | frontx_ind | type expected, got |
| DBType.asType | Examples/DependentTypes/DB.lean:10 | frontx_ind | frontx_ind: unsupported result type |
| DBType.beq | Examples/DependentTypes/DB.lean:39 | frontx_ind | frontx_ind: unsupported parameter type |
| Row | Examples/DependentTypes/DB.lean:84 | frontx_compile | frontx: unsupported result type |
| Table | Examples/DependentTypes/DB.lean:104 | frontx_compile | frontx: unsupported result type |
| Row.bEq | Examples/DependentTypes/DB.lean:167 | frontx_compile | frontx: unsupported parameter type |
| Row.get | Examples/DependentTypes/DB.lean:193 | frontx_ind | type expected, got |
| Subschema.addColumn | Examples/DependentTypes/DB.lean:314 | frontx_ind | type expected, got |
| addVal | Examples/DependentTypes/DB.lean:330 | frontx_compile | frontx: unsupported result type |
| Row.project | Examples/DependentTypes/DB.lean:337 | frontx_ind | type expected, got |
| DBExpr.evaluate | Examples/DependentTypes/DB.lean:372 | frontx_ind | Application type mismatch: The argument |
| disjoint | Examples/DependentTypes/DB.lean:412 | frontx_view + frontx_compile | frontx_view: the body is not a `match` |
| Schema.renameColumn | Examples/DependentTypes/DB.lean:418 | frontx_ind | type expected, got |
| Row.append | Examples/DependentTypes/DB.lean:448 | frontx_compile | frontx: unsupported result type |
| Mine.List.flatMap | Examples/DependentTypes/DB.lean:458 | frontx_view + frontx_compile | frontx: unsupported parameter type |
| Table.cartesianProduct | Examples/DependentTypes/DB.lean:465 | frontx_compile | frontx: unsupported result type |
| OrElse.Table.cartesianProduct | Examples/DependentTypes/DB.lean:472 | frontx_compile | frontx: unsupported result type |
| List.without | Examples/DependentTypes/DB.lean:493 | frontx_view + frontx_compile | frontx_view: the body is not a `match` |
| Row.rename | Examples/DependentTypes/DB.lean:499 | frontx_ind | type expected, got |
| prefixRow | Examples/DependentTypes/DB.lean:509 | frontx_compile | frontx: unsupported result type |
| NDBType.asType | Examples/DependentTypes/DB.lean:657 | frontx_ind | frontx_ind: equation ite.eq_1 has no constructor pattern |
| NatOrBool.asType | Examples/DependentTypes/Finite.lean:20 | frontx_ind | frontx_ind: unsupported result type |
| decode | Examples/DependentTypes/Finite.lean:32 | frontx_ind | frontx_ind: unsupported parameter type |
| NestedPairs.asType | Examples/DependentTypes/Finite.lean:48 | frontx_ind | frontx_ind: unsupported result type |
| NestedPairs.beq | Examples/DependentTypes/Finite.lean:68 | frontx_ind | frontx_ind: unsupported parameter type |
| Finite.asType | Examples/DependentTypes/Finite.lean:88 | frontx_ind | frontx_ind: unsupported result type |
| Finite.count | Examples/DependentTypes/Finite.lean:95 | frontx_ind | frontx_ind: unsupported term |
| List.product | Examples/DependentTypes/Finite.lean:103 | frontx_view + frontx_compile | frontx_view: the body is not a `match` |
| ListExtras.List.foldr | Examples/DependentTypes/Finite.lean:118 | frontx_view + frontx_compile | Tactic `rewrite` failed: motive is not type correct: |
| Finite.isSingleton | Examples/DependentTypes/Finite.lean:215 | frontx_ind | unsolved goals |
| Nat.plusL | Examples/DependentTypes/Pitfalls.lean:8 | frontx_compile | frontx: unsupported match |
| Nat.plusR | Examples/DependentTypes/Pitfalls.lean:15 | frontx_compile | frontx: unsupported match |
| ApplicativeToFunctor.map | Examples/FunctorApplicativeMonad.lean:557 | frontx_compile | frontx: unsupported result type |
| MonadApplicative.seq | Examples/FunctorApplicativeMonad.lean:592 | frontx_compile | frontx: unsupported result type |
| MonadApplicativeDesugar.seq | Examples/FunctorApplicativeMonad.lean:602 | frontx_compile | frontx: unsupported result type |
| Many.orElse | Examples/FunctorApplicativeMonad.lean:1501 | frontx_ind | frontx_ind: unsupported parameter type |
| report | Examples/FunctorApplicativeMonad.lean:1588 | frontx_ind | Unknown identifier `TreeError` |
| simpleConst | Examples/FunctorApplicativeMonad/ActualDefs.lean:29 | frontx_compile | frontx: unsupported result type |

## Notes

- The combined `BookS1.lean` does not compile cleanly (`lake env lean -DmaxErrors=100000 Riscv/Frontx/BookS1.lean`: exit 1). Several errors are reported at positions outside their block, and there are `PANIC at Lean.Expr.appArg!` messages (4) that I could not attribute to a row. Use the table above, not the combined output, for the per-row errors.
- `-DmaxErrors` is needed: `set_option maxErrors` in the file header is ignored by the frontend.
- Survey harness (`run.py`, `gen.py`, `assemble.py`) is not committed; it is the one in `Testing/notes/book_tries3/` on `booksurvey3`, run here with `TMO=900` and 4 jobs.
