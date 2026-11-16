# Book survey 3: all pure functions of "Functional Programming in Lean" against current `main`

Source: `github.com/leanprover/fp-lean` @0abeea5, `examples/` (57 `.lean` files, 37 example modules; same commit as `BOOK_SURVEY.md`). Compiler: `main` @ce989e1 (front ends `frontx_compile`, `frontx_view`, `frontx_ind`, `wa_compile`; NOTES §15-21), Lean 4.29.0, Sail model `opencompl/sail-riscv-lean` built from scratch. Data: `book_survey3.csv` (one row per top-level `def`/`abbrev`), scripts: `book_tries3/`. Compiler sources are untouched.

## Totals

| | rows | distinct bodies |
|---|---|---|
| top-level `def`/`abbrev` in the 37 example modules + `ExampleSupport.lean` | 580 | |
| not book functions: Lean elaborator code of `ExampleSupport.lean` | 13 | |
| IO / effects (skipped, out of scope) | 77 | |
| not a function (constants, types, `abbrev`s of types: nothing to compile) | 131 | |
| **pure functions (the survey's population)** | **359** | **352** |
| &nbsp;&nbsp;compiled verbatim, default command of the right front end (this survey's harness) | 56 | 55 |
| &nbsp;&nbsp;compiled verbatim on `main` with a hand-given directive or entry (`using`, `with`, `from`, `frontx_ind … using`, wrapper entry), found in `Riscv/Frontx/*.lean` | 29 | 28 |
| **compiled (the two lines above)** | **85** | **83** |
| blocked: a front end rejects it (message and blocker below) | 213 | 208 |
| not run: the verbatim def does not elaborate in isolation (book's own broken/illustrative examples, or context my extractor did not carry; see below) | 61 | 61 |

The 117 `instance` commands are not rows: an instance has no entry point (`Add Pos` is compiled when `Pos.mul` is, `+` calls it). Rates: compiled / pure functions = 85/359 = 23% by rows, 83/352 by distinct bodies (the book restates `length`, `halve`, `even`, ... in several namespaces).

## Method (what "verbatim" and "right front end" mean here)

1. `extract.py` splits each file into top-level commands with `file:line-end`; drops the book's `discarding … stop discarding` (intentional errors), `evaluation steps` blocks, `#check_msgs`, docstrings and comments. The def text is copied unchanged, including `open … in` prefixes (except `open SubVerso.Examples in`).
2. `gen.py` writes one Lean file per def: the def, plus the transitive closure of the book declarations it names (same file and the example modules it imports; inductives, structures, helper defs, instances of included types, namespaces it opens), each in its original `namespace`/`open`/`variable` scope, all inside `namespace Proven.Frontx.Run`. Then the compile command.
3. `run.py` tries, in this order, the first that succeeds wins: `frontx_compile f`; if `List` is in the signature `frontx_view f` + `frontx_compile f.view from f.view.eq measure …` (0-2 extra arguments), and the same through the callee of a one-line wrapper (`def sum xs := sumHelper 0 xs`); if a user inductive/structure is in the signature `frontx_ind_type` (type parameters := `Nat`) + `frontx_ind f on T [using R]`; if `Array` is in it `wa_compile f`. Success = the compiler's own success line after a marker, no error after the marker, no `sorry`, no panic. Generated theorems are the compiler's (no hand proofs, none of the compiled rows needed a `requires`/`with`/`using` hint).
4. Things the default commands cannot guess (`requires`, `with` invariants, `using` lemma, `from … spec`, `frontx_tailcopy`, glue entries) are taken from the files already on `main` (`gt.py`): a book def counts as `compiled on main (hand directive)` when a def in `Riscv/Frontx/*.lean` has the same body text (comments/whitespace/qualifiers normalised) and a `frontx_*` command on it. I built those 12 modules here (`lake build`, 254 jobs, no error) but did not re-derive the directives.
5. Blockers: the first error message of the most specialised failing attempt + the printed signature, mapped to one bucket by a fixed rule list (`survey3.py`, order = table order). A row has exactly one primary bucket; the second table counts every feature present in the source of each non-compiled row. Both are heuristics.

## Compiled

| book def | compiled by | provenance of directive |
|---|---|---|
| `Classes.lean:181` `Pos.plus` | `frontx_ind` | |
| `Classes.lean:232` `Pos.toNat` | `frontx_ind` | |
| `Classes.lean:303` `Pos.mul` | `frontx_ind` | |
| `Classes.lean:1210` `Pos.comp` | frontx_ind Pos.comp on PosT using Proven.Frontx.IndCmp.OrdT | Riscv/Frontx/Ind2Examples.lean:50 |
| `Classes.lean:1259` `eqBinTree` | `frontx_ind` | |
| `Classes.lean:1534` `L.List.last?` | `frontx_view`+`frontx_compile` | |
| `Classes/Even.lean:8` `Even.Even.plus` | `frontx_ind` | |
| `Classes/Even.lean:21` `Even.Even.toNat` | `frontx_ind` | |
| `FunctorApplicativeMonad.lean:238` `MythicalCreature.small` | `frontx_compile` | |
| `Induction.lean:318` `BinTree.count` | `frontx_ind` | |
| `Induction.lean:516` `BinTree.graftLeft` | `frontx_ind` | |
| `Intro.lean:179` `add1` | `frontx_compile` | |
| `Intro.lean:239` `maximum` | `frontx_compile` | |
| `Intro.lean:509` `zeroX` | frontx_compile zeroX | Riscv/Frontx/DataExamples.lean:21 |
| `Intro.lean:779` `isZero` | `frontx_compile` | |
| `Intro.lean:830` `pred` | `frontx_compile` | |
| `Intro.lean:887` `even` | `frontx_compile` | |
| `Intro.lean:931` `plus` | `frontx_compile` | |
| `Intro.lean:971` `times` | frontx_compile times using plus_eq | Riscv/Frontx/BookExamples.lean:38 |
| `Intro.lean:980` `minus` | frontx_compile minus with (fun n _ _ acc => acc ≤ n) | Riscv/Frontx/BookExamples.lean:42 |
| `Intro.lean:1136` `Ooops.length` | `frontx_view`+`frontx_compile` | |
| `Intro.lean:1192` `Oooops.length` | `frontx_view`+`frontx_compile` | |
| `Intro.lean:1203` `BetterPlicity.replaceX` | inlined in / wrapped by hand-written entry | Riscv/Frontx/PairExamples.lean:69 |
| `Intro.lean:1217` `BetterPlicity.length` | `frontx_view`+`frontx_compile` | |
| `Intro.lean:1428` `Floop.List.head?` | `frontx_view`+`frontx_compile` | |
| `Intro.lean:1498` `Floop.List.final?` | `frontx_view`+`frontx_compile` | |
| `Intro.lean:1555` `List.findFirst?` | inlined in / wrapped by hand-written entry | Riscv/Frontx/ListExamples.lean:94 |
| `Intro.lean:1605` `take` | `frontx_view`+`frontx_compile` | |
| `Intro.lean:1822` `Nested.sameLength` | `frontx_view`+`frontx_compile` | |
| `Intro.lean:1837` `Both.sameLength` | `frontx_view`+`frontx_compile` | |
| `Intro.lean:1847` `AutoImpl.length` | `frontx_view`+`frontx_compile` | |
| `Intro.lean:1860` `MatchDef.length` | `frontx_view`+`frontx_compile` | |
| `Intro.lean:1868` `drop` | frontx_view drop | Riscv/Frontx/ListOutExamples.lean:26 |
| `Intro.lean:1879` `fromOption` | inlined in / wrapped by hand-written entry | Riscv/Frontx/PairExamples.lean:71 |
| `Intro.lean:2036` `Match.drop` | frontx_view drop | Riscv/Frontx/ListOutExamples.lean:35 |
| `Intro.lean:2044` `Match.even` | `frontx_compile` | |
| `Intro.lean:2051` `Match.Explicit.halve` | `frontx_compile` | |
| `Intro.lean:2060` `Match.halve` | `frontx_compile` | |
| `Intro.lean:2140` `Double.double` | `frontx_compile` | |
| `Intro.lean:2188` `Nat.double` | `frontx_compile` | |
| `Intro.lean:2212` `NewNamespace.triple` | `frontx_compile` | |
| `Intro.lean:2213` `NewNamespace.quadruple` | `frontx_compile` | |
| `Intro.lean:2243` `timesTwelve` | `frontx_compile` | |
| `MonadTransformers/Conveniences.lean:45` `PipelineEx.times3` | `frontx_compile` | |
| `Monads.lean:23` `Monads.Option.first` | inlined in / wrapped by hand-written entry | Riscv/Frontx/ExceptBook.lean:12 |
| `Monads.lean:29` `Monads.Option.firstThird` | `frontx_view`+`frontx_compile` | |
| `Monads.lean:41` `Monads.Option.firstThirdFifth` | `frontx_view`+`frontx_compile` | |
| `Monads.lean:56` `Monads.Option.firstThirdFifthSeventh` | `frontx_view`+`frontx_compile` | |
| `Monads.lean:74` `Monads.Option.M.andThen` | inlined in / wrapped by hand-written entry | Riscv/Frontx/ExceptBook.lean:52 |
| `Monads.lean:82` `Monads.Option.M.firstThird` | `frontx_view`+`frontx_compile` | |
| `Monads.lean:90` `Monads.Option.M.ExplicitParens.firstThird` | `frontx_view`+`frontx_compile` | |
| `Monads.lean:127` `Monads.Option.M.firstThirdInfix` | inlined in / wrapped by hand-written entry | Riscv/Frontx/ExceptBook.lean:71 |
| `Monads.lean:135` `Monads.Option.M.firstThirdFifthSeventh` | inlined in / wrapped by hand-written entry | Riscv/Frontx/ExceptBook.lean:76 |
| `Monads.lean:167` `Monads.Err.get` | inlined in / wrapped by hand-written entry | Riscv/Frontx/ExceptBook.lean:88 |
| `Monads.lean:197` `Monads.Err.first` | `frontx_view`+`frontx_compile` | |
| `Monads.lean:203` `Monads.Err.firstThird` | `frontx_view`+`frontx_compile` | |
| `Monads.lean:215` `Monads.Err.firstThirdFifth` | `frontx_view`+`frontx_compile` | |
| `Monads.lean:230` `Monads.Err.firstThirdFifthSeventh` | `frontx_view`+`frontx_compile` | |
| `Monads.lean:248` `Monads.Err.andThen` | inlined in / wrapped by hand-written entry | Riscv/Frontx/ExceptBook.lean:132 |
| `Monads.lean:256` `Monads.Err.AndThen.firstThird'` | `frontx_view`+`frontx_compile` | |
| `Monads.lean:270` `Monads.Err.ok` | inlined in / wrapped by hand-written entry | Riscv/Frontx/ExceptBook.lean:146 |
| `Monads.lean:274` `Monads.Err.fail` | inlined in / wrapped by hand-written entry | Riscv/Frontx/ExceptBook.lean:148 |
| `Monads.lean:279` `Monads.Err.Eff.get` | inlined in / wrapped by hand-written entry | Riscv/Frontx/ExceptBook.lean:151 |
| `Monads.lean:288` `Monads.Err.WithInfix.firstThird` | frontx_view Monads.Option.firstThird | Riscv/Frontx/ExceptBook.lean:158 |
| `Monads.lean:295` `Monads.Err.WithInfix.firstThirdFifthSeventh` | frontx_view Monads.Option.firstThirdFifthSeventh | Riscv/Frontx/ExceptBook.lean:163 |
| `Monads/Class.lean:93` `Errs.getOrExcept` | inlined in / wrapped by hand-written entry | Riscv/Frontx/ExceptBook.lean:88 |
| `Monads/Conveniences.lean:45` `Old.BinTree.mirror` | `frontx_ind` | |
| `Monads/Conveniences.lean:53` `BinTree.mirror` | `frontx_ind` | |
| `Monads/Conveniences.lean:85` `A.Weekday.isWeekend` | `frontx_ind` | |
| `Monads/Conveniences.lean:95` `B.Weekday.isWeekend` | `frontx_ind` | |
| `Monads/Conveniences.lean:105` `C.Weekday.isWeekend` | `frontx_ind` | |
| `Monads/Conveniences.lean:115` `D.Weekday.isWeekend` | `frontx_ind` | |
| `Monads/Many.lean:16` `Many.union` | `frontx_ind` | |
| `ProgramsProofs/Div.lean:45` `div` | `frontx_compile` | |
| `ProgramsProofs/TCO.lean:6` `NonTail.sum` | `frontx_view`+`frontx_compile` | |
| `ProgramsProofs/TCO.lean:40` `Tail.sumHelper` | inlined in / wrapped by hand-written entry | Riscv/Frontx/IndExamples.lean:62 |
| `ProgramsProofs/TCO.lean:44` `Tail.sum` | frontx_ind NonTail.sum on LN | Riscv/Frontx/IndExamples.lean:66 |
| `ProgramsProofs/TCO.lean:74` `NonTail.reverse` | frontx_ind NonTail.reverse on LN | Riscv/Frontx/Ind2Examples.lean:30 |
| `ProgramsProofs/TCO.lean:102` `Tail.reverseHelper` | inlined in / wrapped by hand-written entry | Riscv/Frontx/IndExamples.lean:70 |
| `ProgramsProofs/TCO.lean:106` `Tail.reverse` | frontx_ind Tail.reverse on LN | Riscv/Frontx/IndExamples.lean:74 |
| `ProgramsProofs/TCO.lean:127` `Slow.mirror` | `frontx_ind` | |
| `ProgramsProofs/TCO.lean:157` `NonTail.length` | `frontx_view`+`frontx_compile` | |
| `ProgramsProofs/TCO.lean:162` `Tail.lengthHelper` | frontx_view lengthHelper | Riscv/Frontx/ListExamples.lean:74 |
| `ProgramsProofs/TCO.lean:166` `Tail.length` | inlined in / wrapped by hand-written entry | Riscv/Frontx/ListExamples.lean:77 |
| `ProgramsProofs/TCO.lean:183` `NonTail.filter` | inlined in / wrapped by hand-written entry | Riscv/Frontx/ListOutExamples.lean:59 |

## Blockers, ranked (primary bucket per blocked row; 213 rows)

| # | feature | rows | examples |
|---|---|---|---|
| 1 | dependent types / type-valued functions | 60 | `NonEmptyList.inBounds` `Classes.lean:1004`, `MMM.foldMap` `Classes.lean:1743`, `foldMap` `Classes.lean:1759`, `natOrStringThree` `DependentTypes.lean:6` |
| 2 | monad / higher-kinded (`m α`, State/Reader/WithLog as functions, `do`) | 26 | `List.product` `DependentTypes/Finite.lean:103`, `ApplicativeToFunctor.map` `FunctorApplicativeMonad.lean:557`, `MonadApplicative.seq` `FunctorApplicativeMonad.lean:592`, `MonadApplicativeDesugar.seq` `FunctorApplicativeMonad.lean:602` |
| 3 | Int / signed arithmetic | 23 | `posOrNegThree` `Intro.lean:1567`, `Evaluator.bind` `MonadTransformers.lean:36`, `Evaluator.lookup` `MonadTransformers.lean:43`, `Evaluator.applyPrim` `MonadTransformers.lean:49` |
| 4 | inductive / structure shapes not supported (no equations, nested patterns, `brecOn`, projections, hash) | 20 | `addNatPos` `Classes.lean:757`, `addPosNat` `Classes.lean:761`, `hashPos` `Classes.lean:1245`, `hashBinTree` `Classes.lean:1270` |
| 5 | list of pairs / pair-of-lists / list of structures | 15 | `NonEmptyList.toList` `Classes.lean:961`, `NonEmptyList.get?` `Classes.lean:989`, `UseList.NonEmptyList.get?` `Classes.lean:997`, `NonEmptyList.get` `Classes.lean:1010` |
| 6 | String / Char | 13 | `Argh.posToString` `Classes.lean:240`, `String.separate` `Classes.lean:1636`, `dropDecimals` `Classes.lean:1671`, `spaceBetween` `Intro.lean:249` |
| 7 | polymorphic result/parameter type (`α`, `Option α`, `Except ε α`) not instantiated | 12 | `simpleConst` `FunctorApplicativeMonad/ActualDefs.lean:29`, `NT.id` `Intro.lean:1961`, `NRT.id` `Intro.lean:1979`, `Monads.State.set` `Monads.lean:500` |
| 8 | list-view shapes not supported (non-`match` body, non-view recursive call, list result) | 11 | `Extras.List.replicate` `DependentTypes.lean:237`, `disjoint` `DependentTypes/DB.lean:412`, `List.without` `DependentTypes/DB.lean:493`, `howManyDogs` `Intro.lean:1356` |
| 9 | higher-order argument (function/predicate parameter) | 10 | `listMonoid` `Classes.lean:1737`, `Mine.List.flatMap` `DependentTypes/DB.lean:458`, `Many.orElse` `FunctorApplicativeMonad.lean:1501`, `EarlyReturn.Non.List.find?` `MonadTransformers/Do.lean:93` |
| 10 | Float | 8 | `Oops.zeroX` `Intro.lean:503`, `addPoints` `Intro.lean:589`, `Point.modifyBoth` `Intro.lean:651`, `distance` `Intro.lean:678` |
| 11 | Array of non-bytes / generic Array code | 8 | `arrayMapHelper` `ProgramsProofs/Arrays.lean:274`, `TailRec.Array.map` `ProgramsProofs/Arrays.lean:285`, `Partial.insertionSortLoop` `ProgramsProofs/InsertionSort.lean:328`, `insertionSortLoop` `ProgramsProofs/InsertionSort.lean:430` |
| 12 | compiler error (unknown free variable / universe levels / introN) | 3 | `Nat.plusL` `DependentTypes/Pitfalls.lean:8`, `Nat.plusR` `DependentTypes/Pitfalls.lean:15`, `getTheString` `Monads/Conveniences.lean:155` |
| 13 | multiply / divide by a variable (`unsupported term`) | 3 | `volume` `Intro.lean:316`, `NonTail.factorial` `ProgramsProofs/TCO.lean:171`, `Tail.factHelper` `ProgramsProofs/TCO.lean:176` |
| 14 | other: Unknown identifier `TreeError` | 1 | `report` `FunctorApplicativeMonad.lean:1588` |

Second view, every feature present (not exclusive) over the 274 non-compiled rows (blocked + not run): polymorphism (`α`) 141, user inductive / structure 135, monad-style (`do`, `State`, `Except`, `m α`) 62, higher-order argument 50, pairs / tuples 50, type class (`[C α]`, instances) 42, String / Char 41, dependent types 40, Int 37, Array 14, Float 6.

### Not run (verbatim def does not elaborate in isolation): 61 rows

- 46: context my closure did not carry (a later-defined structure/field, `c!` macro, `Pure (State Nat)` instance, scope nesting): needs hand-made context, **not counted as blocked**
- 15: the book shows this def failing (termination, type error, missing instance, `Oops` variants) or uses book notation that needs `ExampleSupport` macros

## Delta vs `BOOK_SURVEY.md` (survey 2, `booksurvey2`)

Survey 2 (read from `main`, not rebuilt) listed 38 matching rows as compiled verbatim on `main` (15 machine theorem, 23 source theorem; its CSV has 39, one of them (`Div.lean:26`) is the book's non-terminating `div`, which this survey's extractor drops with the `discarding` region) and 7 as `not-on-main`, and 35 B rows `likely-untried` (34 matched here) (judged by reading, never run). Now: **85 compiled rows** (83 distinct bodies), of which 34 were already listed and **51 are new**; 4 listed rows are not in the compiled set (below).

| survey 2 status | rows | compiled now | still blocked / not run / other |
|---|---|---|---|
| machine-thm | 15 | 13 | 2 |
| source-thm | 23 | 21 | 2 |
| not-on-main | 6 | 2 | 4 |
| likely-untried | 34 | 17 | 17 |
| (no survey 2 verdict B) | 32 compiled now | | |

Listed in survey 2 and not compiled now:

- `Intro.lean:1009` `div`: not run: def does not elaborate in isolation (fail to show termination for Proven.Frontx.Run.div with errors failed to infer structural recursion:)
- `Intro.lean:2081` `Match.Oops.halve`: not run: def does not elaborate in isolation (Invalid pattern(s): `n` is an explicit pattern variable, but it only occurs in positions that are in)
- `Intro.lean:2489` `Oops.List.findFirst?`: not run: def does not elaborate in isolation (expected token)
- `ProgramsProofs/TCO.lean:33` `MoreClear.Tail.sumHelper`: blocked (frontx: could not prove B[i].toNat + soFar < 2 ^ 64 goal: B : ByteArray i soFar : Nat σ : BState h0 )

Survey 2 rows `not-on-main` or `likely-untried` that are still blocked: `DependentTypes.lean:237` `Extras.List.replicate` (list-view shapes not supported), `DependentTypes/Pitfalls.lean:8` `Nat.plusL` (compiler error), `DependentTypes/Pitfalls.lean:15` `Nat.plusR` (compiler error), `FunctorApplicativeMonad/ActualDefs.lean:29` `simpleConst` (polymorphic result/parameter type), `Intro.lean:1050` `replaceX` (inductive / structure shapes not supported), `Intro.lean:1813` `sameLength` (needs a loop/recursion invariant hint), `Intro.lean:1928` `reverse` (list-view shapes not supported), `Intro.lean:1961` `NT.id` (polymorphic result/parameter type), `Intro.lean:1979` `NRT.id` (polymorphic result/parameter type), `Intro.lean:2494` `Oops.Prod.switch` (other: expected token), `Monads.lean:494` `Monads.State.get` (not a function (constant / type)), `Monads.lean:500` `Monads.State.set` (polymorphic result/parameter type), `Monads.lean:516` `Monads.State.ok` (polymorphic result/parameter type), `Monads/Class.lean:659` `read` (not a function (constant / type)), `Monads/Class.lean:808` `Reader.pure` (polymorphic result/parameter type), `ProgramsProofs/Fin.lean:48` `Fin.next?` (dependent types / type-valued functions), `ProgramsProofs/InsertionSort.lean:441` `insertionSort` (Array of non-bytes / generic Array code), `ProgramsProofs/InstrumentedInsertionSort.lean:35` `insertionSort` (Array of non-bytes / generic Array code), `ProgramsProofs/TCO.lean:200` `Tail.filter` (other: Unknown identifier `filterHelper`), `Props.lean:95` `second` (list-view shapes not supported), `Props.lean:278` `thirdOption` (list-view shapes not supported).

## Newly compiling functions (51 rows; the front end is the one that worked)

| book def | status | front end | survey 2 |
|---|---|---|---|
| `Classes.lean:181` `Pos.plus` | default command | `frontx_ind` | C or not listed |
| `Classes.lean:232` `Pos.toNat` | default command | `frontx_ind` | C or not listed |
| `Classes.lean:303` `Pos.mul` | default command | `frontx_ind` | C or not listed |
| `Classes.lean:1210` `Pos.comp` | on main, hand directive | frontx_ind Pos.comp on PosT using Proven.Frontx.IndCmp.OrdT | C or not listed |
| `Classes.lean:1259` `eqBinTree` | default command | `frontx_ind` | C or not listed |
| `Classes.lean:1534` `L.List.last?` | default command | `frontx_view` | likely-untried |
| `Classes/Even.lean:8` `Even.Even.plus` | default command | `frontx_ind` | C or not listed |
| `Classes/Even.lean:21` `Even.Even.toNat` | default command | `frontx_ind` | C or not listed |
| `FunctorApplicativeMonad.lean:238` `MythicalCreature.small` | default command | `frontx_compile` | likely-untried |
| `Induction.lean:318` `BinTree.count` | default command | `frontx_ind` | C or not listed |
| `Induction.lean:516` `BinTree.graftLeft` | default command | `frontx_ind` | C or not listed |
| `Intro.lean:509` `zeroX` | on main, hand directive | frontx_compile zeroX | C or not listed |
| `Intro.lean:1203` `BetterPlicity.replaceX` | on main, hand directive | inlined in / wrapped by hand-written entry | likely-untried |
| `Intro.lean:1822` `Nested.sameLength` | default command | `frontx_view` | likely-untried |
| `Intro.lean:1837` `Both.sameLength` | default command | `frontx_view` | likely-untried |
| `Intro.lean:1879` `fromOption` | on main, hand directive | inlined in / wrapped by hand-written entry | likely-untried |
| `MonadTransformers/Conveniences.lean:45` `PipelineEx.times3` | default command | `frontx_compile` | likely-untried |
| `Monads.lean:23` `Monads.Option.first` | on main, hand directive | inlined in / wrapped by hand-written entry | likely-untried |
| `Monads.lean:29` `Monads.Option.firstThird` | default command | `frontx_view` | likely-untried |
| `Monads.lean:41` `Monads.Option.firstThirdFifth` | default command | `frontx_view` | likely-untried |
| `Monads.lean:56` `Monads.Option.firstThirdFifthSeventh` | default command | `frontx_view` | likely-untried |
| `Monads.lean:74` `Monads.Option.M.andThen` | on main, hand directive | inlined in / wrapped by hand-written entry | C or not listed |
| `Monads.lean:82` `Monads.Option.M.firstThird` | default command | `frontx_view` | likely-untried |
| `Monads.lean:90` `Monads.Option.M.ExplicitParens.firstThird` | default command | `frontx_view` | likely-untried |
| `Monads.lean:127` `Monads.Option.M.firstThirdInfix` | on main, hand directive | inlined in / wrapped by hand-written entry | likely-untried |
| `Monads.lean:135` `Monads.Option.M.firstThirdFifthSeventh` | on main, hand directive | inlined in / wrapped by hand-written entry | likely-untried |
| `Monads.lean:167` `Monads.Err.get` | on main, hand directive | inlined in / wrapped by hand-written entry | C or not listed |
| `Monads.lean:197` `Monads.Err.first` | default command | `frontx_view` | C or not listed |
| `Monads.lean:203` `Monads.Err.firstThird` | default command | `frontx_view` | C or not listed |
| `Monads.lean:215` `Monads.Err.firstThirdFifth` | default command | `frontx_view` | C or not listed |
| `Monads.lean:230` `Monads.Err.firstThirdFifthSeventh` | default command | `frontx_view` | C or not listed |
| `Monads.lean:248` `Monads.Err.andThen` | on main, hand directive | inlined in / wrapped by hand-written entry | C or not listed |
| `Monads.lean:256` `Monads.Err.AndThen.firstThird'` | default command | `frontx_view` | C or not listed |
| `Monads.lean:270` `Monads.Err.ok` | on main, hand directive | inlined in / wrapped by hand-written entry | likely-untried |
| `Monads.lean:274` `Monads.Err.fail` | on main, hand directive | inlined in / wrapped by hand-written entry | likely-untried |
| `Monads.lean:279` `Monads.Err.Eff.get` | on main, hand directive | inlined in / wrapped by hand-written entry | C or not listed |
| `Monads.lean:288` `Monads.Err.WithInfix.firstThird` | on main, hand directive | frontx_view Monads.Option.firstThird | C or not listed |
| `Monads.lean:295` `Monads.Err.WithInfix.firstThirdFifthSeventh` | on main, hand directive | frontx_view Monads.Option.firstThirdFifthSeventh | C or not listed |
| `Monads/Class.lean:93` `Errs.getOrExcept` | on main, hand directive | inlined in / wrapped by hand-written entry | C or not listed |
| `Monads/Conveniences.lean:45` `Old.BinTree.mirror` | default command | `frontx_ind` | C or not listed |
| `Monads/Conveniences.lean:53` `BinTree.mirror` | default command | `frontx_ind` | C or not listed |
| `Monads/Conveniences.lean:85` `A.Weekday.isWeekend` | default command | `frontx_ind` | C or not listed |
| `Monads/Conveniences.lean:95` `B.Weekday.isWeekend` | default command | `frontx_ind` | C or not listed |
| `Monads/Conveniences.lean:105` `C.Weekday.isWeekend` | default command | `frontx_ind` | C or not listed |
| `Monads/Conveniences.lean:115` `D.Weekday.isWeekend` | default command | `frontx_ind` | C or not listed |
| `Monads/Many.lean:16` `Many.union` | default command | `frontx_ind` | C or not listed |
| `ProgramsProofs/Div.lean:45` `div` | default command | `frontx_compile` | C or not listed |
| `ProgramsProofs/TCO.lean:74` `NonTail.reverse` | on main, hand directive | frontx_ind NonTail.reverse on LN | not-on-main |
| `ProgramsProofs/TCO.lean:102` `Tail.reverseHelper` | on main, hand directive | inlined in / wrapped by hand-written entry | C or not listed |
| `ProgramsProofs/TCO.lean:106` `Tail.reverse` | on main, hand directive | frontx_ind Tail.reverse on LN | not-on-main |
| `ProgramsProofs/TCO.lean:127` `Slow.mirror` | default command | `frontx_ind` | C or not listed |

## By chapter

| chapter | pure functions | compiled | blocked | not run |
|---|---|---|---|---|
| 1 Getting to Know Lean | 67 | 32 | 28 | 7 |
| 3 Propositions, Proofs, Indexing | 4 | 0 | 3 | 1 |
| 4 Overloading and Type Classes | 29 | 8 | 18 | 3 |
| 5 Monads | 97 | 29 | 56 | 12 |
| 6 Functor, Applicative, Monad | 22 | 1 | 6 | 15 |
| 7 Monad Transformers | 28 | 1 | 24 | 3 |
| 8 Dependent Types | 57 | 0 | 43 | 14 |
| 8 Dependent Types (universes) | 2 | 0 | 2 | 0 |
| 9 Programming, Proving, Performance | 41 | 14 | 25 | 2 |
| support / other | 12 | 0 | 8 | 4 |

## Observations about the compiler (from the 446 failing standalone attempts)

- 139 attempts print `PANIC at Lean.Expr.appArg! … application expected` (with a backtrace on stderr) after an `unsupported … type` message. The rejection is correct; the panic is in the error-reporting path (printing the type), not a wrong result. 7 attempts fail with ``Tactic `introN` failed`` and 6 with `incorrect number of universe levels … .eq_def` (`findHelper`, `List.find?` variants: `Type u` polymorphism), and several with `unknown free variable _fvar.N` (String-valued defs such as `spaceBetween`, `joinStringsWith`, `dropDecimals`): internal errors rather than clean rejections.
- No attempt printed `sorry`, and no accepted attempt needed a hint. Accepted `Except String α` functions (`Monads.Err.*`) keep the tag and the payload only: the error string is not in the result (NOTES §16), so they compile a coarser function than the book's.
- Type parameters are instantiated by the harness (`α := Nat` in `frontx_ind_type`, `UInt8` in `frontx_view`), exactly as the examples on `main` do; a polymorphic function is thus compiled at one instance, not generically.
- `Nat` results/arguments are one 64-bit word with `n < 2^64` side conditions (BookExamples.lean header); `List Nat` inputs are bytes (ListExamples.lean header). So "compiled" means: accepted with an automatic source-level theorem under those representation conventions, not "equal to the book's unbounded-`Nat` function on all inputs".

## Caveats

- The extractor is regex based. It drops 3 rows survey 2 listed (`Div.lean:26`, `Inequalities.lean:63`, `FunctorApplicativeMonad.lean:1081`: inside `discarding` regions or not split out). 117 `instance` commands, `theorem`s and `structure`/`inductive` declarations are not rows.
- The closure picks book declarations by name; a few contexts are wrong or incomplete (the "context" part of the not-run rows). Those 61 rows are neither compiled nor blocked here; a hand-made context may compile some (e.g. `Validate`-based checkers will not: they are monadic). In the blocker table they are absent; the "every feature" line includes them.
- `compiled on main (hand directive)` rows are not re-derived: they rest on the existing example files building (they do) and on equal normalised text. 17 of them are helpers that main compiles only inlined into a hand-written entry (`ExceptBook.lean`, `PairExamples.lean`, `IndExamples.lean`): they count as compiled because the book text is accepted verbatim as part of a compiled function, not as a standalone entry.
- Blocker buckets are by the first applicable rule (table order); a row blocked by both `String` and a dependent type is listed under the earlier one. The ranking shape (dependent types, monad/higher-kinded, `Int`, inductive shapes) is robust to this; the exact counts are not.
- The machine-level three-way tests of survey 2 were not repeated. This survey only asks whether the front end accepts the book text and generates its theorem; generated machine theorems (`Implements1`) exist only for the entries in `Riscv/Frontx/Machine.lean` and the examples built above.

## Reproduce

`Testing/notes/book_tries3/README.md`: `BS3_ROOT` layout, `extract.py` → `gen.py`/`run.py` (about 15 min, 4 cores, 1 200 Lean runs) → `gt.py` → `survey3.py` → `final.py`.
