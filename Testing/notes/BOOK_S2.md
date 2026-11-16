# Book survey 3, second third: retry of the blocked rows

Scope: the 98 `blocked` rows of `Testing/notes/book_survey3.csv` (branch `booksurvey3`) whose file is in the second third of the
sorted list of the 46 example files (`Examples/MonadTransformers.lean` … `Examples/ProgramsProofs/InstrumentedInsertionSort.lean`,
files 16-30 of 46). Book source: fp-lean @0abeea5. Compiler: `main` @f1430de (`frontx_hof`, §27; `frontx_ind` with §25 shapes).
Lean 4.29.0.

## Result

- **4 rows compile** (verbatim book text with the `ANCHOR` lines removed, `frontx_hof_entry` generates `g.prog`/`g.exec`; `#print axioms` of
  each `.exec` and of `arrFindGt3.hof`: `propext`, `Classical.choice`, `Quot.sound` only; `frontx_implements` not run): `EarlyReturn.Non.List.find?` (`Do.lean:93`), `EarlyReturn.List.find?` (`Do.lean:105`),
  `findHelper` (`Arrays.lean:293`, compiled as the callee of the entry `arrFindGt3`), `Array.find` (`Arrays.lean:304`).
  File: `Riscv/Frontx/BookS2.lean` (`lake env lean` clean, no `sorry`, no `axiom` declaration, no `native_decide`).
- **94 rows stay blocked.** All 98 rows were run through `frontx_compile`, `frontx_view`/`frontx_compile` (0-2 extra arguments),
  `frontx_ind`, `wa_compile`, and the `helper` variant; the table below gives the first error of the most specialised
  front end tried (`frontx_ind` > `wa_compile` > `frontx_view` > `frontx_compile`).
- **No test cases added.** (a) The 3 entries that compile (`nonFindGt3`, `findGt3`, `arrFindGt3`) are the same functions as the
  existing `hof_nonfindgt3`, `hof_findgt3`, `hof_arrfindgt3` tests (`Riscv/Frontx/HofExamples.lean`), so new cases would repeat them.
  (b) `Testing/asm/frontx_test.py check 50` needs `qemu-system-riscv64`, which is not installed in this container; I did not run it
  and did not install QEMU. `Testing/asm/ctest` was never created.

## Newly compiling functions

| book def | entry (`BookS2.lean`) | front end | note |
|---|---|---|---|
| `EarlyReturn.Non.List.find?` `MonadTransformers/Do.lean:93` | `nonFindGt3` (`(· > 3)`) | `frontx_hof_entry` | `.hof1` copy, `.hof`, `.exec` |
| `EarlyReturn.List.find?` `Do.lean:105` | `findGt3` (`(· > 3)`) | `frontx_hof_entry` | `do`/`failure`/`return` |
| `findHelper` `ProgramsProofs/Arrays.lean:293` | `arrFindGt3` (callee) | `frontx_hof_entry` | `.hof1.ba` over `Array UInt8` |
| `Array.find` `ProgramsProofs/Arrays.lean:304` | `arrFindGt3` (`Array.find xs.data (· > 3)`) | `frontx_hof_entry` | unfolded, then `findHelper` specialised |

The entry wrapper (`def nonFindGt3 (xs : ByteArray) …`) is ours, as in `HofExamples.lean`: the book definition takes its function
as a parameter, so `frontx_hof` needs a call with a known function.

## Blocked after retry (first error)

Errors are the first `error:` message of the attempt, with the signature the translator printed. Warnings (unused variables) are skipped.

| row | name | front end | first error | note |
|---|---|---|---|---|
| `MonadTransformers.lean:24` | `Evaluator.Eval` | frontx_compile | `frontx: unsupported result type Type` |  |
| `MonadTransformers.lean:36` | `Evaluator.bind` | frontx_compile | `frontx: unsupported result type Eval α` |  |
| `MonadTransformers.lean:40` | `Evaluator.crash` | frontx_compile | `frontx: unsupported result type Eval α` |  |
| `MonadTransformers.lean:43` | `Evaluator.lookup` | frontx_compile | `frontx: unsupported result type Eval Int lookup : Var → Eval Int` |  |
| `MonadTransformers.lean:49` | `Evaluator.applyPrim` | frontx_ind | `frontx_ind: unsupported parameter type Int applyPrim : Prim → Int → Int → Eval Int` |  |
| `MonadTransformers.lean:60` | `Evaluator.evaluate` | frontx_ind | `frontx_ind: unsupported result type Eval Int evaluate : Expr → Eval Int` |  |
| `MonadTransformers/Defs.lean:18` | `Opt.OptionT` | frontx_compile | `frontx: unsupported result type Type v` |  |
| `MonadTransformers/Defs.lean:83` | `Opt.OptionT.mk` | frontx_compile | `frontx: unsupported result type OptionT m α` |  |
| `MonadTransformers/Defs.lean:85` | `Opt.OptionT.run` | frontx_compile | `frontx: unsupported result type m (Option α)` |  |
| `MonadTransformers/Do.lean:66` | `ThenDoUnless.count` | frontx_view (+ compile) | `failed to synthesize Monad m` |  |
| `MonadTransformers/Do.lean:76` | `ThenDoUnless.countNot` | frontx_view (+ compile) | `failed to synthesize Monad m` |  |
| `MonadTransformers/Do.lean:114` | `EarlyReturn.runCatch` | frontx_compile | `frontx: unsupported result type m α` |  |
| `MonadTransformers/Do.lean:123` | `EarlyReturn.Desugared.List.find?` | frontx_view (+ compile) | `frontx: unsupported parameter type UInt8 → Bool` | higher-order; not retried with `frontx_hof`: NOTES §27 lists `Desugared.List.find?` as not done (`ExceptT … Option`) |
| `MonadTransformers/Do.lean:132` | `EarlyReturn.List.lookup` | frontx_view (+ compile) | `frontx_view: unsupported element type UInt8 × UInt8` |  |
| `MonadTransformers/Do.lean:141` | `EarlyReturn.greet` | frontx_compile | `unknown free variable `_fvar.680` greet : String → String` |  |
| `MonadTransformers/Do.lean:161` | `Many.forM` | frontx_ind | `frontx_ind: unsupported parameter type Type → Type ?u.3198` |  |
| `MonadTransformers/Do.lean:186` | `Loops.Fake.List.forM` | frontx_view (+ compile) | `failed to synthesize Monad m` |  |
| `MonadTransformers/Do.lean:222` | `Loops.AllLessThan.forM` | frontx_ind | `frontx_ind: Proven.Frontx.Run.Loops.AllLessThan.forM.countdown has no argument of a declared type` |  |
| `MonadTransformers/Do.lean:258` | `Loops.Transformed.OptionT.exec` | frontx_compile | `frontx: unsupported result type m Unit` |  |
| `MonadTransformers/Do.lean:324` | `Loops.List.find?` | frontx_view (+ compile) | `frontx_view: the body is not a `match` do let r ← forIn (view B i) ⟨none, PUnit.unit⟩ fun x r => have r := r.snd; if p x = true then pure (ForInStep.d` |  |
| `MonadTransformers/Do.lean:332` | `Loops.Cont.List.find?` | frontx_view (+ compile) | `frontx_view: the body is not a `match` do let r ← forIn (view B i) ⟨none, PUnit.unit⟩ fun x r => have r := r.snd; have __do_jp := fun y => pure (ForIn` |  |
| `MonadTransformers/Do.lean:345` | `Loops.List.count` | frontx_view (+ compile) | `frontx_view: the body is not a `match` (have found := 0; do let r ← forIn (view B i) found fun x r => have found := r; if p x = true then have found :` |  |
| `Monads.lean:316` | `Monads.Writer.isEven` | frontx_compile | `frontx: unsupported parameter type Int` |  |
| `Monads.lean:325` | `Monads.Writer.sumAndFindEvens` | frontx_view (+ compile) | `frontx_view: unsupported element type Int` |  |
| `Monads.lean:334` | `Monads.Writer.MoreMonadic.sumAndFindEvens` | frontx_view (+ compile) | `frontx_view: unsupported element type Int` |  |
| `Monads.lean:344` | `Monads.Writer.inorderSum` | frontx_ind | `frontx_ind: Proven.Frontx.Run.Monads.Writer.inorderSum: type mismatch inorderSum : BinTree Int → List Int × Int` |  |
| `Monads.lean:369` | `Monads.Writer.andThen` | frontx_ind | `frontx_ind: unsupported parameter type Nat → WithLog Nat ?γ` | higher-order; not retried with `frontx_hof`: NOTES §27 lists `Writer.andThen` as not done (monad `WithLog`) |
| `Monads.lean:377` | `Monads.Writer.ok` | frontx_ind | `frontx_ind: Proven.Frontx.Run.Monads.Writer.WithLog.mk has no equations` |  |
| `Monads.lean:382` | `Monads.Writer.save` | frontx_ind | `frontx_ind: Proven.Frontx.Run.Monads.Writer.WithLog.mk has no equations` |  |
| `Monads.lean:390` | `Monads.Writer.WithAndThen.sumAndFindEvens` | frontx_ind | `frontx_ind: List.brecOn has no argument of a declared type sumAndFindEvens : List Int → WithLog Int Int` |  |
| `Monads.lean:400` | `Monads.Writer.WithAndThen.inorderSum` | frontx_ind | `frontx_ind: Proven.Frontx.Run.Monads.Writer.WithAndThen.inorderSum: type mismatch inorderSum : BinTree Int → WithLog Int Int` |  |
| `Monads.lean:460` | `Monads.State.number` | frontx_ind | `frontx_ind: Prod.snd has no argument of a declared type` |  |
| `Monads.lean:488` | `Monads.State.State` | frontx_compile | `frontx: unsupported result type Type` |  |
| `Monads.lean:500` | `Monads.State.set` | frontx_compile | `frontx: unsupported result type State σ Unit` |  |
| `Monads.lean:506` | `Monads.State.andThen` | frontx_compile | `frontx: unsupported result type State σ β` |  |
| `Monads.lean:516` | `Monads.State.ok` | frontx_compile | `frontx: unsupported result type State σ α` |  |
| `Monads/Class.lean:49` | `firstThirdFifthSeventh` | frontx_view (+ compile) | `failed to synthesize Monad m` |  |
| `Monads/Class.lean:125` | `IdentMonad.Id` | frontx_compile | `frontx: unsupported result type Type` |  |
| `Monads/Class.lean:148` | `MyListStuff.mapM` | frontx_view (+ compile) | `failed to synthesize Monad m` |  |
| `Monads/Class.lean:346` | `One.evaluateOption` | frontx_ind | `frontx_ind: Proven.Frontx.Run.One.evaluateOption: type mismatch evaluateOption : Expr Arith → Option Int` |  |
| `Monads/Class.lean:362` | `Two.applyPrim` | frontx_ind | `frontx_ind: unsupported parameter type Int applyPrim : Arith → Int → Int → Option Int` |  |
| `Monads/Class.lean:368` | `Two.evaluateOption` | frontx_ind | `frontx_ind: Proven.Frontx.Run.Two.evaluateOption: type mismatch evaluateOption : Expr Arith → Option Int` |  |
| `Monads/Class.lean:391` | `Three.applyPrim` | frontx_ind | `frontx_ind: unsupported parameter type Int applyPrim : Arith → Int → Int → Except String Int` |  |
| `Monads/Class.lean:400` | `Three.evaluateExcept` | frontx_ind | `frontx_ind: Proven.Frontx.Run.Three.evaluateExcept: type mismatch evaluateExcept : Expr Arith → Except String Int` |  |
| `Monads/Class.lean:414` | `Four.applyPrimOption` | frontx_ind | `frontx_ind: unsupported parameter type Int applyPrimOption : Arith → Int → Int → Option Int` |  |
| `Monads/Class.lean:423` | `Four.applyPrimExcept` | frontx_ind | `frontx_ind: unsupported parameter type Int applyPrimExcept : Arith → Int → Int → Except String Int` |  |
| `Monads/Class.lean:432` | `Four.evaluateM` | frontx_ind | `frontx_ind: Proven.Frontx.Run.Four.evaluateM: type mismatch` |  |
| `Monads/Class.lean:464` | `FourPointFive.applyDivOption` | frontx_compile | `frontx: unsupported result type Option Int` |  |
| `Monads/Class.lean:469` | `FourPointFive.applyDivExcept` | frontx_compile | `frontx: unsupported result type Except String Int` |  |
| `Monads/Class.lean:474` | `FourPointFive.applyPrim` | frontx_ind | `frontx_ind: unsupported parameter type Type → Type ?u.5563` |  |
| `Monads/Class.lean:482` | `FourPointFive.evaluateM` | frontx_ind | `frontx_ind: Proven.Frontx.Run.FourPointFive.evaluateM: type mismatch` |  |
| `Monads/Class.lean:525` | `divOption` | frontx_ind | `frontx_ind: unsupported parameter type Int divOption : CanFail → Int → Int → Option Int` |  |
| `Monads/Class.lean:528` | `divExcept` | frontx_ind | `frontx_ind: unsupported parameter type Int divExcept : CanFail → Int → Int → Except String Int` |  |
| `Monads/Class.lean:534` | `applyPrim` | frontx_ind | `frontx_ind: unsupported parameter type Type → Type ?u.6249` |  |
| `Monads/Class.lean:542` | `evaluateM` | frontx_ind | `frontx_ind: Proven.Frontx.Run.evaluateM: type mismatch` |  |
| `Monads/Class.lean:554` | `applyEmpty` | frontx_compile | `frontx: unsupported result type m Int` |  |
| `Monads/Class.lean:585` | `applySearch` | frontx_ind | `frontx_ind: unsupported parameter type Int applySearch : NeedsSearch → Int → Int → Many Int` |  |
| `Monads/Class.lean:657` | `Reader` | frontx_compile | `frontx: unsupported result type Type` |  |
| `Monads/Class.lean:778` | `Temp.Reader.bind` | frontx_compile | `frontx: unsupported result type β` |  |
| `Monads/Class.lean:787` | `Reader.bind` | frontx_compile | `frontx: unsupported result type Reader ρ β` |  |
| `Monads/Class.lean:808` | `Reader.pure` | frontx_compile | `frontx: unsupported result type Reader ρ α` |  |
| `Monads/Class.lean:954` | `Exercises.BinTree.mapM` | frontx_ind | `frontx_ind: unsupported parameter type Type → Type ?u.4314` |  |
| `Monads/Class.lean:1025` | `Exercises.ReaderOption` | frontx_compile | `frontx: unsupported result type Type` |  |
| `Monads/Class.lean:1027` | `Exercises.ReaderExcept` | frontx_compile | `frontx: unsupported result type Type` |  |
| `Monads/Conveniences.lean:20` | `Old.equal?` | frontx_compile | `frontx: unsupported result type Option α` |  |
| `Monads/Conveniences.lean:32` | `New.equal?` | frontx_compile | `frontx: unsupported result type Option α` |  |
| `Monads/Conveniences.lean:124` | `condense` | frontx_compile | `frontx: unsupported result type α` |  |
| `Monads/Conveniences.lean:139` | `getTheNat` | frontx_compile | `frontx: unsupported parameter type Type` |  |
| `Monads/Conveniences.lean:155` | `getTheString` | frontx_compile | `unknown free variable `_fvar.1312`` |  |
| `Monads/Do.lean:110` | `WithDo.firstThirdFifthSeventh` | frontx_view (+ compile) | `failed to synthesize Monad m` |  |
| `Monads/Do.lean:121` | `WithDo.mapM` | frontx_view (+ compile) | `failed to synthesize Monad m` |  |
| `Monads/Do.lean:133` | `mapM` | frontx_view (+ compile) | `failed to synthesize Monad m` |  |
| `Monads/Many.lean:11` | `Many.one` | frontx_ind | `frontx_ind: Proven.Frontx.Run.Many.more has no equations` |  |
| `Monads/Many.lean:24` | `Many.fromList` | frontx_ind | `frontx_ind: List.brecOn has no argument of a declared type` |  |
| `Monads/Many.lean:31` | `Many.take` | frontx_ind | `frontx_ind: unsupported result type List Nat` |  |
| `Monads/Many.lean:36` | `Many.takeAll` | frontx_ind | `frontx_ind: unsupported result type List Nat` |  |
| `Monads/Many.lean:172` | `Many.range` | frontx_ind | `frontx_ind: Proven.Frontx.Run.Many.range._unary has no argument of a declared type Many.range : Nat → Nat → Many Nat` |  |
| `Monads/Many.lean:270` | `addsTo` | frontx_ind | `frontx_ind: List.brecOn has no argument of a declared type addsTo : Nat → List Nat → Many (List Nat)` |  |
| `ProgramsProofs/Arrays.lean:274` | `arrayMapHelper` | wa_compile | `wa_compile: expected a function of one ByteArray` |  |
| `ProgramsProofs/Arrays.lean:285` | `TailRec.Array.map` | wa_compile | `wa_compile: expected a function of one ByteArray` |  |
| `ProgramsProofs/Arrays.lean:316` | `Huh.findHelper` | wa_compile | `wa_compile: expected a function of one ByteArray` | same body as `findHelper` (Arrays.lean:293), namespace `Huh`; retried with `wa_compile` only |
| `ProgramsProofs/Fin.lean:48` | `Fin.next?` | frontx_compile | `frontx: unsupported result type Option (Fin n)` |  |
| `ProgramsProofs/Fin.lean:82` | `Finny.findHelper` | wa_compile | `wa_compile: expected a function of one ByteArray` |  |
| `ProgramsProofs/Fin.lean:93` | `Finny.Array.find` | wa_compile | `wa_compile: expected a function of one ByteArray` |  |
| `ProgramsProofs/Inequalities.lean:15` | `merge` | frontx_view (+ compile) | `frontx_view: cannot reduce match compare B[i] B[k] with / Ordering.lt => B[i] :: merge (view B (i + 1)) (B[k] :: view B (k + 1)) / Ordering.eq => B[i]` |  |
| `ProgramsProofs/Inequalities.lean:27` | `splitList` | frontx_view (+ compile) | `frontx: unsupported result type List UInt8 × List UInt8` |  |
| `ProgramsProofs/Inequalities.lean:767` | `mergeSort` | frontx_view (+ compile) | `frontx_view: the body is not a `match` if h : (view B i).length < 2 then match view B i, h with / [], h => [] / [x], h => [x] else let halves := split` |  |
| `ProgramsProofs/InsertionSort.lean:49` | `insertSorted` | wa_compile | `wa_compile: expected a function of one ByteArray` |  |
| `ProgramsProofs/InsertionSort.lean:328` | `Partial.insertionSortLoop` | wa_compile | `wa_compile: expected a function of one ByteArray` |  |
| `ProgramsProofs/InsertionSort.lean:430` | `insertionSortLoop` | wa_compile | `wa_compile: expected a function of one ByteArray` |  |
| `ProgramsProofs/InsertionSort.lean:441` | `insertionSort` | wa_compile | `wa_compile: expected a function of one ByteArray` |  |
| `ProgramsProofs/InstrumentedInsertionSort.lean:6` | `insertSorted` | wa_compile | `wa_compile: expected a function of one ByteArray` |  |
| `ProgramsProofs/InstrumentedInsertionSort.lean:26` | `insertionSortLoop` | wa_compile | `wa_compile: expected a function of one ByteArray` |  |
| `ProgramsProofs/InstrumentedInsertionSort.lean:35` | `insertionSort` | wa_compile | `wa_compile: expected a function of one ByteArray` |  |
