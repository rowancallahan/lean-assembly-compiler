# BOOK_S4: blocked survey rows with an `Int`, monad, `Except`/`State` or tuple error, retried on `main`

Source: `Testing/notes/book_survey3.csv` (branch `booksurvey3`), book `fp-lean` @0abeea5, base `origin/main` (NOTES §25-§32).
Build: `lake build Frontx` succeeds. Harness: `Riscv/Frontx/BookS4.lean`, emitter `Testing/asm/emit_s4.lean`.

## Result

- Candidate rows: **114** blocked rows whose blocker or first error mentions structures, `Int`, monads / `State` / `Except` / `Reader`, or tuples.
- Retried with the survey's variants (`frontx_compile`, `frontx_view` + `frontx_compile`, `frontx_ind` with the inductive argument, `wa_compile`): **1 compiles**, `Finite.isSingleton`, which is already in `BookS1.lean`. No new row from those variants.
- Retried by hand with a `requires` range (the `Int` convention of `IntExamples.lean`): **1 new row compiles**, `Monads.Writer.isEven` (`Monads.lean:316`), as `isEvenE`.
- Machine check: `python3 Testing/asm/frontx_test.py check 50 s4_iseven` → `50 cases ok (QEMU == Sail == Lean)`.

| row | file:line | command | result |
|---|---|---|---|
| `Monads.Writer.isEven` | `Examples/Monads.lean:316` | `frontx_compile … requires fun i => -2^63 ≤ i ∧ i < 2^63` + glue `isEvenE`, `frontx_implementsC` | **compiles, tested** |

## Why the other 113 still fail (first error, grouped)

- **`Option Int`, `Except String Int`, `Eval Int`, `m Int` results**: the front ends take scalar, `Option`/`Except` of scalars, not a monadic result of `Int` (`divOption`, `Two.evaluateOption`, `Evaluator.*`, `OptionT.*`).
- **Enum or inductive parameters** (`CanFail`, `Arith`, `Expr Arith`, `Many`, `NestedPairs`): `frontx_compile` says `unsupported parameter type`; `frontx_ind` gives `no equations` or `Type mismatch` for the monadic ones.
- **Tuples and lists of pairs** (`List Int × Int`, `List (α × β)`, `unzip`, `mergeSort`): unsupported result or element type.
- **Structures with `Float` or `String` fields** (`Point`, `Config`): `Point.mk has no equations`.
- **`Nat.brecOn` / `List.brecOn` / `Many` recursion** (`addNatPos`, `Many.one`, `Many.fromList`): `frontx_ind` cannot build the equations.
- **Generic `[Monad m]` / `m α` definitions** (`mapM`, `firstThirdFifthSeventh`, `List.forM`, `evaluateM`): the harness does not specialise; the monadic entries of §29 need a concrete monad and a hand-written entry.
- **Polymorphic `α`, `State σ α`, `Reader ρ α`**: `unsupported result type`.

Not done: the `frontx_monad_entry` / `frontx_hof_entry` specialisations of the generic monadic rows (they need hand-written entries, which are not verbatim retries). Those are the next candidates.

## Verbatim copies

`Riscv/Frontx/BookS4.lean` holds the definition verbatim (`Monads.lean:316-317`). The `namespace Monads.Writer` wrapper, `requires`, glue `isEvenAt`/`isEvenE` and the commands are ours, as in `IntExamples.lean`. No book code was edited; no `sorry`, axiom or `native_decide`; no compiler source was modified.

## Reproduce

`lake build Frontx`; `lake env lean --tstack=400000 Testing/asm/emit_s4.lean`; `python3 Testing/asm/frontx_test.py check 50 s4_iseven`.
Survey harness used for the 114 rows (outside the repo): `book_tries3/run.py` and `gen.py` of `booksurvey3`, with `BS3_ROOT` pointing at an fp-lean checkout at 0abeea5.
