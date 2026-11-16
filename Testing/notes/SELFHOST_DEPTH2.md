# Self-hosting depth probe 2: the compiler's pure core against current `main`

Branch `selfhost-depth2` (from `origin/main` @ b8199bc). Lean 4.29.0, Sail model `opencompl/sail-riscv-lean` @ 51c635c.
Same method as `SELFHOST_DEPTH.md` (branch `selfhost-depth`): call graph read from the Lean environment (`scripts/Cg2.lean`), then
`frontx_compile f` on each definition (verbatim, no source changed), then `frontx_ind f on T` on the definitions whose first message names a type.
Facts = from runs. Inferences are marked **(inf.)**. No compiler source was modified.

## 0. What was run

1. Roots: every non-Prop, non-type definition of `Compiler.Ir.*` (except `Examples`, `Sim`), `Compiler.Opt.*`, `Riscv.Back.IrTop` (`Ir.compile`, `compileW`),
   `Riscv.Back.IrTarget`, `Riscv.Back.Wide` (encoders), `Spec.Code` (encoders), plus `Proven.Top.compile`. **597 roots; closure 1 163 rows: 858 definitions**,
   76 inductives, 225 constructors (`out/cg.tsv`). The first probe had 460 definitions from `Top.compile`, so the denominators differ.
   Of the 858, **236 are generated or type-valued** (`.elim`, `ctorElim`, `ctorElimType`, `toCtorIdx`, instances, `Repr`, `DecidableEq`, results `Type`/`Prop`/`Sort`/`Decidable`); they are reported separately and leave **622 program definitions**, the denominator of §2. The per-definition split is in `out/blockers_per_def.tsv`.
2. `frontx_compile f` on all 858 (`P1`): 10 compile.
3. The 848 failing ones: the 328 whose signature mentions one of 24 types that `frontx_ind_type` now accepts were retried as `frontx_ind f on T` (`P2`). The type `T` is the first accepted type in the signature (the others go into `using`). This mapping is coarse (see caveats).
4. Type gate (`T2.lean`, `out/T2.out`): **all 25 types accepted**, including the ones rejected in the first probe: `Mach.IR.Code Nat` (3 recursive fields, rejected as `loop2` before),
   `Mach.IR.Ins Nat` (more than one scalar), `Mach.BStmt`, `Mach.Sel.SExp`, `Exp`, `AExp`, `Mach.BExp`, `Ir.Inst/Rhs/Term/Block Nat`, all enums (`Op`, `MOp`, `Cond`, `WOp`, `LiStep`, `Ir.EOp`, `Ind.Kd`, `Ind.Fld`).
   Acceptance of the type is not acceptance of a function over it (see §2).

## 1. Result: totals against the first probe

| | first probe (`SELFHOST_DEPTH.md`) | this probe |
|---|---|---|
| definitions probed | 460 (Top.compile closure) | 858 (IR + Opt + encoders + Top.compile closure) |
| generated / type-valued, excluded | — | 236 |
| compile verbatim (`frontx_compile`) | 5 | **10** (`Sel.tk`, `rn`, `RedC.k`, `RedC.loop`, `CS.onOut`, `CS.rev`, `CS.s0`, `Ir.GS.cl`, `Ir.GS.nl`, `Ir.Lay.ex`) |
| compile via `frontx_ind` (`P2`), no message | 4 (`Op.f3`, `Op.f7`, `MOp.f3`, `Cond.neg`) | **21 further program defs** with no error (incl. the same four) |
| **program definitions OK, upper bound** | 5 of 460 (1 %) | **31 of 622 (5 %)**; 10 of these are verified by a message, 21 are not |
| blocked | 455 | 591 of 622 (95 %) |

Verification: each `frontx_compile` success prints `frontx: <f>: … translate + step proof …` (checked for all 10; `Sel.tk.step1` checked by `#check`).
A `frontx_ind` success prints nothing; the 21 are the lines with no error at their position. Consistent with the first probe (the four known ones are among them), but **not verified**.

## 2. Blocker table (program definitions, 622; final class after the `frontx_ind` retry)

Class = the feature named by the first message (`out/blockers_per_def.tsv`, `scripts/analyze3.py`). "own" = definitions blocked by that class first.

| # | class | own | what the message says (top examples) |
|---|---|---:|---|
| 1 | **translator / `frontx_ind` shape, no type named** | **217** | `frontx_ind: X has no argument of a declared type` 32; `Unknown constant` 29 (`Ir.IndLow.bin`, `*.elim`); `equation ite.eq_1 has no constructor pattern` 22; `List.brecOn has no argument …` 16; `invalid instantiateForall, too many parameters` 15 (`Mach.WideF.frameAt`); `Application type mismatch … Base.get` 10; kernel `Sim argument has type Type 1` 6; `more than one extra parameter` 5; `a scalar parameter needs an entry` 5 |
| 2 | List of non-bytes (`List (BitVec 32)`, `List Nat`, `List WOp`, `List α`, `List (Nat×Nat)`) | 95 | `unsupported result type List (BitVec 32)` (29), `List Nat`, `List α` |
| 3 | inductive / structure type as parameter or result (shape or arguments) | 88 | `unsupported parameter type Proven.…` for `IR.Code ρ`, `Wide`, `Tst`, `XStage`, `CS` |
| 4 | record / monad / structure result, record with function fields (`Mach.Wide`, `WideF`, `Base`, `Core`, `Ir.SC/TC/GS`, `Ir.Func`, `Ir.Prog`) | 61 | `unsupported result type Proven.Ir.SC` (monadic structure, `Ir.Struct`), `Ir.Func VReg`, `Option (List (BitVec 32))` |
| 5 | sized `BitVec` (32/12/20/3) and `Fin n` | 47 | `BitVec 32` (34), `BitVec 12` (5), `Fin 32` (5), `Fin 4 → BitVec 64` |
| 6 | tuples (`×`) | 23 | `Option (Nat × Nat)`, `List X × X` |
| 7 | `Option` / `Except` with payload | 18 | `Option (List UInt8)`, `Option (Nat → …)`, `Option Nat` |
| 8 | polymorphism (`ρ`, `α`, `σ`, `β`) | 15 | `unsupported result type X ρ`, `Ir.Tst.map` |
| 9 | higher-order (`Nat → Reg`, `(Nat → Nat → …) × …`, `Nat → Bool`) | 14 | `Option (Nat → Reg)`, `Sel.gen`, `Exp.denote` |
| 10 | non-computation (`Decidable`, `Type`, `Prop`, `Sort`) | 8 | `unsupported parameter type Type` |
| 11 | other (`Op.eval`, `LiStep.eval`) | 5 | enum-valued result, `BitVec 64` parameter |
| | **OK** | **31** | 10 verified, 21 unverified |

Own features are **read from messages**, so a definition can have several features; the first message is what the translator reports.

## 3. Smallest feature set that unblocks the most

Greedy on the closure (exact call graph): a definition is unblocked if every definition in its closure is OK or has a feature in the set.
Baseline 30 of 622. Class 1 (translator / `frontx_ind` shape, 217 own) is not a feature in this list and is never unlocked by one.

| step | add | unblocked (of 622) |
|---|---|---:|
| 0 | — | 30 |
| 1 | inductives / structures (class 3) | 98 |
| 2 | + List of non-bytes (class 2) | 146 |
| 3 | + sized BitVec / Fin (class 5) | 196 |
| 4 | + records / monads (class 4) | 224 |
| 5 | + tuples (class 6) | 242 |
| 6 | + Option / Except payload (class 7) | 263 |
| 7 | + polymorphism (class 8) | 283 |
| 8 | + non-computations (class 10) | 293 |
| 9 | + higher-order (class 9) | 301 |

Reading. 301 of 622 is the ceiling for the nine features; the remaining 321 are held up by class 1 (translator crashes and `frontx_ind` shape rejections).
The first probe ended its greedy at 382 of 391 nodes (records last); the numbers are not comparable (different roots and denominators).
**(inf.)** The step that matters most now is inductives (class 3, +68), and it is cheaper than the first probe suggested because the shape gate has already accepted the n-ary types. The largest remaining block is no longer a missing feature but translator behaviour (class 1).

## 4. The IR back end: `Ir.compile` and its passes

`Ir.compile` (`Riscv/Back/IrTop.lean:31`) and `Ir.compileW` (`:25`): closure 256 and 218 nodes.

* **First message of `Ir.compile` (fact):** `Application type mismatch: The argument Proven.Mach.Wide.fr has type (self : Mach.Wide) → self.S → BitVec 64 … apply_ite Proven.Mach.Wide.fr`.
  So the root fails on a **record field of function type applied as a function** (class 4). `compileW` fails the same way.
* **Blocked nodes in the closure of `Ir.compile` (fact):** TRANS 76, BV 40, LIST 35, REC 26, IND 16, NONCOMP 6, POLY 6, TUP 5, OPT 5, OTHER 4, HO 3.
  Of the 76 TRANS nodes: `frontx_ind` "no argument of a declared type" 14, `instantiateForall` 12, `ite.eq_1` 10, `List.brecOn` 9, kernel `Sim` 5, others.
* **Single feature (inf.):** none makes `Ir.compile` compile on its own. The root's own message is a record-field projection (REC). Removing REC alone leaves 40 BV nodes, 35 LIST nodes and 76 translator-level nodes in its closure.
  The smallest set I can name from the data is {REC, BV, LIST} plus fixing the translator-level shape rejections (class 1) for `IndLow`/`Struct`. This is an inference from the classes, not a tested compile.

## 5. Caveats

* **Retry mapping is coarse.** Each `frontx_ind` retry uses the first type in the signature. 32 of the 97+ `frontx_ind` errors are `… has no argument of a declared type`, which is the wrong-target case: the function takes no argument of that type. Some blocked definitions would pass with the right `T`; I did not search over `T`.
* **21 `frontx_ind` successes are unverified** by message (see §1); the 10 `frontx_compile` successes are verified.
* **Classes are regex over messages**, not over types. The class-1 bucket (217) is the largest and least precisely identified.
* Generated / type-valued exclusion (236) is a name and result-type regex; some instance-like programs may be excluded by mistake.
* Build: `lake build Frontx` needed a Sail rebuild (374 jobs) because the build cache is for `fa8183c`, not `b8199bc`; the Frontx build itself has no errors.
* `P1.out` (65 545 lines) is not committed; per-definition results are in `out/blockers_per_def.tsv`.

## 6. Reproduce

```
lake build Frontx
lake env lean --tstack=4000000 Testing/selfhost-depth2/scripts/Cg2.lean > out/cg.tsv      # roots = IR/Opt/encoder modules
python3 scripts/mkprobe2.py    # frontx_compile on each def  (run from the probe directory with out/cg.tsv)
lake env lean --tstack=4000000 -DmaxErrors=100000 P1.lean > P1.out
python3 scripts/mkP2.py        # frontx_ind retry (328)
lake env lean --tstack=4000000 -DmaxErrors=100000 P2.lean > P2.out
python3 scripts/analyze3.py    # classes, greedy, Ir.compile closure
```
`scripts/T2.lean`: type gate. `scripts/fullmsg.py`: multi-line message capture.
