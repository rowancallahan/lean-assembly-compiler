# Self-hosting depth probe: the compiler's pure core through the front ends

Branch `selfhost-depth` (from `main` @ 46759c8; nothing in `Spec/ Compiler/ Riscv/ Arm/` changed). Lean 4.29.0, Sail model `opencompl/sail-riscv-lean` @ 51c635c.
Same method as `CONLECHE_DEPTH.md` (branch `conleche-depth`), but the call graph is **exact**: it is read from the Lean environment (constants in each definition's value,
`Testing/selfhost-depth/scripts/Cg.lean`), not from names. Tags: **run** = the front end's own message; **read** = from types/constants of the definitions (regex, not machine-checked).

## 0. What was done

1. Roots: `Proven.Top.compile` (`Riscv/Back/Top.lean:183`, → `compileX1` → `compileBFO`/`pickB`, the optimiser `Compiler/Opt/*`, the encoders, `XPipe` front half),
   plus the inductive path: `Mach.Ind.indProgM` (`Compiler/Ind.lean:503`) and `MachineC.compP` (`Compiler/CProg.lean:68`). Result: **460 definitions** (theorems, inductives, constructors, `match_`/`eq_` auxiliaries excluded);
   **391 under `Top.compile`**, 299 under `compBFO`, 32 under `indProgM`, 42 under `compP`. `out/cg.tsv`: kind, name, module, line, callees, type, Lean-core constants used.
2. Each of the 460 definitions, **verbatim** (the compiler's own modules imported, no copy): `frontx_compile f` (`out/P1.lean/.out`), `wa_compile f` (`out/P3.*`).
3. For the 31 functions whose first message names only a type that `frontx_ind_type` accepts: `frontx_ind f on T` (`out/P2.*`). Types tried (`out/T1.lean`): accepted `IR.Arg Nat`, `IR.Tst Nat`, `AStmt`, `Op`, `Cond`, `LiStep`, `BPred`, `XStage`, `Kd`, `YOp`, `XOp`, `Stage`, `MOp`;
   **rejected**: `IR.Code Nat` (`loop2`: more than two recursive fields), `IR.Ins Nat` (`ldS`: more than one scalar), `BStmt`, `Mach.BStmt` (`load`: more than one scalar), `AExp`, `BExp`, `Mach.BExp`, `ByteExp`, `Sel.SExp` (`ite`: more than two recursive fields), `Mach.CStmt` (`call`: more than one scalar), `Mach.WOp` (`br`: more than one scalar).
4. `wa_compile`: **0 of 460** (414 "expected a function of one ByteArray"; the rest are the same non-function cases). No function of the core takes a byte array, so the word-array route is not applicable here.

## 1. Result

**5 of 460 compile verbatim**, none with a body that is more than a table:

| function | where | route |
|---|---|---|
| `Sel.tk` | `Compiler/Opt/Sel.lean:34` | `frontx_compile` (7 variables) |
| `Op.f3`, `Op.f7` | `Spec/Code.lean:66,65` | `frontx_ind … on TOp` (11 arms) |
| `MOp.f3` | `Riscv/Back/Wide.lean:158` | `frontx_ind … on TMOp` (3 arms) |
| `Cond.neg` | `Compiler/Wide.lean:24` | `frontx_ind … on TCond` (6 arms, tree result) |

I did not run `implements1`/QEMU on them. **The roots fail at once on the result type**: `Top.compile` (`Option Compiled`), `compileX1` (`Except String (List (BitVec 32))`), `compBFO` (`List (BitVec 32)`), `pickB`/`compileOptB`/`tryB`/`tryL` (translator error `Application type mismatch … Base.get`, i.e. a record-valued argument).
336 of the 391 functions under `Top.compile` (86 %) fail at the **type gate** ("unsupported result/parameter type"); the translator checks result then parameter types before the body, so every body-level blocker below the gate is only known by **read**.
Of 159 leaf functions (no callee in the graph) 5 compile.
The five encoders surveyed in `SELFHOST_SURVEY.md` are unchanged: `encR/encI/wB/wJ/G.encU/encL/encS` → `unsupported result type BitVec 32`, `brOff` → `BitVec 12`, `jOff` → `BitVec 20`, `condF3` → `BitVec 3`, `phys` → `Fin 32`, `fits12` → `unsupported term … toInt % …`; `Op.f3` (survey: `unsupported parameter type Op`) **now compiles** through `frontx_ind`.

## 2. Blocker table (sorted by impact; subset = under `Top.compile`, 391 functions)

"first" = functions whose **first** message (run) is this class (result or parameter type). "own" = functions whose type or body uses the feature (read). "trans" = functions with a callee, itself included, that uses it (read, exact graph, so a true count of the closure, not an upper bound; but a feature in a branch that is never reached still counts). Example = `function file:line`.

| # | feature | first (run) | own | trans | example |
|---|---|---:|---:|---:|---|
| 1 | higher-order arguments / function-valued results (`Nat → Code Nat`, `Nat → Reg`, closure params of `foldl/filter/mergeSort/any`) | 3 (`function type`) + hidden | 187 | 226 | `IR.SR.isInc` `Compiler/Opt/SR.lean:565`; `IR.Hoist.repA` `Opt/Hoist.lean:39`; `IR.color` `Opt/Color.lean` (result `Option (Nat → Reg)`) |
| 2 | recursive inductive with **> 2 recursive fields**: `IR.Code` (`loop2`), `AExp/BExp/ByteExp/Sel.SExp` (`ite`) | 96 | 121 | 176 | `IR.Peep.peep` `Opt/Peep.lean:193`; `BExp.av` `Front/PipeI.lean:63`; `ByteExp.noAcc` `Front/Pipe.lean:54` |
| 3 | `List` of non-bytes (`List (BitVec 32)`, `List Nat`, `List (Nat×Nat)`, `List BStmt/AStmt/AExp/YOp/XOp/WOp/LiStep`) and `++ map filter foldl flatMap mergeSort` | 61 | 150 | 173 | `Wide.wenc` `Back/Wide.lean`; `compBFO` `Back/OptB.lean:270`; `mgenB` `Compiler/BStmt.lean` |
| 4 | recursive inductive with **> 1 scalar field**: `BStmt`, `Mach.BStmt`, `CStmt`, `IR.Ins`, `WOp`, `CS`/`Prog` | 49 | 102 | 142 | `okR` `Front/PipeI.lean:70`; `IR.Ins.regs` `Opt/Alloc.lean:40`; `CS.clean` `Front/Pipe.lean:171` |
| 5 | `Fin n` values (`Reg = Fin 15`, `Fin 32`, `Fin 8`) | 17 | 95 | 140 | `phys` `Back/Wide.lean`; `rn` `Front/PipeStdB.lean:22`; `Base.get` `Compiler/Iface.lean:75` |
| 6 | sized `BitVec` (32/12/20/3) results and ops (`setWidth`, `signExtend`, `extractLsb'`, `++`) | 40 | 74 | 103 | `encR` `Spec/Code.lean`; `brOff` `Back/Wide.lean`; `fits12` `Back/Wide.lean:21` (`toInt %`); `zx` `Front/Pipe.lean:60` (`Decidable.rec`) |
| 7 | `Option` / `Except` with payload (`Option Compiled`, `Option (List (BitVec 32))`, `Except String …`) | 9 | 75 | 117 | `Top.compile` `Back/Top.lean:183`; `pickB` `Back/OptB.lean:156`; `Sel.opnd` `Opt/Sel.lean:74` |
| 8 | enum inductives as values (`Op`, `Cond`, `LiStep`, `MOp`, `XStage`): **accepted by `frontx_ind` now**; remaining block is the scalar parameter next to them (`BitVec 64`) | 5 (`unsupported parameter type BitVec 64`) | 40 | 113 | `Op.eval` `Spec/Code.lean:11`; `Cond.eval` `Compiler/Wide.lean:16`; `LiStep.eval` `Back/Wide.lean:38`; `Riscv.liPlan` `Back/Wide.lean:67` |
| 9 | tuples as values (`List Nat × …`, `Code × Arg × Nat`) | 3 + | 56 | 90 | `Sel.ops2` `Opt/Sel.lean:96`; `IR.ig` `Opt/Color.lean` |
| 10 | record / structure with function fields (`Machine`, `MachineF`, `MachineC`, `WideF`, `Wide`, `Core`, `Base`, `Fn`) | 19 | 47 | 55 | `WideF.optB` `Opt/BFn.lean:98`; `Base.get` `Iface.lean:75` (`invalid instantiateForall`) |
| 11 | non-computations: `Type`, `Prop`, `Decidable`, `DecidableEq`, polymorphic `α/ρ` | 29 | 54 | 173 | `XPipe` `Front/PipeStd.lean:179` (`def XPipe := List XStage`, result `Type`); `IR.subL` `Opt/Live.lean:93` |
| 12 | `String` values (error messages only) | 0 first | 9 | 9 | `wfErrB` `Front/PipeStdBMachine.lean:26`; `compileOptB` `Back/OptB.lean:185` |
| 13 | translator/shape failures that are not a type: `unknown free variable _fvar` crash ×5 (`XPipe.chkErr`, `XStage.chk`, `Stage.chk`, `Red.chk`, `wfErrB`), `invalid instantiateForall` ×7 (`Wide.immOK/offOK/jOK/brOK`, `MachineF.frameAt`, …), `frontx_ind` "has no equations"/"nested patterns"/`brecOn` ×~12, "could not prove `BExp.denote …`" ×2 (`jOK`, `brOK`) | ~40 | – | – | `XStage.isSort` `Front/PipeStdB.lean:244` (nested patterns); `loopV` `Front/Pipe.lean:188` (`AStmt.seq has no equations`); `fetchG` `Pipe.lean:181` (`List.brecOn`) |

Not present in the core (so not blockers, unlike con-leche): `HashMap`, `Array`, `Int` (only `toInt` inside `fits12`/`brOff`), `partial`, `USize`, monads/`StateT`, nullary constants (1: `NS`, `introN failed`).
Full per-class counts: `out/an_compile.txt` (also `an_ind.txt`, `an_compP.txt`, `an_all.txt` for the other roots; for `indProgM` all 32 functions are blocked, 19 first at a `BStmt`/`CStmt`-class result).

## 3. Call tree of `Top.compile`

Full DFS with every one of the 391 nodes, status and the read features: `out/tree.txt` (716 lines with repeats). First levels, **run** status; `{}` = features by read:

```
Top.compile [Back/Top.lean:183]                BLOCKED result Option Compiled           {Opt,Str}
├ compileX1 [Front/PipeIMachine.lean:153]      BLOCKED result Except String (List (BitVec 32))  {BV,List,Opt,Str}
│ ├ XPipe.chkErr [Front/PipeStdMachine.lean:10] BLOCKED translator crash (unknown free variable)  {List,Opt,Str}
│ │ └ XStage.chk → Stage.chk, Red.chk → BPred.noAcc, ByteExp.noAcc   BLOCKED crash / parameter ByteExp (>2 rec. fields)
│ ├ okR [Front/PipeI.lean:70]                  BLOCKED parameter BStmt (>1 scalar)      → BExp.av  BLOCKED parameter BExp
│ ├ XPipe.progB [Front/PipeStdB.lean:272]      BLOCKED result BStmt                     {Fin,HO,List,RecS}
│ │ ├ AStmt.rB → rn (Fin 8), AExp.rB           BLOCKED result BStmt / BExp / parameter Fin 8
│ │ └ xstmtsB [PipeStdB:268]                   BLOCKED result List BStmt
│ │   ├ mat, CS.clean/onOut/rev/s0/gs, revC, loopV, fetch, fetchG   BLOCKED parameter CS / result List AStmt / AStmt.seq has no equations / brecOn
│ │   └ xstageB [PipeStdB:260] → XStage.isSort (nested patterns), sortB → CS.isIn, msortG → passM → runM/ltE/minE/addE   BLOCKED result BStmt/BExp, parameter CS
│ ├ wfErrB [Front/PipeStdBMachine.lean:26]     BLOCKED translator crash                 {String,List,Opt}
│ └ progI → compileBFO = compBFO [Back/OptB.lean:270]   BLOCKED result List (BitVec 32)   {HO,List,Opt,RecS}
│     └ pickB [OptB:156]                       BLOCKED Application type mismatch … Base.get (record argument)   {HO,List,Opt,Tup}
│       ├ tryB [OptB:77], tryL [OptB:106], compileOptB [OptB:185]   BLOCKED same (Base.get)
│       ├ rvF.compBF → MachineF.compB/mgenB      BLOCKED result List XOp / BStmt
│       ├ BSel: irB/okB/toS                      BLOCKED result Code Nat / parameter BStmt
│       ├ Sel.* (gen ops2 opnd tstUses argUses)  BLOCKED result closure pair / tuple / Bool.or has no argument / scalar parameter entry; Sel.tk COMPILES
│       ├ SR.* (sr cpA okL isInc …)              BLOCKED result Code Nat / Cp / Bool.and has no argument / closure
│       ├ Color.* (color ig mvIns)               BLOCKED result Option (Nat → Reg) / List (Nat×Nat) × List (Nat×Nat)
│       ├ Live.* (lv lvIns lvIter subL chk)      BLOCKED result List α / Code Nat
│       ├ Alloc.* (map regs injOn), Peep.*, Hoist.*, Flow.*   BLOCKED result Code Nat / Ins Nat / Fs / List (BitVec 64) / Nat.brecOn
│       └ Wide/Lower: low lowIns wenc immWords liCode liPlan tz encR… brOff jOff condF3 phys
│            BLOCKED result List WOp / List (BitVec 32) / BitVec 32 / BitVec 12 / BitVec 20 / Fin 32 / List LiStep; fits12 toInt; MOp.f3, Op.f3, Op.f7, Cond.neg COMPILE
```
Counts by module under `Top.compile`: `Front/PipeStd` 26, `Opt/SR` 26, `Opt/Flow` 26, `Opt/Sel` 25, `Front/Pipe` 24, `Back/Wide` 22, `Back/OptB` 20, `Spec/Code` 20 (more in `out/cg.tsv`). About 40 of the 391 are example programs (`Direct/SortIns`, `SortMergeSrc/Gen`, `Arr2Code`) that the standard-stage table `XPipe` references; they are in the graph, they are not the compiler's logic.

## 4. Smallest feature set that unblocks the most

Greedy over the 12 features of §2 (read), on the 391 functions under `Top.compile`: "alone" = functions whose own features are all in the set; "closure" = functions whose whole call closure is. Necessary, not sufficient (bodies behind the type gate and one-function-per-program can still reject). Baseline 9 / 8.

| step | add | alone | closure |
|---|---|---:|---:|
| 1 | sized `BitVec` values and ops | 27 | 22 |
| 2 | + inductives with > 2 recursive fields (`Code`, `AExp`, `BExp`, `SExp`) | 42 | 35 |
| 3 | + `Fin n` | 71 | 55 |
| 4 | + higher-order arguments / function results | 111 | 93 |
| 5 | + inductives with > 1 scalar field (`BStmt`, `CStmt`, `Ins`, `WOp`) | 136 | 115 |
| 6 | + `List` of non-bytes | 191 | 145 |
| 7 | + polymorphism / `Type`/`Prop`/`Decidable` | 223 | 184 |
| 8 | + enums as values | 252 | 226 |
| 9 | + `Option`/`Except` payload | 282 | 264 |
| 10 | + tuples | 335 | 331 |
| 11 | + records with function fields | 382 | 382 |
| 12 | + `String` | 391 | 391 |

Reading: steps 2 + 5 are **one feature**, the n-ary constructor/field layout of `frontx_ind_type` (same wall as `Expr.letE` in con-leche): it takes the two AST families (`Code`, `BStmt`/`BExp`/`AExp`) from rejected to representable. Steps 1, 3 are the cheap, local ones (the encoders; `SELFHOST_SURVEY.md` items 1, 6). Nothing closes before step 6 + 4 (lists and closures): every IR pass is a recursive function over `Code` that builds a list and takes a closure, so the middle of the compiler stays blocked until both are in. The record step (11) only matters at the very top (`pickB`, `compBFO`, `Base.get`), where the instance `rvF`/`rvwF` has to be specialised away.

## 5. Comparison with `SELFHOST_SURVEY.md` and `CONLECHE_DEPTH.md`

| blocker (this probe) | `SELFHOST_SURVEY.md` (read, 39 groups) | `CONLECHE_DEPTH.md` (run, 1 093 fns) | shared? |
|---|---|---|---|
| n-ary recursive inductive (`> 2` recursive / `> 1` scalar fields) | item 3 (recursive data + calls), item 7 (payload inductives) | row 1 `Expr` (`letE`: 3 recursive fields), row 2 `Name` | **yes, the same wall** (`frontx_ind_type` shape) |
| `List` of non-bytes | item 4 | row 3 | **yes** |
| record / multi-field structure with function fields | item 8 (`WideF`) | row 4 (`Env`, `FEnv`, …) and row 6 | yes |
| `Option` of heap object | item 4/10 | row 5 | yes |
| higher-order arguments | item 5 | row 6 | **yes** |
| `Type`/`Prop`/`Decidable`/polymorphism | item 9 | row 9 | yes |
| translator crash `unknown free variable` | – | 13 functions | yes (5 here) |
| sized `BitVec` | item 1 | – (`Int`, row 13, is con-leche's) | survey only; fails 40 here |
| `Fin n` | item 6 | – | survey only |
| enums | item 2 | – | survey: **partly done** (accepted in `frontx_ind`, `Op.f3` compiles) |
| `String` | item 10 (messages) | row 14 (algorithms) | different use: only messages here |
| monads / `StateT` / `[Monad m]`, `HashMap`, `Array`, `Int`, `partial`, `USize`, nullary constants | – | rows 8, 11, 12, 13, 15, 16, 10 | **not needed by the compiler core**; con-leche only |

So the two codebases share the **data-model wall (n-ary constructors with typed fields), lists of heap objects, records, `Option`, higher-order arguments and non-computational types**; one data-layout feature serves both. con-leche additionally needs a monad (444 first failures) and caches; the compiler core needs sized `BitVec` and `Fin`, which con-leche does not. The survey's prediction is confirmed for the leaves (items 1, 6 still block every encoder) and refined for the middle: it counted `IR.Code` among "recursive data", but the shape check rejects it specifically (`Code.loop2` has three recursive fields), as it rejects `Expr.letE`.

## 6. Caveats

- "Verbatim": no function text was changed; the probes call the repo's own modules. The front ends were not modified.
- Run counts are exact (first message only). Features, "own"/"trans" counts and greedy sets are regex over types and constants (**read**); the feature regexes are coarse (for example "higher-order" counts any function-typed binder, "polymorphism" any `Type/α/Prop`). They give ranking, not precise numbers.
- Reach is the structural reference graph (includes functions that appear only in a structure field or table); it is larger than the dynamic call set.
- The translator prints `PANIC` backtraces (189 in `P1.out`) on many rejections; the command still reports its error.
- `frontx_ind` was tried only for the 31 functions whose first message named an accepted type alone; types in the rejected group were not retried with `nesting`.

## 7. Reproduce

```
lake build Riscv.Frontx.Translate Riscv.Frontx.IndCmd Riscv.Frontx.WaCmd Riscv.Back.Top Compiler.IndSup Riscv.Back.CallsImpl1W
lake env lean Testing/selfhost-depth/scripts/Cg.lean > Testing/selfhost-depth/out/cg.tsv      # exact call graph
python3 Testing/selfhost-depth/scripts/mkprobe.py                                              # out/P1.lean (frontx_compile on each def)
lake env lean --tstack=4000000 -DmaxErrors=100000 Testing/selfhost-depth/out/P1.lean > out/P1.out
python3 Testing/selfhost-depth/scripts/parse.py out/P1.lean out/P1.out out/P1.json
lake env lean --tstack=4000000 -DmaxErrors=100000 Testing/selfhost-depth/out/T1.lean            # type shapes
lake env lean --tstack=4000000 -DmaxErrors=100000 Testing/selfhost-depth/out/P2.lean > out/P2.out   # frontx_ind
python3 Testing/selfhost-depth/scripts/analyze.py Proven.Top.compile ; python3 Testing/selfhost-depth/scripts/tree.py
```
(Toolchain: Lean 4.29.0 from GitHub releases; the Sail model cloned to `../deps/sail-riscv-lean` at 51c635c. `P2.lean` and `T1.lean` were generated inline, their content is in `out/`.)
