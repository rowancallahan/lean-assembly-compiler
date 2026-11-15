# con-leche blocking targets (type gate)

Source: branch `conleche-depth` (`Testing/conleche-depth/out/`, `Testing/notes/CONLECHE_DEPTH.md`). Base path of every `file:line` is `ConLeche/` in `leanprover/con-leche` @ `6810492c1`.

## 0. Method and tags

- **Population**: the 1 093 con-leche functions probed in `F2.lean.txt` (the 1 103 keys in `final.json` minus 8 `beside.*` names that are not con-leche functions, minus 2 names below). The notes say 10 names were excluded as unresolved; `final.json` contains 8 `beside.*` keys, so the count differs by 2 and is not reconciled here.. 6 already pass verbatim and are excluded from every target list.
- **Feature set per function** (`final.json` `S`): regex over the signature, from `scripts/final.py`. **inferred** (read from the signature text, not from the compiler).
- **First failure** (`final.json` `first`, from `Ffail.json`): **run**, the front end's own message. A target is tagged `run` when its first message names the same type; `inferred` when the first message names another type, so the target rests on the signature alone.
- **Line count**: computed here from `out/F2.lean.txt` (its segments are 1:1 copies of the con-leche files, only `module`/`import` lines commented out). Count = lines from the `def` line to the last non-blank line before the next top-level command (includes the body, excludes trailing doc comments of the next decl).
- **Callees / leaves**: **read**, token match of identifiers in each body against the short names of every `def`/`abbrev`/`opaque` in the concatenated source (comments stripped, names of any length, self-calls ignored). Over-approximation of callees, so a leaf here is a true leaf by name. Calls through record fields (`CoreFns`) are invisible.
- **Not in the lists**: `ConLeche.checkDecl` and `ConLeche.checkDeclKind` (`Kernel/CheckDecl.lean:169`, `:29` per notes): their source is not in `F2.lean.txt`, so no line count from the branch. `ConLeche.checkDecl` is probed with a result type `Except (CheckError × Nat) Env` (notes, **read**); `checkDeclKind` has `Expr`/`Name`/`Declaration` features in `final.json` (**inferred**). Add them when the source is pulled.
- **Not captured by the signature**: `partial` (row 15) and `USize` (row 16) are body features. The notes name `Expr.hasStrLitGo` (`partial`) and `Expr.beqKey` (`USize`); both also have signature features, so neither is a single-feature target.

## 1. Single-feature targets, by blocking feature

A function is listed under feature F when its signature mentions F and nothing else from the table (`S == {F}`), so it is blocked by F alone at the type gate. Sorted by line count, smallest first.

| # | Feature (table row, notes §2) | Functions with S = {F} | Notes |
|---|---|---:|---|
| 1 | Expr | 97 | Expr-only: `S` is one type; some first failures name `Type` instead (see tags). |
| 2 | Name | 62 | Also needs String literals for `Name.str … "Nat"` constants (**read**, notes §4 step 1). |
| 3 | List of non-bytes | 2 |  |
| 4 | multi-field structure/record | 89 |  |
| 5 | Option of heap object | 1 |  |
| 6 | higher-order args | 0 | no function needs this feature alone |
| 7 | Level outside shape | 2 |  |
| 8 | HashMap/HashSet/CState | 0 | no function needs this feature alone |
| 9 | type-class/universe/dependent | 4 |  |
| 10 | nullary constant | 14 | Tag `run`: the front end reports `introN failed` (0-ary def). |
| 11 | state monad / Except / [Monad m] | 5 |  |
| 12 | Array of heap objects | 0 | no function needs this feature alone |
| 13 | Int | 0 | no function needs this feature alone |
| 14 | String/Char | 9 | `Display.*` members fail with a translator crash (`unknown free variable`), not a type-gate message. |

### Row 1: Expr (97 functions)

| # | Function | file:line | lines | first failure (run) | tag |
|---:|---|---|---:|---|---|
| 1 | `Expr.hasLooseBVarBP` | Cached/ExprOpsC.lean:1490 | 1 | frontx: unsupported parameter type Expr | run |
| 2 | `Cached.whnfWalkFuelC` | Cached/IndPositivity.lean:188 | 1 | frontx: unsupported parameter type Expr | run |
| 3 | `BasisDSL.prop` | Kernel/Basis/Builder.lean:67 | 1 | frontx: unsupported result type Expr | run |
| 4 | `BasisDSL.type1` | Kernel/Basis/Builder.lean:70 | 1 | frontx: unsupported result type Expr | run |
| 5 | `natT` | Kernel/Basis/Nat.lean:22 | 1 | frontx: unsupported result type Expr | run |
| 6 | `natRecMotive` | Kernel/Basis/Nat.lean:37 | 1 | frontx: unsupported result type Expr | run |
| 7 | `quotRel` | Kernel/Basis/Quot.lean:29 | 1 | frontx: unsupported result type Expr | run |
| 8 | `quotLiftF` | Kernel/Basis/Quot.lean:46 | 1 | frontx: unsupported result type Expr | run |
| 9 | `Expr.hasLP` | Kernel/Expr.lean:482 | 1 | frontx: unsupported parameter type Expr | run |
| 10 | `Expr.bvarBRaw` | Kernel/Expr.lean:485 | 1 | frontx: unsupported parameter type Expr | run |
| 11 | `Expr.fvarBRaw` | Kernel/Expr.lean:488 | 1 | frontx: unsupported parameter type Expr | run |
| 12 | `Expr.BeqOutX` | Kernel/Expr.lean:1064 | 1 | frontx: unsupported result type Type | inferred (run msg names another type) |
| 13 | `classBinder` | Kernel/Inductives/GenRec.lean:107 | 1 | frontx: unsupported result type Expr | run |
| 14 | `ClassGen.binder` | Kernel/Inductives/GenRec.lean:110 | 1 | frontx: unsupported result type Expr | run |
| 15 | `ClassGen.slotVar` | Kernel/Inductives/GenRec.lean:113 | 1 | frontx: unsupported result type Expr | run |
| 16 | `whnfWalkFuel` | Kernel/Inductives/Positivity.lean:315 | 1 | frontx: unsupported parameter type Expr | run |
| 17 | `reduceBoolDeclPin` | Kernel/TrustPins.lean:43 | 1 | frontx: unsupported result type Expr | run |
| 18 | `reduceNatDeclPin` | Kernel/TrustPins.lean:46 | 1 | frontx: unsupported result type Expr | run |
| 19 | `Expr.depthC` | Cached/ExprOpsC.lean:1940 | 2 | frontx: unsupported parameter type Expr | run |
| 20 | `Expr.abstractPrefixC` | Cached/ExprOpsC.lean:2217 | 2 | frontx: unsupported result type Expr | run |
| 21 | `Cached.eraseFVarTysC` | Cached/IndRec.lean:162 | 2 | frontx: unsupported result type Expr | run |
| 22 | `Cached.inst1M` | Cached/StateC.lean:336 | 2 | frontx: unsupported result type CheckCM Expr | run |
| 23 | `andRecMotive` | Kernel/Basis/And.lean:62 | 2 | frontx: unsupported result type Expr | run |
| 24 | `quotIndMotive` | Kernel/Basis/Quot.lean:77 | 2 | frontx: unsupported result type Expr | run |
| 25 | `Expr.mkBvar` | Kernel/Expr.lean:1346 | 2 | frontx: unsupported result type Expr | run |
| 26 | `ClassGen.motVar` | Kernel/Inductives/GenRec.lean:116 | 2 | frontx: unsupported result type Expr | run |
| 27 | `Cached.Expr.dropVarsC` | Cached/CheckerC.lean:73 | 3 | frontx: unsupported result type Expr | run |
| 28 | `Cached.iotaNumArgs` | Cached/CoreC.lean:140 | 3 | frontx: unsupported parameter type Expr | run |
| 29 | `Cached.isStuckHeadC` | Cached/CoreC.lean:182 | 3 | frontx: unsupported parameter type Expr | run |
| 30 | `Cached.whnfCoreEasy` | Cached/CoreC.lean:242 | 3 | frontx: unsupported parameter type Expr | run |
| 31 | `Cached.whnfEasy` | Cached/CoreC.lean:322 | 3 | frontx: unsupported parameter type Expr | run |
| 32 | `Expr.isCompound` | Cached/ExprOpsC.lean:116 | 3 | frontx: unsupported parameter type Expr | run |
| 33 | `Expr.liftLooseBVarsC` | Cached/ExprOpsC.lean:327 | 3 | frontx: unsupported result type Expr | run |
| 34 | `Expr.instantiate1C` | Cached/ExprOpsC.lean:487 | 3 | frontx: unsupported result type Expr | run |
| 35 | `Expr.abstract1C` | Cached/ExprOpsC.lean:847 | 3 | frontx: unsupported result type Expr | run |
| 36 | `Expr.isCompoundF` | Cached/ExprOpsC.lean:1298 | 3 | frontx: unsupported parameter type Expr | run |
| 37 | `eqRecMotive` | Kernel/Basis/Eq.lean:38 | 3 | frontx: unsupported result type Expr | run |
| 38 | `quotIndMk` | Kernel/Basis/Quot.lean:82 | 3 | frontx: unsupported result type Expr | run |
| 39 | `Expr.isStrLit` | Kernel/Core.lean:791 | 3 | frontx: unsupported parameter type Expr | run |
| 40 | `Expr.isLit` | Kernel/Core.lean:1119 | 3 | frontx: unsupported parameter type Expr | run |
| 41 | `Expr.isEagerReduce` | Kernel/CoreDefs.lean:439 | 3 | frontx: unsupported parameter type Expr | run |
| 42 | `Expr.isBoolTrue` | Kernel/CoreDefs.lean:448 | 3 | frontx: unsupported parameter type Expr | run |
| 43 | `Expr.beqRecursive` | Kernel/Expr.lean:790 | 3 | frontx: unsupported parameter type Expr | run |
| 44 | `Expr.beqIsApp` | Kernel/Expr.lean:795 | 3 | frontx: unsupported parameter type Expr | run |
| 45 | `Expr.BeqSt.recordEq` | Kernel/Expr.lean:1049 | 3 | frontx: unsupported result type Expr.BeqSt | run |
| 46 | `Expr.BeqOutX.cast` | Kernel/Expr.lean:1083 | 3 | frontx: unsupported result type c.BeqOutX d | inferred (run msg names another type) |
| 47 | `Expr.bvarB` | Kernel/ExprOps.lean:214 | 3 | frontx: unsupported parameter type Expr | run |
| 48 | `Expr.isForallE` | Kernel/ExprOps.lean:836 | 3 | frontx: unsupported parameter type Expr | run |
| 49 | `Expr.getAppFn` | Kernel/ExprOps.lean:848 | 3 | frontx: unsupported result type Expr | run |
| 50 | `Expr.piResult` | Kernel/ExprOps.lean:880 | 3 | frontx: unsupported result type Expr | run |
| 51 | `Expr.fvarTypeD` | Kernel/ExprOps.lean:905 | 3 | frontx: unsupported result type Expr | run |
| 52 | `Expr.abstractPrefix` | Kernel/Inductives/RecCheck.lean:431 | 3 | frontx: unsupported result type Expr | run |
| 53 | `Expr.dropVars` | Kernel/Install.lean:36 | 3 | frontx: unsupported result type Expr | run |
| 54 | `Expr.numArgs` | Kernel/PropRead.lean:56 | 3 | frontx: unsupported parameter type Expr | run |
| 55 | `Cached.whnfCoreKeyC` | Cached/CoreC.lean:254 | 4 | frontx: unsupported parameter type Expr | run |
| 56 | `Cached.whnfCoreStoresDone` | Cached/CoreC.lean:264 | 4 | frontx: unsupported parameter type Expr | run |
| 57 | `Expr.wscopedBC` | Cached/ExprOpsC.lean:1482 | 4 | frontx: unsupported parameter type Expr | run |
| 58 | `Expr.leafGuard` | Cached/ExprOpsC.lean:2113 | 4 | frontx: unsupported parameter type Expr | run |
| 59 | `Cached.structUsedLaterC` | Cached/IndPositivity.lean:273 | 4 | frontx: unsupported parameter type Expr | run |
| 60 | `andRecMinor` | Kernel/Basis/And.lean:68 | 4 | frontx: unsupported result type Expr | run |
| 61 | `natRecSucc` | Kernel/Basis/Nat.lean:41 | 4 | frontx: unsupported result type Expr | run |
| 62 | `Expr.isNatZero` | Kernel/Core.lean:1527 | 4 | frontx: unsupported parameter type Expr | run |
| 63 | `Expr.headIsProj` | Kernel/Core.lean:1554 | 4 | frontx: unsupported parameter type Expr | run |
| 64 | `Expr.ioNeutral` | Kernel/CoreDefs.lean:42 | 4 | frontx: unsupported parameter type Expr | run |
| 65 | `natLitToConstructor` | Kernel/CoreDefs.lean:157 | 4 | frontx: unsupported result type Expr | run |
| 66 | `structUsedLater` | Kernel/CoreDefs.lean:846 | 4 | frontx: unsupported parameter type Expr | run |
| 67 | `classLeafAt` | Kernel/Inductives/GenRec.lean:270 | 4 | frontx: unsupported parameter type TargetMajor | inferred (run msg names another type) |
| 68 | `nestResHead` | Kernel/Inductives/Positivity.lean:625 | 4 | frontx: unsupported parameter type Expr | run |
| 69 | `quotLiftH` | Kernel/Basis/Quot.lean:50 | 5 | frontx: unsupported result type Expr | run |
| 70 | `sameConstHeads` | Kernel/CoreDefs.lean:147 | 6 | frontx: unsupported parameter type Expr | run |
| 71 | `Cached.whnfCoreCheapSafeC` | Cached/CoreC.lean:275 | 7 | frontx: unsupported parameter type Expr | run |
| 72 | `Expr.depthP` | Cached/ExprOpsC.lean:1901 | 7 | frontx: unsupported parameter type Expr | run |
| 73 | `Cached.sameConstHeadsC` | Cached/StateC.lean:73 | 7 | frontx: unsupported parameter type Expr | run |
| 74 | `Cached.natResultRefused` | Cached/StateC.lean:257 | 7 | frontx: unsupported parameter type NatBinOp | inferred (run msg names another type) |
| 75 | `Expr.sizeF` | Kernel/ExprOps.lean:788 | 7 | frontx: unsupported parameter type Expr | run |
| 76 | `Expr.depth` | Kernel/Inductives/Positivity.lean:305 | 7 | frontx: unsupported parameter type Expr | run |
| 77 | `Expr.hasLooseBVarInC` | Cached/ExprOpsC.lean:1676 | 8 | frontx: unsupported parameter type Expr | run |
| 78 | `Expr.wscopedBP` | Cached/ExprOpsC.lean:1393 | 9 | frontx: unsupported parameter type Expr | run |
| 79 | `Expr.looseBVarsBounded` | Kernel/ExprOps.lean:46 | 10 | frontx: unsupported parameter type Expr | run |
| 80 | `Expr.abstract1P` | Cached/ExprOpsC.lean:789 | 11 | frontx: unsupported result type Expr | run |
| 81 | `Expr.hasLooseBVarBC` | Cached/ExprOpsC.lean:1578 | 11 | frontx: unsupported parameter type Expr | run |
| 82 | `Expr.hasLooseBVarInP` | Cached/ExprOpsC.lean:1593 | 11 | frontx: unsupported parameter type Expr | run |
| 83 | `Expr.instantiate1P` | Cached/ExprOpsC.lean:426 | 12 | frontx: unsupported result type Expr | run |
| 84 | `Expr.instantiate1` | Kernel/ExprOps.lean:27 | 13 | frontx: unsupported result type Expr | run |
| 85 | `Expr.abstract1` | Kernel/ExprOps.lean:739 | 13 | frontx: unsupported result type Expr | run |
| 86 | `Expr.wscopedB` | Kernel/ExprOps.lean:821 | 13 | frontx: unsupported parameter type Expr | run |
| 87 | `Expr.liftLooseBVarsP` | Cached/ExprOpsC.lean:263 | 14 | frontx: unsupported result type Expr | run |
| 88 | `Expr.abstractRangeC` | Cached/ExprOpsC.lean:917 | 14 | frontx: unsupported result type Expr | run |
| 89 | `Expr.hasLooseBVarB` | Kernel/CoreDefs.lean:827 | 14 | frontx: unsupported parameter type Expr | run |
| 90 | `Expr.abstractRangeP` | Cached/ExprOpsC.lean:853 | 15 | frontx: unsupported result type Expr | run |
| 91 | `Cached.NatBinOp.result` | Cached/StateC.lean:218 | 15 | frontx: unsupported result type Expr | run |
| 92 | `Expr.fvarB` | Kernel/ExprOps.lean:221 | 15 | frontx: unsupported parameter type Expr | run |
| 93 | `Expr.liftLooseBVars` | Kernel/ExprOps.lean:677 | 15 | frontx: unsupported result type Expr | run |
| 94 | `Expr.hasFvar` | Kernel/ExprOps.lean:60 | 16 | frontx: unsupported parameter type Expr | run |
| 95 | `Expr.eraseFVarTys` | Kernel/Inductives/RecCheck.lean:134 | 24 | frontx: unsupported result type Expr | run |
| 96 | `Expr.probeHit` | Kernel/Expr.lean:960 | 51 | frontx: unsupported result type { h // h = true → a = b } | inferred (run msg names another type) |
| 97 | `Expr.beqGoX` | Kernel/Expr.lean:1134 | 104 | frontx: unsupported result type a.BeqOutX b | inferred (run msg names another type) |

### Row 2: Name (62 functions)

| # | Function | file:line | lines | first failure (run) | tag |
|---:|---|---|---:|---|---|
| 1 | `Cached.nameIsC` | Cached/StateC.lean:197 | 1 | frontx_ind: Bool.and has no argument of a declared type | inferred (run msg names another type) |
| 2 | `andIntroName` | Kernel/Basis/And.lean:40 | 1 | frontx_ind: Name.str has no equations | run |
| 3 | `andRecName` | Kernel/Basis/And.lean:43 | 1 | frontx_ind: Name.str has no equations | run |
| 4 | `eqName` | Kernel/Basis/Names.lean:18 | 1 | frontx_ind: Name.str has no equations | run |
| 5 | `eqReflName` | Kernel/Basis/Names.lean:21 | 1 | frontx_ind: Name.str has no equations | run |
| 6 | `natName` | Kernel/Basis/Names.lean:24 | 1 | frontx_ind: Name.str has no equations | run |
| 7 | `natZeroName` | Kernel/Basis/Names.lean:27 | 1 | frontx_ind: Name.str has no equations | run |
| 8 | `natSuccName` | Kernel/Basis/Names.lean:30 | 1 | frontx_ind: Name.str has no equations | run |
| 9 | `emptyName` | Kernel/Basis/Names.lean:32 | 1 | frontx_ind: Name.str has no equations | run |
| 10 | `falseName` | Kernel/Basis/Names.lean:38 | 1 | frontx_ind: Name.str has no equations | run |
| 11 | `quotName` | Kernel/Basis/Names.lean:41 | 1 | frontx_ind: Name.str has no equations | run |
| 12 | `quotMkName` | Kernel/Basis/Names.lean:44 | 1 | frontx_ind: Name.str has no equations | run |
| 13 | `quotLiftName` | Kernel/Basis/Names.lean:47 | 1 | frontx_ind: Name.str has no equations | run |
| 14 | `quotIndName` | Kernel/Basis/Names.lean:50 | 1 | frontx_ind: Name.str has no equations | run |
| 15 | `stringName` | Kernel/Basis/Names.lean:63 | 1 | frontx_ind: Name.str has no equations | run |
| 16 | `stringOfListName` | Kernel/Basis/Names.lean:66 | 1 | frontx_ind: Name.str has no equations | run |
| 17 | `listName` | Kernel/Basis/Names.lean:69 | 1 | frontx_ind: Name.str has no equations | run |
| 18 | `listNilName` | Kernel/Basis/Names.lean:72 | 1 | frontx_ind: Name.str has no equations | run |
| 19 | `listConsName` | Kernel/Basis/Names.lean:75 | 1 | frontx_ind: Name.str has no equations | run |
| 20 | `charName` | Kernel/Basis/Names.lean:78 | 1 | frontx_ind: Name.str has no equations | run |
| 21 | `andName` | Kernel/Basis/Names.lean:90 | 1 | frontx_ind: Name.str has no equations | run |
| 22 | `charOfNatName` | Kernel/Basis/Names.lean:93 | 1 | frontx_ind: Name.str has no equations | run |
| 23 | `sorryAxName` | Kernel/Basis/Names.lean:118 | 1 | frontx_ind: Name.str has no equations | run |
| 24 | `natPredName` | Kernel/CoreDefs.lean:415 | 1 | frontx_ind: Name.str has no equations | run |
| 25 | `natAddName` | Kernel/CoreDefs.lean:416 | 1 | frontx_ind: Name.str has no equations | run |
| 26 | `natSubName` | Kernel/CoreDefs.lean:417 | 1 | frontx_ind: Name.str has no equations | run |
| 27 | `natMulName` | Kernel/CoreDefs.lean:418 | 1 | frontx_ind: Name.str has no equations | run |
| 28 | `natPowName` | Kernel/CoreDefs.lean:419 | 1 | frontx_ind: Name.str has no equations | run |
| 29 | `natBeqName` | Kernel/CoreDefs.lean:420 | 1 | frontx_ind: Name.str has no equations | run |
| 30 | `natBleName` | Kernel/CoreDefs.lean:421 | 1 | frontx_ind: Name.str has no equations | run |
| 31 | `natDivName` | Kernel/CoreDefs.lean:422 | 1 | frontx_ind: Name.str has no equations | run |
| 32 | `natModName` | Kernel/CoreDefs.lean:423 | 1 | frontx_ind: Name.str has no equations | run |
| 33 | `natGcdName` | Kernel/CoreDefs.lean:424 | 1 | frontx_ind: Name.str has no equations | run |
| 34 | `natLandName` | Kernel/CoreDefs.lean:425 | 1 | frontx_ind: Name.str has no equations | run |
| 35 | `natLorName` | Kernel/CoreDefs.lean:426 | 1 | frontx_ind: Name.str has no equations | run |
| 36 | `natXorName` | Kernel/CoreDefs.lean:427 | 1 | frontx_ind: Name.str has no equations | run |
| 37 | `natShiftLeftName` | Kernel/CoreDefs.lean:428 | 1 | frontx_ind: Name.str has no equations | run |
| 38 | `natShiftRightName` | Kernel/CoreDefs.lean:429 | 1 | frontx_ind: Name.str has no equations | run |
| 39 | `boolName` | Kernel/CoreDefs.lean:430 | 1 | frontx_ind: Name.str has no equations | run |
| 40 | `eagerReduceName` | Kernel/CoreDefs.lean:434 | 1 | frontx_ind: Name.str has no equations | run |
| 41 | `boolTrueName` | Kernel/CoreDefs.lean:442 | 1 | frontx_ind: Name.str has no equations | run |
| 42 | `boolFalseName` | Kernel/CoreDefs.lean:443 | 1 | frontx_ind: Name.str has no equations | run |
| 43 | `propextName` | Kernel/StdAxioms.lean:34 | 1 | frontx_ind: Name.str has no equations | run |
| 44 | `choiceName` | Kernel/StdAxioms.lean:37 | 1 | frontx_ind: Name.str has no equations | run |
| 45 | `iffName` | Kernel/StdAxioms.lean:40 | 1 | frontx_ind: Name.str has no equations | run |
| 46 | `iffIntroName` | Kernel/StdAxioms.lean:43 | 1 | frontx_ind: Name.str has no equations | run |
| 47 | `iffRecName` | Kernel/StdAxioms.lean:46 | 1 | frontx_ind: Name.str has no equations | run |
| 48 | `nonemptyName` | Kernel/StdAxioms.lean:49 | 1 | frontx_ind: Name.str has no equations | run |
| 49 | `nonemptyIntroName` | Kernel/StdAxioms.lean:52 | 1 | frontx_ind: Name.str has no equations | run |
| 50 | `nonemptyRecName` | Kernel/StdAxioms.lean:55 | 1 | frontx_ind: Name.str has no equations | run |
| 51 | `trueName` | Kernel/TrustAxioms.lean:50 | 1 | frontx_ind: Name.str has no equations | run |
| 52 | `trueIntroName` | Kernel/TrustAxioms.lean:53 | 1 | frontx_ind: Name.str has no equations | run |
| 53 | `trustCompilerName` | Kernel/TrustAxioms.lean:56 | 1 | frontx_ind: Name.str has no equations | run |
| 54 | `reduceNatName` | Kernel/TrustAxioms.lean:59 | 1 | frontx_ind: Name.str has no equations | run |
| 55 | `reduceBoolName` | Kernel/TrustAxioms.lean:62 | 1 | frontx_ind: Name.str has no equations | run |
| 56 | `ofReduceNatName` | Kernel/TrustAxioms.lean:65 | 1 | frontx_ind: Name.str has no equations | run |
| 57 | `ofReduceBoolName` | Kernel/TrustAxioms.lean:68 | 1 | frontx_ind: Name.str has no equations | run |
| 58 | `reservedRecName` | Kernel/CoreDefs.lean:517 | 4 | frontx_ind: Bool.or has no argument of a declared type | inferred (run msg names another type) |
| 59 | `Cached.NatBinOp.name` | Cached/StateC.lean:190 | 5 | frontx_ind: NatBinOp.name.match_1 has no equations | inferred (run msg names another type) |
| 60 | `quotSoundName` | Kernel/Basis/Names.lean:53 | 8 | frontx_ind: Name.str has no equations | run |
| 61 | `ofReduceOp` | Kernel/TrustAxioms.lean:74 | 8 | frontx_ind: equation ite.eq_1 has no constructor pattern | inferred (run msg names another type) |
| 62 | `natOpName` | Kernel/CoreDefs.lean:480 | 18 | frontx_ind: Bool.or has no argument of a declared type | inferred (run msg names another type) |

### Row 3: List of non-bytes (2 functions)

| # | Function | file:line | lines | first failure (run) | tag |
|---:|---|---|---:|---|---|
| 1 | `ClassRead.classes` | Kernel/Inductives/ClassRead.lean:66 | 2 | frontx: unsupported result type List ClassKey | run |
| 2 | `nestKindsFlat` | Kernel/Inductives/Positivity.lean:337 | 2 | frontx: unsupported parameter type List (List (List NestFieldKind)) | run |

### Row 4: multi-field structure/record (89 functions)

| # | Function | file:line | lines | first failure (run) | tag |
|---:|---|---|---:|---|---|
| 1 | `Env.empty` | Kernel/Env.lean:465 | 1 | frontx: unsupported result type Env | run |
| 2 | `BlockShape.numCtors` | Kernel/Inductives/BlockShape.lean:158 | 1 | frontx: unsupported parameter type BlockShape | run |
| 3 | `NestCtx.hiAt` | Kernel/Inductives/Positivity.lean:442 | 1 | frontx: unsupported parameter type NestCtx | inferred (run msg names another type) |
| 4 | `trueCvA` | Kernel/TrustAxioms.lean:84 | 1 | frontx: unsupported result type ConstantVal | run |
| 5 | `trueIntroCvA` | Kernel/TrustAxioms.lean:87 | 1 | frontx: unsupported result type ConstantVal | run |
| 6 | `trustCompilerA` | Kernel/TrustAxioms.lean:90 | 1 | frontx: unsupported result type ConstantVal | run |
| 7 | `boolCvA` | Kernel/TrustAxioms.lean:93 | 1 | frontx: unsupported result type ConstantVal | run |
| 8 | `reduceNatCvA` | Kernel/TrustAxioms.lean:120 | 1 | frontx: unsupported result type ConstantVal | run |
| 9 | `reduceBoolCvA` | Kernel/TrustAxioms.lean:123 | 1 | frontx: unsupported result type ConstantVal | run |
| 10 | `ofReduceNatA` | Kernel/TrustAxioms.lean:126 | 1 | frontx: unsupported result type ConstantVal | run |
| 11 | `ofReduceBoolA` | Kernel/TrustAxioms.lean:129 | 1 | frontx: unsupported result type ConstantVal | run |
| 12 | `Cached.blockIsRecC` | Cached/CheckerC.lean:68 | 2 | frontx: unsupported parameter type BlockShape | run |
| 13 | `Cached.auxRuleFireC` | Cached/IndTail.lean:36 | 2 | frontx: unsupported result type RecRuleFire | inferred (run msg names another type) |
| 14 | `quotPin` | Kernel/Basis.lean:164 | 2 | frontx: unsupported result type ConstantInfo | run |
| 15 | `quotAt` | Kernel/Basis.lean:169 | 2 | frontx: unsupported result type ConstantInfo | run |
| 16 | `emptyA` | Kernel/Basis/Empty.lean:22 | 2 | frontx: unsupported result type ConstantInfo | run |
| 17 | `falseA` | Kernel/Basis/False.lean:38 | 2 | frontx: unsupported result type ConstantInfo | run |
| 18 | `natA` | Kernel/Basis/Nat.lean:25 | 2 | frontx: unsupported result type ConstantInfo | run |
| 19 | `natZeroA` | Kernel/Basis/Nat.lean:29 | 2 | frontx: unsupported result type ConstantInfo | run |
| 20 | `natSuccA` | Kernel/Basis/Nat.lean:33 | 2 | frontx: unsupported result type ConstantInfo | run |
| 21 | `formerDefHeaded` | Kernel/CoreDefs.lean:66 | 2 | frontx: unsupported parameter type ConstantVal | run |
| 22 | `natLitStored` | Kernel/CoreDefs.lean:193 | 2 | frontx: unsupported parameter type Env | run |
| 23 | `mkFEnv` | Kernel/FEnv.lean:93 | 2 | frontx: unsupported result type FEnv | run |
| 24 | `FEnv.push` | Kernel/FEnv.lean:133 | 2 | frontx: unsupported result type FEnv | run |
| 25 | `FEnv.pushTable` | Kernel/FEnv.lean:140 | 2 | frontx: unsupported result type FEnv | run |
| 26 | `natLitStoredF` | Kernel/FEnv.lean:201 | 2 | frontx: unsupported parameter type FEnv | run |
| 27 | `BlockShape.rulePrefixAt` | Kernel/Inductives/BlockShape.lean:181 | 2 | frontx: unsupported parameter type BlockShape | run |
| 28 | `BlockShape.majorIdxAt` | Kernel/Inductives/BlockShape.lean:186 | 2 | frontx: unsupported parameter type BlockShape | run |
| 29 | `blockRecNamesUnreserved` | Kernel/Inductives/BlockShape.lean:371 | 2 | frontx: unsupported parameter type BlockShape | run |
| 30 | `nestNonValid` | Kernel/Inductives/Positivity.lean:436 | 2 | frontx: unsupported result type CheckError | run |
| 31 | `auxRuleFire` | Kernel/Inductives/RecCheck.lean:441 | 2 | frontx: unsupported result type RecRuleFire | inferred (run msg names another type) |
| 32 | `Cached.natNumeralTooBig` | Cached/StateC.lean:166 | 3 | frontx: unsupported result type CheckError | run |
| 33 | `pinAgrees` | Kernel/Basis.lean:83 | 3 | frontx: unsupported parameter type ConstantInfo | run |
| 34 | `andRaw` | Kernel/Basis/And.lean:46 | 3 | frontx: unsupported result type ConstantInfo | run |
| 35 | `natLitSupported` | Kernel/CoreDefs.lean:187 | 3 | frontx: unsupported parameter type Env | run |
| 36 | `CheckMode.verifiedChecks` | Kernel/Env.lean:79 | 3 | frontx: unsupported parameter type CheckMode | inferred (run msg names another type) |
| 37 | `ProjTable.entry` | Kernel/Env.lean:284 | 3 | frontx: unsupported result type ProjEntry | inferred (run msg names another type) |
| 38 | `ConstantInfo.toConstantVal` | Kernel/Env.lean:427 | 3 | frontx: unsupported result type ConstantVal | run |
| 39 | `natLitSupportedF` | Kernel/FEnv.lean:196 | 3 | frontx: unsupported parameter type FEnv | run |
| 40 | `blockLargeElimAllowed` | Kernel/Inductives/BlockRec.lean:82 | 3 | frontx: unsupported parameter type BlockShape | run |
| 41 | `PropWhen.isProp` | Kernel/PropRead.lean:199 | 3 | frontx: unsupported parameter type PropWhen | inferred (run msg names another type) |
| 42 | `PropWhen.isNever` | Kernel/PropWhen.lean:53 | 3 | frontx: unsupported parameter type PropWhen | inferred (run msg names another type) |
| 43 | `ConstantVal.matchesPin` | Kernel/StdAxioms.lean:89 | 3 | frontx: unsupported parameter type ConstantVal | run |
| 44 | `pinCopyOk` | Kernel/Basis.lean:89 | 4 | frontx: unsupported parameter type ConstantInfo | run |
| 45 | `quotPinHit` | Kernel/Basis.lean:175 | 4 | frontx: unsupported parameter type QuotKind | inferred (run msg names another type) |
| 46 | `quotA` | Kernel/Basis/Quot.lean:32 | 4 | frontx: unsupported result type ConstantInfo | run |
| 47 | `ConstantVal.canon` | Kernel/Canon.lean:67 | 4 | frontx: unsupported result type ConstantVal | run |
| 48 | `formerZ` | Kernel/CoreDefs.lean:72 | 4 | frontx: unsupported result type PropWhen | inferred (run msg names another type) |
| 49 | `blockIsRec` | Kernel/Inductives/BlockInstall.lean:102 | 4 | frontx: unsupported parameter type BlockShape | run |
| 50 | `blockRecLpsOk` | Kernel/Inductives/BlockShape.lean:334 | 4 | frontx: unsupported parameter type BlockShape | run |
| 51 | `recKExpected` | Kernel/Inductives/RecCheck.lean:463 | 4 | frontx: unsupported parameter type BlockShape | run |
| 52 | `generatedFire` | Kernel/Inductives/StreamRecs.lean:133 | 4 | frontx: unsupported result type RecRuleFire | inferred (run msg names another type) |
| 53 | `PropWhen.inter` | Kernel/PropWhen.lean:73 | 4 | frontx: unsupported result type PropWhen | inferred (run msg names another type) |
| 54 | `choiceA` | Kernel/StdAxioms.lean:163 | 4 | frontx: unsupported result type ConstantVal | run |
| 55 | `Cached.nestUniformOkC` | Cached/IndPositivity.lean:451 | 5 | frontx: unsupported parameter type NestCtx | inferred (run msg names another type) |
| 56 | `emptyRecA` | Kernel/Basis/Empty.lean:28 | 5 | frontx: unsupported result type ConstantInfo | run |
| 57 | `falseRecA` | Kernel/Basis/False.lean:44 | 5 | frontx: unsupported result type ConstantInfo | run |
| 58 | `strLitStored` | Kernel/CoreDefs.lean:363 | 5 | frontx: unsupported parameter type Env | run |
| 59 | `strLitStoredF` | Kernel/FEnv.lean:205 | 5 | frontx: unsupported parameter type FEnv | run |
| 60 | `blockRecNameSetOk` | Kernel/Inductives/BlockShape.lean:357 | 5 | frontx: unsupported parameter type BlockShape | run |
| 61 | `nestUniformOk` | Kernel/Inductives/Positivity.lean:995 | 5 | frontx: unsupported parameter type NestCtx | inferred (run msg names another type) |
| 62 | `Cached.generatedFireC` | Cached/IndTail.lean:59 | 6 | frontx: unsupported result type RecRuleFire | inferred (run msg names another type) |
| 63 | `andPinOk` | Kernel/Basis.lean:209 | 6 | frontx: unsupported parameter type Declaration | run |
| 64 | `eqReflA` | Kernel/Basis/Eq.lean:29 | 6 | frontx: unsupported result type ConstantInfo | run |
| 65 | `quotMkA` | Kernel/Basis/Quot.lean:38 | 6 | frontx: unsupported result type ConstantInfo | run |
| 66 | `ofReduceAxOkF` | Kernel/DeclCheck.lean:147 | 6 | frontx: unsupported parameter type FEnv | run |
| 67 | `propextA` | Kernel/StdAxioms.lean:128 | 6 | frontx: unsupported result type ConstantVal | run |
| 68 | `basisNamesOk` | Kernel/Basis.lean:144 | 8 | frontx: unsupported parameter type Declaration | run |
| 69 | `basisNamesError` | Kernel/Basis.lean:154 | 8 | frontx: unsupported result type CheckError | run |
| 70 | `andIntroRaw` | Kernel/Basis/And.lean:51 | 8 | frontx: unsupported result type ConstantInfo | run |
| 71 | `trustCompilerOkF` | Kernel/DeclCheck.lean:120 | 8 | frontx: unsupported parameter type FEnv | run |
| 72 | `trustCompilerOk` | Kernel/TrustAxioms.lean:145 | 8 | frontx: unsupported parameter type Env | run |
| 73 | `ofReduceAxOk` | Kernel/TrustAxioms.lean:179 | 8 | frontx: unsupported parameter type Env | run |
| 74 | `quotSoundA` | Kernel/Basis/Quot.lean:105 | 11 | frontx: unsupported result type ConstantInfo | run |
| 75 | `Cached.recFireC` | Cached/CheckerC.lean:79 | 12 | frontx: unsupported result type RecRuleFire | inferred (run msg names another type) |
| 76 | `blockCapsAt` | Kernel/Inductives/BlockInstall.lean:71 | 12 | frontx: unsupported result type IndCaps | inferred (run msg names another type) |
| 77 | `recFire` | Kernel/Install.lean:44 | 12 | frontx: unsupported result type RecRuleFire | inferred (run msg names another type) |
| 78 | `quotIndA` | Kernel/Basis/Quot.lean:88 | 14 | frontx: unsupported result type ConstantInfo | run |
| 79 | `eqRecA` | Kernel/Basis/Eq.lean:44 | 16 | frontx: unsupported result type ConstantInfo | run |
| 80 | `quotLiftA` | Kernel/Basis/Quot.lean:58 | 16 | frontx: unsupported result type ConstantInfo | run |
| 81 | `andRecRaw` | Kernel/Basis/And.lean:76 | 17 | frontx: unsupported result type ConstantInfo | run |
| 82 | `natRecA` | Kernel/Basis/Nat.lean:48 | 18 | frontx: unsupported result type ConstantInfo | run |
| 83 | `ConstantInfo.canon` | Kernel/Canon.lean:73 | 19 | frontx: unsupported result type ConstantInfo | run |
| 84 | `Cached.checkConstantValC` | Cached/IndPass.lean:39 | 20 | frontx: unsupported result type CheckCM Unit | inferred (run msg names another type) |
| 85 | `checkConstantVal` | Kernel/CheckerBase.lean:104 | 20 | frontx: unsupported result type m Unit | inferred (run msg names another type) |
| 86 | `checkConstantValF` | Kernel/DeclCheck.lean:219 | 20 | frontx: unsupported result type m Unit | inferred (run msg names another type) |
| 87 | `stdAxiomOkF` | Kernel/DeclCheck.lean:88 | 30 | frontx: unsupported parameter type FEnv | run |
| 88 | `stdAxiomOk` | Kernel/StdAxioms.lean:185 | 30 | frontx: unsupported parameter type Env | run |
| 89 | `litShapeOk` | Kernel/CoreDefs.lean:374 | 40 | frontx: unsupported parameter type ConstantInfo | run |

### Row 5: Option of heap object (1 functions)

| # | Function | file:line | lines | first failure (run) | tag |
|---:|---|---|---:|---|---|
| 1 | `ClassRead.motiveSlot` | Kernel/Inductives/ClassRead.lean:70 | 4 | frontx: unsupported parameter type ClassRead | inferred (run msg names another type) |

### Row 6: higher-order args (0 functions)

None. Every function that mentions this type also mentions another blocking type.

### Row 7: Level outside shape (2 functions)

| # | Function | file:line | lines | first failure (run) | tag |
|---:|---|---|---:|---|---|
| 1 | `Level.isAlwaysZero` | Kernel/Level.lean:201 | 4 | frontx_ind: Level.isAlwaysZero.match_1 has no equations | run |
| 2 | `Level.zeroWhereZero` | Kernel/Level.lean:209 | 5 | frontx_ind: PropWhen.inter.match_1 has no equations | inferred (run msg names another type) |

### Row 8: HashMap/HashSet/CState (0 functions)

None. Every function that mentions this type also mentions another blocking type.

### Row 9: type-class/universe/dependent (4 functions)

| # | Function | file:line | lines | first failure (run) | tag |
|---:|---|---|---:|---|---|
| 1 | `Expr.resBool` | Cached/ExprOpsC.lean:1374 | 2 | frontx: unsupported parameter type Type | run |
| 2 | `Expr.resNat` | Cached/ExprOpsC.lean:1892 | 2 | frontx: unsupported parameter type Type | run |
| 3 | `ptrDecEq` | Kernel/PtrDecEq.lean:28 | 3 | frontx: unsupported result type Decidable (a = b) | run |
| 4 | `Literal.decEq` | Kernel/Expr.lean:149 | 6 | frontx: unsupported result type Decidable (a = b) | run |

### Row 10: nullary constant (14 functions)

| # | Function | file:line | lines | first failure (run) | tag |
|---:|---|---|---:|---|---|
| 1 | `Cached.natCountMax` | Cached/StateC.lean:163 | 1 | Tactic `introN` failed: There are no additional binders or `let` bindi | run |
| 2 | `Cached.instCCapC` | Cached/StateC.lean:312 | 1 | Tactic `introN` failed: There are no additional binders or `let` bindi | run |
| 3 | `Cached.peelFuel` | Cached/StateC.lean:322 | 1 | Tactic `introN` failed: There are no additional binders or `let` bindi | run |
| 4 | `unitLikeFuel` | Kernel/Core.lean:450 | 1 | Tactic `introN` failed: There are no additional binders or `let` bindi | run |
| 5 | `whnfCoreLoopFuel` | Kernel/Core.lean:1092 | 1 | Tactic `introN` failed: There are no additional binders or `let` bindi | run |
| 6 | `whnfLoopFuel` | Kernel/Core.lean:1116 | 1 | Tactic `introN` failed: There are no additional binders or `let` bindi | run |
| 7 | `bindersFuel` | Kernel/Core.lean:1460 | 1 | Tactic `introN` failed: There are no additional binders or `let` bindi | run |
| 8 | `defeqLoopFuel` | Kernel/Core.lean:1661 | 1 | Tactic `introN` failed: There are no additional binders or `let` bindi | run |
| 9 | `checkFuel` | Kernel/Core.lean:1918 | 1 | Tactic `introN` failed: There are no additional binders or `let` bindi | run |
| 10 | `satRange` | Kernel/Expr.lean:241 | 1 | Tactic `introN` failed: There are no additional binders or `let` bindi | run |
| 11 | `Expr.bvarPoolSize` | Kernel/Expr.lean:1339 | 1 | Tactic `introN` failed: There are no additional binders or `let` bindi | run |
| 12 | `fuelSlack` | Kernel/Inductives/Positivity.lean:300 | 1 | Tactic `introN` failed: There are no additional binders or `let` bindi | run |
| 13 | `Level.defaultFuel` | Kernel/Level.lean:142 | 1 | Tactic `introN` failed: There are no additional binders or `let` bindi | run |
| 14 | `Display.maxLen` | Kernel/Name.lean:155 | 1 | Tactic `introN` failed: There are no additional binders or `let` bindi | run |

### Row 11: state monad / Except / [Monad m] (5 functions)

| # | Function | file:line | lines | first failure (run) | tag |
|---:|---|---|---:|---|---|
| 1 | `Cached.CheckCM` | Cached/StateC.lean:316 | 1 | frontx: unsupported result type Type | inferred (run msg names another type) |
| 2 | `Cached.peelFuelM` | Cached/StateC.lean:324 | 1 | frontx: unsupported result type CheckCM Nat | run |
| 3 | `Cached.flushC` | Cached/StateC.lean:508 | 1 | frontx: unsupported result type CheckCM Unit | run |
| 4 | `CheckM` | Kernel/Error.lean:42 | 1 | frontx: unsupported result type Type u_1 | inferred (run msg names another type) |
| 5 | `Cached.maxNatSizeM` | Cached/StateC.lean:328 | 5 | frontx: unsupported result type CheckCM Nat | run |

### Row 12: Array of heap objects (0 functions)

None. Every function that mentions this type also mentions another blocking type.

### Row 13: Int (0 functions)

None. Every function that mentions this type also mentions another blocking type.

### Row 14: String/Char (9 functions)

| # | Function | file:line | lines | first failure (run) | tag |
|---:|---|---|---:|---|---|
| 1 | `Display.Acc.chars` | Kernel/Name.lean:178 | 2 | unknown free variable `_fvar.4981325` | inferred (run msg names another type) |
| 2 | `Display.Acc.finish` | Kernel/Name.lean:190 | 2 | unknown free variable `_fvar.4981561` | inferred (run msg names another type) |
| 3 | `divModAttemptReason` | Kernel/Checker.lean:372 | 3 | unknown free variable `_fvar.5079642` | inferred (run msg names another type) |
| 4 | `Display.codeEscape` | Kernel/Name.lean:158 | 3 | unknown free variable `_fvar.4981295` | inferred (run msg names another type) |
| 5 | `Display.Acc.component` | Kernel/Name.lean:205 | 3 | unknown free variable `_fvar.4981699` | inferred (run msg names another type) |
| 6 | `Display.Acc.piece` | Kernel/Name.lean:172 | 4 | unknown free variable `_fvar.4981311` | inferred (run msg names another type) |
| 7 | `Display.idShaped` | Kernel/Name.lean:197 | 4 | frontx: unsupported match match s.toList with \| [] => false | inferred (run msg names another type) |
| 8 | `Display.Acc.escaped` | Kernel/Name.lean:183 | 5 | unknown free variable `_fvar.4981341` | inferred (run msg names another type) |
| 9 | `Display.unsafeChar` | Kernel/Name.lean:142 | 11 | frontx: unsupported parameter type Char | run |

## 2. Functions with no table feature in the signature

These are blocked by nothing in the table at the signature level (body features only). Of these, the 6 accepted ones are excluded.

10 functions. Each first failure is shown.

| # | Function | file:line | lines | first failure (run) | tag |
|---:|---|---|---:|---|---|
| 1 | `Cached.natSizeBytes` | Cached/StateC.lean:159 | 1 | frontx: unsupported term Nat.rec (motive := fun x => Nat → Nat) (fun x | run |
| 2 | `Expr.EqPair.dflt` | Kernel/Expr.lean:813 | 1 | frontx: unsupported result type Expr.EqPair | run |
| 3 | `Expr.BeqMap` | Kernel/Expr.lean:816 | 1 | frontx: unsupported result type Type | run |
| 4 | `Expr.BeqOk` | Kernel/Expr.lean:1057 | 1 | frontx: unsupported result type Type | run |
| 5 | `QuotKind.slot` | Kernel/Env.lean:329 | 2 | frontx: unsupported parameter type QuotKind | run |
| 6 | `Expr.beqKey` | Kernel/Expr.lean:824 | 2 | frontx: unsupported parameter type USize | run |
| 7 | `ReducibilityHint.sameRegular` | Kernel/Env.lean:173 | 3 | frontx: unsupported parameter type ReducibilityHint | run |
| 8 | `ClassSlot.isMinor` | Kernel/Inductives/GenRec.lean:215 | 3 | frontx: unsupported parameter type ClassSlot | run |
| 9 | `NestFieldKind.flat` | Kernel/Inductives/Positivity.lean:330 | 3 | frontx: unsupported parameter type NestFieldKind | run |
| 10 | `Expr.BeqSt.record` | Kernel/Expr.lean:1034 | 4 | frontx: unsupported result type Expr.BeqSt | run |

## 3. Leaves: functions with no callees

111 non-accepted functions have no callees by the token match. Accepted leaves (already pass, excluded): `bvarOfData`, `fvarOfData`, `lpOfData`, `Level.isNeverZero`, `Level.combining`.

| # | Function | file:line | lines | needs (table rows, from S) | first failure (run) |
|---:|---|---|---:|---|---|
| 1 | `Expr.HTab` | Cached/ExprOpsC.lean:204 | 1 | Expr, higher-order args | frontx: unsupported result type Type |
| 2 | `Expr.BTab` | Cached/ExprOpsC.lean:1324 | 1 | Expr, higher-order args | frontx: unsupported result type Type |
| 3 | `Expr.NTab` | Cached/ExprOpsC.lean:1857 | 1 | Expr, higher-order args | frontx: unsupported result type Type |
| 4 | `Cached.natSizeBytes` | Cached/StateC.lean:159 | 1 | none (already supported signature) | frontx: unsupported term Nat.rec (motive := fun x => Nat → Nat) (fun x |
| 5 | `Cached.natCountMax` | Cached/StateC.lean:163 | 1 | nullary constant | Tactic `introN` failed: There are no additional binders or `let` bindi |
| 6 | `Cached.nameIsC` | Cached/StateC.lean:197 | 1 | Name | frontx_ind: Bool.and has no argument of a declared type |
| 7 | `Cached.instCCapC` | Cached/StateC.lean:312 | 1 | nullary constant | Tactic `introN` failed: There are no additional binders or `let` bindi |
| 8 | `Cached.peelFuel` | Cached/StateC.lean:322 | 1 | nullary constant | Tactic `introN` failed: There are no additional binders or `let` bindi |
| 9 | `BasisDSL.prop` | Kernel/Basis/Builder.lean:67 | 1 | Expr | frontx: unsupported result type Expr |
| 10 | `BasisDSL.type1` | Kernel/Basis/Builder.lean:70 | 1 | Expr | frontx: unsupported result type Expr |
| 11 | `unitLikeFuel` | Kernel/Core.lean:450 | 1 | nullary constant | Tactic `introN` failed: There are no additional binders or `let` bindi |
| 12 | `whnfCoreLoopFuel` | Kernel/Core.lean:1092 | 1 | nullary constant | Tactic `introN` failed: There are no additional binders or `let` bindi |
| 13 | `whnfLoopFuel` | Kernel/Core.lean:1116 | 1 | nullary constant | Tactic `introN` failed: There are no additional binders or `let` bindi |
| 14 | `bindersFuel` | Kernel/Core.lean:1460 | 1 | nullary constant | Tactic `introN` failed: There are no additional binders or `let` bindi |
| 15 | `defeqLoopFuel` | Kernel/Core.lean:1661 | 1 | nullary constant | Tactic `introN` failed: There are no additional binders or `let` bindi |
| 16 | `checkFuel` | Kernel/Core.lean:1918 | 1 | nullary constant | Tactic `introN` failed: There are no additional binders or `let` bindi |
| 17 | `Env.empty` | Kernel/Env.lean:465 | 1 | multi-field structure/record | frontx: unsupported result type Env |
| 18 | `CheckM` | Kernel/Error.lean:42 | 1 | state monad / Except / [Monad m] | frontx: unsupported result type Type u_1 |
| 19 | `satRange` | Kernel/Expr.lean:241 | 1 | nullary constant | Tactic `introN` failed: There are no additional binders or `let` bindi |
| 20 | `Expr.EqPair.dflt` | Kernel/Expr.lean:813 | 1 | none (already supported signature) | frontx: unsupported result type Expr.EqPair |
| 21 | `Expr.BeqMap` | Kernel/Expr.lean:816 | 1 | none (already supported signature) | frontx: unsupported result type Type |
| 22 | `Expr.bvarPoolSize` | Kernel/Expr.lean:1339 | 1 | nullary constant | Tactic `introN` failed: There are no additional binders or `let` bindi |
| 23 | `BlockShape.formers` | Kernel/Inductives/BlockShape.lean:136 | 1 | List of non-bytes, multi-field structure/record | frontx: unsupported result type List ConstantVal |
| 24 | `BlockShape.nIdxs` | Kernel/Inductives/BlockShape.lean:162 | 1 | List of non-bytes, multi-field structure/record | frontx: unsupported result type List Nat |
| 25 | `ClassGen.slotVar` | Kernel/Inductives/GenRec.lean:113 | 1 | Expr | frontx: unsupported result type Expr |
| 26 | `fuelSlack` | Kernel/Inductives/Positivity.lean:300 | 1 | nullary constant | Tactic `introN` failed: There are no additional binders or `let` bindi |
| 27 | `NestCtx.hiAt` | Kernel/Inductives/Positivity.lean:442 | 1 | multi-field structure/record | frontx: unsupported parameter type NestCtx |
| 28 | `nestPhs` | Kernel/Inductives/Positivity.lean:546 | 1 | Expr, List of non-bytes | frontx: unsupported result type List Expr |
| 29 | `Level.defaultFuel` | Kernel/Level.lean:142 | 1 | nullary constant | Tactic `introN` failed: There are no additional binders or `let` bindi |
| 30 | `Display.maxLen` | Kernel/Name.lean:155 | 1 | nullary constant | Tactic `introN` failed: There are no additional binders or `let` bindi |
| 31 | `Cached.pushKey` | Cached/CoreC.lean:297 | 2 | Expr, List of non-bytes | frontx: unsupported result type List Expr |
| 32 | `Expr.resTerm` | Cached/ExprOpsC.lean:122 | 2 | Expr, type-class/universe/dependent | frontx: unsupported result type Expr |
| 33 | `Expr.resBool` | Cached/ExprOpsC.lean:1374 | 2 | type-class/universe/dependent | frontx: unsupported parameter type Type |
| 34 | `Expr.resNat` | Cached/ExprOpsC.lean:1892 | 2 | type-class/universe/dependent | frontx: unsupported parameter type Type |
| 35 | `Cached.CState.modeMemos` | Cached/StateC.lean:511 | 2 | multi-field structure/record, HashMap/HashSet/CState | frontx: unsupported result type ModeMemos |
| 36 | `BasisDSL.rule` | Kernel/Basis/Builder.lean:116 | 2 | Expr, Name, multi-field structure/record | frontx: unsupported result type RecRule |
| 37 | `BasisDSL.ruleAt` | Kernel/Basis/Builder.lean:120 | 2 | Expr, Name, List of non-bytes, multi-field structure/record, Level outside shape | frontx: unsupported result type RecRule |
| 38 | `etaProjs` | Kernel/CoreDefs.lean:701 | 2 | Expr, Name, List of non-bytes | frontx: unsupported result type List Expr |
| 39 | `QuotKind.slot` | Kernel/Env.lean:329 | 2 | none (already supported signature) | frontx: unsupported parameter type QuotKind |
| 40 | `Expr.beqKey` | Kernel/Expr.lean:824 | 2 | none (already supported signature) | frontx: unsupported parameter type USize |
| 41 | `FEnv.overlay` | Kernel/FEnv.lean:165 | 2 | List of non-bytes, multi-field structure/record | frontx: unsupported result type FEnv |
| 42 | `nestOutKinds` | Kernel/Inductives/BlockInstall.lean:274 | 2 | Expr, List of non-bytes | frontx: unsupported result type List (List (List NestFieldKind)) |
| 43 | `BlockShape.memberCtors` | Kernel/Inductives/BlockShape.lean:139 | 2 | List of non-bytes, multi-field structure/record | frontx: unsupported result type List (List (ConstantVal × Nat)) |
| 44 | `BlockShape.rulePrefixAt` | Kernel/Inductives/BlockShape.lean:181 | 2 | multi-field structure/record | frontx: unsupported parameter type BlockShape |
| 45 | `BlockShape.majorIdxAt` | Kernel/Inductives/BlockShape.lean:186 | 2 | multi-field structure/record | frontx: unsupported parameter type BlockShape |
| 46 | `classOfMotiveVar` | Kernel/Inductives/ClassRead.lean:79 | 2 | List of non-bytes, Option of heap object | frontx: unsupported parameter type List Nat |
| 47 | `nestNonValid` | Kernel/Inductives/Positivity.lean:436 | 2 | multi-field structure/record | frontx: unsupported result type CheckError |
| 48 | `NestCtx.rootHoles` | Kernel/Inductives/Positivity.lean:447 | 2 | List of non-bytes, multi-field structure/record | frontx: unsupported result type List NestHole |
| 49 | `nestKeyMap` | Kernel/Inductives/Positivity.lean:566 | 2 | Expr, List of non-bytes, Option of heap object | frontx: unsupported result type Option Expr |
| 50 | `structProjArgP` | Kernel/Inductives/StructParts.lean:86 | 2 | Expr, Name | frontx: unsupported result type Expr |
| 51 | `blockCtors` | Kernel/Install.lean:32 | 2 | List of non-bytes, multi-field structure/record | frontx: unsupported result type List ConstantInfo |
| 52 | `Display.Acc.finish` | Kernel/Name.lean:190 | 2 | String/Char | unknown free variable `_fvar.4981561` |
| 53 | `Cached.iotaNumArgs` | Cached/CoreC.lean:140 | 3 | Expr | frontx: unsupported parameter type Expr |
| 54 | `Cached.getAppArgsArrGo` | Cached/CoreC.lean:146 | 3 | Expr, Array of heap objects | frontx: unsupported result type Array Expr |
| 55 | `Cached.mkAppRange` | Cached/CoreC.lean:161 | 3 | Expr, Array of heap objects | frontx: unsupported result type Expr |
| 56 | `Cached.isStuckHeadC` | Cached/CoreC.lean:182 | 3 | Expr | frontx: unsupported parameter type Expr |
| 57 | `Cached.whnfCoreEasy` | Cached/CoreC.lean:242 | 3 | Expr | frontx: unsupported parameter type Expr |
| 58 | `Cached.whnfEasy` | Cached/CoreC.lean:322 | 3 | Expr | frontx: unsupported parameter type Expr |
| 59 | `Expr.getAppArgsAccC` | Cached/ExprOpsC.lean:30 | 3 | Expr, List of non-bytes | frontx: unsupported result type List Expr |
| 60 | `Expr.isCompound` | Cached/ExprOpsC.lean:116 | 3 | Expr | frontx: unsupported parameter type Expr |
| 61 | `Expr.isCompoundF` | Cached/ExprOpsC.lean:1298 | 3 | Expr | frontx: unsupported parameter type Expr |
| 62 | `Cached.natNumeralTooBig` | Cached/StateC.lean:166 | 3 | multi-field structure/record | frontx: unsupported result type CheckError |
| 63 | `divModAttemptReason` | Kernel/Checker.lean:372 | 3 | String/Char | unknown free variable `_fvar.5079642` |
| 64 | `liftFueled` | Kernel/Core.lean:164 | 3 | state monad / Except / [Monad m], String/Char, Option of heap object, type-class/universe/dependent | frontx: unsupported result type m α |
| 65 | `Expr.isStrLit` | Kernel/Core.lean:791 | 3 | Expr | frontx: unsupported parameter type Expr |
| 66 | `Expr.isLit` | Kernel/Core.lean:1119 | 3 | Expr | frontx: unsupported parameter type Expr |
| 67 | `CheckMode.verifiedChecks` | Kernel/Env.lean:79 | 3 | multi-field structure/record | frontx: unsupported parameter type CheckMode |
| 68 | `ReducibilityHint.sameRegular` | Kernel/Env.lean:173 | 3 | none (already supported signature) | frontx: unsupported parameter type ReducibilityHint |
| 69 | `ProjTable.entry` | Kernel/Env.lean:284 | 3 | multi-field structure/record | frontx: unsupported result type ProjEntry |
| 70 | `Expr.beqRecursive` | Kernel/Expr.lean:790 | 3 | Expr | frontx: unsupported parameter type Expr |
| 71 | `Expr.beqIsApp` | Kernel/Expr.lean:795 | 3 | Expr | frontx: unsupported parameter type Expr |
| 72 | `Expr.isForallE` | Kernel/ExprOps.lean:836 | 3 | Expr | frontx: unsupported parameter type Expr |
| 73 | `Expr.getAppFn` | Kernel/ExprOps.lean:848 | 3 | Expr | frontx: unsupported result type Expr |
| 74 | `Expr.getAppArgs` | Kernel/ExprOps.lean:853 | 3 | Expr, List of non-bytes | frontx: unsupported result type List Expr |
| 75 | `Expr.mkAppN` | Kernel/ExprOps.lean:858 | 3 | Expr, List of non-bytes | frontx: unsupported result type Expr |
| 76 | `Expr.piResult` | Kernel/ExprOps.lean:880 | 3 | Expr | frontx: unsupported result type Expr |
| 77 | `Expr.fvarTypeD` | Kernel/ExprOps.lean:905 | 3 | Expr | frontx: unsupported result type Expr |
| 78 | `ClassSlot.isMinor` | Kernel/Inductives/GenRec.lean:215 | 3 | none (already supported signature) | frontx: unsupported parameter type ClassSlot |
| 79 | `NestFieldKind.flat` | Kernel/Inductives/Positivity.lean:330 | 3 | none (already supported signature) | frontx: unsupported parameter type NestFieldKind |
| 80 | `consSumCtors` | Kernel/Inductives/SumInstall.lean:123 | 3 | Name, List of non-bytes, multi-field structure/record | frontx: unsupported result type Env |
| 81 | `Name.nodup` | Kernel/Level.lean:228 | 3 | Name, List of non-bytes | frontx: unsupported parameter type List Name |
| 82 | `Expr.numArgs` | Kernel/PropRead.lean:56 | 3 | Expr | frontx: unsupported parameter type Expr |
| 83 | `PropWhen.isProp` | Kernel/PropRead.lean:199 | 3 | multi-field structure/record | frontx: unsupported parameter type PropWhen |
| 84 | `PropWhen.isNever` | Kernel/PropWhen.lean:53 | 3 | multi-field structure/record | frontx: unsupported parameter type PropWhen |
| 85 | `canonNameMap` | Kernel/Canon.lean:60 | 4 | Name, List of non-bytes | frontx_ind: Expr.bvarBoundGo.match_3 has no equations |
| 86 | `listBeqBy` | Kernel/Canon.lean:292 | 4 | List of non-bytes, higher-order args, type-class/universe/dependent | frontx: unsupported parameter type Type |
| 87 | `unwrapOr` | Kernel/CheckerBase.lean:128 | 4 | state monad / Except / [Monad m], multi-field structure/record, Option of heap object, type-class/universe/dependent | frontx: unsupported result type m α |
| 88 | `natIndOk` | Kernel/CoreDefs.lean:163 | 4 | multi-field structure/record, Option of heap object | frontx: unsupported parameter type Option ConstantInfo |
| 89 | `Expr.substConst0` | Kernel/CoreDefs.lean:631 | 4 | Expr, Name | frontx: unsupported result type Expr |
| 90 | `Expr.piSortTeleLen?` | Kernel/Env.lean:385 | 4 | Expr, Option of heap object | frontx: unsupported parameter type Expr |
| 91 | `Expr.binderPair?` | Kernel/ExprOps.lean:842 | 4 | Expr, Option of heap object | frontx: unsupported result type Option (Expr × Expr × Expr × Expr) |
| 92 | `MemberShape.structCtor?` | Kernel/Inductives/BlockShape.lean:105 | 4 | multi-field structure/record, Option of heap object | frontx: unsupported result type Option (ConstantVal × Nat) |
| 93 | `ClassRead.motiveSlot` | Kernel/Inductives/ClassRead.lean:70 | 4 | Option of heap object | frontx: unsupported parameter type ClassRead |
| 94 | `Expr.phApp?` | Kernel/Inductives/Positivity.lean:516 | 4 | Expr, Name, List of non-bytes, Option of heap object, Level outside shape | frontx: unsupported result type Option (Name × List Level) |
| 95 | `targetHoles` | Kernel/Inductives/RecCheck.lean:90 | 4 | Expr, List of non-bytes | frontx: unsupported result type List Expr |
| 96 | `Display.idShaped` | Kernel/Name.lean:197 | 4 | String/Char | frontx: unsupported match match s.toList with \| [] => false |
| 97 | `PropWhen.inter` | Kernel/PropWhen.lean:73 | 4 | multi-field structure/record | frontx: unsupported result type PropWhen |
| 98 | `Expr.constHoleAt?` | Cached/IndPositivity.lean:50 | 5 | Expr, Name, List of non-bytes, Option of heap object, higher-order args, Level outside shape | frontx: unsupported result type Option Expr |
| 99 | `Cached.CState.flushed` | Cached/StateC.lean:502 | 5 | multi-field structure/record, HashMap/HashSet/CState | frontx: unsupported result type CState |
| 100 | `stringTyOk` | Kernel/CoreDefs.lean:265 | 5 | multi-field structure/record, Option of heap object | frontx: unsupported parameter type Option ConstantInfo |
| 101 | `charTyOk` | Kernel/CoreDefs.lean:273 | 5 | multi-field structure/record, Option of heap object | frontx: unsupported parameter type Option ConstantInfo |
| 102 | `recFireLevelCount` | Kernel/CoreDefs.lean:968 | 5 | Name, List of non-bytes, multi-field structure/record | frontx: unsupported parameter type RecRule |
| 103 | `Expr.piBinders` | Kernel/Inductives/FieldTele.lean:47 | 5 | Expr, List of non-bytes | frontx: unsupported result type List Expr × Expr |
| 104 | `targetPinTys` | Kernel/Inductives/RecCheck.lean:307 | 5 | Expr, state monad / Except / [Monad m], List of non-bytes, multi-field structure/record | frontx: unsupported result type m Unit |
| 105 | `Level.allParamsDefined` | Kernel/Level.lean:45 | 5 | Name, List of non-bytes, Level outside shape | frontx: unsupported parameter type List Name |
| 106 | `Expr.depthP` | Cached/ExprOpsC.lean:1901 | 7 | Expr | frontx: unsupported parameter type Expr |
| 107 | `Expr.sizeF` | Kernel/ExprOps.lean:788 | 7 | Expr | frontx: unsupported parameter type Expr |
| 108 | `classMinorSlot` | Kernel/Inductives/GenRec.lean:220 | 9 | state monad / Except / [Monad m], Name, List of non-bytes | frontx: unsupported result type m (Nat × List (Nat × Nat)) |
| 109 | `Expr.hasFvar` | Kernel/ExprOps.lean:60 | 16 | Expr | frontx: unsupported parameter type Expr |
| 110 | `natOpName` | Kernel/CoreDefs.lean:480 | 18 | Name | frontx_ind: Bool.or has no argument of a declared type |
| 111 | `structElimLevel` | Kernel/Inductives/StructParts.lean:45 | 21 | Name, Level outside shape | frontx_ind: equation ite.eq_1 has no constructor pattern |

## 4. Counts

- Probed functions in this report: 1093 (incl. 6 accepted).
- Single-feature targets: 285; no-feature functions (section 2): 10; leaves: 111 (of which 8 have no table feature).
- Rows with zero single-feature targets: 6 higher-order args, 8 HashMap/HashSet/CState, 12 Array of heap objects, 13 Int.
- Functions with `S` mentioning a feature in `final.json` but no single-feature version are multi-feature: they become targets only after all their listed features land.
