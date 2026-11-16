# con-leche depth probe, rerun on current main

Companion to `CONLECHE_DEPTH.md` (first probe, main at that time). Same source, same 1 103 names, same roots.
Branch `conleche-depth2`; compiler sources not modified. Scripts and raw output: `Testing/conleche-depth2/`.
Evidence tags: **run** = a Lean message from this session; **read** = from source text; **inference** = my reasoning from run/read facts.

## 0. What was run

- Compiler: `main` @ `b8199bc` (Lean 4.29.0). Build cache restored (`repo-build.tar.zst.part-*`, `sail-riscv-lean`, `sailsim`); `lake build Frontx` succeeded (374 jobs; cache was at `fa8183c`, so modules changed since were rebuilt).
- Source: `Testing/conleche-depth/out/F2.lean.txt` from `origin/conleche-depth` (56 files, E1 edits only). Its old probe section was dropped; everything else is unchanged.
- Declared in the probe file (not imported, because `ConLeche.Expr` is defined both in the source and in `Riscv/Frontx/ExprExamples.lean`):
  `frontx_ind_type TExpr := ConLeche.Expr nesting ConLeche.Level, ConLeche.Name, List ConLeche.Level, ConLeche.Literal, List ConLeche.Expr, Option ConLeche.Expr`. **run**: accepted, shape printed.
- Per name, two commands: `frontx_compile f` and `frontx_ind_gate f on TExpr`.
- Names: the 1 103 of the first probe (`out/names_first_probe.json`). Same set, so the totals are comparable.
- Runs: `F2P` (compile + gate) took 7 min. `F2I` (real `frontx_ind f on TExpr` for the 42 gate-passing names) is in §4.

## 1. Totals

| | first probe | this run (main `b8199bc`) |
|---|---:|---:|
| names | 1 103 (1 093 resolved) | 1 103 (1 093 resolved) |
| `frontx_compile` passes | 3 | 4 (`bvarOfData`, `fvarOfData`, `lpOfData`, `Display.unsafeChar`) |
| gate passes (`gate ok; arms ok`) | 3 (on `TLevel`) | 42 (on `TExpr`) |
| accepted (compile or gate) | 6 | **46** |
| blocked (gate fail 982 + body/arms fail 65) | 1 087 | **1 047** |
| unresolved names | 10 | 10 (see §2 note) |

All counts **run**. The 46 accepted sets do not overlap. `Expr.instantiate1` (a root) now passes the gate. `Display.unsafeChar` compiles now; in the first probe it was a `String/Char` failure. The gate covers `frontx_ind` only: a gate pass means the type gate and the arms translate, not that the function compiles end to end (see §4).

## 2. Blocker table (first failure per function, sorted by count)

First failure = the first message of `frontx_ind_gate` (**run**). The gate stops at the first failing signature, so later blockers are hidden for these functions. Counts are of the 1 047 blocked names.

| # | first failure (class) | count | example (`file` in con-leche) |
|---:|---|---:|---|
| 1 | no parameter of the `Expr`/`Name`/`Level` family (0-ary, or only `Env`, `BlockShape`, `CState`, `Nat`, `Bool` …) | 347 | `Env.empty`, `mkFEnv`, `natName`, `stringName`, `Cached.declStep` |
| 2 | monad / higher-kinded: `Type → Type` (`[Monad m]`), `m α`, `CheckM`, `CheckCM`, `CoreFns m` | 206 | `whnfBody` `Core.lean:1153`, `inferBody`, `defeqBody`, `ensureSort` |
| 3 | `<f>: type mismatch` (message has no detail; 43 of 115 are `Cached.*`) | 115 | `Cached.CState.leaveEager`, `Cached.blockRecsC`, `checkBlockAgree` |
| 4 | `List`/`Array`/`Option` of a non-family element (`List Name`, `Array Expr`, `Option ConstantInfo`, `List ConstantInfo`) | 93 | `Expr.instantiateLevelParams` (`List Name`) |
| 5 | multi-field structure outside the family (`Env`, `FEnv`, `ConstantInfo`, `CheckMode`, `NestCtx`, `ProjTable`, `ProjEntry`, `CheckError`, …) | 82 | `Env.find?` `Env.lean:467`, `ProjEntry.typeAt`, `whnf` (`CheckMode`) |
| 6 | body (arms): pattern on a `Level`/`Expr` literal, `ite`, `decEq` | 48 | `Expr.isBoolTrue` (see row 11) |
| 7 | function-valued parameter (`Name → …`, `Name → List Level → Option Expr`) | 42 | `Cached.memoBI` `CoreC.lean:348` |
| 8 | two scalar parameters (only one allowed) | 32 | `Expr.abstract1` |
| 9 | two declared-type parameters besides the structural one | 13 | `BasisDSL.ruleAt` |
| 10 | other types: memo/HashMap/Beq state 16 (`Expr.MemoXP`, `MemoB`, `MemoN`, `Std.HashMap Expr Nat`, `Expr.Beq*`), `NatOpPinSet` 6, `String` 5, `BlockShape` 4, `ClassGen` 4, `ClassKey` 3, `TargetMajor` 3, `Int` 3, `FBase` 2, `Cached.NatBinOp`/`CState` 2, `PropWhen` 1, `Type` 1 | 50 | `Int`: `Level.rest` etc. |
| 11 | body (arms): string literal constant `TExpr.lit.s…` not generated (`Unknown constant`); 7 messages mention it, overlapping rows 6 and 12 | 7 | `Expr.isBoolTrue` (`Expr.lit` of `"Bool"`) |
| 12 | body (arms): nested patterns (5), dropped field (6), unsupported term (3), pattern on another argument (2), recursive call not on a child (1), `==` on `Level` (1), not a constant (1) | 19 | `natOpName` (`comparison of an unsupported type Level`) |
| 13 | `no equations` (partial) | 1 | `Expr.hasStrLitGo` |

Notes on the table:
- Rows 1-5 and 7-10 are signature failures. Rows 6, 11-12 are body failures; they are reached only when the signature passes (65 `ARMS_FAIL` in total).
- 10 names are unresolved: `ConLeche.checkDecl`, `ConLeche.checkDeclKind` (defined in `Kernel/CheckDecl.lean`, outside the import closure of `Kernel/Core` + `Cached/Decls` that the source file was built from) and 8 `beside.ConLeche.Expr.mk*` names (`Cached/ExprNodes`, same reason, plus a name-index artifact of the first probe). **run** (unknown constant) + **read** (file location).
- "Transitive" counts are not reported. The name-graph closure is an over-approximation: `whnfBody`, `inferBody`, `defeqBody` share one 252-name closure, and `Cached.checkDecls` has 961 names in its closure, 846 of them gate-failing. These are upper bounds, not blocker counts.

## 3. Greedy smallest feature set (signature level)

Method: features from the signature text (regex, **read**); a function is covered when all its signature features are in the chosen set, or it already passes the gate (**run**). Necessary, not sufficient: bodies are not counted except as §2 rows 6-12. Baseline (no features, or already passing): 183 of 1 101 probed in the index.

| step | add | covered (of 1 101) |
|---:|---|---:|
| 1 | multi-field structure outside the family (`Env`, `FEnv`, `ConstantInfo`, `CheckMode`, `NestCtx`, …) | 320 |
| 2 | monad (`Type → Type`, `m α`, `CheckM`, `CheckCM`, `CoreFns`) | 529 |
| 3 | `List`/`Array`/`Option` of a non-family element | 757 |
| 4 | nullary constants (0-ary `def`) | 959 |
| 5 | `HashMap`/`HashSet`/memo state | 1 016 |
| 6 | function-valued parameters | 1 076 |
| 7 | `String`/`Char` | 1 097 |
| 8 | `Int` | 1 101 |

Reading: the first three steps cover ~757 of 1 101 (**run**-checked signatures, regex features). The nullary-constant rule is a crude regex (230 mentions), so step 4 is the least reliable number. The result is the same ordering as the first probe: data model first, then monad, then the collections.

## 4. What blocks `whnfBody`, `inferBody`, `defeqBody`, `checkDecl` now

- **`whnfBody`** (`Core.lean:1153`): first failure **run**: `unsupported parameter type Type → Type` (the `m` of `[Monad m]`). Hidden after that (**read** from the signature): `r : CoreFns m` (a record of closures, row 5 + 7), result `m Expr` (row 2). Direct callees: `whnfLoopFuel` (nullary: 2^62), `whnfLoop` (`Type → Type`), `Expr.depth` (passes).
- **`inferBody`** (`Core.lean:1226`): first failure **run**: `Type → Type`. Hidden (**read**): `CoreFns m`, `m Expr`. Direct callees that fail on their own: `Expr.instantiateLevelParams` (`List Name`), `Expr.abstract1` (two scalars), `Env.find?`, `Env.findProj?`, `ProjTable.entry`, `ConstantInfo.toConstantVal`, `ProjEntry.typeAt`, `FBase.find?`, `FEnv.find?`, `natName`/`stringName` (nullary `Name` constants), `unknownConstError` (`CheckError` result), `whnf` (`CheckMode`), `ensureSort` (`Type → Type`). Passing callees: `Expr.instantiate1`, `Expr.getAppFn`, `Expr.getAppArgs`.
- **`defeqBody`** (`Core.lean:1830`): first failure **run**: `Type → Type`. Hidden (**read**): `eager : Bool`, `CoreFns m`, result `m Bool`. Direct callees: `propIrrel`, `boolTrueShortcut`, `quickDefEq`, `lazyDeltaReduction`, `defeqProjPair`, `defeqStuck` (all `Type → Type`), `defeqLoopFuel` (nullary), `whnfCore` (`CheckMode`), `Expr.isBoolTrue` (passes the gate; arms fail on the string literal constant `TExpr.lit.s…`, row 11).
- **`checkDecl`** (`CheckDecl.lean:169`): **not probed**: the definition is outside the source file's import closure (§2). Its root in the probe, `Cached.checkDecls` (`Cached/Decls.lean:89`), fails first with `no argument of a declared type` (**run**; parameters `CheckMode`, `List NatOpPinSet`, `Nat`, `Array Declaration`; result `Except (CheckError × Nat) Env`). Its direct callees `Env.empty`, `mkFEnv`, `Cached.declStep` fail on `Env`/`FEnv` results (**run**).

**Inference:** `whnfBody`/`inferBody`/`defeqBody` need two things before their bodies are reached: a monad fixed at the use site (row 2) and the `CoreFns m` record (rows 5 and 7). Neither is in `frontx_ind` now. Whether the bodies then pass is not known from this run.

**Inference:** `Expr.isBoolTrue`-style functions need a generated `TExpr.lit.s…` constant for every string literal in an Expr-family body. The `ConLecheBlk.lean` mechanism does this for `Name` constants. Not tested here.

## 5. Real `frontx_ind` (not only the gate)

See §6 for the status of the `F2I` run (real `frontx_ind f on TExpr` for the 42 gate-passing names).

## 6. Caveats

- The gate result is per function, one message each; it stops at the first failing signature.
- `frontx_compile` and `frontx_ind_gate` were run on the same probe file; no function was compiled twice.
- Regex-based features (§3) are reading, not running.
- `checkDecl` and `Cached/ExprNodes` are outside the source file; they need the rest of con-leche to be probed.
- No compiler source was modified.

## 7. Reproduce

```
git checkout conleche-depth2   # Testing/conleche-depth2/scripts/{index,mkprobe,parse,analyze,greedy}.py
python3 Testing/conleche-depth2/scripts/index.py        # index of F2.lean.txt (reach set)
python3 Testing/conleche-depth2/scripts/mkprobe.py      # writes out/F2P.lean (1 103 names, compile + gate)
lake env lean --tstack=4000000 -DmaxErrors=100000 Testing/conleche-depth2/out/F2P.lean > out/F2P.out   # ~7 min
python3 Testing/conleche-depth2/scripts/parse.py out/F2P.out out/results_gate_compile.json
python3 Testing/conleche-depth2/scripts/analyze.py      # tables (paths point to /home/user/scratch/cl2; adjust)
python3 Testing/conleche-depth2/scripts/greedy.py
```
