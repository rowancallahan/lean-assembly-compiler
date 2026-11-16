# CONLECHE_S1: con-leche batch functions, numbers % 4 == 1

Batch sources: `Testing/conleche-batches/batchA.lean` and `batchB.lean` (con-leche @6810492c1). Targets are the
`-- frontx_ind NAME on TExpr` markers, numbered in file order: batchA 1-27, batchB 28-257. The 65 with number % 4 == 1 are below.

## Result

- Gate (`frontx_ind_gate`): 20 of the 61 targets with a verdict pass the type gate (`gate ok`).
- `frontx_ind`: tried on those 20, **2 compile**: `Expr.beqIsApp` (5), `Cached.whnfCoreEasy` (241).
- Tests: `expr_beqisapp` and `cached_whnfcoreeasy`, 50 cases each, **QEMU only**: all cases equal Lean's results.
  The Sail half of `frontx_test.py` was **not run**: no Sail simulator is available here (`/home/user/deps/sailsim` is absent,
  and the `sail-riscv` release is not reachable through `gh`).
- `Riscv/Frontx/ConLecheS1.lean` holds only the two compiled functions (a file with errors cannot be imported).
  It compiles with no errors; `#print axioms` gives `propext` for each function (the `implements1` wrappers carry the Sail axiom set, as in ExprExamples).
- The diagnostic for all 65 (gate + `frontx_ind` attempts, 73 errors) is `Testing/notes/frontx/conleche_s1_gate_diag.lean.txt`
  (not compiled; the tools that produce it are in `Testing/notes/frontx/conleche_s1_tools/`).

## Notes on the setup

- `batchA.lean` is not on `origin/conleche-batch-b`. It is taken from `origin/conleche-batch-b2`, which holds both batch files and differs from `origin/conleche-batch-a`'s copy.
- The batch files are not self-contained (see the blockers below). Each target's closure (defs, structures, inductives, and `instance`s
  when `=`/`decide` is used) was copied verbatim, with its namespace/`open`/`variable` context. Names already defined in `Riscv/Frontx` were not re-emitted.
- Blockers seen in the diagnostic (not the frontx gate): `_cut` theorems referenced but never copied (`instantiate1P_cut`, `abstractRangeP_cut`, ...);
  `pi`, `lm`, `cnst`, `instantiateListXP`, `Level.allParamsDefined`, `Expr.mkBvar`, `Expr.ptrDec` unknown; `Expr.decEq` does not elaborate
  (needs `DecidableEq` for `Name`/`Level`, which is not in the batch), so `DecidableEq Expr` is unavailable.

## Per function

| # | function | gate | `frontx_ind` compiled | error (exact, first line) |
|---:|---|---|---|---|
| 1 | `Expr.hasLP` | ok, arms FAIL | no | UInt64.decEq has no argument of a declared type |
| 5 | `Expr.beqIsApp` | ok, arms ok | yes |  |
| 9 | `Expr.BeqOutX.cast` | FAIL: more than one extra parameter of a declared type | not tried |  |
| 13 | `Expr.looseBVarsBounded` | already in Riscv/Frontx (not re-run) | n/a |  |
| 17 | `Expr.liftLooseBVars` | FAIL: more than one scalar parameter | not tried |  |
| 21 | `Expr.isForallE` | already in Riscv/Frontx (not re-run) | n/a |  |
| 25 | `Expr.mkAppN` | ok, arms FAIL | no | unsupported variable (a dropped field?) |
| 29 | `natPredName` | FAIL: ConLeche.natPredName has no argument of a declared type | not tried |  |
| 33 | `natPowName` | FAIL: ConLeche.natPowName has no argument of a declared type | not tried |  |
| 37 | `natModName` | FAIL: ConLeche.natModName has no argument of a declared type | not tried |  |
| 41 | `natXorName` | FAIL: ConLeche.natXorName has no argument of a declared type | not tried |  |
| 45 | `natSuccName` | FAIL: ConLeche.natSuccName has no argument of a declared type | not tried |  |
| 49 | `listNilName` | FAIL: ConLeche.listNilName has no argument of a declared type | not tried |  |
| 53 | `Expr.depth` | already in Riscv/Frontx (not re-run) | n/a |  |
| 57 | `Expr.instantiate1C` | ok, arms FAIL | no | dite has no argument of a declared type |
| 61 | `Expr.piSortTeleLen?` | FAIL: unsupported result type | not tried |  |
| 65 | `lamProj?` | FAIL: unsupported result type | not tried |  |
| 69 | `falseName` | FAIL: ConLeche.falseName has no argument of a declared type | not tried |  |
| 73 | `quotIndName` | FAIL: ConLeche.quotIndName has no argument of a declared type | not tried |  |
| 77 | `BasisDSL.prop` | FAIL: ConLeche.BasisDSL.prop has no argument of a declared type | not tried |  |
| 81 | `natRecMotive` | FAIL: ConLeche.natRecMotive has no argument of a declared type | not tried |  |
| 85 | `quotLiftH` | FAIL: ConLeche.quotLiftH has no argument of a declared type | not tried |  |
| 89 | `andRecName` | FAIL: ConLeche.andRecName has no argument of a declared type | not tried |  |
| 93 | `pinLinkOk` | FAIL: ConLeche.pinLinkOk has no argument of a declared type | not tried |  |
| 97 | `rawNatLit?` | FAIL: unsupported result type | not tried |  |
| 101 | `boolTrueName` | FAIL: ConLeche.boolTrueName has no argument of a declared type | not tried |  |
| 105 | `reservedRecName` | ok, arms FAIL | no | Bool.or has no argument of a declared type |
| 109 | `Expr.substConst0` | FAIL: more than one extra parameter of a declared type | not tried |  |
| 113 | `unitFieldTele` | ok, arms FAIL | no | unsupported parameter type |
| 117 | `Expr.hasLooseBVarB` | ok, arms FAIL | no | equation ConLeche.Expr.bvarB.eq_1 has no constructor pattern |
| 121 | `Expr.isLit` | already in Riscv/Frontx (not re-run) | n/a |  |
| 125 | `propextName` | FAIL: ConLeche.propextName has no argument of a declared type | not tried |  |
| 129 | `iffRecName` | FAIL: ConLeche.iffRecName has no argument of a declared type | not tried |  |
| 133 | `structPsAt` | FAIL: ConLeche.structPsAt has no argument of a declared type | not tried |  |
| 137 | `structProjBodiesGo` | FAIL: more than one extra parameter of a declared type | not tried |  |
| 141 | `Expr.nestOcc` | FAIL: unsupported parameter type | not tried |  |
| 145 | `nestKeyMap` | ok, arms FAIL | no | equation ite.eq_1 has no constructor pattern |
| 149 | `reduceBoolDeclPin` | FAIL: ConLeche.reduceBoolDeclPin has no argument of a declared type | not tried |  |
| 153 | `trustCompilerName` | FAIL: ConLeche.trustCompilerName has no argument of a declared type | not tried |  |
| 157 | `ofReduceBoolName` | FAIL: ConLeche.ofReduceBoolName has no argument of a declared type | not tried |  |
| 161 | `reduceCertVar` | ok, arms FAIL | no | ConLeche.Expr.fvar has no equations |
| 165 | `targetPiDomsWith` | FAIL: unsupported result type | not tried |  |
| 169 | `divModDeclPin` | FAIL: unsupported parameter type | not tried |  |
| 173 | `divModCertApplied` | ok, arms FAIL | no | nested patterns are not supported (ConLeche.divModCertApplied.eq_1) |
| 177 | `ClassGen.binder` | FAIL: unsupported parameter type | not tried |  |
| 181 | `ClassGen.motiveTy` | FAIL: ConLeche.ClassGen.motiveTy has no argument of a declared type | not tried |  |
| 185 | `ClassGen.prefixBinders` | FAIL: ConLeche.ClassGen.prefixBinders has no argument of a declared type | not tried |  |
| 189 | `Expr.dropVars` | ok, arms FAIL | no | Nat.brecOn has no argument of a declared type |
| 193 | `Expr.liftLooseBVarsC` | FAIL: more than one scalar parameter | not tried |  |
| 197 | `Expr.abstractRangeP` | FAIL: more than one scalar parameter | not tried |  |
| 201 | `Expr.wscopedBP` | ok, arms FAIL | no | equation ConLeche.Expr.fvarB.eq_1 has no constructor pattern |
| 205 | `Expr.hasLooseBVarInP` | FAIL: more than one scalar parameter | not tried |  |
| 209 | `Expr.mentionsAnyConstP` | FAIL: unsupported parameter type | not tried |  |
| 213 | `Expr.fvarLeavesC` | FAIL: unsupported result type | not tried |  |
| 217 | `Expr.leafGuard` | ok, arms FAIL | no | Bool.or has no argument of a declared type |
| 221 | `Expr.piResidual` | ok, arms FAIL | no | more than one extra parameter of a declared type |
| 225 | `Expr.closeLamsC` | ok, arms FAIL | no | more than one scalar parameter |
| 229 | `Expr.allLevelParamsDefinedP` | FAIL: unsupported parameter type | not tried |  |
| 233 | `Cached.nameIsC` | ok, arms FAIL | no | Bool.and has no argument of a declared type |
| 237 | `Cached.inst1M` | FAIL: unsupported result type | not tried |  |
| 241 | `Cached.whnfCoreEasy` | ok, arms ok | yes |  |
| 245 | `Cached.pushKey` | ok, arms ok | no | equation ite.eq_1 has no constructor pattern |
| 249 | `Cached.structUsedLaterC` | FAIL: more than one scalar parameter | not tried |  |
| 253 | `Cached.eraseFVarTysC` | ok, arms FAIL | no | sorryAx has no equations |
| 257 | `Cached.Expr.dropVarsC` | ok, arms FAIL | no | Nat.brecOn has no argument of a declared type |

"already in Riscv/Frontx" = the name is defined there by an earlier branch (not re-run). "not tried" = gate failed.

## Gate failure kinds (41)

- `has no argument of a declared type` (nullary `Name` constants, scalar-only functions): 22
- `more than one scalar parameter` (5) / `more than one extra parameter of a declared type` (3): 8
- `unsupported result type` (6) / `unsupported parameter type` (5): 11
