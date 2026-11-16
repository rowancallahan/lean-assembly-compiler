# CONLECHE_S0: frontx_ind on con-leche batch functions (numbers % 4 == 0)

## Summary

- Functions: 376 top-level `def`/`abbrev` in batchA (49) then batchB (327), numbered in file order. Targets: the 94 with number % 4 == 0 (92 distinct names; `Expr.hasFvar` and `Expr.piResult` occur in both batches).
- Gate (`frontx_ind_gate`): 23 distinct PASS, 69 FAIL.
- `frontx_ind` compiled: 9 distinct (`beqRecursive`, `hasFvar`, `piResult`, `numArgs`, `teleArityOk`, `isLit`, `depth`, `isCompound`, `whnfCoreKeyC`).
- Tests (`check 50`, QEMU == Sail == Lean): 8 pass. `teleArityOk` compiled but has no test (its second input is a `List Expr`; I found no encoder for it in the emit helpers).
- Axioms (`#print axioms`, at end of `Riscv/Frontx/ConLecheS0.lean`): the tested functions depend only on `propext`; `hasFvar` on none. No `sorryAx` in them. I wrote no `sorry`, `axiom`, or `native_decide` in code.

## Deviations and blockers (read first)

1. **Batch A source.** `origin/conleche-batch-b` has no `batchA.lean`. I used `origin/conleche-batch-a` (`Testing/conleche-batches/batchA.lean`). Batch B is from `origin/conleche-batch-b`.
2. **Whole source dump, not a minimal closure.** The batch files are not self-contained. They drop dot-constructor helpers (`BeqOutX.yes/no/mk`, found in the dump) and helpers such as `BeqSt.record` and `Expr.beqIsApp`. I first tried a name-based closure over the dump, which dropped scope lines and instances and gave about 2,600 errors. The whole dump with gates gave 34 error lines before the `frontx_ind` lines were added. So `Riscv/Frontx/ConLecheS0.lean` is the complete `origin/conleche-depth` dump (`Testing/conleche-depth/out/F2.lean.txt`, con-leche @6810492c1) with its probe lines removed (`frontx...` commands and stray `#` lines), then the gate lines, `frontx_ind` lines and test emitters. This contains more definitions than the targets need. Con-leche code is otherwise verbatim.
3. **The file does not compile cleanly under Lean 4.29.** The final file has 44 errors in the dump region: 18 from `ite_eq_left` / `ite_eq_right` (absent in this Lean version; the dump comes from the con-leche toolchain), 19 `unsolved goals` that follow from them, 3 `rewrite` failures, 2 application mismatches, 1 `include_str` parse error, 1 `simp` failure. The `frontx_ind` region has 14 errors, one for each failing row in the table. Three definitions (`instantiateLiftC`, `resBool`, `depthC`) were elaborated with `sorry` after errors in their bodies. None of the 8 tested functions depends on a `sorry` (see above).
4. **Branch build.** `Riscv/Frontx/ConLecheS0.lean` is inside the `Frontx` library glob, so `lake build Frontx` fails on this branch until it is moved or fixed. I kept the requested path.
5. **Gate and frontx_ind results are from the full file.** Gate outcomes depend on what elaborates in this file: a target fails the gate if one of its dependencies failed to elaborate.

## Setup (done)

- Build cache: `origin/build-cache` `sail-riscv-lean.tar.zst` extracted to `../deps/sail-riscv-lean`. elan installed; toolchain Lean 4.29.0.
- `lake build Frontx`: completed (301 jobs).
- Test tools: `qemu-system-misc`, `gcc-riscv64-linux-gnu`, `binutils-riscv64-linux-gnu` from apt. Sail simulator from the `sail-riscv` 0.9 release, installed at `/home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim`, the path `frontx_test.py` expects.
- `Testing/asm/ctest` removed after each test run.

## Tests

- Emitters: `namespace S0Emit` and the `#eval` blocks at the end of `Riscv/Frontx/ConLecheS0.lean` (helpers copied from `Testing/asm/emit_expr.lean`). They write `Testing/asm/frontx-words/s0_*.words` and `.cases`.
- Run: `python3 Testing/asm/frontx_test.py check 50 s0_<name>`, one per tested function. All 8 printed `50 cases ok (QEMU == Sail == Lean ...)`.
- `Testing/conleche-s0/make_s0.py` regenerates the numbered target list and the gate lines. It does not regenerate the `frontx_ind` lines or the emitters, which I added by hand.

## Per-function results

- *gate*: `frontx_ind_gate` output. PASS means `gate ok` (with `arms ok` or `arms FAIL` in the message).
- *frontx_ind*: `yes` = no error at the command's line in the compile. `no` = error, shown in the last column. `not attempted` = the gate failed, so `frontx_ind` was not tried (per the task).
- Rows marked *same name as #N* repeat a function from batch A or B. They are gated twice but `frontx_ind` only once.
- The three `declaration uses sorry` warnings (#248, #280, #312 in the table) come from Lean's error recovery in those definitions, not from code I wrote.

| # | src:line | function | gate | gate message | frontx_ind | tests | error (exact) |
|---:|---|---|---|---|---|---|---|
| 4 | batchA:40 | `ConLeche.withExcl` | FAIL | gate FAIL: frontx_ind: unsupported parameter type | not attempted (gate failed) | - | frontx_ind: unsupported parameter type |
| 8 | batchA:59 | `ConLeche.lpOfData` | FAIL | gate FAIL: frontx_ind: ConLeche.lpOfData has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.lpOfData has no argument of a declared type |
| 12 | batchA:85 | `ConLeche.Expr.beqRecursive` | PASS | gate ok; arms ok (1 function(s)) | yes | yes: 50 cases, QEMU == Sail == Lean |  |
| 16 | batchA:126 | `ConLeche.Expr.beqKey` | FAIL | gate FAIL: frontx_ind: ConLeche.Expr.beqKey has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.Expr.beqKey has no argument of a declared type |
| 20 | batchA:266 | `ConLeche.Expr.probeHit` | FAIL | gate FAIL: frontx_ind: unsupported parameter type | not attempted (gate failed) | - | frontx_ind: unsupported parameter type |
| 24 | batchA:371 | `ConLeche.Expr.BeqOutX.cast` | FAIL | gate FAIL: frontx_ind: more than one extra parameter of a declared type | not attempted (gate failed) | - | frontx_ind: more than one extra parameter of a declared type |
| 28 | batchA:537 | `ConLeche.Expr.bvarPool` | FAIL | gate FAIL: frontx_ind: ConLeche.Expr.bvarPool has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.Expr.bvarPool has no argument of a declared type |
| 32 | batchA:591 | `ConLeche.Expr.hasFvar` | PASS | gate ok; arms ok (1 function(s)) | yes | yes: 50 cases, QEMU == Sail == Lean |  |
| 36 | batchA:670 | `ConLeche.Expr.fvarRangeMemo` | PASS | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.fvarRangeMemo.eq_1 has no constructor pattern | no | - | frontx_ind: Prod.fst has no argument of a declared type |
| 40 | batchA:731 | `ConLeche.Expr.abstract1` | FAIL | gate FAIL: frontx_ind: more than one scalar parameter | not attempted (gate failed) | - | frontx_ind: more than one scalar parameter |
| 44 | batchA:796 | `ConLeche.Expr.binderPair?` | FAIL | gate FAIL: frontx_ind: unsupported result type | not attempted (gate failed) | - | frontx_ind: unsupported result type |
| 48 | batchA:826 | `ConLeche.Expr.piResult` | PASS | gate ok; arms ok (1 function(s)) | yes | yes: 50 cases, QEMU == Sail == Lean |  |
| 52 | batchB:42 | `ConLeche.Expr.allLevelParamsDefined` | FAIL | gate FAIL: frontx_ind: unsupported parameter type | not attempted (gate failed) | - | frontx_ind: unsupported parameter type |
| 56 | batchB:143 | `ConLeche.Expr.numArgs` | PASS | gate ok; arms ok (1 function(s)) | yes | yes: 50 cases, QEMU == Sail == Lean |  |
| 60 | batchB:195 | `ConLeche.natName` | FAIL | gate FAIL: frontx_ind: ConLeche.natName has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.natName has no argument of a declared type |
| 64 | batchB:237 | `ConLeche.falseName` | FAIL | gate FAIL: frontx_ind: ConLeche.falseName has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.falseName has no argument of a declared type |
| 68 | batchB:277 | `ConLeche.quotIndName` | FAIL | gate FAIL: frontx_ind: ConLeche.quotIndName has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.quotIndName has no argument of a declared type |
| 72 | batchB:323 | `ConLeche.listName` | FAIL | gate FAIL: frontx_ind: ConLeche.listName has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.listName has no argument of a declared type |
| 76 | batchB:372 | `ConLeche.andName` | FAIL | gate FAIL: frontx_ind: ConLeche.andName has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.andName has no argument of a declared type |
| 80 | batchB:425 | `ConLeche.BasisDSL.type1` | FAIL | gate FAIL: frontx_ind: ConLeche.BasisDSL.type1 has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.BasisDSL.type1 has no argument of a declared type |
| 84 | batchB:479 | `ConLeche.natRecSucc` | FAIL | gate FAIL: frontx_ind: ConLeche.natRecSucc has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.natRecSucc has no argument of a declared type |
| 88 | batchB:544 | `ConLeche.quotIndMotive` | FAIL | gate FAIL: frontx_ind: ConLeche.quotIndMotive has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.quotIndMotive has no argument of a declared type |
| 92 | batchB:616 | `ConLeche.andRecMotive` | FAIL | gate FAIL: frontx_ind: ConLeche.andRecMotive has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.andRecMotive has no argument of a declared type |
| 96 | batchB:696 | `ConLeche.pinLinkOk` | FAIL | gate FAIL: frontx_ind: ConLeche.pinLinkOk has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.pinLinkOk has no argument of a declared type |
| 100 | batchB:777 | `ConLeche.natLitToConstructor` | FAIL | gate FAIL: frontx_ind: ConLeche.natLitToConstructor has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.natLitToConstructor has no argument of a declared type |
| 104 | batchB:844 | `ConLeche.natSubName` | FAIL | gate FAIL: frontx_ind: ConLeche.natSubName has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.natSubName has no argument of a declared type |
| 108 | batchB:876 | `ConLeche.natBleName` | FAIL | gate FAIL: frontx_ind: ConLeche.natBleName has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.natBleName has no argument of a declared type |
| 112 | batchB:908 | `ConLeche.natLandName` | FAIL | gate FAIL: frontx_ind: ConLeche.natLandName has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.natLandName has no argument of a declared type |
| 116 | batchB:940 | `ConLeche.natShiftRightName` | FAIL | gate FAIL: frontx_ind: ConLeche.natShiftRightName has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.natShiftRightName has no argument of a declared type |
| 120 | batchB:979 | `ConLeche.boolTrueName` | FAIL | gate FAIL: frontx_ind: ConLeche.boolTrueName has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.boolTrueName has no argument of a declared type |
| 124 | batchB:1031 | `ConLeche.reservedRecName` | PASS | gate ok; arms FAIL: frontx_ind: equation ConLeche.reservedRecName.eq_1 has no constructor pattern | no | - | frontx_ind: Bool.or has no argument of a declared type |
| 128 | batchB:1146 | `ConLeche.Expr.substConst0` | FAIL | gate FAIL: frontx_ind: more than one extra parameter of a declared type | not attempted (gate failed) | - | frontx_ind: more than one extra parameter of a declared type |
| 132 | batchB:1233 | `ConLeche.etaProjs` | PASS | gate ok; arms FAIL: frontx_ind: equation ConLeche.etaProjs.eq_1 has no constructor pattern | no | - | frontx_ind: unsupported parameter type |
| 136 | batchB:1326 | `ConLeche.teleArityOk` | PASS | gate ok; arms ok (2 function(s)) | yes | no: List Expr input, no encoder in emit helpers |  |
| 140 | batchB:1396 | `ConLeche.Expr.bvarBoundGo` | FAIL | gate FAIL: frontx_ind: unsupported parameter type | not attempted (gate failed) | - | frontx_ind: unsupported parameter type |
| 144 | batchB:1474 | `ConLeche.Expr.stripPis` | FAIL | gate FAIL: frontx_ind: unsupported result type | not attempted (gate failed) | - | frontx_ind: unsupported result type |
| 148 | batchB:1543 | `ConLeche.Expr.isLit` | PASS | gate ok; arms ok (1 function(s)) | yes | yes: 50 cases, QEMU == Sail == Lean |  |
| 152 | batchB:1619 | `ConLeche.propextName` | FAIL | gate FAIL: frontx_ind: ConLeche.propextName has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.propextName has no argument of a declared type |
| 156 | batchB:1663 | `ConLeche.iffRecName` | FAIL | gate FAIL: frontx_ind: ConLeche.iffRecName has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.iffRecName has no argument of a declared type |
| 160 | batchB:1733 | `ConLeche.structPsAt` | FAIL | gate FAIL: frontx_ind: ConLeche.structPsAt has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.structPsAt has no argument of a declared type |
| 164 | batchB:1806 | `ConLeche.Expr.liftLooseBVars` | FAIL | gate FAIL: frontx_ind: more than one scalar parameter | not attempted (gate failed) | - | frontx_ind: more than one scalar parameter |
| 168 | batchB:1921 | `ConLeche.Expr.piBinders` | FAIL | gate FAIL: frontx_ind: unsupported result type | not attempted (gate failed) | - | frontx_ind: unsupported result type |
| 172 | batchB:2099 | `ConLeche.Expr.depth` | PASS | gate ok; arms ok (1 function(s)) | yes | yes: 50 cases, QEMU == Sail == Lean |  |
| 176 | batchB:2165 | `ConLeche.nestKeyMap` | PASS | gate ok; arms FAIL: frontx_ind: equation ConLeche.nestKeyMap.eq_1 has no constructor pattern | no | - | frontx_ind: equation ite.eq_1 has no constructor pattern |
| 180 | batchB:2289 | `ConLeche.reduceBoolDeclPin` | FAIL | gate FAIL: frontx_ind: ConLeche.reduceBoolDeclPin has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.reduceBoolDeclPin has no argument of a declared type |
| 184 | batchB:2366 | `ConLeche.trustCompilerName` | FAIL | gate FAIL: frontx_ind: ConLeche.trustCompilerName has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.trustCompilerName has no argument of a declared type |
| 188 | batchB:2410 | `ConLeche.ofReduceBoolName` | FAIL | gate FAIL: frontx_ind: ConLeche.ofReduceBoolName has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.ofReduceBoolName has no argument of a declared type |
| 192 | batchB:2462 | `ConLeche.reduceCertVar` | PASS | gate ok; arms FAIL: frontx_ind: equation ConLeche.reduceElemTy.eq_1 has no constructor pattern | no | - | frontx_ind: ConLeche.Expr.fvar has no equations |
| 196 | batchB:2532 | `ConLeche.targetPiDomsWith` | FAIL | gate FAIL: frontx_ind: unsupported result type | not attempted (gate failed) | - | frontx_ind: unsupported result type |
| 200 | batchB:2600 | `ConLeche.nestOutKinds` | FAIL | gate FAIL: frontx_ind: ConLeche.nestOutKinds has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.nestOutKinds has no argument of a declared type |
| 204 | batchB:2686 | `ConLeche.divModCertStmts` | FAIL | gate FAIL: frontx_ind: unsupported result type | not attempted (gate failed) | - | frontx_ind: unsupported result type |
| 208 | batchB:2826 | `ConLeche.closeLams` | PASS | gate ok; arms FAIL: frontx_ind: unsupported variable (a dropped field?) | no | - | frontx_ind: unsupported variable (a dropped field?) |
| 212 | batchB:2868 | `ConLeche.ClassGen.slotVar` | FAIL | gate FAIL: frontx_ind: ConLeche.ClassGen.slotVar has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.ClassGen.slotVar has no argument of a declared type |
| 216 | batchB:2910 | `ConLeche.ClassGen.major` | FAIL | gate FAIL: frontx_ind: ConLeche.ClassGen.major has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.ClassGen.major has no argument of a declared type |
| 220 | batchB:2960 | `ConLeche.ClassGen.minorTy` | FAIL | gate FAIL: frontx_ind: ConLeche.ClassGen.minorTy has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.ClassGen.minorTy has no argument of a declared type |
| 224 | batchB:3036 | `ConLeche.classKeyCanon` | FAIL | gate FAIL: frontx_ind: unsupported parameter type | not attempted (gate failed) | - | frontx_ind: unsupported parameter type |
| 228 | batchB:3171 | `ConLeche.Expr.isCompound` | PASS | gate ok; arms ok (1 function(s)) | yes | yes: 50 cases, QEMU == Sail == Lean |  |
| 232 | batchB:3244 | `ConLeche.Expr.mkApp` | PASS | gate ok; arms ok (1 function(s)) | no | - | frontx_ind: ConLeche.Expr.app has no equations |
| 236 | batchB:3275 | `ConLeche.Expr.mkProj` | PASS | gate ok; arms ok (1 function(s)) | no | - | frontx_ind: ConLeche.Expr.proj has no equations |
| 240 | batchB:3334 | `ConLeche.Expr.MemoXP` | FAIL | gate FAIL: frontx_ind: ConLeche.Expr.MemoXP has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.Expr.MemoXP has no argument of a declared type |
| 244 | batchB:3406 | `ConLeche.Expr.liftLooseBVarsC` | FAIL | gate FAIL: frontx_ind: more than one scalar parameter | not attempted (gate failed) | - | frontx_ind: more than one scalar parameter |
| 248 | batchB:3506 | `ConLeche.Expr.instantiateLiftC` | PASS | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.instantiateLiftC.eq_1 has no constructor pattern | no | - | frontx_ind: dite has no argument of a declared type |
| 252 | batchB:3592 | `ConLeche.Expr.instantiate1C` | PASS | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.instantiate1C.eq_1 has no constructor pattern | no | - | frontx_ind: dite has no argument of a declared type |
| 256 | batchB:3691 | `ConLeche.Expr.enterListP` | FAIL | gate FAIL: frontx_ind: unsupported parameter type | not attempted (gate failed) | - | frontx_ind: unsupported parameter type |
| 260 | batchB:3780 | `ConLeche.fvarOfData` | FAIL | gate FAIL: frontx_ind: ConLeche.fvarOfData has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.fvarOfData has no argument of a declared type |
| 264 | batchB:3840 | `ConLeche.Expr.fvarB` | PASS | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.fvarB.eq_1 has no constructor pattern | no | - | frontx_ind: ConLeche.Expr.fvarB is neither recursive nor `g c₁ …` |
| 268 | batchB:3922 | `ConLeche.Expr.abstract1C` | FAIL | gate FAIL: frontx_ind: more than one scalar parameter | not attempted (gate failed) | - | frontx_ind: more than one scalar parameter |
| 272 | batchB:4010 | `ConLeche.Expr.abstractRangeC` | FAIL | gate FAIL: frontx_ind: more than one scalar parameter | not attempted (gate failed) | - | frontx_ind: more than one scalar parameter |
| 276 | batchB:4069 | `ConLeche.Expr.substConstAllXP` | FAIL | gate FAIL: frontx_ind: more than one extra parameter of a declared type | not attempted (gate failed) | - | frontx_ind: more than one extra parameter of a declared type |
| 280 | batchB:4198 | `ConLeche.Expr.resBool` | FAIL | gate FAIL: frontx_ind: ConLeche.Expr.resBool has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.Expr.resBool has no argument of a declared type |
| 284 | batchB:4236 | `ConLeche.Expr.enterWSP` | FAIL | gate FAIL: frontx_ind: unsupported parameter type | not attempted (gate failed) | - | frontx_ind: unsupported parameter type |
| 288 | batchB:4343 | `ConLeche.Expr.enterLBP` | FAIL | gate FAIL: frontx_ind: unsupported parameter type | not attempted (gate failed) | - | frontx_ind: unsupported parameter type |
| 292 | batchB:4473 | `ConLeche.Expr.enterLIP` | FAIL | gate FAIL: frontx_ind: more than one scalar parameter | not attempted (gate failed) | - | frontx_ind: more than one scalar parameter |
| 296 | batchB:4591 | `ConLeche.Expr.MemoB0` | FAIL | gate FAIL: frontx_ind: ConLeche.Expr.MemoB0 has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.Expr.MemoB0 has no argument of a declared type |
| 300 | batchB:4666 | `ConLeche.Expr.nestOccC` | FAIL | gate FAIL: frontx_ind: unsupported parameter type | not attempted (gate failed) | - | frontx_ind: unsupported parameter type |
| 304 | batchB:4761 | `ConLeche.Expr.mentionsAnyConstC` | FAIL | gate FAIL: frontx_ind: unsupported parameter type | not attempted (gate failed) | - | frontx_ind: unsupported parameter type |
| 308 | batchB:4804 | `ConLeche.Expr.MemoN` | FAIL | gate FAIL: frontx_ind: ConLeche.Expr.MemoN has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.Expr.MemoN has no argument of a declared type |
| 312 | batchB:4861 | `ConLeche.Expr.depthC` | PASS | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.depthC.eq_1 has no constructor pattern | no | - | frontx_ind: ConLeche.Expr.resNat has no argument of a declared type |
| 316 | batchB:4959 | `ConLeche.Expr.leavesSubP` | FAIL | gate FAIL: frontx_ind: unsupported parameter type | not attempted (gate failed) | - | frontx_ind: unsupported parameter type |
| 320 | batchB:5075 | `ConLeche.Expr.hasFvar` (same name as #32) | PASS | gate ok; arms ok (1 function(s)) | see #32 | see #32 |  |
| 324 | batchB:5130 | `ConLeche.Expr.piResidualAcc` | FAIL | gate FAIL: frontx_ind: more than one extra parameter of a declared type | not attempted (gate failed) | - | frontx_ind: more than one extra parameter of a declared type |
| 328 | batchB:5190 | `ConLeche.Expr.closeLamsGoC` | FAIL | gate FAIL: frontx_ind: more than one scalar parameter | not attempted (gate failed) | - | frontx_ind: more than one scalar parameter |
| 332 | batchB:5236 | `ConLeche.Expr.targetPiDomsWithC` | FAIL | gate FAIL: frontx_ind: unsupported result type | not attempted (gate failed) | - | frontx_ind: unsupported result type |
| 336 | batchB:5284 | `ConLeche.Expr.allLevelParamsDefinedP` | FAIL | gate FAIL: frontx_ind: unsupported parameter type | not attempted (gate failed) | - | frontx_ind: unsupported parameter type |
| 340 | batchB:5416 | `ConLeche.Cached.sameConstHeadsC` | PASS | gate ok; arms FAIL: frontx_ind: a pattern on another argument (ConLeche.Cached.sameConstHeadsC.eq_1) | no | - | frontx_ind: a pattern on another argument (ConLeche.Cached.sameConstHeadsC.eq_1) |
| 344 | batchB:5470 | `ConLeche.Cached.NatBinOp.ofName?` | FAIL | gate FAIL: frontx_ind: unsupported result type | not attempted (gate failed) | - | frontx_ind: unsupported result type |
| 348 | batchB:5546 | `ConLeche.CheckM` | FAIL | gate FAIL: frontx_ind: ConLeche.CheckM has no argument of a declared type | not attempted (gate failed) | - | frontx_ind: ConLeche.CheckM has no argument of a declared type |
| 352 | batchB:5588 | `ConLeche.Cached.instListM` | FAIL | gate FAIL: frontx_ind: unsupported result type | not attempted (gate failed) | - | frontx_ind: unsupported result type |
| 356 | batchB:5663 | `ConLeche.Cached.whnfCoreKeyC` | PASS | gate ok; arms ok (2 function(s)) | yes | yes: 50 cases, QEMU == Sail == Lean |  |
| 360 | batchB:5732 | `ConLeche.Cached.pushCheapKey` | FAIL | gate FAIL: frontx_ind: more than one scalar parameter | not attempted (gate failed) | - | frontx_ind: more than one scalar parameter |
| 364 | batchB:5786 | `ConLeche.Cached.piDomsOccC` | FAIL | gate FAIL: frontx_ind: unsupported parameter type | not attempted (gate failed) | - | frontx_ind: unsupported parameter type |
| 368 | batchB:5856 | `ConLeche.Expr.replaceFVarsXP` | FAIL | gate FAIL: frontx_ind: unsupported parameter type | not attempted (gate failed) | - | frontx_ind: unsupported parameter type |
| 372 | batchB:5928 | `ConLeche.Expr.piResult` (same name as #48) | PASS | gate ok; arms ok (1 function(s)) | see #48 | see #48 |  |
| 376 | batchB:6015 | `ConLeche.Cached.Expr.dropVarsC` | PASS | gate ok; arms FAIL: frontx_ind: equation ConLeche.Cached.Expr.dropVarsC.eq_1 has no constructor pattern | no | - | frontx_ind: Nat.brecOn has no argument of a declared type |
