# CONLECHE_S3: con-leche functions, number % 4 == 3

Branch `conleche-s3`, from `origin/main` (con-leche `Expr` support, `Riscv/Frontx/ExprExamples.lean`).

## Method

- **Numbering.** The targets of `origin/conleche-batch-a` `Testing/conleche-batches/batchA.md` (27, numbered 1 to 27 in the table) and of `origin/conleche-batch-b` `batchB.md` (230, numbered 1 to 230) are numbered in file order, batch A first: batch B's `n` is number `27 + n`. Selected: numbers 3, 7, ..., 255 (64 functions). Note: batch A is on `origin/conleche-batch-a`, not `conleche-batch-b`.
- **Copies.** Each selected function and its verbatim dependency closure (from the batch files, comments stripped before name matching, first copy kept for duplicated declarations) are in the probe files. Only the two functions that pass are in `Riscv/Frontx/ConLecheS3.lean`.
- **Gate and compile.** Per function, a probe file `import`s `Riscv.Frontx.ExprExamples` and `Riscv.Frontx.IndGate`, then runs `frontx_ind_gate f on TExpr`, `frontx_ind f on TExpr` and `#print axioms f`. Probes were compiled with `lake env lean`, four at a time.
- **Tests.** `Testing/asm/emit_conleche_s3.lean` (modelled on `emit_expr.lean`) emits cases for the two new functions. `frontx_test.py check 50` ran on QEMU and Sail; `Testing/asm/ctest` was deleted after each run. The four existing ExprExamples entries were re-checked with `check 50`.
- **Axioms.** The two compiled functions depend only on `propext`. No `sorry`, no `native_decide`, and no compiler sources were changed.

## Result

- Gate ok and compiled: **2 new** (`classBinder`, `Cached.whnfEasy`). Both pass `check 50` on QEMU, Sail and Lean.
- Gate ok and already compiled: **4** (`Expr.sizeF`, `Expr.getAppFn`, `Expr.fvarTypeD`, `Expr.isLit`), already in `ExprExamples.lean`; their `check 50` tests also pass.
- Other 58: not compiled (reasons below). The dominant causes are constants (`Name` values, no argument, so the gate rejects them), functions whose batch copy is incomplete or broken (`BeqSt.record` excluded from batch A; `.no` and `Squash` in `beqGoX`; `sorry` in the batch text; unresolved identifiers), and features `frontx_ind` does not take.

## Per function

| # | Function | Source | Gate | Compiled | Tests | Error (first) |
|---:|---|---|---|---|---|---|
| 3 | `Expr.fvarBRaw` | `ConLeche.Expr.fvarBRaw` | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.fvarBRaw.eq_1 has no constructor pattern | no | — | `error: frontx_ind: UInt64.toNat has no argument of a declared type` |
| 7 | `Expr.BeqSt.recordEq` | `ConLeche.Expr.BeqSt.recordEq` | gate FAIL: frontx_ind: unsupported parameter type | no | — | `error(lean.invalidField): Invalid field `record`: The environment does not contain `ConLeche.Expr.BeqSt.record`, so it is not possible to project the field `record` from an expression` (copy contains `sorry`) |
| 11 | `Expr.mkBvar` | `ConLeche.Expr.mkBvar` | gate FAIL: frontx_ind: ConLeche.Expr.mkBvar has no argument of a declared type | no | — | `error: frontx_ind: dite has no argument of a declared type` |
| 15 | `Expr.bvarB` | `ConLeche.Expr.bvarB` | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.bvarB.eq_1 has no constructor pattern | no | — | `error(lean.synthInstanceFailed): failed to synthesize instance of type class` (copy contains `sorry`) |
| 19 | `Expr.sizeF` | `ConLeche.Expr.sizeF` | gate ok; arms ok (1 function(s)) | yes (already in ExprExamples; not re-declared) | `expr_sizef` | — |
| 23 | `Expr.getAppFn` | `ConLeche.Expr.getAppFn` | gate ok; arms ok (1 function(s)) | yes (already in ExprExamples; not re-declared) | `expr_getappfn` | — |
| 27 | `Expr.fvarTypeD` | `ConLeche.Expr.fvarTypeD` | gate ok; arms ok (1 function(s)) | yes (already in ExprExamples; not re-declared) | `expr_fvartyped` | — |
| 31 | `Expr.peelPis` | `ConLeche.Expr.peelPis` | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.peelPis.eq_1 has no constructor pattern | no | — | `error: frontx_ind: equation ConLeche.Expr.peelPis.eq_1 has no constructor pattern` |
| 35 | `eqName` | `ConLeche.eqName` | gate FAIL: frontx_ind: ConLeche.eqName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 39 | `natSuccName` | `ConLeche.natSuccName` | gate FAIL: frontx_ind: ConLeche.natSuccName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 43 | `quotMkName` | `ConLeche.quotMkName` | gate FAIL: frontx_ind: ConLeche.quotMkName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 47 | `stringName` | `ConLeche.stringName` | gate FAIL: frontx_ind: ConLeche.stringName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 51 | `listConsName` | `ConLeche.listConsName` | gate FAIL: frontx_ind: ConLeche.listConsName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 55 | `sorryAxName` | `ConLeche.sorryAxName` | gate FAIL: frontx_ind: ConLeche.sorryAxName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 59 | `natT` | `ConLeche.natT` | gate FAIL: frontx_ind: ConLeche.natT has no argument of a declared type | no | — | `error(lean.unknownIdentifier): Unknown identifier `cnst`` (copy contains `sorry`) |
| 63 | `quotLiftF` | `ConLeche.quotLiftF` | gate FAIL: frontx_ind: ConLeche.quotLiftF has no argument of a declared type | no | — | `error(lean.unknownIdentifier): Unknown identifier `pi`` (copy contains `sorry`) |
| 67 | `andIntroName` | `ConLeche.andIntroName` | gate FAIL: frontx_ind: ConLeche.andIntroName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 71 | `canonNameMap` | `ConLeche.canonNameMap` | gate FAIL: frontx_ind: unsupported parameter type | no | — | `error: frontx_ind: ConLeche.canonNameMap.match_1 has no equations` |
| 75 | `natLitToConstructor` | `ConLeche.natLitToConstructor` | gate FAIL: frontx_ind: ConLeche.natLitToConstructor has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.natLitToConstructor.match_1 has no equations` |
| 79 | `natSubName` | `ConLeche.natSubName` | gate FAIL: frontx_ind: ConLeche.natSubName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 83 | `natBleName` | `ConLeche.natBleName` | gate FAIL: frontx_ind: ConLeche.natBleName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 87 | `natLandName` | `ConLeche.natLandName` | gate FAIL: frontx_ind: ConLeche.natLandName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 91 | `natShiftRightName` | `ConLeche.natShiftRightName` | gate FAIL: frontx_ind: ConLeche.natShiftRightName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 95 | `boolTrueName` | `ConLeche.boolTrueName` | gate FAIL: frontx_ind: ConLeche.boolTrueName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 99 | `reservedRecName` | `ConLeche.reservedRecName` | gate ok; arms FAIL: frontx_ind: equation ConLeche.reservedRecName.eq_1 has no constructor pattern | no | — | `error(lean.unknownIdentifier): Unknown identifier `litGuardNames.contains`` (copy contains `sorry`) |
| 103 | `Expr.substConst0` | `ConLeche.Expr.substConst0` | gate FAIL: frontx_ind: more than one extra parameter of a declared type | no | — | `error: frontx_ind: more than one extra parameter of a declared type` |
| 107 | `unitFieldTele` | `ConLeche.unitFieldTele` | gate ok; arms FAIL: frontx_ind: equation ConLeche.unitFieldTele.eq_1 has no constructor pattern | no | — | `error: frontx_ind: unsupported parameter type` |
| 111 | `Expr.hasLooseBVarB` | `ConLeche.Expr.hasLooseBVarB` | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.bvarB.eq_1 has no constructor pattern | no | — | `error(lean.synthInstanceFailed): failed to synthesize instance of type class` (copy contains `sorry`) |
| 115 | `Expr.isLit` | `ConLeche.Expr.isLit` | gate ok; arms ok (1 function(s)) | yes (already in ExprExamples; not re-declared) | `expr_islit` | — |
| 119 | `propextName` | `ConLeche.propextName` | gate FAIL: frontx_ind: ConLeche.propextName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 123 | `iffRecName` | `ConLeche.iffRecName` | gate FAIL: frontx_ind: ConLeche.iffRecName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 127 | `structPsAt` | `ConLeche.structPsAt` | gate FAIL: frontx_ind: ConLeche.structPsAt has no argument of a declared type | no | — | `error: frontx_ind: unsupported parameter type` |
| 131 | `structProjBodiesGo` | `ConLeche.structProjBodiesGo` | gate FAIL: frontx_ind: more than one extra parameter of a declared type | no | — | `error: frontx_ind: more than one extra parameter of a declared type` |
| 135 | `Expr.nestOcc` | `ConLeche.Expr.nestOcc` | gate FAIL: frontx_ind: unsupported parameter type | no | — | `error: frontx_ind: unsupported parameter type` |
| 139 | `nestPhs` | `ConLeche.nestPhs` | gate FAIL: frontx_ind: ConLeche.nestPhs has no argument of a declared type | no | — | `error: frontx_ind: unsupported parameter type` |
| 143 | `recTargetOf` | `ConLeche.recTargetOf` | gate FAIL: frontx_ind: unsupported parameter type | no | — | `error: frontx_ind: ConLeche.recTargetOf.match_1 has no equations` |
| 147 | `trueIntroName` | `ConLeche.trueIntroName` | gate FAIL: frontx_ind: ConLeche.trueIntroName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 151 | `ofReduceNatName` | `ConLeche.ofReduceNatName` | gate FAIL: frontx_ind: ConLeche.ofReduceNatName has no argument of a declared type | no | — | `error: frontx_ind: ConLeche.Name.str has no equations` |
| 155 | `reduceDeclPin` | `ConLeche.reduceDeclPin` | gate ok; arms FAIL: frontx_ind: equation ConLeche.reduceDeclPin.eq_1 has no constructor pattern | no | — | `error(lean.unknownIdentifier): Unknown identifier `lm`` |
| 159 | `targetCanonParams` | `ConLeche.targetCanonParams` | gate ok; arms FAIL: frontx_ind: equation ConLeche.targetCanonParams.eq_1 has no constructor pattern | no | — | `error(lean.invalidField): Invalid field `replaceFVars`: The environment does not contain `ConLeche.Expr.replaceFVars`, so it is not possible to project the field `replaceFVars` from an expression` (copy contains `sorry`) |
| 163 | `nestOutKinds` | `ConLeche.nestOutKinds` | gate FAIL: frontx_ind: ConLeche.nestOutKinds has no argument of a declared type | no | — | `error: frontx_ind: unsupported parameter type` |
| 167 | `divModCertStmts` | `ConLeche.divModCertStmts` | gate FAIL: frontx_ind: unsupported result type | no | — | `error: frontx_ind: ConLeche.divModCertStmts is neither recursive nor `g c₁ …`` |
| 171 | `classBinder` | `ConLeche.classBinder` | gate ok; arms ok (2 function(s)) | yes | `s3_classbinder` | — |
| 175 | `ClassGen.major` | `ConLeche.ClassGen.major` | gate FAIL: frontx_ind: more than one scalar parameter | no | — | `error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression` (copy contains `sorry`) |
| 179 | `ClassGen.prefixBinders` | `ConLeche.ClassGen.prefixBinders` | gate FAIL: frontx_ind: unsupported result type | no | — | `error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression` (copy contains `sorry`) |
| 183 | `Expr.dropVars` | `ConLeche.Expr.dropVars` | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.dropVars.eq_1 has no constructor pattern | no | — | `error: frontx_ind: Nat.brecOn has no argument of a declared type` |
| 187 | `Expr.liftLooseBVarsP` | `ConLeche.Expr.liftLooseBVarsP` | gate FAIL: frontx_ind: more than one scalar parameter | no | — | `error(lean.synthInstanceFailed): failed to synthesize instance of type class` (copy contains `sorry`) |
| 191 | `Expr.instantiate1C` | `ConLeche.Expr.instantiate1C` | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.instantiate1C.eq_1 has no constructor pattern | no | — | `error(lean.synthInstanceFailed): failed to synthesize instance of type class` (copy contains `sorry`) |
| 195 | `Expr.abstractRangeP` | `ConLeche.Expr.abstractRangeP` | gate FAIL: frontx_ind: more than one scalar parameter | no | — | `error(lean.synthInstanceFailed): failed to synthesize instance of type class` (copy contains `sorry`) |
| 199 | `Expr.wscopedBP` | `ConLeche.Expr.wscopedBP` | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.fvarB.eq_1 has no constructor pattern | no | — | `error(lean.synthInstanceFailed): failed to synthesize instance of type class` (copy contains `sorry`) |
| 203 | `Expr.hasLooseBVarInP` | `ConLeche.Expr.hasLooseBVarInP` | gate FAIL: frontx_ind: more than one scalar parameter | no | — | `error(lean.synthInstanceFailed): failed to synthesize instance of type class` (copy contains `sorry`) |
| 207 | `Expr.mentionsAnyConstP` | `ConLeche.Expr.mentionsAnyConstP` | gate FAIL: frontx_ind: unsupported parameter type | no | — | `error: frontx_ind: unsupported parameter type` |
| 211 | `Expr.fvarLeavesC` | `ConLeche.Expr.fvarLeavesC` | gate FAIL: frontx_ind: unsupported result type | no | — | `error(lean.synthInstanceFailed): failed to synthesize instance of type class` (copy contains `sorry`) |
| 215 | `Expr.leafGuard` | `ConLeche.Expr.leafGuard` | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.leafGuard.eq_1 has no constructor pattern | no | — | `error(lean.synthInstanceFailed): failed to synthesize instance of type class` (copy contains `sorry`) |
| 219 | `Expr.piResidual` | `ConLeche.Expr.piResidual` | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.piResidual.eq_1 has no constructor pattern | no | — | `error(lean.synthInstanceFailed): failed to synthesize instance of type class` (copy contains `sorry`) |
| 223 | `Expr.closeLamsC` | `ConLeche.Expr.closeLamsC` | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.closeLamsC.eq_1 has no constructor pattern | no | — | `error(lean.synthInstanceFailed): failed to synthesize instance of type class` (copy contains `sorry`) |
| 227 | `Expr.piDomsMentionAnyC` | `ConLeche.Expr.piDomsMentionAnyC` | gate FAIL: frontx_ind: unsupported parameter type | no | — | `error: Tactic `rewrite` failed: Did not find an occurrence of the pattern` |
| 231 | `Cached.rawNatLitC?` | `ConLeche.Cached.rawNatLitC?` | gate FAIL: frontx_ind: unsupported result type | no | — | `error: frontx_ind: unsupported result type` |
| 235 | `Cached.NatBinOp.result` | `ConLeche.Cached.NatBinOp.result` | gate FAIL: frontx_ind: more than one scalar parameter | no | — | `error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.add`` (copy contains `sorry`) |
| 239 | `Cached.iotaNumArgs` | `ConLeche.Cached.iotaNumArgs` | gate ok; arms ok (1 function(s)) | no | — | `error: frontx_ind: a scalar parameter needs an entry `f xs = ConLeche.Cached.iotaNumArgs n xs`` |
| 243 | `Cached.whnfCoreStoresDone` | `ConLeche.Cached.whnfCoreStoresDone` | gate ok; arms FAIL: frontx_ind: unsupported term | no | — | `error(lean.synthInstanceFailed): failed to synthesize instance of type class` (copy contains `sorry`) |
| 247 | `Cached.whnfEasy` | `ConLeche.Cached.whnfEasy` | gate ok; arms ok (1 function(s)) | yes | `s3_whnfeasy` | — |
| 251 | `Cached.classGenRecTyC` | `ConLeche.Cached.classGenRecTyC` | gate ok; arms FAIL: frontx_ind: equation ConLeche.Cached.classGenRecTyC.eq_1 has no constructor pattern | no | — | `error(lean.synthInstanceFailed): failed to synthesize instance of type class` (copy contains `sorry`) |
| 255 | `Cached.classKeyCanonC` | `ConLeche.Cached.classKeyCanonC` | gate ok; arms FAIL: frontx_ind: equation ConLeche.Cached.classKeyCanonC.eq_1 has no constructor pattern | no | — | `error(lean.synthInstanceFailed): failed to synthesize instance of type class` (copy contains `sorry`) |

`Expr.dropVars` (183) and `Expr.fvarBRaw` (3) pass the gate and fail on arm translation or on `UInt64.toNat`. The batch copies were never compiled ("Not compiled" in the batch notes), so these errors come from the copies, not from `frontx_ind`'s limits alone.

## Files

- `Riscv/Frontx/ConLecheS3.lean`: the two compiled functions (verbatim) and the gate/`frontx_ind` commands, plus gate lines for the four existing functions.
- `Testing/asm/emit_conleche_s3.lean`, `Testing/asm/frontx-words/s3_classbinder.*`, `Testing/asm/frontx-words/s3_whnfeasy.*`.
