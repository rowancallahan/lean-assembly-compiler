# Nano/V2Self reorganization proposal (O)

Status: DONE (2a02149; cleanup 5024388, 4d17b0a). The mapping below uses the names from BEFORE the move. Basis: the dead-code audit in `NANO_V2_DEADCODE.md` and its import
closure from `Nano/Main/REVIEW.lean`.

## Target layout

```
Nano/V2Self/
  Prelude.lean                 buffers / prims of the self-language (unchanged)
  C/                           THE COMPILER (Base, Lex2, Par1, Own, Gen): unchanged paths; self_S.lean, B1 and the
                               certificate are generated from these files
  Proof/
    Lex/      the lexer spec (Lex2Spec), its soundness (Lex2Sound), token well-formedness
    Parser/   ParSpec (reference grammar), ParRun* (Layer 2), ParInv* (Layer 3, Par1 ↔ ParRun), width cap, parsed bounds
    Own/      OwnSpec, OwnWF, OwnP0–30, OwnStage
    Gen/      Gen's code / width relations on success (GenRef, GenTop, GenWidth, GenAll), Fixup, BufL, DBNode
    Machine/  the J machine, the templates, the node / def / program theorems, the Sail lift (SimW…), the start code,
              the capacity / OOM exits, the host lift (HostMain, GenImpl, GenMain)
    Bridge/   Sem ⇐ E's semantics (MainBridge*), the converse (MainConv*), the kind typing (MainTy), MainOk, SemX
    Cert/     the generated meaning certificate (unchanged)
    SrcLink/  SrcLink.lean plus the generated Src/* chunks (C's text lexes and parses to Cert.PC.all)
    Main/     Main (Sem, ImplementsC, the stage props), MainTop (compileC, CompileCorrectL), the final theorem, SelfC
  REVIEW.lean
```

The rules are by prefix, so every live module has exactly one place. The full mapping is below; it was generated from
the closure, all 369 modules are mapped, and none is unassigned.

## Deletions (after the owner agrees; all are outside REVIEW's closure or have no reachable declaration)

1. **F's abandoned certificate:** `Proof/MainCert`, `MainCertC0`–`C9`, `MainCertRules`, `MainPure` (about 2,870 lines).
   `Proof/Cert` supersedes it, and nothing imports it. C3–C5 do not even build.
2. **The old compiler chain:** `Nano/V2Self/{Asm,Bridge,Driver,Expand,Inl,Lex,Parse}.lean` and
   `Nano/V2Self/C/{Asm,Expand,Inl,Lex,Main,Par0,Parse}.lean` (about 1,440 lines). Only Testing scripts use them:
   `diff_test`, `chain_test`, `native_ref`, `sizes`, `cg_par`, `cg_chain`, `cg_witness`, `stage_dump`. Either delete
   them together with those scripts, or move all of it to `Nano/V2Self/Legacy/` (owner's choice).
3. **Superseded proof modules:** `ParInvGlue` (`h_core`; ParInvRun proves the step without it), `ParLet` (Astra-11
   parser probe), `MainConvX1` (31 lemmas, none reachable; imported only by MainConvX2), and `StartAll` (`start_run`,
   superseded by StartAllS's `start_runX`; it needs its two importers re-pointed first), and `Cert/Fun.lean`
   (`g56_fun`, unused since G's generic `den_unfold`). `GenRef.g35_fun` in GenTop is still reachable through Gen's
   proofs, so it stays. Mark each [check] before deleting. Not dead: `RunsShift` (E's new, in-progress statement for
   D).
4. **The 310 unreachable declarations** in live modules (list in NANO_V2_DEADCODE.md §4). The large groups are in
   `ParInv` (31), `Templates` (26), `ParRunArgs` (12), `ExprEV` (11), `Call` (9) and `GenRef` (8). Delete them per
   module, with one build per module.
5. **Keep as tests:** `OwnNV` and `MainWitness` are non-vacuity proofs, not dead code. Move them to
   `Proof/Main/NonVacuity/`, or to Testing as `#guard` files.

## Merges of duplicates

- **The final theorem chain:** `MainTop.C_correctL (HB HG)` → `MainTopE.C_correctLE (HB HDB)` →
  `DBStageE.C_correctLC (HB HC)` → `ParCapBnd.C_correctLO` (no premises). Keep one final `NanoMain.C_correct` in
  `Main/Final.lean` (= C_correctLO), with the stage lemmas `parStage`, `ownStage`, `genStage`, `bndStage`, `capStage`,
  `dbStage` beside it. Delete the intermediate `C_correctL*` names or mark them `private`. REVIEW and SelfLink then cite
  one name.
- **Lex2Spec / Lex2Sound:** these are proof and spec files living in `C/`, which holds compiler source. Move them to
  `Proof/Lex/`. build_self_S.py concatenates only Base, Lex2, Par1, Own and Gen, so the move does not affect the
  self-compilation.
- **Call / CallA:** `CallA` has the A-variants of `Call`'s prologue and call lemmas with the real capacity jumps, and
  9 of `Call`'s declarations are unreachable. Merge them into one `Machine/Call.lean` that keeps only the variants
  in use.
- **NdTop / NdTop2, StartAll / StartAllS, GenRun / GenRunS, EVX* / EVS*:** the later safe-run (`S`) versions superseded
  the earlier ones. After the dead-declaration pass, fold whatever of the old file survives into the new one.
- **MainBridge2–15 and OwnP0–30:** these are numbered because of the 5 min / 8 GB per-module limit. Keep the numbering,
  and give each directory a `README` comment in its first file listing what each number holds.

## How to move (mechanical)

1. `git mv` each file per the table below. Namespaces do not change; only module paths do.
2. Rewrite every `import Nano.V2Self.Proof.X` line repo-wide with a sed script generated from the same table:
   `Nano/`, `Testing/` scripts, `REVIEW.lean` and `Testing/scripts/deadcode.lean`.
3. Update the generators that print import lines:
   - `Testing/nano/v2self/cert/gen_cert.py`: the Cert paths stay. Since G's generic `den_unfold` (728a92b) it has no
     FUNEQ table, so there is nothing else to change.
   - `Testing/nano/v2self/srclink/gen.lean` prints `Nano.V2Self.Proof.Src.*` and imports `Proof.ParSpec`. Either
     change it to `Proof.SrcLink.*`, or keep the subfolder name `Src` under `SrcLink/` to leave the generator alone.
4. `lakefile.toml` needs no change (the `Nano` lib glob is `Nano.+`).
5. Rebuild REVIEW plus every moved module, then rerun `Testing/scripts/deadcode.sh`; it should give the same counts.

**Fit for the sprint:** the move itself (steps 1–5) is mechanical and scriptable in one commit, but it touches about
370 files and every agent's working tree. It needs a freeze window in which nobody else edits Nano/V2Self, and one
full rebuild. It is NOT good as several parallel sprint units, because of merge conflicts on the import lines. Better
as one unit run by one agent, after the deletions above. The deletions and merges each need a build and a judgement
call per module, so they fit as separate small units, one per module group.

## Mapping (every module in REVIEW's closure)

### Lex (4)

| now | new |
|---|---|
| `Nano.V2Self.C.Lex2Sound` | `Nano.Lexer.Lex2Sound` |
| `Nano.V2Self.C.Lex2Spec` | `Nano.Lexer.Lex2Spec` |
| `Nano.V2Self.Proof.MainTokWF` | `Nano.Lexer.MainTokWF` |
| `Nano.V2Self.Proof.ParTokWF` | `Nano.Lexer.ParTokWF` |

### Parser (89)

| now | new |
|---|---|
| `Nano.V2Self.Proof.DBPar` | `Nano.Parser.DBPar` |
| `Nano.V2Self.Proof.MainTyP` | `Nano.Parser.MainTyP` |
| `Nano.V2Self.Proof.ParCapBnd` | `Nano.Parser.ParCapBnd` |
| `Nano.V2Self.Proof.ParInv` | `Nano.Parser.ParInv` |
| `Nano.V2Self.Proof.ParInvApi` | `Nano.Parser.ParInvApi` |
| `Nano.V2Self.Proof.ParInvAppend` | `Nano.Parser.ParInvAppend` |
| `Nano.V2Self.Proof.ParInvArg` | `Nano.Parser.ParInvArg` |
| `Nano.V2Self.Proof.ParInvArgName` | `Nano.Parser.ParInvArgName` |
| `Nano.V2Self.Proof.ParInvArm` | `Nano.Parser.ParInvArm` |
| `Nano.V2Self.Proof.ParInvAssign` | `Nano.Parser.ParInvAssign` |
| `Nano.V2Self.Proof.ParInvAtom` | `Nano.Parser.ParInvAtom` |
| `Nano.V2Self.Proof.ParInvBind` | `Nano.Parser.ParInvBind` |
| `Nano.V2Self.Proof.ParInvBuild` | `Nano.Parser.ParInvBuild` |
| `Nano.V2Self.Proof.ParInvCall` | `Nano.Parser.ParInvCall` |
| `Nano.V2Self.Proof.ParInvClose` | `Nano.Parser.ParInvClose` |
| `Nano.V2Self.Proof.ParInvDefs` | `Nano.Parser.ParInvDefs` |
| `Nano.V2Self.Proof.ParInvExpr` | `Nano.Parser.ParInvExpr` |
| `Nano.V2Self.Proof.ParInvExpr2` | `Nano.Parser.ParInvExpr2` |
| `Nano.V2Self.Proof.ParInvFin` | `Nano.Parser.ParInvFin` |
| `Nano.V2Self.Proof.ParInvFinish` | `Nano.Parser.ParInvFinish` |
| `Nano.V2Self.Proof.ParInvFlatM` | `Nano.Parser.ParInvFlatM` |
| `Nano.V2Self.Proof.ParInvGroup` | `Nano.Parser.ParInvGroup` |
| `Nano.V2Self.Proof.ParInvHdr` | `Nano.Parser.ParInvHdr` |
| `Nano.V2Self.Proof.ParInvInit` | `Nano.Parser.ParInvInit` |
| `Nano.V2Self.Proof.ParInvIntern` | `Nano.Parser.ParInvIntern` |
| `Nano.V2Self.Proof.ParInvIte` | `Nano.Parser.ParInvIte` |
| `Nano.V2Self.Proof.ParInvLet` | `Nano.Parser.ParInvLet` |
| `Nano.V2Self.Proof.ParInvLetEnd` | `Nano.Parser.ParInvLetEnd` |
| `Nano.V2Self.Proof.ParInvLetPair` | `Nano.Parser.ParInvLetPair` |
| `Nano.V2Self.Proof.ParInvLetSemi` | `Nano.Parser.ParInvLetSemi` |
| `Nano.V2Self.Proof.ParInvMkPair` | `Nano.Parser.ParInvMkPair` |
| `Nano.V2Self.Proof.ParInvName` | `Nano.Parser.ParInvName` |
| `Nano.V2Self.Proof.ParInvNum` | `Nano.Parser.ParInvNum` |
| `Nano.V2Self.Proof.ParInvOps` | `Nano.Parser.ParInvOps` |
| `Nano.V2Self.Proof.ParInvPair` | `Nano.Parser.ParInvPair` |
| `Nano.V2Self.Proof.ParInvPrev` | `Nano.Parser.ParInvPrev` |
| `Nano.V2Self.Proof.ParInvPrim` | `Nano.Parser.ParInvPrim` |
| `Nano.V2Self.Proof.ParInvPrimary` | `Nano.Parser.ParInvPrimary` |
| `Nano.V2Self.Proof.ParInvRep` | `Nano.Parser.ParInvRep` |
| `Nano.V2Self.Proof.ParInvRun` | `Nano.Parser.ParInvRun` |
| `Nano.V2Self.Proof.ParInvSelf` | `Nano.Parser.ParInvSelf` |
| `Nano.V2Self.Proof.ParInvShP` | `Nano.Parser.ParInvShP` |
| `Nano.V2Self.Proof.ParInvState` | `Nano.Parser.ParInvState` |
| `Nano.V2Self.Proof.ParInvStep` | `Nano.Parser.ParInvStep` |
| `Nano.V2Self.Proof.ParInvTop` | `Nano.Parser.ParInvTop` |
| `Nano.V2Self.Proof.ParInvTy` | `Nano.Parser.ParInvTy` |
| `Nano.V2Self.Proof.ParInvVal` | `Nano.Parser.ParInvVal` |
| `Nano.V2Self.Proof.ParInvValRep` | `Nano.Parser.ParInvValRep` |
| `Nano.V2Self.Proof.ParRep` | `Nano.Parser.ParRep` |
| `Nano.V2Self.Proof.ParRun` | `Nano.Parser.ParRun` |
| `Nano.V2Self.Proof.ParRunArena` | `Nano.Parser.ParRunArena` |
| `Nano.V2Self.Proof.ParRunArgs` | `Nano.Parser.ParRunArgs` |
| `Nano.V2Self.Proof.ParRunAtom` | `Nano.Parser.ParRunAtom` |
| `Nano.V2Self.Proof.ParRunBnd` | `Nano.Parser.ParRunBnd` |
| `Nano.V2Self.Proof.ParRunBody` | `Nano.Parser.ParRunBody` |
| `Nano.V2Self.Proof.ParRunCInv` | `Nano.Parser.ParRunCInv` |
| `Nano.V2Self.Proof.ParRunCall` | `Nano.Parser.ParRunCall` |
| `Nano.V2Self.Proof.ParRunCallSpec` | `Nano.Parser.ParRunCallSpec` |
| `Nano.V2Self.Proof.ParRunDef` | `Nano.Parser.ParRunDef` |
| `Nano.V2Self.Proof.ParRunDefs` | `Nano.Parser.ParRunDefs` |
| `Nano.V2Self.Proof.ParRunExpr` | `Nano.Parser.ParRunExpr` |
| `Nano.V2Self.Proof.ParRunExprInv` | `Nano.Parser.ParRunExprInv` |
| `Nano.V2Self.Proof.ParRunExprMain` | `Nano.Parser.ParRunExprMain` |
| `Nano.V2Self.Proof.ParRunFlat` | `Nano.Parser.ParRunFlat` |
| `Nano.V2Self.Proof.ParRunHCall` | `Nano.Parser.ParRunHCall` |
| `Nano.V2Self.Proof.ParRunHdr` | `Nano.Parser.ParRunHdr` |
| `Nano.V2Self.Proof.ParRunLoop` | `Nano.Parser.ParRunLoop` |
| `Nano.V2Self.Proof.ParRunNames` | `Nano.Parser.ParRunNames` |
| `Nano.V2Self.Proof.ParRunObl` | `Nano.Parser.ParRunObl` |
| `Nano.V2Self.Proof.ParRunPrim` | `Nano.Parser.ParRunPrim` |
| `Nano.V2Self.Proof.ParRunPrimS` | `Nano.Parser.ParRunPrimS` |
| `Nano.V2Self.Proof.ParRunProg` | `Nano.Parser.ParRunProg` |
| `Nano.V2Self.Proof.ParRunRow` | `Nano.Parser.ParRunRow` |
| `Nano.V2Self.Proof.ParRunSelf` | `Nano.Parser.ParRunSelf` |
| `Nano.V2Self.Proof.ParRunShape` | `Nano.Parser.ParRunShape` |
| `Nano.V2Self.Proof.ParRunSmall` | `Nano.Parser.ParRunSmall` |
| `Nano.V2Self.Proof.ParRunStar` | `Nano.Parser.ParRunStar` |
| `Nano.V2Self.Proof.ParRunTup` | `Nano.Parser.ParRunTup` |
| `Nano.V2Self.Proof.ParRunTy` | `Nano.Parser.ParRunTy` |
| `Nano.V2Self.Proof.ParRunWF` | `Nano.Parser.ParRunWF` |
| `Nano.V2Self.Proof.ParRunWFFr` | `Nano.Parser.ParRunWFFr` |
| `Nano.V2Self.Proof.ParRunWFInv` | `Nano.Parser.ParRunWFInv` |
| `Nano.V2Self.Proof.ParRunWFPres` | `Nano.Parser.ParRunWFPres` |
| `Nano.V2Self.Proof.ParRunWFStep` | `Nano.Parser.ParRunWFStep` |
| `Nano.V2Self.Proof.ParSerLen` | `Nano.Parser.ParSerLen` |
| `Nano.V2Self.Proof.ParSpec` | `Nano.Parser.ParSpec` |
| `Nano.V2Self.Proof.ParSpecLen` | `Nano.Parser.ParSpecLen` |
| `Nano.V2Self.Proof.ParSpecTail` | `Nano.Parser.ParSpecTail` |
| `Nano.V2Self.Proof.ParTreeOK` | `Nano.Parser.ParTreeOK` |

### Own (35)

| now | new |
|---|---|
| `Nano.V2Self.Proof.MainKeep` | `Nano.Ownership.MainKeep` |
| `Nano.V2Self.Proof.OwnP0` | `Nano.Ownership.OwnP0` |
| `Nano.V2Self.Proof.OwnP1` | `Nano.Ownership.OwnP1` |
| `Nano.V2Self.Proof.OwnP10` | `Nano.Ownership.OwnP10` |
| `Nano.V2Self.Proof.OwnP11` | `Nano.Ownership.OwnP11` |
| `Nano.V2Self.Proof.OwnP12` | `Nano.Ownership.OwnP12` |
| `Nano.V2Self.Proof.OwnP13` | `Nano.Ownership.OwnP13` |
| `Nano.V2Self.Proof.OwnP14` | `Nano.Ownership.OwnP14` |
| `Nano.V2Self.Proof.OwnP15` | `Nano.Ownership.OwnP15` |
| `Nano.V2Self.Proof.OwnP16` | `Nano.Ownership.OwnP16` |
| `Nano.V2Self.Proof.OwnP17` | `Nano.Ownership.OwnP17` |
| `Nano.V2Self.Proof.OwnP18` | `Nano.Ownership.OwnP18` |
| `Nano.V2Self.Proof.OwnP19` | `Nano.Ownership.OwnP19` |
| `Nano.V2Self.Proof.OwnP2` | `Nano.Ownership.OwnP2` |
| `Nano.V2Self.Proof.OwnP20` | `Nano.Ownership.OwnP20` |
| `Nano.V2Self.Proof.OwnP21` | `Nano.Ownership.OwnP21` |
| `Nano.V2Self.Proof.OwnP22` | `Nano.Ownership.OwnP22` |
| `Nano.V2Self.Proof.OwnP23` | `Nano.Ownership.OwnP23` |
| `Nano.V2Self.Proof.OwnP24` | `Nano.Ownership.OwnP24` |
| `Nano.V2Self.Proof.OwnP25` | `Nano.Ownership.OwnP25` |
| `Nano.V2Self.Proof.OwnP26` | `Nano.Ownership.OwnP26` |
| `Nano.V2Self.Proof.OwnP27` | `Nano.Ownership.OwnP27` |
| `Nano.V2Self.Proof.OwnP28` | `Nano.Ownership.OwnP28` |
| `Nano.V2Self.Proof.OwnP29` | `Nano.Ownership.OwnP29` |
| `Nano.V2Self.Proof.OwnP3` | `Nano.Ownership.OwnP3` |
| `Nano.V2Self.Proof.OwnP30` | `Nano.Ownership.OwnP30` |
| `Nano.V2Self.Proof.OwnP4` | `Nano.Ownership.OwnP4` |
| `Nano.V2Self.Proof.OwnP5` | `Nano.Ownership.OwnP5` |
| `Nano.V2Self.Proof.OwnP6` | `Nano.Ownership.OwnP6` |
| `Nano.V2Self.Proof.OwnP7` | `Nano.Ownership.OwnP7` |
| `Nano.V2Self.Proof.OwnP8` | `Nano.Ownership.OwnP8` |
| `Nano.V2Self.Proof.OwnP9` | `Nano.Ownership.OwnP9` |
| `Nano.V2Self.Proof.OwnSpec` | `Nano.Ownership.OwnSpec` |
| `Nano.V2Self.Proof.OwnStage` | `Nano.Ownership.OwnStage` |
| `Nano.V2Self.Proof.OwnWF` | `Nano.Ownership.OwnWF` |

### Gen (7)

| now | new |
|---|---|
| `Nano.V2Self.Proof.BufL` | `Nano.Codegen.BufL` |
| `Nano.V2Self.Proof.DBNode` | `Nano.Codegen.DBNode` |
| `Nano.V2Self.Proof.Fixup` | `Nano.Codegen.Fixup` |
| `Nano.V2Self.Proof.GenAll` | `Nano.Codegen.GenAll` |
| `Nano.V2Self.Proof.GenRef` | `Nano.Codegen.GenRef` |
| `Nano.V2Self.Proof.GenTop` | `Nano.Codegen.GenTop` |
| `Nano.V2Self.Proof.GenWidth` | `Nano.Codegen.GenWidth` |

### Machine (66)

| now | new |
|---|---|
| `Nano.SelfHost.Bridge` | `Nano.Run.Bridge` |
| `Nano.V2Self.Proof.Call` | `Nano.Run.Call` |
| `Nano.V2Self.Proof.CallA` | `Nano.Run.CallA` |
| `Nano.V2Self.Proof.CallExact` | `Nano.Run.CallExact` |
| `Nano.V2Self.Proof.CapHost` | `Nano.Run.CapHost` |
| `Nano.V2Self.Proof.CapNode` | `Nano.Run.CapNode` |
| `Nano.V2Self.Proof.CapProg` | `Nano.Run.CapProg` |
| `Nano.V2Self.Proof.CapRun` | `Nano.Run.CapRun` |
| `Nano.V2Self.Proof.CapStart` | `Nano.Run.CapStart` |
| `Nano.V2Self.Proof.EVSCall` | `Nano.Run.EVSCall` |
| `Nano.V2Self.Proof.EVSComp` | `Nano.Run.EVSComp` |
| `Nano.V2Self.Proof.EVSDefs` | `Nano.Run.EVSDefs` |
| `Nano.V2Self.Proof.EVSFin` | `Nano.Run.EVSFin` |
| `Nano.V2Self.Proof.EVSLeaf` | `Nano.Run.EVSLeaf` |
| `Nano.V2Self.Proof.EVSLoop` | `Nano.Run.EVSLoop` |
| `Nano.V2Self.Proof.EVSProg` | `Nano.Run.EVSProg` |
| `Nano.V2Self.Proof.EVSRun` | `Nano.Run.EVSRun` |
| `Nano.V2Self.Proof.EVSTail` | `Nano.Run.EVSTail` |
| `Nano.V2Self.Proof.EVX` | `Nano.Run.EVX` |
| `Nano.V2Self.Proof.EVXC` | `Nano.Run.EVXC` |
| `Nano.V2Self.Proof.EVXF` | `Nano.Run.EVXF` |
| `Nano.V2Self.Proof.EVXL` | `Nano.Run.EVXL` |
| `Nano.V2Self.Proof.EVXP` | `Nano.Run.EVXP` |
| `Nano.V2Self.Proof.EVXT` | `Nano.Run.EVXT` |
| `Nano.V2Self.Proof.Expr` | `Nano.Run.Expr` |
| `Nano.V2Self.Proof.ExprBridge` | `Nano.Run.ExprBridge` |
| `Nano.V2Self.Proof.ExprEV` | `Nano.Run.ExprEV` |
| `Nano.V2Self.Proof.ExprExact` | `Nano.Run.ExprExact` |
| `Nano.V2Self.Proof.GenImpl` | `Nano.Run.GenImpl` |
| `Nano.V2Self.Proof.GenMain` | `Nano.Run.GenMain` |
| `Nano.V2Self.Proof.GenRun` | `Nano.Run.GenRun` |
| `Nano.V2Self.Proof.GenRunS` | `Nano.Run.GenRunS` |
| `Nano.V2Self.Proof.Heap` | `Nano.Run.Heap` |
| `Nano.V2Self.Proof.HeapEV` | `Nano.Run.HeapEV` |
| `Nano.V2Self.Proof.HostLift` | `Nano.Run.HostLift` |
| `Nano.V2Self.Proof.HostMain` | `Nano.Run.HostMain` |
| `Nano.V2Self.Proof.HostTiny` | `Nano.Run.HostTiny` |
| `Nano.V2Self.Proof.Loop` | `Nano.Run.Loop` |
| `Nano.V2Self.Proof.MachExact` | `Nano.Run.MachExact` |
| `Nano.V2Self.Proof.NdCG` | `Nano.Run.NdCG` |
| `Nano.V2Self.Proof.NdCGm` | `Nano.Run.NdCGm` |
| `Nano.V2Self.Proof.NdCGt` | `Nano.Run.NdCGt` |
| `Nano.V2Self.Proof.NdCGv` | `Nano.Run.NdCGv` |
| `Nano.V2Self.Proof.NdCGw` | `Nano.Run.NdCGw` |
| `Nano.V2Self.Proof.NdDef` | `Nano.Run.NdDef` |
| `Nano.V2Self.Proof.NdProg` | `Nano.Run.NdProg` |
| `Nano.V2Self.Proof.NdProgW` | `Nano.Run.NdProgW` |
| `Nano.V2Self.Proof.NdRun` | `Nano.Run.NdRun` |
| `Nano.V2Self.Proof.NdSem` | `Nano.Run.NdSem` |
| `Nano.V2Self.Proof.NdTop` | `Nano.Run.NdTop` |
| `Nano.V2Self.Proof.NdTop2` | `Nano.Run.NdTop2` |
| `Nano.V2Self.Proof.NdWidth` | `Nano.Run.NdWidth` |
| `Nano.V2Self.Proof.NdWidthB` | `Nano.Run.NdWidthB` |
| `Nano.V2Self.Proof.NoW` | `Nano.Run.NoW` |
| `Nano.V2Self.Proof.RoomRun` | `Nano.Run.RoomRun` |
| `Nano.V2Self.Proof.SafeRun` | `Nano.Run.SafeRun` |
| `Nano.V2Self.Proof.SimW` | `Nano.Run.SimW` |
| `Nano.V2Self.Proof.SimX` | `Nano.Run.SimX` |
| `Nano.V2Self.Proof.SimXB` | `Nano.Run.SimXB` |
| `Nano.V2Self.Proof.StartAll` | `Nano.Run.StartAll` |
| `Nano.V2Self.Proof.StartAllS` | `Nano.Run.StartAllS` |
| `Nano.V2Self.Proof.StartCode` | `Nano.Run.StartCode` |
| `Nano.V2Self.Proof.StartRun` | `Nano.Run.StartRun` |
| `Nano.V2Self.Proof.StartSafe` | `Nano.Run.StartSafe` |
| `Nano.V2Self.Proof.Templates` | `Nano.Run.Templates` |
| `Nano.V2Self.Proof.TmGood` | `Nano.Run.TmGood` |

### Bridge (40)

| now | new |
|---|---|
| `Nano.V2Self.Proof.MainBridge` | `Nano.SelfHost.Bridge.MainBridge` |
| `Nano.V2Self.Proof.MainBridge10` | `Nano.SelfHost.Bridge.MainBridge10` |
| `Nano.V2Self.Proof.MainBridge11` | `Nano.SelfHost.Bridge.MainBridge11` |
| `Nano.V2Self.Proof.MainBridge12` | `Nano.SelfHost.Bridge.MainBridge12` |
| `Nano.V2Self.Proof.MainBridge13` | `Nano.SelfHost.Bridge.MainBridge13` |
| `Nano.V2Self.Proof.MainBridge14` | `Nano.SelfHost.Bridge.MainBridge14` |
| `Nano.V2Self.Proof.MainBridge15` | `Nano.SelfHost.Bridge.MainBridge15` |
| `Nano.V2Self.Proof.MainBridge2` | `Nano.SelfHost.Bridge.MainBridge2` |
| `Nano.V2Self.Proof.MainBridge3` | `Nano.SelfHost.Bridge.MainBridge3` |
| `Nano.V2Self.Proof.MainBridge4` | `Nano.SelfHost.Bridge.MainBridge4` |
| `Nano.V2Self.Proof.MainBridge5` | `Nano.SelfHost.Bridge.MainBridge5` |
| `Nano.V2Self.Proof.MainBridge6` | `Nano.SelfHost.Bridge.MainBridge6` |
| `Nano.V2Self.Proof.MainBridge7` | `Nano.SelfHost.Bridge.MainBridge7` |
| `Nano.V2Self.Proof.MainBridge8` | `Nano.SelfHost.Bridge.MainBridge8` |
| `Nano.V2Self.Proof.MainBridge9` | `Nano.SelfHost.Bridge.MainBridge9` |
| `Nano.V2Self.Proof.MainConv1` | `Nano.SelfHost.Bridge.MainConv1` |
| `Nano.V2Self.Proof.MainConv2` | `Nano.SelfHost.Bridge.MainConv2` |
| `Nano.V2Self.Proof.MainConv3` | `Nano.SelfHost.Bridge.MainConv3` |
| `Nano.V2Self.Proof.MainConv4` | `Nano.SelfHost.Bridge.MainConv4` |
| `Nano.V2Self.Proof.MainConv5` | `Nano.SelfHost.Bridge.MainConv5` |
| `Nano.V2Self.Proof.MainConv6` | `Nano.SelfHost.Bridge.MainConv6` |
| `Nano.V2Self.Proof.MainConv7` | `Nano.SelfHost.Bridge.MainConv7` |
| `Nano.V2Self.Proof.MainConv8` | `Nano.SelfHost.Bridge.MainConv8` |
| `Nano.V2Self.Proof.MainConvF2` | `Nano.SelfHost.Bridge.MainConvF2` |
| `Nano.V2Self.Proof.MainConvF3` | `Nano.SelfHost.Bridge.MainConvF3` |
| `Nano.V2Self.Proof.MainConvF4` | `Nano.SelfHost.Bridge.MainConvF4` |
| `Nano.V2Self.Proof.MainConvF5` | `Nano.SelfHost.Bridge.MainConvF5` |
| `Nano.V2Self.Proof.MainConvF6` | `Nano.SelfHost.Bridge.MainConvF6` |
| `Nano.V2Self.Proof.MainConvF7` | `Nano.SelfHost.Bridge.MainConvF7` |
| `Nano.V2Self.Proof.MainConvG` | `Nano.SelfHost.Bridge.MainConvG` |
| `Nano.V2Self.Proof.MainConvX1` | `Nano.SelfHost.Bridge.MainConvX1` |
| `Nano.V2Self.Proof.MainConvX2` | `Nano.SelfHost.Bridge.MainConvX2` |
| `Nano.V2Self.Proof.MainConvX3` | `Nano.SelfHost.Bridge.MainConvX3` |
| `Nano.V2Self.Proof.MainConvX4` | `Nano.SelfHost.Bridge.MainConvX4` |
| `Nano.V2Self.Proof.MainConvX5` | `Nano.SelfHost.Bridge.MainConvX5` |
| `Nano.V2Self.Proof.MainConvX6` | `Nano.SelfHost.Bridge.MainConvX6` |
| `Nano.V2Self.Proof.MainConvX7` | `Nano.SelfHost.Bridge.MainConvX7` |
| `Nano.V2Self.Proof.MainOk` | `Nano.SelfHost.Bridge.MainOk` |
| `Nano.V2Self.Proof.MainTy` | `Nano.SelfHost.Bridge.MainTy` |
| `Nano.V2Self.Proof.SemX` | `Nano.SelfHost.Bridge.SemX` |

### Cert (50)

| now | new |
|---|---|
| `Nano.SelfHost.Cert.All` | (same) |
| `Nano.SelfHost.Cert.Asm` | (same) |
| `Nano.SelfHost.Cert.Defs0` | (same) |
| `Nano.SelfHost.Cert.Defs1` | (same) |
| `Nano.SelfHost.Cert.Defs10` | (same) |
| `Nano.SelfHost.Cert.Defs11` | (same) |
| `Nano.SelfHost.Cert.Defs12` | (same) |
| `Nano.SelfHost.Cert.Defs13` | (same) |
| `Nano.SelfHost.Cert.Defs14` | (same) |
| `Nano.SelfHost.Cert.Defs15` | (same) |
| `Nano.SelfHost.Cert.Defs16` | (same) |
| `Nano.SelfHost.Cert.Defs17` | (same) |
| `Nano.SelfHost.Cert.Defs18` | (same) |
| `Nano.SelfHost.Cert.Defs19` | (same) |
| `Nano.SelfHost.Cert.Defs2` | (same) |
| `Nano.SelfHost.Cert.Defs20` | (same) |
| `Nano.SelfHost.Cert.Defs21` | (same) |
| `Nano.SelfHost.Cert.Defs22` | (same) |
| `Nano.SelfHost.Cert.Defs23` | (same) |
| `Nano.SelfHost.Cert.Defs24` | (same) |
| `Nano.SelfHost.Cert.Defs25` | (same) |
| `Nano.SelfHost.Cert.Defs26` | (same) |
| `Nano.SelfHost.Cert.Defs27` | (same) |
| `Nano.SelfHost.Cert.Defs28` | (same) |
| `Nano.SelfHost.Cert.Defs29` | (same) |
| `Nano.SelfHost.Cert.Defs3` | (same) |
| `Nano.SelfHost.Cert.Defs30` | (same) |
| `Nano.SelfHost.Cert.Defs31` | (same) |
| `Nano.SelfHost.Cert.Defs32` | (same) |
| `Nano.SelfHost.Cert.Defs33` | (same) |
| `Nano.SelfHost.Cert.Defs34` | (same) |
| `Nano.SelfHost.Cert.Defs35` | (same) |
| `Nano.SelfHost.Cert.Defs36` | (same) |
| `Nano.SelfHost.Cert.Defs37` | (same) |
| `Nano.SelfHost.Cert.Defs38` | (same) |
| `Nano.SelfHost.Cert.Defs39` | (same) |
| `Nano.SelfHost.Cert.Defs4` | (same) |
| `Nano.SelfHost.Cert.Defs40` | (same) |
| `Nano.SelfHost.Cert.Defs41` | (same) |
| `Nano.SelfHost.Cert.Defs42` | (same) |
| `Nano.SelfHost.Cert.Defs5` | (same) |
| `Nano.SelfHost.Cert.Defs6` | (same) |
| `Nano.SelfHost.Cert.Defs7` | (same) |
| `Nano.SelfHost.Cert.Defs8` | (same) |
| `Nano.SelfHost.Cert.Defs9` | (same) |
| `Nano.SelfHost.Cert.OutSpec` | (same) |
| `Nano.SelfHost.Cert.PC` | (same) |
| `Nano.SelfHost.Cert.Rules` | (same) |
| `Nano.SelfHost.Cert.Specs` | (same) |
| `Nano.SelfHost.Cert.Tac` | (same) |

### SrcLink (65)

| now | new |
|---|---|
| `Nano.V2Self.Proof.Src.Chain` | `Nano.SelfHost.SrcLink.Chain` |
| `Nano.V2Self.Proof.Src.Chk0` | `Nano.SelfHost.SrcLink.Chk0` |
| `Nano.V2Self.Proof.Src.Chk1` | `Nano.SelfHost.SrcLink.Chk1` |
| `Nano.V2Self.Proof.Src.Chk10` | `Nano.SelfHost.SrcLink.Chk10` |
| `Nano.V2Self.Proof.Src.Chk11` | `Nano.SelfHost.SrcLink.Chk11` |
| `Nano.V2Self.Proof.Src.Chk12` | `Nano.SelfHost.SrcLink.Chk12` |
| `Nano.V2Self.Proof.Src.Chk13` | `Nano.SelfHost.SrcLink.Chk13` |
| `Nano.V2Self.Proof.Src.Chk14` | `Nano.SelfHost.SrcLink.Chk14` |
| `Nano.V2Self.Proof.Src.Chk15` | `Nano.SelfHost.SrcLink.Chk15` |
| `Nano.V2Self.Proof.Src.Chk16` | `Nano.SelfHost.SrcLink.Chk16` |
| `Nano.V2Self.Proof.Src.Chk17` | `Nano.SelfHost.SrcLink.Chk17` |
| `Nano.V2Self.Proof.Src.Chk18` | `Nano.SelfHost.SrcLink.Chk18` |
| `Nano.V2Self.Proof.Src.Chk19` | `Nano.SelfHost.SrcLink.Chk19` |
| `Nano.V2Self.Proof.Src.Chk2` | `Nano.SelfHost.SrcLink.Chk2` |
| `Nano.V2Self.Proof.Src.Chk20` | `Nano.SelfHost.SrcLink.Chk20` |
| `Nano.V2Self.Proof.Src.Chk21` | `Nano.SelfHost.SrcLink.Chk21` |
| `Nano.V2Self.Proof.Src.Chk22` | `Nano.SelfHost.SrcLink.Chk22` |
| `Nano.V2Self.Proof.Src.Chk23` | `Nano.SelfHost.SrcLink.Chk23` |
| `Nano.V2Self.Proof.Src.Chk24` | `Nano.SelfHost.SrcLink.Chk24` |
| `Nano.V2Self.Proof.Src.Chk25` | `Nano.SelfHost.SrcLink.Chk25` |
| `Nano.V2Self.Proof.Src.Chk26` | `Nano.SelfHost.SrcLink.Chk26` |
| `Nano.V2Self.Proof.Src.Chk27` | `Nano.SelfHost.SrcLink.Chk27` |
| `Nano.V2Self.Proof.Src.Chk28` | `Nano.SelfHost.SrcLink.Chk28` |
| `Nano.V2Self.Proof.Src.Chk29` | `Nano.SelfHost.SrcLink.Chk29` |
| `Nano.V2Self.Proof.Src.Chk3` | `Nano.SelfHost.SrcLink.Chk3` |
| `Nano.V2Self.Proof.Src.Chk30` | `Nano.SelfHost.SrcLink.Chk30` |
| `Nano.V2Self.Proof.Src.Chk4` | `Nano.SelfHost.SrcLink.Chk4` |
| `Nano.V2Self.Proof.Src.Chk5` | `Nano.SelfHost.SrcLink.Chk5` |
| `Nano.V2Self.Proof.Src.Chk6` | `Nano.SelfHost.SrcLink.Chk6` |
| `Nano.V2Self.Proof.Src.Chk7` | `Nano.SelfHost.SrcLink.Chk7` |
| `Nano.V2Self.Proof.Src.Chk8` | `Nano.SelfHost.SrcLink.Chk8` |
| `Nano.V2Self.Proof.Src.Chk9` | `Nano.SelfHost.SrcLink.Chk9` |
| `Nano.V2Self.Proof.Src.Data0` | `Nano.SelfHost.SrcLink.Data0` |
| `Nano.V2Self.Proof.Src.Data1` | `Nano.SelfHost.SrcLink.Data1` |
| `Nano.V2Self.Proof.Src.Data10` | `Nano.SelfHost.SrcLink.Data10` |
| `Nano.V2Self.Proof.Src.Data11` | `Nano.SelfHost.SrcLink.Data11` |
| `Nano.V2Self.Proof.Src.Data12` | `Nano.SelfHost.SrcLink.Data12` |
| `Nano.V2Self.Proof.Src.Data13` | `Nano.SelfHost.SrcLink.Data13` |
| `Nano.V2Self.Proof.Src.Data14` | `Nano.SelfHost.SrcLink.Data14` |
| `Nano.V2Self.Proof.Src.Data15` | `Nano.SelfHost.SrcLink.Data15` |
| `Nano.V2Self.Proof.Src.Data16` | `Nano.SelfHost.SrcLink.Data16` |
| `Nano.V2Self.Proof.Src.Data17` | `Nano.SelfHost.SrcLink.Data17` |
| `Nano.V2Self.Proof.Src.Data18` | `Nano.SelfHost.SrcLink.Data18` |
| `Nano.V2Self.Proof.Src.Data19` | `Nano.SelfHost.SrcLink.Data19` |
| `Nano.V2Self.Proof.Src.Data2` | `Nano.SelfHost.SrcLink.Data2` |
| `Nano.V2Self.Proof.Src.Data20` | `Nano.SelfHost.SrcLink.Data20` |
| `Nano.V2Self.Proof.Src.Data21` | `Nano.SelfHost.SrcLink.Data21` |
| `Nano.V2Self.Proof.Src.Data22` | `Nano.SelfHost.SrcLink.Data22` |
| `Nano.V2Self.Proof.Src.Data23` | `Nano.SelfHost.SrcLink.Data23` |
| `Nano.V2Self.Proof.Src.Data24` | `Nano.SelfHost.SrcLink.Data24` |
| `Nano.V2Self.Proof.Src.Data25` | `Nano.SelfHost.SrcLink.Data25` |
| `Nano.V2Self.Proof.Src.Data26` | `Nano.SelfHost.SrcLink.Data26` |
| `Nano.V2Self.Proof.Src.Data27` | `Nano.SelfHost.SrcLink.Data27` |
| `Nano.V2Self.Proof.Src.Data28` | `Nano.SelfHost.SrcLink.Data28` |
| `Nano.V2Self.Proof.Src.Data29` | `Nano.SelfHost.SrcLink.Data29` |
| `Nano.V2Self.Proof.Src.Data3` | `Nano.SelfHost.SrcLink.Data3` |
| `Nano.V2Self.Proof.Src.Data30` | `Nano.SelfHost.SrcLink.Data30` |
| `Nano.V2Self.Proof.Src.Data4` | `Nano.SelfHost.SrcLink.Data4` |
| `Nano.V2Self.Proof.Src.Data5` | `Nano.SelfHost.SrcLink.Data5` |
| `Nano.V2Self.Proof.Src.Data6` | `Nano.SelfHost.SrcLink.Data6` |
| `Nano.V2Self.Proof.Src.Data7` | `Nano.SelfHost.SrcLink.Data7` |
| `Nano.V2Self.Proof.Src.Data8` | `Nano.SelfHost.SrcLink.Data8` |
| `Nano.V2Self.Proof.Src.Data9` | `Nano.SelfHost.SrcLink.Data9` |
| `Nano.V2Self.Proof.Src.Top` | `Nano.SelfHost.SrcLink.Top` |
| `Nano.SelfHost.SrcLink` | `Nano.SelfHost.SrcLink.SrcLink` |

### Main (7)

| now | new |
|---|---|
| `Nano.V2Self.Proof.DBStageE` | `Nano.Main.DBStageE` |
| `Nano.V2Self.Proof.GenStageE` | `Nano.Main.GenStageE` |
| `Nano.Main` | `Nano.Main.Main` |
| `Nano.V2Self.Proof.MainTop` | `Nano.Main.MainTop` |
| `Nano.V2Self.Proof.MainTopE` | `Nano.Main.MainTopE` |
| `Nano.V2Self.Proof.SelfC` | `Nano.Main.SelfC` |
| `Nano.V2Self.Proof.SelfLink` | `Nano.Main.SelfLink` |

### C (compiler, unchanged) (5)

| now | new |
|---|---|
| `Nano.Main.Chain` | (same) |
| `Nano.Codegen.Gen` | (same) |
| `Nano.Lexer.Lex2` | (same) |
| `Nano.Ownership.Own` | (same) |
| `Nano.Parser.Par1` | (same) |

### top (1)

| now | new |
|---|---|
| `Nano.Main.Prelude` | (same) |
