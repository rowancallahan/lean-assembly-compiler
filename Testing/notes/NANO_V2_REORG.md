# Nano/V2Self reorganization proposal (O)

Status: proposal only; nothing has been moved yet. Basis: the dead-code audit in `NANO_V2_DEADCODE.md` and its import
closure from `Nano/V2Self/REVIEW.lean`.

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
| `Nano.V2Self.C.Lex2Sound` | `Nano.V2Self.Proof.Lex.Lex2Sound` |
| `Nano.V2Self.C.Lex2Spec` | `Nano.V2Self.Proof.Lex.Lex2Spec` |
| `Nano.V2Self.Proof.MainTokWF` | `Nano.V2Self.Proof.Lex.MainTokWF` |
| `Nano.V2Self.Proof.ParTokWF` | `Nano.V2Self.Proof.Lex.ParTokWF` |

### Parser (89)

| now | new |
|---|---|
| `Nano.V2Self.Proof.DBPar` | `Nano.V2Self.Proof.Parser.DBPar` |
| `Nano.V2Self.Proof.MainTyP` | `Nano.V2Self.Proof.Parser.MainTyP` |
| `Nano.V2Self.Proof.ParCapBnd` | `Nano.V2Self.Proof.Parser.ParCapBnd` |
| `Nano.V2Self.Proof.ParInv` | `Nano.V2Self.Proof.Parser.ParInv` |
| `Nano.V2Self.Proof.ParInvApi` | `Nano.V2Self.Proof.Parser.ParInvApi` |
| `Nano.V2Self.Proof.ParInvAppend` | `Nano.V2Self.Proof.Parser.ParInvAppend` |
| `Nano.V2Self.Proof.ParInvArg` | `Nano.V2Self.Proof.Parser.ParInvArg` |
| `Nano.V2Self.Proof.ParInvArgName` | `Nano.V2Self.Proof.Parser.ParInvArgName` |
| `Nano.V2Self.Proof.ParInvArm` | `Nano.V2Self.Proof.Parser.ParInvArm` |
| `Nano.V2Self.Proof.ParInvAssign` | `Nano.V2Self.Proof.Parser.ParInvAssign` |
| `Nano.V2Self.Proof.ParInvAtom` | `Nano.V2Self.Proof.Parser.ParInvAtom` |
| `Nano.V2Self.Proof.ParInvBind` | `Nano.V2Self.Proof.Parser.ParInvBind` |
| `Nano.V2Self.Proof.ParInvBuild` | `Nano.V2Self.Proof.Parser.ParInvBuild` |
| `Nano.V2Self.Proof.ParInvCall` | `Nano.V2Self.Proof.Parser.ParInvCall` |
| `Nano.V2Self.Proof.ParInvClose` | `Nano.V2Self.Proof.Parser.ParInvClose` |
| `Nano.V2Self.Proof.ParInvDefs` | `Nano.V2Self.Proof.Parser.ParInvDefs` |
| `Nano.V2Self.Proof.ParInvExpr` | `Nano.V2Self.Proof.Parser.ParInvExpr` |
| `Nano.V2Self.Proof.ParInvExpr2` | `Nano.V2Self.Proof.Parser.ParInvExpr2` |
| `Nano.V2Self.Proof.ParInvFin` | `Nano.V2Self.Proof.Parser.ParInvFin` |
| `Nano.V2Self.Proof.ParInvFinish` | `Nano.V2Self.Proof.Parser.ParInvFinish` |
| `Nano.V2Self.Proof.ParInvFlatM` | `Nano.V2Self.Proof.Parser.ParInvFlatM` |
| `Nano.V2Self.Proof.ParInvGroup` | `Nano.V2Self.Proof.Parser.ParInvGroup` |
| `Nano.V2Self.Proof.ParInvHdr` | `Nano.V2Self.Proof.Parser.ParInvHdr` |
| `Nano.V2Self.Proof.ParInvInit` | `Nano.V2Self.Proof.Parser.ParInvInit` |
| `Nano.V2Self.Proof.ParInvIntern` | `Nano.V2Self.Proof.Parser.ParInvIntern` |
| `Nano.V2Self.Proof.ParInvIte` | `Nano.V2Self.Proof.Parser.ParInvIte` |
| `Nano.V2Self.Proof.ParInvLet` | `Nano.V2Self.Proof.Parser.ParInvLet` |
| `Nano.V2Self.Proof.ParInvLetEnd` | `Nano.V2Self.Proof.Parser.ParInvLetEnd` |
| `Nano.V2Self.Proof.ParInvLetPair` | `Nano.V2Self.Proof.Parser.ParInvLetPair` |
| `Nano.V2Self.Proof.ParInvLetSemi` | `Nano.V2Self.Proof.Parser.ParInvLetSemi` |
| `Nano.V2Self.Proof.ParInvMkPair` | `Nano.V2Self.Proof.Parser.ParInvMkPair` |
| `Nano.V2Self.Proof.ParInvName` | `Nano.V2Self.Proof.Parser.ParInvName` |
| `Nano.V2Self.Proof.ParInvNum` | `Nano.V2Self.Proof.Parser.ParInvNum` |
| `Nano.V2Self.Proof.ParInvOps` | `Nano.V2Self.Proof.Parser.ParInvOps` |
| `Nano.V2Self.Proof.ParInvPair` | `Nano.V2Self.Proof.Parser.ParInvPair` |
| `Nano.V2Self.Proof.ParInvPrev` | `Nano.V2Self.Proof.Parser.ParInvPrev` |
| `Nano.V2Self.Proof.ParInvPrim` | `Nano.V2Self.Proof.Parser.ParInvPrim` |
| `Nano.V2Self.Proof.ParInvPrimary` | `Nano.V2Self.Proof.Parser.ParInvPrimary` |
| `Nano.V2Self.Proof.ParInvRep` | `Nano.V2Self.Proof.Parser.ParInvRep` |
| `Nano.V2Self.Proof.ParInvRun` | `Nano.V2Self.Proof.Parser.ParInvRun` |
| `Nano.V2Self.Proof.ParInvSelf` | `Nano.V2Self.Proof.Parser.ParInvSelf` |
| `Nano.V2Self.Proof.ParInvShP` | `Nano.V2Self.Proof.Parser.ParInvShP` |
| `Nano.V2Self.Proof.ParInvState` | `Nano.V2Self.Proof.Parser.ParInvState` |
| `Nano.V2Self.Proof.ParInvStep` | `Nano.V2Self.Proof.Parser.ParInvStep` |
| `Nano.V2Self.Proof.ParInvTop` | `Nano.V2Self.Proof.Parser.ParInvTop` |
| `Nano.V2Self.Proof.ParInvTy` | `Nano.V2Self.Proof.Parser.ParInvTy` |
| `Nano.V2Self.Proof.ParInvVal` | `Nano.V2Self.Proof.Parser.ParInvVal` |
| `Nano.V2Self.Proof.ParInvValRep` | `Nano.V2Self.Proof.Parser.ParInvValRep` |
| `Nano.V2Self.Proof.ParRep` | `Nano.V2Self.Proof.Parser.ParRep` |
| `Nano.V2Self.Proof.ParRun` | `Nano.V2Self.Proof.Parser.ParRun` |
| `Nano.V2Self.Proof.ParRunArena` | `Nano.V2Self.Proof.Parser.ParRunArena` |
| `Nano.V2Self.Proof.ParRunArgs` | `Nano.V2Self.Proof.Parser.ParRunArgs` |
| `Nano.V2Self.Proof.ParRunAtom` | `Nano.V2Self.Proof.Parser.ParRunAtom` |
| `Nano.V2Self.Proof.ParRunBnd` | `Nano.V2Self.Proof.Parser.ParRunBnd` |
| `Nano.V2Self.Proof.ParRunBody` | `Nano.V2Self.Proof.Parser.ParRunBody` |
| `Nano.V2Self.Proof.ParRunCInv` | `Nano.V2Self.Proof.Parser.ParRunCInv` |
| `Nano.V2Self.Proof.ParRunCall` | `Nano.V2Self.Proof.Parser.ParRunCall` |
| `Nano.V2Self.Proof.ParRunCallSpec` | `Nano.V2Self.Proof.Parser.ParRunCallSpec` |
| `Nano.V2Self.Proof.ParRunDef` | `Nano.V2Self.Proof.Parser.ParRunDef` |
| `Nano.V2Self.Proof.ParRunDefs` | `Nano.V2Self.Proof.Parser.ParRunDefs` |
| `Nano.V2Self.Proof.ParRunExpr` | `Nano.V2Self.Proof.Parser.ParRunExpr` |
| `Nano.V2Self.Proof.ParRunExprInv` | `Nano.V2Self.Proof.Parser.ParRunExprInv` |
| `Nano.V2Self.Proof.ParRunExprMain` | `Nano.V2Self.Proof.Parser.ParRunExprMain` |
| `Nano.V2Self.Proof.ParRunFlat` | `Nano.V2Self.Proof.Parser.ParRunFlat` |
| `Nano.V2Self.Proof.ParRunHCall` | `Nano.V2Self.Proof.Parser.ParRunHCall` |
| `Nano.V2Self.Proof.ParRunHdr` | `Nano.V2Self.Proof.Parser.ParRunHdr` |
| `Nano.V2Self.Proof.ParRunLoop` | `Nano.V2Self.Proof.Parser.ParRunLoop` |
| `Nano.V2Self.Proof.ParRunNames` | `Nano.V2Self.Proof.Parser.ParRunNames` |
| `Nano.V2Self.Proof.ParRunObl` | `Nano.V2Self.Proof.Parser.ParRunObl` |
| `Nano.V2Self.Proof.ParRunPrim` | `Nano.V2Self.Proof.Parser.ParRunPrim` |
| `Nano.V2Self.Proof.ParRunPrimS` | `Nano.V2Self.Proof.Parser.ParRunPrimS` |
| `Nano.V2Self.Proof.ParRunProg` | `Nano.V2Self.Proof.Parser.ParRunProg` |
| `Nano.V2Self.Proof.ParRunRow` | `Nano.V2Self.Proof.Parser.ParRunRow` |
| `Nano.V2Self.Proof.ParRunSelf` | `Nano.V2Self.Proof.Parser.ParRunSelf` |
| `Nano.V2Self.Proof.ParRunShape` | `Nano.V2Self.Proof.Parser.ParRunShape` |
| `Nano.V2Self.Proof.ParRunSmall` | `Nano.V2Self.Proof.Parser.ParRunSmall` |
| `Nano.V2Self.Proof.ParRunStar` | `Nano.V2Self.Proof.Parser.ParRunStar` |
| `Nano.V2Self.Proof.ParRunTup` | `Nano.V2Self.Proof.Parser.ParRunTup` |
| `Nano.V2Self.Proof.ParRunTy` | `Nano.V2Self.Proof.Parser.ParRunTy` |
| `Nano.V2Self.Proof.ParRunWF` | `Nano.V2Self.Proof.Parser.ParRunWF` |
| `Nano.V2Self.Proof.ParRunWFFr` | `Nano.V2Self.Proof.Parser.ParRunWFFr` |
| `Nano.V2Self.Proof.ParRunWFInv` | `Nano.V2Self.Proof.Parser.ParRunWFInv` |
| `Nano.V2Self.Proof.ParRunWFPres` | `Nano.V2Self.Proof.Parser.ParRunWFPres` |
| `Nano.V2Self.Proof.ParRunWFStep` | `Nano.V2Self.Proof.Parser.ParRunWFStep` |
| `Nano.V2Self.Proof.ParSerLen` | `Nano.V2Self.Proof.Parser.ParSerLen` |
| `Nano.V2Self.Proof.ParSpec` | `Nano.V2Self.Proof.Parser.ParSpec` |
| `Nano.V2Self.Proof.ParSpecLen` | `Nano.V2Self.Proof.Parser.ParSpecLen` |
| `Nano.V2Self.Proof.ParSpecTail` | `Nano.V2Self.Proof.Parser.ParSpecTail` |
| `Nano.V2Self.Proof.ParTreeOK` | `Nano.V2Self.Proof.Parser.ParTreeOK` |

### Own (35)

| now | new |
|---|---|
| `Nano.V2Self.Proof.MainKeep` | `Nano.V2Self.Proof.Own.MainKeep` |
| `Nano.V2Self.Proof.OwnP0` | `Nano.V2Self.Proof.Own.OwnP0` |
| `Nano.V2Self.Proof.OwnP1` | `Nano.V2Self.Proof.Own.OwnP1` |
| `Nano.V2Self.Proof.OwnP10` | `Nano.V2Self.Proof.Own.OwnP10` |
| `Nano.V2Self.Proof.OwnP11` | `Nano.V2Self.Proof.Own.OwnP11` |
| `Nano.V2Self.Proof.OwnP12` | `Nano.V2Self.Proof.Own.OwnP12` |
| `Nano.V2Self.Proof.OwnP13` | `Nano.V2Self.Proof.Own.OwnP13` |
| `Nano.V2Self.Proof.OwnP14` | `Nano.V2Self.Proof.Own.OwnP14` |
| `Nano.V2Self.Proof.OwnP15` | `Nano.V2Self.Proof.Own.OwnP15` |
| `Nano.V2Self.Proof.OwnP16` | `Nano.V2Self.Proof.Own.OwnP16` |
| `Nano.V2Self.Proof.OwnP17` | `Nano.V2Self.Proof.Own.OwnP17` |
| `Nano.V2Self.Proof.OwnP18` | `Nano.V2Self.Proof.Own.OwnP18` |
| `Nano.V2Self.Proof.OwnP19` | `Nano.V2Self.Proof.Own.OwnP19` |
| `Nano.V2Self.Proof.OwnP2` | `Nano.V2Self.Proof.Own.OwnP2` |
| `Nano.V2Self.Proof.OwnP20` | `Nano.V2Self.Proof.Own.OwnP20` |
| `Nano.V2Self.Proof.OwnP21` | `Nano.V2Self.Proof.Own.OwnP21` |
| `Nano.V2Self.Proof.OwnP22` | `Nano.V2Self.Proof.Own.OwnP22` |
| `Nano.V2Self.Proof.OwnP23` | `Nano.V2Self.Proof.Own.OwnP23` |
| `Nano.V2Self.Proof.OwnP24` | `Nano.V2Self.Proof.Own.OwnP24` |
| `Nano.V2Self.Proof.OwnP25` | `Nano.V2Self.Proof.Own.OwnP25` |
| `Nano.V2Self.Proof.OwnP26` | `Nano.V2Self.Proof.Own.OwnP26` |
| `Nano.V2Self.Proof.OwnP27` | `Nano.V2Self.Proof.Own.OwnP27` |
| `Nano.V2Self.Proof.OwnP28` | `Nano.V2Self.Proof.Own.OwnP28` |
| `Nano.V2Self.Proof.OwnP29` | `Nano.V2Self.Proof.Own.OwnP29` |
| `Nano.V2Self.Proof.OwnP3` | `Nano.V2Self.Proof.Own.OwnP3` |
| `Nano.V2Self.Proof.OwnP30` | `Nano.V2Self.Proof.Own.OwnP30` |
| `Nano.V2Self.Proof.OwnP4` | `Nano.V2Self.Proof.Own.OwnP4` |
| `Nano.V2Self.Proof.OwnP5` | `Nano.V2Self.Proof.Own.OwnP5` |
| `Nano.V2Self.Proof.OwnP6` | `Nano.V2Self.Proof.Own.OwnP6` |
| `Nano.V2Self.Proof.OwnP7` | `Nano.V2Self.Proof.Own.OwnP7` |
| `Nano.V2Self.Proof.OwnP8` | `Nano.V2Self.Proof.Own.OwnP8` |
| `Nano.V2Self.Proof.OwnP9` | `Nano.V2Self.Proof.Own.OwnP9` |
| `Nano.V2Self.Proof.OwnSpec` | `Nano.V2Self.Proof.Own.OwnSpec` |
| `Nano.V2Self.Proof.OwnStage` | `Nano.V2Self.Proof.Own.OwnStage` |
| `Nano.V2Self.Proof.OwnWF` | `Nano.V2Self.Proof.Own.OwnWF` |

### Gen (7)

| now | new |
|---|---|
| `Nano.V2Self.Proof.BufL` | `Nano.V2Self.Proof.Gen.BufL` |
| `Nano.V2Self.Proof.DBNode` | `Nano.V2Self.Proof.Gen.DBNode` |
| `Nano.V2Self.Proof.Fixup` | `Nano.V2Self.Proof.Gen.Fixup` |
| `Nano.V2Self.Proof.GenAll` | `Nano.V2Self.Proof.Gen.GenAll` |
| `Nano.V2Self.Proof.GenRef` | `Nano.V2Self.Proof.Gen.GenRef` |
| `Nano.V2Self.Proof.GenTop` | `Nano.V2Self.Proof.Gen.GenTop` |
| `Nano.V2Self.Proof.GenWidth` | `Nano.V2Self.Proof.Gen.GenWidth` |

### Machine (66)

| now | new |
|---|---|
| `Nano.V2Self.Proof.Bridge` | `Nano.V2Self.Proof.Machine.Bridge` |
| `Nano.V2Self.Proof.Call` | `Nano.V2Self.Proof.Machine.Call` |
| `Nano.V2Self.Proof.CallA` | `Nano.V2Self.Proof.Machine.CallA` |
| `Nano.V2Self.Proof.CallExact` | `Nano.V2Self.Proof.Machine.CallExact` |
| `Nano.V2Self.Proof.CapHost` | `Nano.V2Self.Proof.Machine.CapHost` |
| `Nano.V2Self.Proof.CapNode` | `Nano.V2Self.Proof.Machine.CapNode` |
| `Nano.V2Self.Proof.CapProg` | `Nano.V2Self.Proof.Machine.CapProg` |
| `Nano.V2Self.Proof.CapRun` | `Nano.V2Self.Proof.Machine.CapRun` |
| `Nano.V2Self.Proof.CapStart` | `Nano.V2Self.Proof.Machine.CapStart` |
| `Nano.V2Self.Proof.EVSCall` | `Nano.V2Self.Proof.Machine.EVSCall` |
| `Nano.V2Self.Proof.EVSComp` | `Nano.V2Self.Proof.Machine.EVSComp` |
| `Nano.V2Self.Proof.EVSDefs` | `Nano.V2Self.Proof.Machine.EVSDefs` |
| `Nano.V2Self.Proof.EVSFin` | `Nano.V2Self.Proof.Machine.EVSFin` |
| `Nano.V2Self.Proof.EVSLeaf` | `Nano.V2Self.Proof.Machine.EVSLeaf` |
| `Nano.V2Self.Proof.EVSLoop` | `Nano.V2Self.Proof.Machine.EVSLoop` |
| `Nano.V2Self.Proof.EVSProg` | `Nano.V2Self.Proof.Machine.EVSProg` |
| `Nano.V2Self.Proof.EVSRun` | `Nano.V2Self.Proof.Machine.EVSRun` |
| `Nano.V2Self.Proof.EVSTail` | `Nano.V2Self.Proof.Machine.EVSTail` |
| `Nano.V2Self.Proof.EVX` | `Nano.V2Self.Proof.Machine.EVX` |
| `Nano.V2Self.Proof.EVXC` | `Nano.V2Self.Proof.Machine.EVXC` |
| `Nano.V2Self.Proof.EVXF` | `Nano.V2Self.Proof.Machine.EVXF` |
| `Nano.V2Self.Proof.EVXL` | `Nano.V2Self.Proof.Machine.EVXL` |
| `Nano.V2Self.Proof.EVXP` | `Nano.V2Self.Proof.Machine.EVXP` |
| `Nano.V2Self.Proof.EVXT` | `Nano.V2Self.Proof.Machine.EVXT` |
| `Nano.V2Self.Proof.Expr` | `Nano.V2Self.Proof.Machine.Expr` |
| `Nano.V2Self.Proof.ExprBridge` | `Nano.V2Self.Proof.Machine.ExprBridge` |
| `Nano.V2Self.Proof.ExprEV` | `Nano.V2Self.Proof.Machine.ExprEV` |
| `Nano.V2Self.Proof.ExprExact` | `Nano.V2Self.Proof.Machine.ExprExact` |
| `Nano.V2Self.Proof.GenImpl` | `Nano.V2Self.Proof.Machine.GenImpl` |
| `Nano.V2Self.Proof.GenMain` | `Nano.V2Self.Proof.Machine.GenMain` |
| `Nano.V2Self.Proof.GenRun` | `Nano.V2Self.Proof.Machine.GenRun` |
| `Nano.V2Self.Proof.GenRunS` | `Nano.V2Self.Proof.Machine.GenRunS` |
| `Nano.V2Self.Proof.Heap` | `Nano.V2Self.Proof.Machine.Heap` |
| `Nano.V2Self.Proof.HeapEV` | `Nano.V2Self.Proof.Machine.HeapEV` |
| `Nano.V2Self.Proof.HostLift` | `Nano.V2Self.Proof.Machine.HostLift` |
| `Nano.V2Self.Proof.HostMain` | `Nano.V2Self.Proof.Machine.HostMain` |
| `Nano.V2Self.Proof.HostTiny` | `Nano.V2Self.Proof.Machine.HostTiny` |
| `Nano.V2Self.Proof.Loop` | `Nano.V2Self.Proof.Machine.Loop` |
| `Nano.V2Self.Proof.MachExact` | `Nano.V2Self.Proof.Machine.MachExact` |
| `Nano.V2Self.Proof.NdCG` | `Nano.V2Self.Proof.Machine.NdCG` |
| `Nano.V2Self.Proof.NdCGm` | `Nano.V2Self.Proof.Machine.NdCGm` |
| `Nano.V2Self.Proof.NdCGt` | `Nano.V2Self.Proof.Machine.NdCGt` |
| `Nano.V2Self.Proof.NdCGv` | `Nano.V2Self.Proof.Machine.NdCGv` |
| `Nano.V2Self.Proof.NdCGw` | `Nano.V2Self.Proof.Machine.NdCGw` |
| `Nano.V2Self.Proof.NdDef` | `Nano.V2Self.Proof.Machine.NdDef` |
| `Nano.V2Self.Proof.NdProg` | `Nano.V2Self.Proof.Machine.NdProg` |
| `Nano.V2Self.Proof.NdProgW` | `Nano.V2Self.Proof.Machine.NdProgW` |
| `Nano.V2Self.Proof.NdRun` | `Nano.V2Self.Proof.Machine.NdRun` |
| `Nano.V2Self.Proof.NdSem` | `Nano.V2Self.Proof.Machine.NdSem` |
| `Nano.V2Self.Proof.NdTop` | `Nano.V2Self.Proof.Machine.NdTop` |
| `Nano.V2Self.Proof.NdTop2` | `Nano.V2Self.Proof.Machine.NdTop2` |
| `Nano.V2Self.Proof.NdWidth` | `Nano.V2Self.Proof.Machine.NdWidth` |
| `Nano.V2Self.Proof.NdWidthB` | `Nano.V2Self.Proof.Machine.NdWidthB` |
| `Nano.V2Self.Proof.NoW` | `Nano.V2Self.Proof.Machine.NoW` |
| `Nano.V2Self.Proof.RoomRun` | `Nano.V2Self.Proof.Machine.RoomRun` |
| `Nano.V2Self.Proof.SafeRun` | `Nano.V2Self.Proof.Machine.SafeRun` |
| `Nano.V2Self.Proof.SimW` | `Nano.V2Self.Proof.Machine.SimW` |
| `Nano.V2Self.Proof.SimX` | `Nano.V2Self.Proof.Machine.SimX` |
| `Nano.V2Self.Proof.SimXB` | `Nano.V2Self.Proof.Machine.SimXB` |
| `Nano.V2Self.Proof.StartAll` | `Nano.V2Self.Proof.Machine.StartAll` |
| `Nano.V2Self.Proof.StartAllS` | `Nano.V2Self.Proof.Machine.StartAllS` |
| `Nano.V2Self.Proof.StartCode` | `Nano.V2Self.Proof.Machine.StartCode` |
| `Nano.V2Self.Proof.StartRun` | `Nano.V2Self.Proof.Machine.StartRun` |
| `Nano.V2Self.Proof.StartSafe` | `Nano.V2Self.Proof.Machine.StartSafe` |
| `Nano.V2Self.Proof.Templates` | `Nano.V2Self.Proof.Machine.Templates` |
| `Nano.V2Self.Proof.TmGood` | `Nano.V2Self.Proof.Machine.TmGood` |

### Bridge (40)

| now | new |
|---|---|
| `Nano.V2Self.Proof.MainBridge` | `Nano.V2Self.Proof.Bridge.MainBridge` |
| `Nano.V2Self.Proof.MainBridge10` | `Nano.V2Self.Proof.Bridge.MainBridge10` |
| `Nano.V2Self.Proof.MainBridge11` | `Nano.V2Self.Proof.Bridge.MainBridge11` |
| `Nano.V2Self.Proof.MainBridge12` | `Nano.V2Self.Proof.Bridge.MainBridge12` |
| `Nano.V2Self.Proof.MainBridge13` | `Nano.V2Self.Proof.Bridge.MainBridge13` |
| `Nano.V2Self.Proof.MainBridge14` | `Nano.V2Self.Proof.Bridge.MainBridge14` |
| `Nano.V2Self.Proof.MainBridge15` | `Nano.V2Self.Proof.Bridge.MainBridge15` |
| `Nano.V2Self.Proof.MainBridge2` | `Nano.V2Self.Proof.Bridge.MainBridge2` |
| `Nano.V2Self.Proof.MainBridge3` | `Nano.V2Self.Proof.Bridge.MainBridge3` |
| `Nano.V2Self.Proof.MainBridge4` | `Nano.V2Self.Proof.Bridge.MainBridge4` |
| `Nano.V2Self.Proof.MainBridge5` | `Nano.V2Self.Proof.Bridge.MainBridge5` |
| `Nano.V2Self.Proof.MainBridge6` | `Nano.V2Self.Proof.Bridge.MainBridge6` |
| `Nano.V2Self.Proof.MainBridge7` | `Nano.V2Self.Proof.Bridge.MainBridge7` |
| `Nano.V2Self.Proof.MainBridge8` | `Nano.V2Self.Proof.Bridge.MainBridge8` |
| `Nano.V2Self.Proof.MainBridge9` | `Nano.V2Self.Proof.Bridge.MainBridge9` |
| `Nano.V2Self.Proof.MainConv1` | `Nano.V2Self.Proof.Bridge.MainConv1` |
| `Nano.V2Self.Proof.MainConv2` | `Nano.V2Self.Proof.Bridge.MainConv2` |
| `Nano.V2Self.Proof.MainConv3` | `Nano.V2Self.Proof.Bridge.MainConv3` |
| `Nano.V2Self.Proof.MainConv4` | `Nano.V2Self.Proof.Bridge.MainConv4` |
| `Nano.V2Self.Proof.MainConv5` | `Nano.V2Self.Proof.Bridge.MainConv5` |
| `Nano.V2Self.Proof.MainConv6` | `Nano.V2Self.Proof.Bridge.MainConv6` |
| `Nano.V2Self.Proof.MainConv7` | `Nano.V2Self.Proof.Bridge.MainConv7` |
| `Nano.V2Self.Proof.MainConv8` | `Nano.V2Self.Proof.Bridge.MainConv8` |
| `Nano.V2Self.Proof.MainConvF2` | `Nano.V2Self.Proof.Bridge.MainConvF2` |
| `Nano.V2Self.Proof.MainConvF3` | `Nano.V2Self.Proof.Bridge.MainConvF3` |
| `Nano.V2Self.Proof.MainConvF4` | `Nano.V2Self.Proof.Bridge.MainConvF4` |
| `Nano.V2Self.Proof.MainConvF5` | `Nano.V2Self.Proof.Bridge.MainConvF5` |
| `Nano.V2Self.Proof.MainConvF6` | `Nano.V2Self.Proof.Bridge.MainConvF6` |
| `Nano.V2Self.Proof.MainConvF7` | `Nano.V2Self.Proof.Bridge.MainConvF7` |
| `Nano.V2Self.Proof.MainConvG` | `Nano.V2Self.Proof.Bridge.MainConvG` |
| `Nano.V2Self.Proof.MainConvX1` | `Nano.V2Self.Proof.Bridge.MainConvX1` |
| `Nano.V2Self.Proof.MainConvX2` | `Nano.V2Self.Proof.Bridge.MainConvX2` |
| `Nano.V2Self.Proof.MainConvX3` | `Nano.V2Self.Proof.Bridge.MainConvX3` |
| `Nano.V2Self.Proof.MainConvX4` | `Nano.V2Self.Proof.Bridge.MainConvX4` |
| `Nano.V2Self.Proof.MainConvX5` | `Nano.V2Self.Proof.Bridge.MainConvX5` |
| `Nano.V2Self.Proof.MainConvX6` | `Nano.V2Self.Proof.Bridge.MainConvX6` |
| `Nano.V2Self.Proof.MainConvX7` | `Nano.V2Self.Proof.Bridge.MainConvX7` |
| `Nano.V2Self.Proof.MainOk` | `Nano.V2Self.Proof.Bridge.MainOk` |
| `Nano.V2Self.Proof.MainTy` | `Nano.V2Self.Proof.Bridge.MainTy` |
| `Nano.V2Self.Proof.SemX` | `Nano.V2Self.Proof.Bridge.SemX` |

### Cert (50)

| now | new |
|---|---|
| `Nano.V2Self.Proof.Cert.All` | (same) |
| `Nano.V2Self.Proof.Cert.Asm` | (same) |
| `Nano.V2Self.Proof.Cert.Defs0` | (same) |
| `Nano.V2Self.Proof.Cert.Defs1` | (same) |
| `Nano.V2Self.Proof.Cert.Defs10` | (same) |
| `Nano.V2Self.Proof.Cert.Defs11` | (same) |
| `Nano.V2Self.Proof.Cert.Defs12` | (same) |
| `Nano.V2Self.Proof.Cert.Defs13` | (same) |
| `Nano.V2Self.Proof.Cert.Defs14` | (same) |
| `Nano.V2Self.Proof.Cert.Defs15` | (same) |
| `Nano.V2Self.Proof.Cert.Defs16` | (same) |
| `Nano.V2Self.Proof.Cert.Defs17` | (same) |
| `Nano.V2Self.Proof.Cert.Defs18` | (same) |
| `Nano.V2Self.Proof.Cert.Defs19` | (same) |
| `Nano.V2Self.Proof.Cert.Defs2` | (same) |
| `Nano.V2Self.Proof.Cert.Defs20` | (same) |
| `Nano.V2Self.Proof.Cert.Defs21` | (same) |
| `Nano.V2Self.Proof.Cert.Defs22` | (same) |
| `Nano.V2Self.Proof.Cert.Defs23` | (same) |
| `Nano.V2Self.Proof.Cert.Defs24` | (same) |
| `Nano.V2Self.Proof.Cert.Defs25` | (same) |
| `Nano.V2Self.Proof.Cert.Defs26` | (same) |
| `Nano.V2Self.Proof.Cert.Defs27` | (same) |
| `Nano.V2Self.Proof.Cert.Defs28` | (same) |
| `Nano.V2Self.Proof.Cert.Defs29` | (same) |
| `Nano.V2Self.Proof.Cert.Defs3` | (same) |
| `Nano.V2Self.Proof.Cert.Defs30` | (same) |
| `Nano.V2Self.Proof.Cert.Defs31` | (same) |
| `Nano.V2Self.Proof.Cert.Defs32` | (same) |
| `Nano.V2Self.Proof.Cert.Defs33` | (same) |
| `Nano.V2Self.Proof.Cert.Defs34` | (same) |
| `Nano.V2Self.Proof.Cert.Defs35` | (same) |
| `Nano.V2Self.Proof.Cert.Defs36` | (same) |
| `Nano.V2Self.Proof.Cert.Defs37` | (same) |
| `Nano.V2Self.Proof.Cert.Defs38` | (same) |
| `Nano.V2Self.Proof.Cert.Defs39` | (same) |
| `Nano.V2Self.Proof.Cert.Defs4` | (same) |
| `Nano.V2Self.Proof.Cert.Defs40` | (same) |
| `Nano.V2Self.Proof.Cert.Defs41` | (same) |
| `Nano.V2Self.Proof.Cert.Defs42` | (same) |
| `Nano.V2Self.Proof.Cert.Defs5` | (same) |
| `Nano.V2Self.Proof.Cert.Defs6` | (same) |
| `Nano.V2Self.Proof.Cert.Defs7` | (same) |
| `Nano.V2Self.Proof.Cert.Defs8` | (same) |
| `Nano.V2Self.Proof.Cert.Defs9` | (same) |
| `Nano.V2Self.Proof.Cert.OutSpec` | (same) |
| `Nano.V2Self.Proof.Cert.PC` | (same) |
| `Nano.V2Self.Proof.Cert.Rules` | (same) |
| `Nano.V2Self.Proof.Cert.Specs` | (same) |
| `Nano.V2Self.Proof.Cert.Tac` | (same) |

### SrcLink (65)

| now | new |
|---|---|
| `Nano.V2Self.Proof.Src.Chain` | `Nano.V2Self.Proof.SrcLink.Chain` |
| `Nano.V2Self.Proof.Src.Chk0` | `Nano.V2Self.Proof.SrcLink.Chk0` |
| `Nano.V2Self.Proof.Src.Chk1` | `Nano.V2Self.Proof.SrcLink.Chk1` |
| `Nano.V2Self.Proof.Src.Chk10` | `Nano.V2Self.Proof.SrcLink.Chk10` |
| `Nano.V2Self.Proof.Src.Chk11` | `Nano.V2Self.Proof.SrcLink.Chk11` |
| `Nano.V2Self.Proof.Src.Chk12` | `Nano.V2Self.Proof.SrcLink.Chk12` |
| `Nano.V2Self.Proof.Src.Chk13` | `Nano.V2Self.Proof.SrcLink.Chk13` |
| `Nano.V2Self.Proof.Src.Chk14` | `Nano.V2Self.Proof.SrcLink.Chk14` |
| `Nano.V2Self.Proof.Src.Chk15` | `Nano.V2Self.Proof.SrcLink.Chk15` |
| `Nano.V2Self.Proof.Src.Chk16` | `Nano.V2Self.Proof.SrcLink.Chk16` |
| `Nano.V2Self.Proof.Src.Chk17` | `Nano.V2Self.Proof.SrcLink.Chk17` |
| `Nano.V2Self.Proof.Src.Chk18` | `Nano.V2Self.Proof.SrcLink.Chk18` |
| `Nano.V2Self.Proof.Src.Chk19` | `Nano.V2Self.Proof.SrcLink.Chk19` |
| `Nano.V2Self.Proof.Src.Chk2` | `Nano.V2Self.Proof.SrcLink.Chk2` |
| `Nano.V2Self.Proof.Src.Chk20` | `Nano.V2Self.Proof.SrcLink.Chk20` |
| `Nano.V2Self.Proof.Src.Chk21` | `Nano.V2Self.Proof.SrcLink.Chk21` |
| `Nano.V2Self.Proof.Src.Chk22` | `Nano.V2Self.Proof.SrcLink.Chk22` |
| `Nano.V2Self.Proof.Src.Chk23` | `Nano.V2Self.Proof.SrcLink.Chk23` |
| `Nano.V2Self.Proof.Src.Chk24` | `Nano.V2Self.Proof.SrcLink.Chk24` |
| `Nano.V2Self.Proof.Src.Chk25` | `Nano.V2Self.Proof.SrcLink.Chk25` |
| `Nano.V2Self.Proof.Src.Chk26` | `Nano.V2Self.Proof.SrcLink.Chk26` |
| `Nano.V2Self.Proof.Src.Chk27` | `Nano.V2Self.Proof.SrcLink.Chk27` |
| `Nano.V2Self.Proof.Src.Chk28` | `Nano.V2Self.Proof.SrcLink.Chk28` |
| `Nano.V2Self.Proof.Src.Chk29` | `Nano.V2Self.Proof.SrcLink.Chk29` |
| `Nano.V2Self.Proof.Src.Chk3` | `Nano.V2Self.Proof.SrcLink.Chk3` |
| `Nano.V2Self.Proof.Src.Chk30` | `Nano.V2Self.Proof.SrcLink.Chk30` |
| `Nano.V2Self.Proof.Src.Chk4` | `Nano.V2Self.Proof.SrcLink.Chk4` |
| `Nano.V2Self.Proof.Src.Chk5` | `Nano.V2Self.Proof.SrcLink.Chk5` |
| `Nano.V2Self.Proof.Src.Chk6` | `Nano.V2Self.Proof.SrcLink.Chk6` |
| `Nano.V2Self.Proof.Src.Chk7` | `Nano.V2Self.Proof.SrcLink.Chk7` |
| `Nano.V2Self.Proof.Src.Chk8` | `Nano.V2Self.Proof.SrcLink.Chk8` |
| `Nano.V2Self.Proof.Src.Chk9` | `Nano.V2Self.Proof.SrcLink.Chk9` |
| `Nano.V2Self.Proof.Src.Data0` | `Nano.V2Self.Proof.SrcLink.Data0` |
| `Nano.V2Self.Proof.Src.Data1` | `Nano.V2Self.Proof.SrcLink.Data1` |
| `Nano.V2Self.Proof.Src.Data10` | `Nano.V2Self.Proof.SrcLink.Data10` |
| `Nano.V2Self.Proof.Src.Data11` | `Nano.V2Self.Proof.SrcLink.Data11` |
| `Nano.V2Self.Proof.Src.Data12` | `Nano.V2Self.Proof.SrcLink.Data12` |
| `Nano.V2Self.Proof.Src.Data13` | `Nano.V2Self.Proof.SrcLink.Data13` |
| `Nano.V2Self.Proof.Src.Data14` | `Nano.V2Self.Proof.SrcLink.Data14` |
| `Nano.V2Self.Proof.Src.Data15` | `Nano.V2Self.Proof.SrcLink.Data15` |
| `Nano.V2Self.Proof.Src.Data16` | `Nano.V2Self.Proof.SrcLink.Data16` |
| `Nano.V2Self.Proof.Src.Data17` | `Nano.V2Self.Proof.SrcLink.Data17` |
| `Nano.V2Self.Proof.Src.Data18` | `Nano.V2Self.Proof.SrcLink.Data18` |
| `Nano.V2Self.Proof.Src.Data19` | `Nano.V2Self.Proof.SrcLink.Data19` |
| `Nano.V2Self.Proof.Src.Data2` | `Nano.V2Self.Proof.SrcLink.Data2` |
| `Nano.V2Self.Proof.Src.Data20` | `Nano.V2Self.Proof.SrcLink.Data20` |
| `Nano.V2Self.Proof.Src.Data21` | `Nano.V2Self.Proof.SrcLink.Data21` |
| `Nano.V2Self.Proof.Src.Data22` | `Nano.V2Self.Proof.SrcLink.Data22` |
| `Nano.V2Self.Proof.Src.Data23` | `Nano.V2Self.Proof.SrcLink.Data23` |
| `Nano.V2Self.Proof.Src.Data24` | `Nano.V2Self.Proof.SrcLink.Data24` |
| `Nano.V2Self.Proof.Src.Data25` | `Nano.V2Self.Proof.SrcLink.Data25` |
| `Nano.V2Self.Proof.Src.Data26` | `Nano.V2Self.Proof.SrcLink.Data26` |
| `Nano.V2Self.Proof.Src.Data27` | `Nano.V2Self.Proof.SrcLink.Data27` |
| `Nano.V2Self.Proof.Src.Data28` | `Nano.V2Self.Proof.SrcLink.Data28` |
| `Nano.V2Self.Proof.Src.Data29` | `Nano.V2Self.Proof.SrcLink.Data29` |
| `Nano.V2Self.Proof.Src.Data3` | `Nano.V2Self.Proof.SrcLink.Data3` |
| `Nano.V2Self.Proof.Src.Data30` | `Nano.V2Self.Proof.SrcLink.Data30` |
| `Nano.V2Self.Proof.Src.Data4` | `Nano.V2Self.Proof.SrcLink.Data4` |
| `Nano.V2Self.Proof.Src.Data5` | `Nano.V2Self.Proof.SrcLink.Data5` |
| `Nano.V2Self.Proof.Src.Data6` | `Nano.V2Self.Proof.SrcLink.Data6` |
| `Nano.V2Self.Proof.Src.Data7` | `Nano.V2Self.Proof.SrcLink.Data7` |
| `Nano.V2Self.Proof.Src.Data8` | `Nano.V2Self.Proof.SrcLink.Data8` |
| `Nano.V2Self.Proof.Src.Data9` | `Nano.V2Self.Proof.SrcLink.Data9` |
| `Nano.V2Self.Proof.Src.Top` | `Nano.V2Self.Proof.SrcLink.Top` |
| `Nano.V2Self.Proof.SrcLink` | `Nano.V2Self.Proof.SrcLink.SrcLink` |

### Main (7)

| now | new |
|---|---|
| `Nano.V2Self.Proof.DBStageE` | `Nano.V2Self.Proof.Main.DBStageE` |
| `Nano.V2Self.Proof.GenStageE` | `Nano.V2Self.Proof.Main.GenStageE` |
| `Nano.V2Self.Proof.Main` | `Nano.V2Self.Proof.Main.Main` |
| `Nano.V2Self.Proof.MainTop` | `Nano.V2Self.Proof.Main.MainTop` |
| `Nano.V2Self.Proof.MainTopE` | `Nano.V2Self.Proof.Main.MainTopE` |
| `Nano.V2Self.Proof.SelfC` | `Nano.V2Self.Proof.Main.SelfC` |
| `Nano.V2Self.Proof.SelfLink` | `Nano.V2Self.Proof.Main.SelfLink` |

### C (compiler, unchanged) (5)

| now | new |
|---|---|
| `Nano.V2Self.C.Base` | (same) |
| `Nano.V2Self.C.Gen` | (same) |
| `Nano.V2Self.C.Lex2` | (same) |
| `Nano.V2Self.C.Own` | (same) |
| `Nano.V2Self.C.Par1` | (same) |

### top (1)

| now | new |
|---|---|
| `Nano.V2Self.Prelude` | (same) |
