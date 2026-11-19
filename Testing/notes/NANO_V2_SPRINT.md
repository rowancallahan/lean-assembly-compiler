# NANO v2 sprint units

## SPRINT UNITS (D)

None: everything in D's area is DONE (no sprint units).
- D-S1 (ParSerLen/MainTyP vs the width cap): done by O (ea78be9/bd41e7d).
- D-S2 (BndStage): done by O (ParCapBnd: bndStage, capStage, C_correctLO).
- Source-text link: done by D (74c831c8): `SrcGen.link_pc : Lexes X0 W0 ∧ ParsesProgram W0 Cert.PC.all`,
  regenerate with `lake env lean --run Testing/nano/v2self/srclink/gen.lean Testing/nano/v2self/self_S_input.txt
  Nano/V2Self/Proof/Src 800`.

## SPRINT UNITS (E)
None. GenStage is assembled (`SimW.gen_stage`, GenStageE.lean, b3b101b), modulo O's `HDB` (∀ d ∈ p, DB d for accepted programs). The room primitives and the OOM stub are done (RoomRun, CapHost).

## SPRINT UNITS (O)
None.  Done before the sprint: parser width cap (ea78be9; Layer-2 width invariant = ParRunSmall, parserSound proved),
DBPar adaptation (bd41e7d), parsed_cap / parsed_bnd / bndStage / capStage / C_correctLO (a5b7ba5, ParCapBnd.lean).

## SPRINT UNITS (O): deletions and pruning, on the NEW layout (2a02149)
**PENDING the owner's OK on the deletion list (lead).**

Common rules for every unit:
- Source of truth: NANO_V2_DEADCODE.md. It uses the old module names; `python3 Testing/scripts/reorg_move.py --dry`
  maps them to the new paths.
- After every unit, rerun `Testing/scripts/deadcode.sh`. The reachable count must be unchanged (9640), and the
  `#print axioms` lines in Nano/V2Self/REVIEW.lean must be byte-identical.
- No proof edits beyond deleting declarations and import lines. Build only the touched modules plus REVIEW.
- One unit per agent. Each unit stays in its own folder, so units do not conflict.

| id | what | files (new paths) | check |
|---|---|---|---|
| O-D1 | delete F's abandoned certificate | `Proof/MainCert.lean`, `MainCertC0`–`C9`, `MainCertRules`, `MainPure`. FIRST: `Proof/Tests/AuditWitness.lean` imports MainCert; drop that import, or ask G | `lake build Nano.V2Self.Proof.Tests.AuditWitness Nano.V2Self.REVIEW` |
| O-D2 | delete superseded proof modules | `Proof/ParInvGlue.lean`, `Proof/ParLet.lean`, `Proof/Cert/Fun.lean` (12 GB, unused), `Proof/Bridge/MainConvX1.lean` (drop its import in MainConvX2), `Proof/Machine/StartAll.lean` (re-point GenRun / StartAllS to what they use, or inline `start_run` if it is used) | build the importers plus REVIEW |
| O-D3 | the old V2Self chain (OWNER CHOICE: delete or move to `Nano/V2Self/Legacy/`) | `Nano/V2Self/{Asm,Bridge,Driver,Expand,Inl,Lex,Parse}.lean`, `Nano/V2Self/C/{Asm,Expand,Inl,Lex,Main,Par0,Parse}.lean`, and the Testing scripts that import them: diff_test, chain_test, native_ref, sizes, cg_par, cg_chain, cg_witness, stage_dump | `lake build Nano` (the glob) has no missing imports |
| O-P1 | prune dead declarations in Parser/ (117 in 33 files; the big ones are ParInv 31, ParRunArgs 12, ParInvOps 7, ParSpec 7) | `Proof/Parser/*` | deadcode.sh |
| O-P2 | Machine/ (105 in 26 files: Templates 26, ExprEV 11, Call 9, Loop 6, Expr 5, StartRun 5) | `Proof/Machine/*` | deadcode.sh |
| O-P3 | Bridge/ + Main/ + SrcLink/ (29: MainOk 6, MainConvX2 4, MainConv8 3, SemX 3, …) | `Proof/Bridge/*`, `Proof/Main/*`, `Proof/SrcLink/SrcLink.lean` | deadcode.sh |
| O-P4 | Gen/ + Lex/ + Own/ (46: GenRef 8, GenAll 7, Lex2Sound 4, OwnP0 4, …) | `Proof/Gen/*`, `Proof/Lex/*`, `Proof/Own/*` | deadcode.sh |
| O-P5 | Cert/ (13: Rules 7, Specs 6). Specs.lean is GENERATED, so edit gen_cert.py, not the file. Coordinate with G | `Proof/Cert/Rules.lean`, `Testing/nano/v2self/cert/gen_cert.py` | regenerate, then deadcode.sh |

Caveat for the pruning units: a DECL-DEAD lemma may be used only by another DECL-DEAD lemma. Delete in reverse
dependency order and rebuild until `lake build` is green. A declaration used by a Tests/ file is not dead; keep it.
