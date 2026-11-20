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

## SPRINT UNITS (O): pruning, on the layout after the cleanup (4d17b0a)
The owner APPROVED the cleanup.
- O-D1 is DONE (5024388). F's MainCertC0–C9, MainCertRules and MainPure are deleted. MainCert holds the Ex1/Ex3
  example certificates used by AuditWitness, so it is kept as `Proof/Tests/MainCert.lean`.
- O-D2 is DONE (5024388). ParInvGlue, ParLet, Cert/Fun and Machine/StartAll are deleted, along with
  `GenRun.gen_run`, StartAll's only user. Bridge/MainConvX1 is KEPT: E's RunsDef uses `semAtF_mo`.
- O-D3 is DONE (4d17b0a). The old chain is in `Nano/V2Self/Legacy/` and `Legacy/C/`, and its 8 Testing scripts are
  re-pointed.

Pruning units: 324 unreachable declarations in live modules. The full list is in NANO_V2_DEADCODE.md §4, with new
module names.

Common rules for every unit:
- Roots: `Testing/scripts/deadcode.lean` (all REVIEW theorems plus every Proof/Tests declaration).
- After the unit, `Testing/scripts/deadcode.sh` must report `REACHABLE 39729` (or the count at your start), and REVIEW's
  `#print axioms` lines must be byte-identical.
- Only delete declarations and now-unused imports. Delete in reverse dependency order, because a dead lemma may be used
  only by another dead lemma.
- Build the touched modules plus `Nano.V2Self.REVIEW`. One folder per agent, so units do not conflict.

| id | folder | dead decls (files) | largest | build check |
|---|---|---|---|---|
| O-P1 | `Proof/Parser/` | 115 (34) | ParInv 31, ParRunArgs 12, ParInvOps 7, ParRunTy 5, ParRep 4, ParRunCallSpec 4 | touched modules + REVIEW |
| O-P2 | `Proof/Machine/` | 105 (26) | Templates 26, ExprEV 11, Call 9, Loop 6, Expr 5, StartRun 5 | touched modules + REVIEW |
| O-P3 | `Proof/Bridge/` + `Proof/Main/` + `Proof/SrcLink/SrcLink.lean` | 45 (23) | MainOk 6, MainConvX2 4, MainConv8 3, MainShift3 3, MainShift4 3, SemX 3, Main 3 | touched modules + REVIEW |
| O-P4 | `Proof/Gen/` + `Proof/Own/` + `Proof/Lex/` | 46 (20) | GenRef 8, GenAll 7, OwnP0 4, Lex2Sound 4, OwnP28 3, Fixup 3 | touched modules + REVIEW |
| O-P5 | `Proof/Cert/` | 13 (2) | Rules 7, Specs 6. **Specs.lean is GENERATED**: change `Testing/nano/v2self/cert/gen_cert.py`, regenerate, and coordinate with G | All.lean + REVIEW |
