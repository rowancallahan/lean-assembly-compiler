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
