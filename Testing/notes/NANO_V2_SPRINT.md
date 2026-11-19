# NANO v2 sprint units

## SPRINT UNITS (D)

D's converse (A) is complete: main_room, main_capR, main_all, gen_R/gen_all in MainConv8/X7/F7/G. What is left in D's
area depends on O's parser width cap (ParSpec.pDef: `2^20 ≤ nslots ∨ 2^20 ≤ res.width → none`). D will take these
itself if O's push lands before 23:10 UTC; otherwise they are sprint units.

### D-S1 (only if O's cap is pushed and ParSerLen is still broken at 23:10)
- File: `Nano/V2Self/Proof/ParSerLen.lean` (edit; nobody else edits it).
- Goal: make the file build again against the capped `ParSpec.pDef`. The statements stay as they are:
  `theorem ParSerLen.ser_len {ts : List UInt64} {p : List DefA} (h : ParsesProgram ts p) : (serialize p).length ≤ 4 * ts.length + 1`
  `theorem ParSerLen.ser_lt … (hts : ts.length < 2 ^ 24) : (serialize p).length < 2 ^ 31`
- What breaks: `pDef_len` walks `pDef`'s `split`/`Option.bind_eq_some_iff` chain; the cap adds one `if … then none`
  per branch. Add one `split at h; · cases h` at each new `if` (both the loop and the plain branch), nothing else.
- Model: the existing `pDef_len` proof in the same file.
- Build: `lake build Nano.V2Self.Proof.ParSerLen` (≈ 4 s). Deps: O's ParSpec push.

### D-S2 (only if O's `parsed_bnd` is pushed)
- File: NEW `Nano/V2Self/Proof/MainBnd.lean` (imports `Nano.V2Self.Proof.MainTop` and O's file with `parsed_bnd`).
- Statements:
  `theorem NanoMain.bndStage : NanoMain.BndStage`
  (`BndStage := ∀ c ts p, ParsesProgram ts p → ts.length < 2 ^ 24 → C.g41 c (serialize p) ≠ [] → BndP p`;
  `BndP p := p.length < 2 ^ 64 ∧ ∀ d ∈ p, d.nslots < 2 ^ 20 ∧ d.nres < 2 ^ 64`, defeq to `OwnWF.Bnd`)
  `theorem NanoMain.C_correctG (HG : NanoMain.GenStage) : CompileCorrectL riscv compileC := NanoMain.C_correctL bndStage HG`
- Proof: `fun _ _ _ hp hts _ => (parsed_bnd hp hts).1` (adjust to O's exact statement).
- Build: `lake build Nano.V2Self.Proof.MainBnd` (MainTop ≈ 12 s). Deps: O's `parsed_bnd`.

## SPRINT UNITS (E)
None. GenStage is assembled (`SimW.gen_stage`, GenStageE.lean, b3b101b), modulo O's `HDB` (∀ d ∈ p, DB d for accepted programs). The room primitives and the OOM stub are done (RoomRun, CapHost).

## SPRINT UNITS (O)
None.  Done before the sprint: parser width cap (ea78be9; Layer-2 width invariant = ParRunSmall, parserSound proved),
DBPar adaptation (bd41e7d), parsed_cap / parsed_bnd / bndStage / capStage / C_correctLO (a5b7ba5, ParCapBnd.lean).
