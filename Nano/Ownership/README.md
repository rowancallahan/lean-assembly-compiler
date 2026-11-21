# Proof/Own — soundness of the ownership stage `C.o41`

**What / where.** `C.o41` (Nano/Ownership/Own.lean) runs between the parser and Gen. Gen's BPUSH/BSET/PUT update buffers in place, so a program must use each buffer linearly. `o41` accepts only such programs; this folder proves **accepted ⇒ `Linear`** (spec: Testing/notes/NANO_V2_OWN.md). Used by Proof/Bridge (MainBridge3) and Proof/Tests/OwnNV.

## Files
- `OwnSpec.lean` — the discipline: `Linear`, `progOk`, `chk`, `dest`, `join`, `okAll`, … (pure Lean, no machine).
- `OwnWF.lean` — well-formedness of parser output (`NdAr` PRIM arities, `Bnd` size bounds).
- `OwnP0–P1` — word arithmetic (`u n`, `uw` simp set); walk-state representation (`AS`, `WCx`, `Fr`, `RS/RF/RV/RT`).
- `OwnP2–P7` — leaf loops/passes of `o41` each equal to an `OwnSpec` function (dest, ok1/okAll, finC/finB/strip, entry pushes, flag loop `o22`, join, let check).
- `OwnP8–P22` — one walk step per frame kind (phase 0/1/2, pops, finishes, IF/LET/LOOP, list nodes), then each node = `OwnSpec.chk`.
- `OwnP23–P26` — `o34` walk loop vs `Reach`; def body = `defOk`.
- `OwnP27–P30` — def-level buffer loops, def table, flags buffer `o42`, program loop `o39` and stage `o41`.
- `MainKeep.lean` — static facts (only owned slots are killed) for read-only liveness.
- `OwnStage.lean` — final theorem.

## Decisions
- Spec is a separate pure function over `DefA`; the machine code is proved equal to it piecewise, so each step lemma is a local simulation (alternative: one monolithic run proof — rejected, too costly to check).
- Numbers are `UInt64` words; `serialize` wraps mod 2^64, so size bounds `Bnd` and `|serialize p| < 2^64` are premises.
- `Reach W σ P`: finitely many `o30` steps ending in P or the error flag — gives soundness without termination bookkeeping.

## Main results
- `OwnStage.lean:own_stage` — `ParsesProgram ts p`, `OwnWF.Bnd p` (and the serialization bound) ⇒ `o41` accepting ⇒ `LinearK`.
- `OwnP30.lean` — program-loop/stage lemma it builds on; `OwnP8.lean:Reach`.

## Check
`lake build Nano.Ownership.OwnStage`; whole repo: `lake build`, then `Testing/scripts/review_axioms.sh` ("OK: 8 theorems, axioms as pinned").

## Limits
Soundness only (accepted ⇒ linear); completeness is not proved. Bounds on nslots/nres (< 251) and serialization length are assumed, discharged by Gen/Bridge. OwnP* are hand-written (not generated).
