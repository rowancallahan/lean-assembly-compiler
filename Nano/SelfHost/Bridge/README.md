# Proof/Bridge — E's machine-level semantics vs the spec `Sem`

## Files
- `MainTy` — kind discipline (`TyN`/`TyB`, word/buffer) for resolved ASTs; progress: a well-kinded program never gets `stuck`.
- `MainOk` — kind judgment ⇒ E's side conditions `OkV`/`OkT` (reads known, let writes fresh, widths = kind counts).
- `SemX` — E's semantics with failure kind (`Fail`: cap/room/stuck); `toO`/`ofO` forget/add the kind.
- `MainBridge`, `MainBridge2..15` — forward bridge "E's `sv` succeeds ⇒ spec `Sem` succeeds, same result": 1 heap image `BufAt`; 2 ghost
  heap σ + value relation; 3 invariants `EnvI`/`ResI`/`Ch`; 4 `NodeOK`; 5 value transfer; 6 operands/IF; 7 LET; 8 arg lists;
  9 prims; 10 CALL against a callee contract `DefR`; 11 all nodes; 12 tail mode; 13 fuel loop; 14 one def; 15 program.
- `MainConv1..8` — converse "`Sem` succeeds ⇒ E succeeds given enough stack room": 1 sp-monotonicity; 2 existence; 3 prims/calls;
  4 tail; 5 loop; 6 def; 7 program; 8 uniform room bound (independent of work base and Gen's table T).
- `MainConvX1..7` — cap half: when `Sem` stops with `cap`, kinded E reports `cap` (same layering 1–7 as above).
- `MainConvF2..7` — failure kinds forward: any E failure is `room`, or `cap` with `Sem` capping there; never `stuck`.
- `MainConvG` — the converse in GenStage vocabulary (`gen_all`).
- `MainShift1..4` — shift invariance: E's outcome kind does not depend on where the 8-aligned work block lies (`ShiftInv`).

## Role
Import chain: `Proof/Main/Sem` → `MainTy` → `MainBridge*` → `MainConv*` → `MainConvX*` → `MainConvF*` → `MainConvG`; `SemX` feeds
`MainConvX1`, `MainShift1`, and `Machine/{CapRun,RunsShift}`. Users: `Machine/GenMain` (`main_bridge`), `Machine/SemCases`
(`MainConvG`/`MainConvX7`/`MainConv8`), `Main/TopOn`, `Main/RunsTopO`, `Tests/AuditSpace` (`MainShift4`).
Fed by `Parser/MainTyP` (kinds), `Own/OwnSpec`+`MainKeep` (ownership walk), `Machine/Nd*` (E's `sv`).

## Decisions
- The converse is split into success (Conv), cap (ConvX) and failure-kind (ConvF) so each file stays a per-node induction with one
  contract; one merged induction was not attempted (statements are used by name in `Machine/SemCases`).
- Callee contract `DefR`/`def_ok` is a hypothesis of the node induction and discharged once per def in `prog_ok` (strong induction
  on call depth), avoiding a mutual node/def induction.
- Room bound is made uniform over work base and T by `semAt_T` and a finite max (`MainConv8`), since `memoryNeeded` cannot depend on them.

## Main results (file:name)
`MainBridge15:main_bridge`, `MainBridge15:prog_ok`, `MainBridge14:def_ok`, `MainConv7:main_ex`, `MainConv8:main_room`,
`MainConvX7:main_cap`/`main_capR`, `MainConvF7:main_kind`/`main_all`, `MainConvG:gen_all`, `MainShift4:shiftInv`.
Assumptions: parsed program with kinds (`TyProg`), ownership check `chk` (via `Own`), input size ≤ 2^20; no axioms beyond the pinned ones.

## Check
`lake build Nano.SelfHost.Bridge.MainConvG Nano.SelfHost.Bridge.MainShift4`; full: `lake build` and `Testing/scripts/review_axioms.sh`.

## Limits
Kinds are only `w`/`b`; a new node kind needs a case in every layer (Bridge, Conv, ConvX, ConvF, Shift). Dead-declaration sweep done
(`SemX.toO_err` kept: `@[simp]`).
