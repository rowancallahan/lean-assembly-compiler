# NANO_V2_OWN: the ownership stage of C (box O)

## Why
Gen's BPUSH / BSET / PUT update buffers IN PLACE; `NanoMain.Sem` is pure.  `let b := bnew; let c := bpush b 7; put [] (bsize b)`
gave [1] (C) vs [0] (Lean) (NANO_V2_MAIN.md "FINDING", `alias_d`).  Fix: a stage between Par1 and Gen that rejects
non-linear buffer use.  Driver (build_self_S.py): `m x = g41 x (o41 (y16 (s10 x)))`.

## Spec: `OwnSpec.Linear p := ∃ Ks, progOk [] [] Ks p = true` (Nano/V2Self/Proof/Own/OwnSpec.lean, on ParSpec.Nd)
* KINDS (existential, per def, static per slot): 0 word, 1 owned buffer, 2 read-only buffer (a borrowed param).
  Params = `K.take npw`; let slots: value kinds = slot kinds; CALL args fit the callee param kinds; CONTINUE payload fits
  the state kinds ⇒ "K s = 0 ⇒ the slot holds `.w`" is an invariant of `NanoMain.ev` (no scoping assumption).
* WALK `chk : Cx → Nd → flags → Option (flags × entries)` in `ev`'s order, dead flags per slot.  Entries: plain kind 0/1,
  or a LOCAL word `k + 4 (s + 1)`; the parent decides: TRANSFER (`tr`: owned ⇒ must be live, becomes dead; read-only ⇒
  reject) for let values, branch / let-body / def results; ARGUMENT LISTS (BIN/IF operands, pair fields, CALL/PRIM args,
  CONTINUE payload) check each argument against its destination (`dest`: 0 word, 1 owned, 2 borrow, 3 read-only only)
  and PIN direct LOCAL args: consumed (dest 1) / re-checked live (dest 2) only after all arguments (`fin` = `finC`, then
  `finB`).  `if` branches from the same flags, union of deaths; `let` bodies, branches, loop arms are transferred (only a LOCAL
  node returns tagged entries).  A LOOP only as the def body; arms start all-live.
* Rejected: `f b b`, `bset b 0 (bsize (bpush b 1))`, `let c := bpush b 7; … b …`, a read-only param transferred.
  Accepted: `f h (bget h 0)`, `v205 16777216 h …` then `h` again (v205's `h` is read-only).

## Implementation: `C.o41` (Nano/V2Self/C/Own.lean, S subset, ~45 defs `o0..o41`)
Per def: kind INFERENCE (mode 1, unverified heuristic) = rounds of the same walk until no change (params start "unused"
3; strong evidence = prim buffer args / owned callee params / owned states; an unused param ends read-only; a let
slot used as a buffer makes its LOCAL source one; pairs keep source tags in mode 1), then VERIFY (mode 0 = `chk`).  Inference is a black box for the proof: it runs on its own s / f / v; verify runs on
separate buffers a / b / c (3 more bnews, so self-compile needs 80 MiB of work memory, was 64) and reads only the
inferred kinds f2[0, n), clamped to ≤ 2 (o42).  The cursor and def count live in a.
Buffers: `s` registers + 8-word frames, `f` = K | dead flags | IF snapshots, `v` value entries, `t` def table
`[npw, nres, unused flags, P, R]`.  4 extra `bnew`s (16 MiB at κ = 2^19).
Python reference model: `Testing/nano/v2self/own_ref.py AST.bin [--verbose]` (same kinds as o41 on C's AST).
Debug: `lake env lean --run Testing/nano/v2self/own/own_dbg.lean AST.bin` (first failing def + walk state);
`own_run.lean` = accept/reject per file.

## Status (2026-11-19)
DONE: spec, S stage, pipeline; C's own source accepted; fixpoint B3 == B2 = 337,856 bytes,
sha256 bb5558a58c98b13ec24ad36e2147a41ff37a3b32debbe9d08523831266e0ec4e (self-run work memory 80 MiB; with the parser width cap) (o41 checks every field it uses < 2^20, the AST < 2^40 words, value stack < 2^24, frames / snapshots < 2^30); alias_d + 5 aliasing programs rejected;
qemu_regress OK.  The checker caught a real slip in o38's first draft (read after consume).
PROOF DONE (Nano/V2Self/Proof/OwnP0..OwnP30, OwnStage, OwnNV; std axioms, no sorry):
* `OwnP.o41_sound : (∀ d ∈ p, WFD d) → |serialize p| < 2^64 → o41 (serialize p) ≠ [] →
  ∃ Ks, progOk [] [] Ks p ∧ ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2` (= Main.LinearK).
* `OwnP.own_stage : ParsesProgram ts p → OwnWF.Bnd p → |serialize p| < 2^64 → o41 (serialize p) ≠ [] → LinearK`
  (WF from C's `OwnWF.parsed_wfp`).  The two size premises are NOT derivable from o41: `serialize` writes fields mod
  2^64, so a wrapped nslots / slot / AST length is invisible to it.  Bnd (nslots < 2^20, nres, |p| < 2^64) comes from
  Gen's success (nslots, nres < 251); |serialize p| < 2^64 from the source size (x ≤ 2^20 bytes).
* Non-vacuity: `OwnNV.pOk_acc` (`decide +kernel`, 2 s) → `pOk_linear`; `#guard` alias_d-shaped `pAlias` rejected.
Proof map: P8 Reach/steps · P9-P20 frame steps per node kind · P21 `sim_all` (all nodes) · P22 root LOOP · P24 fuel ·
P25 root body · P26 `o35_ok` (one verify walk) · P27-P29 table, o42, `o38_ok` · P30 `o39_ok`, `o41_sound`.
OPEN: completeness gap (fuzzer: let-pair over a let-block of Bufs rejected); RG's semrun driver (owner request).

## HANDOFF
See NEXT above.  D (Sem ⇐ sv bridge) builds on `OwnSpec` (MainBridge3/4).

## WIDTH CAP (2026-11-19, O; soundness fix found by D)
Doubling lets `let a(i+1) := (a i, a i)` reach nslots ≥ 2^64 in ~1.6 KB, which `serialize` wraps.  Now:
* Par1 (C): v10 rejects a pair shape of width ≥ 2^20 (new or found row); v116 / v117 (lets), v133 (binders), v136 (loop states)
  reject a slot allocation reaching 2^20.
* ParSpec.pDef: `nslots < 2^20 ∧ res.width < 2^20` (both branches).  ParRun mirrors every Par1 check (Nat) plus the def-end check.
* `ParRunSmall`: Layer-2 invariant `Small` (nx, npw, every stored shape < 2^20) for all reachable states; the Layer-3 handlers
  (letSemi, letPairSemi, assign, stateTy, tyPair, mkPair, defEnd) use it to show Par1's 64-bit checks equal ParRun's.
  `ParInv.parserSound` stays proved (std axioms).
* Regression: Testing/nano/v2self/parcap/cap_test.lean (#guard: Par1 accepts k = 19, rejects 20, 63) and cap_regress.py
  (B1 and the self-compiled B2 reject k = 63, agree on k = 2).
* Downstream: ParSerLen / MainTyP (D) adapted; Proof/Cert/PC.lean regenerated (gen_cert.py), all tracked Cert files build;
  MainCertC3/4/5 (abandoned, unimported) left failing per the lead.
