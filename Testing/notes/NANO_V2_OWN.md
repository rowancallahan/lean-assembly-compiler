# NANO_V2_OWN: the ownership stage of C (box O)

## Why
Gen's BPUSH / BSET / PUT update buffers IN PLACE; `NanoMain.Sem` is pure.  `let b := bnew; let c := bpush b 7; put [] (bsize b)`
gave [1] (C) vs [0] (Lean) (NANO_V2_MAIN.md "FINDING", `alias_d`).  Fix: a stage between Par1 and Gen that rejects
non-linear buffer use.  Driver (build_self_S.py): `m x = g41 x (o41 (y16 (s10 x)))`.

## Spec: `OwnSpec.Linear p := ∃ Ks, progOk [] [] Ks p = true` (Nano/V2Self/Proof/OwnSpec.lean, on ParSpec.Nd)
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
slot used as a buffer makes its LOCAL source one; pairs keep source tags in mode 1), then VERIFY (mode 0 = `chk`).
Buffers: `s` registers + 8-word frames, `f` = K | dead flags | IF snapshots, `v` value entries, `t` def table
`[npw, nres, unused flags, P, R]`.  4 extra `bnew`s (16 MiB at κ = 2^19).
Python reference model: `Testing/nano/v2self/own_ref.py AST.bin [--verbose]` (same kinds as o41 on C's AST).
Debug: `lake env lean --run Testing/nano/v2self/own/own_dbg.lean AST.bin` (first failing def + walk state);
`own_run.lean` = accept/reject per file.

## Status (2026-11-19)
DONE: spec, S stage, pipeline; C's own source accepted; fixpoint B3 == B2 = 329,068 bytes,
sha256 42a2cd59c83e27d3adaa82bd1fe6a79745cc61977ba8cc5e12992be58f5a9e77 (o41 checks every field it uses < 2^20 and the AST < 2^40 words); alias_d + 5 aliasing programs rejected;
qemu_regress OK.  The checker caught a real slip in o38's first draft (read after consume).
NEXT: (1) soundness `C.o41 (serialize p) ≠ [] → WF p → Linear p` (WF: prim arities, numeric fields < 2^64; `Nd.ser`
is not injective otherwise); (2) kernel/#guard accepted example; (3) `ParsesProgram → WF`; (4) fuzz patterns in pargen.py.

## HANDOFF
See NEXT above.  D (Sem ⇐ sv bridge) builds on `OwnSpec` (MainBridge3/4).
