# Astra round 14 — proving Par1 sound on success (ADVICE; owner may override)

Relayed advice, not owner decisions. Skeleton: `NANO_V2_ASTRA14_Skeleton.lean` (type-checks on our Lean 4.29; axioms: propext).

Coordinator note: ParSpec currently DEFINES `ParsesProgram ts p` as `refParse ts = some p` with a fuel bound, so per B.1 budget
adequacy would be a real premise. DECISION (coordinator, owner may override): make `ParsesProgram` an independent inductive
grammar judgment (no fuel); prove the easy lemma `refParse ts = some p → ParsesProgram ts p`; aim the parser proof and Main.lean at
the judgment. refParse stays for differential testing.

Key points:
- Layer 2 target: a SUCCESSFUL run from init yields a reference parse (reflection direction). Do not equate all failures.
  Define the logical step relation as the graph of a pure deterministic dispatcher; Run = finite paths (`Path`). Frames describe
  unfinished reference operations; several machine codes may implement one frame op; pure bookkeeping steps = empty path.
- Keep Rep LOCAL. Reachability comes from composing paths from init (parserSound skeleton), not from a standalone Inv.
  A `Cont` with `isSome` loses the program witness — keep the witness.
- Cursor: index by the actual token encoding (suffix/split witness; machine cursor = encoded prefix length; EOF sentinel outside).
- Preservation guarded on machine success: running→running gives a finite abstract path; accepting step has its own lemma;
  reject/exhausted needs only "cannot return nonempty output". Don't claim equal rejection behaviour.
- Per reference entry: a delimited successful call-segment judgment (ghost delimiter on caller's suffix; returns exactly once,
  never runs caller frames); one reflection lemma per entry by induction on the segment; BIN: q ≥ minp → RHS at q+1, reduce,
  resume at original minp; terminator leaves lookahead; shift-literal fast path separately. Machine induction on v97 fuel only.
- Arena: NodeRep via child chain. TreeAt(i) reads record + children's sibling links but NOT i's own next-sibling word;
  Children(first,count) reads count roots + count−1 links. Local frame lemma: equality on the dynamic read set transports.
  Track live ids below the allocation cursor. Fresh occurrences / disjoint subtrees as the forest invariant.
- Pending bit ≠ shape: a mixed if (value branch + provisional branch) — check against v118/v209 before identifying pending with
  Ty.bot. State v209 as explicit facts, don't assume "inputs valid" in Rep.
- Def reset: at ENDDEF clear the forest, existentially forget the old arena, keep finished words/signatures. Flatten invariant:
  emitted ++ serialization of pending forest = intended serialization; IRV emitted once; header/ENDDEF phases separate.
- Order: one vertical slice first — nested let + binary precedence + tail-enabled if under parens used as a binary operand
  (success, forbidden pending operand, relinking, continuation enqueue), then flatten across a two-def reset. Re-estimate after.
