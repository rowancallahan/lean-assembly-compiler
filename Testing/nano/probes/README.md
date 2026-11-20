# Front-end probes for the self-hosting of `genR` / `nanoElab` (NOT part of the lake build; each file is one `frontx_compile`)
Run: `lake env lean Testing/nano/probes/<file>.lean` from the repo root (3-30 min each).
* `asm_7clauses_ok.lean`: the 10-op assembler (every `if`-chain macro has at most 7 clauses): accepted.
* `asm_8clauses_fails.lean`: the same plus one op that adds an 8th clause to `X1`: `frontx: could not prove` (an `rfl` obligation on the
  `BExp.denote` of the chain). Each of the ops 9..13 added alone to the 10-op version fails (each makes a chain longer than 7 clauses: `X1` gets 8); op 14, which adds no clause to `X0`-`X2` and one to `X3` (7), passes. The hypothesis "at most 7 clauses per chain" is confirmed by the redesigned 15-op `Legacy/Nano/Asm.lean` (7/4/3/6 clauses), which compiles.
* `token_machine.lean`: what `genR` would have to be as a byte machine: tokens `(tag, arg)` expand to up to 5 records (20 bytes) with a depth
  scalar `d` threaded through the recursion. Does not finish (killed after 25 min of CPU with `maxHeartbeats 0`, cf. TINYSELF.md item 5: 8 arms of 12-byte
  chains, 44 variables / 36 slots, 388 obligations, abandoned): constant cons chains cost variables and obligations per byte.
See `Testing/notes/NANO.md` "Self-hosting status".
