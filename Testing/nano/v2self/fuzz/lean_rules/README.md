# lean_rules: differential harness against real Lean 4.34.1 (see Testing/notes/LEAN_RULES.md)
* `diff.py DIR`: for every DIR/*.lean (nano program, optional `-- input (hex): ..`) runs real nano (B2.bin via nanorun) and real Lean
  (`import Nano.Main.Prelude` + program + `#eval m input`); prints same / NANO-ACCEPTS-LEAN-REJECTS / RESULT-DIFF / nano-stricter.
* `gen_trivia_ops.py`, `gen_match_defs_ns.py`: the hand-written case batteries (write DIR/*.lean); `rnd_expr.py SEED N`: random expression programs.
* `toks.lean` + `kwscan.py`: Lean's identifier-like token table and which of those Lean rejects as a name; `lean_reserved_words.txt` (190 words),
  `nano_accepts_reserved.txt` (168 of them nano lexes as an ordinary name).
* `spec_verdict.lean`: spec-level verdict (LexSpec -> DsSpec -> ParSpec) for a directory of programs (needs the oleans of those modules).
Paths are hard-coded at the top of each script. Lean files need `Nano.Main.Prelude` (rd, put, len', Buf, bnew, ...) as real Lean definitions.
