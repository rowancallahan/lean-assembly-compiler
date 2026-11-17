# NANO_V2_IR: frozen intermediate formats for C compiling S (version 1, proposal pending the Opus box's reply)

All stage outputs are `Buf`s of 64-bit words (the lexer's `q0` writes bytes; later stages may write full words). Each stage's output starts with the word `IRV = 1` (version) followed by the stream; a stage that meets a tag/form it does not support
outputs the EMPTY Buf (reject). Differential harness: `Testing/nano/v2self/` decoders in plain Lean (to be written per stage).

## Stage 0 → 1: token stream (DONE, `Nano/V2Self/C/Lex2.lean`, `lex2_test.lean`)
Tags: def 1, let 2, UInt64 3, Int64 4 (reserved, parser rejects), number 5 + 8 LE bytes, `(` 6, `)` 7, `:` 8, `:=` 9, `+` 10, `-` 11, `*` 12, `;` 13, ident 14 + (1,byte)* + 0, `,` 15, `×` 16, `→` 17, `|` 18, `=>` 19, `<` 20, `≤` 21, `≠` 22, `==` 23, `&&` 24, `||` 25, `&&&` 26, `|||` 27, `<<<` 28, `>>>` 29, `[` 30, `]` 31, `if` 32, `then` 33, `else` 34, `Nat` 35, `Buf` 36, `List` 37, `UInt8` 38. (Tokens are bytes, not versioned; empty = reject.)

## Stage 1 → 2: parser output = postfix stream per def (words)
Defs in source order; ids = def index (0-based). Header `DEF=1, id, nparams, kind` (kind 0 plain, 1 fuel loop, 2 constant), body, `ENDDEF=2`.
Body tags (operands follow): `LIT=3 v` | `VAR=4 d` (d = distance from value-stack top at that point; 0 = top) | `BIN=5 op` (ops: add 1, sub 2, mul 3, eq 4, lt 5, and 6, or 7, xor 8 (reserved), shl-k 9 `k`, shr-k 10 `k`; `≤`/`≠`/`&&`/`||` never appear: the parser desugars them)
| `LET=6` (pop value, push as local) … `ENDLET=7 n` (drop n locals, keep result) | `SPLIT=8 n` (pop an n-tuple, push its n components, FIRST component deepest) | `TUP=9 n` (pop n values, push an n-tuple = n adjacent slots) |
`IF=10` cond-stream (leaves 0/1 from `eq`/`lt` only) `THEN=11` t `ELSE=12` e `FI=13` | `CALL=14 id n` | prims `RD=15 LEN=16 PUT=17 BNEW=18 BSIZE=19 BGET=20 BSET=21 BPUSH=22` (operands on the stack in source order) | `LENF=23` (fuel `len' x`) |
loops: the def with kind 1 has body `ZERO=24` z-stream `SUCC=25` s-stream; inside s-stream the tail self-call is `NEXT=26 n` (n new state values already pushed in parameter order = parallel assignment: all computed from the old state first, then stored), every other tail position ends in `EXIT=27` (result on the stack). Non-tail self calls are rejected.
Locals: de Bruijn distances (VAR d) so a body is position-independent; an inlined copy rebases only the args' VARs (arg j is evaluated at depth + j).
Parameter order: first parameter deepest. Reserved/rejected: Int64, `match`, `fun`, `.1/.2`, `Array`, strings, hex.

## Stage 2 → 3: inliner output
Same stream, no `CALL`, defs reduced to the last def (`m`); loops that were callees appear as `LOOP=28 n_state` block: `LOOP n` init (state pushed) `ZERO` … `SUCC` … `ENDLOOP=29` with `NEXT`/`EXIT` as above, inlined copies renumbered by position (labels are assigned by the expander from block nesting, so copies need no fresh names in this stream).

## Stage 3 → 4 → 5: expander / assembler output
Expander: instruction records of `Nano.V2B.I` (Nano/V2/Gen.lean) with the offset/label resolution; assembler: the encoding `I.enc` as little-endian bytes = the final machine code. These two stages follow `cE/cT/SC.flat/genI` instruction by instruction (Opus box); the jal range fix lives there.

Growth order (Astra 7): literals+arith, cmp+if, pairs, buffers, loops, remaining spellings; one tiny example + a rejection test + a differential test per step.
