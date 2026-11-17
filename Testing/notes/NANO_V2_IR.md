# NANO_V2_IR: frozen intermediate formats for C compiling S (version 1, proposal pending the Opus box's reply)

All stage outputs are `Buf`s of 64-bit words (the lexer's `q0` writes bytes; later stages may write full words). Each stage's output starts with the word `IRV = 1` (version) followed by the stream; a stage that meets a tag/form it does not support
outputs the EMPTY Buf (reject). Differential harness: `Testing/nano/v2self/` decoders in plain Lean (to be written per stage).

## Stage 0 → 1: token stream (DONE, `Nano/V2Self/C/Lex2.lean`, `lex2_test.lean`)
Tags: def 1, let 2, UInt64 3, Int64 4 (reserved, parser rejects), number 5 + 8 LE bytes, `(` 6, `)` 7, `:` 8, `:=` 9, `+` 10, `-` 11, `*` 12, `;` 13, ident 14 + (1,byte)* + 0, `,` 15, `×` 16, `→` 17, `|` 18, `=>` 19, `<` 20, `≤` 21, `≠` 22, `==` 23, `&&` 24, `||` 25, `&&&` 26, `|||` 27, `<<<` 28, `>>>` 29, `[` 30, `]` 31, `if` 32, `then` 33, `else` 34, `Nat` 35, `Buf` 36, `List` 37, `UInt8` 38. (Tokens are bytes, not versioned; empty = reject.)

## Stage 1 → 2: parser output = flat PRE-ORDER AST (version 2, replaces the postfix/inliner design after Astra 8: no inliner, real calls)
Word buffer: `IRV=2`, then the defs in source order (callees before callers, the front end already guarantees it); def id = index. Per def: `DEF id nparams nslots kind` (kind 0 plain, 1 fuel loop, 2 constant), the body node, `ENDDEF`.
Every node = a tag word followed by its operands; child nodes follow in order (pre-order, arity fixed by the tag, so a consumer needs only a stack). Locals: `slot` = frame slot index (params 0..nparams-1, then one slot per `let`/split/loop-state variable, never reused; a pair/tuple variable occupies n consecutive slots, first component lowest).
- `CONST v` | `LOCAL slot` | `BIN op a b` (ops add 1 sub 2 mul 3 and 4 or 5 shl 6 shr 7; shifts carry a CONST k as `b`) | `IF cmp a b t e` (cmp: eq 1, lt 2; the source has no other conditions)
- `LET slot v body` | `PAIR n c1..cn` (builds an n-tuple) | `SPLIT n slot1..slotn v body` (`let (a, b) := v`)
- `CALL id n a1..an` (arguments flattened by the callee's parameter widths; result in the caller-provided slots) | prims `RD x i`, `LEN x`, `PUT o b`, `BNEW`, `BSIZE b`, `BGET b i`, `BSET b i v`, `BPUSH b v` as `PRIM p args…` (p = 1..8 in that order)
- loops (fuel recursion recognised by the parser, one per `Nat →` def): the def body is `LOOP n s1..sn init1..initn fuel zero step` where `s_j` are the state slots (the params), `fuel` = `LENF` | `CONST k` | `FADD a b` | `FMUL a b`, `zero` = body of the `0` arm, `step` = body of the `f + 1` arm in which every tail self-call is `CONTINUE n e1..en` (new state computed from the OLD state, then committed: parallel assignment; the fuel decrements) and every other tail leaf is its result; a self-call anywhere else, or a self-call with the wrong arity, rejects.
Rejected (the stage outputs the EMPTY Buf): any token outside Nano/V2Self/C's restricted set (Int64, `&&`, `||`, `≤`, `≠`, `>`, `match`, general `Nat`), undefined names, a use before definition, non-tail recursion, a tuple width mismatch.
Expander+assembler are fused (Opus box): they read this AST and emit machine code with a fixed frame per def (fp-relative slots, saved ra/fp), a memory expression stack, short inverted branch over a fixed-size long `jal`, call = fixed-size `jal`.
