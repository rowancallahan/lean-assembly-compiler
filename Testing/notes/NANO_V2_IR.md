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

## Status of the parser (increment A, `Nano/V2Self/C/Par0.lean`, test `Testing/nano/v2self/par0_test.lean`)
Implemented: `def f (a b : UInt64) (c : UInt64) : UInt64 := EXPR`, EXPR = literals, parameters, parentheses, `|||` `&&&` `+ -` `*` `<<<` `>>>` with Lean precedences (55 60 65 70 75, left assoc; shift rhs = numeral).
Output words: `2 (IRV), 20 (DEF), 0 (id), nparams, nslots, 0 (kind), pre-order nodes, 21 (ENDDEF)`; node tags in use: CONST 1 v, LOCAL 2 slot, BIN 3 op (add 1 sub 2 mul 3 and 4 or 5 shl 6 shr 7) a b. Reserved for the next increments: IF 4, LET 5, PAIR 6, SPLIT 7, CALL 8, PRIM 9, LOOP 10, CONTINUE 11.
Test: 3000 random trees printed with minimal parentheses, lexed, parsed, decoded and evaluated: 0 mismatches; 6 rejection cases (dangling operator, unclosed paren, unknown name, shift by a variable, trailing token, Int64) give the empty Buf. Accepted by `frontElab` (13 defs).
Front-end rules learnt (they shape all later parser code): def/variable names are ONE letter + digits (`tt`, `np`, `ok` are rejected); a Buf passed as a loop argument is MOVED into the loop (a second loop on the same Buf after the first is rejected), so the parser keeps tokens AND working memory in ONE heap Buf `h` (tokens copied to 40000.., size at h[7]) and threads only `h`; reads of `h` are let-bound before `h` is consumed; more than one non-Buf argument is fine.
Capacity note: the heap is 40000 + tokens words (≈ 76k for the S text): κ = 65536 is too small for the parser; use κ = 2^17 (+ the later stages' buffers).

## IR v2.1 (agreed with the Opus box, 2026-11-17): changes to the stage 1 → 2 format above
`DEF id npw nslots kind nres` (npw = parameter WORDS, nslots = frame words, params first, nres = result words); `LOCAL slot w` (w words; a pair is w consecutive slots, first component lowest);
no `SPLIT`: `let (a, b) := v` = `LET slot w v body` with a at `slot`, b at `slot + width a` (the parser maps names to (slot, width)); `PAIR n c1..cn` as before;
`CALL id n a1..an` (n argument EXPRESSIONS, total width = callee npw, result nres words); a fuel def has the fuel as PARAM slot 0, state params after, body `LOOP zero step`, `CONTINUE e` (e of width npw-1);
the call site passes the fuel as an ordinary first argument (`len' x` = `PRIM ISIZE`, `+ *` numerals = BIN/CONST): no LENF/FADD/FMUL; a read-only Buf param of a loop is a state word passed through by CONTINUE;
prims: `ISIZE`, `RD i`, `LEN x`, `PUT o b`, `BNEW`, `BSIZE b`, `BGET b i`, `BSET b i v`, `BPUSH b v` (source order; `[]` = BNEW); `IF cmp a b t e` (eq 1, lt 2 unsigned).
Par0 already emits this header (`... npw nslots 0 1`) and `LOCAL slot 1`.

### Parser increment B (cmp + if) done: `IF cmp a b t e` = tag 4 (cmp eq 1 / lt 2, then the four children in pre-order); `if A == B then T else E` / `<`; branches are full expressions (greedy, Lean's dangling-else), the condition operands are expressions that stop at `==`/`<`/`then`.
Node records are now 8 words (nodes at 10000 + 8 i, flatten stack at 30000, tokens at 40000); capacity grows with the language (the real source has ~tens of thousands of nodes: the layout constants move to a table before the whole-source run).
Test `par0_test.lean`: random trees now include `if` (300 trees, 0 mismatches), rejections of `if a then …`, missing `else`, missing `then`.

### Numeric tags: FINAL = the Opus box's table in `NANO_V2_CG.md` (CONST 1, LOCAL 2, BIN 3, IF 4, LET 5, PAIR 6, CALL 7, PRIM 8, LOOP 9, CONTINUE 10, DEF 11, END 12; prims ISIZE 1 … BPUSH 9). No more changes.
