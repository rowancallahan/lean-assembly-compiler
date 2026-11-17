# NANO_V2_CHECKPOINT: the nano compiler as nano-subset source (owner review before the self-hosting decision)

Branch `nano-v2-src` (merged with origin/main and origin/nano-v2 at eccd515). Folder `Nano/V2Self/`. No sorry, no new
axioms (Bridge/Driver: propext, Quot.sound). Everything below was run here with `Testing/nano/v2self/check.sh`
(`lake build Nano.V2Self.Driver`, the front-end acceptance script, the differential test); each module builds in < 10 s.

## Files and acceptance by nano's own front end (`frontElabK 256`)

| file | stage | lines | defs | accepted by `frontElab` |
|---|---|---|---|---|
| `Prelude.lean` | primitives (`rd len put len' Buf bnew bsize bget bset bpush`) | 16 | – | (the front end's built-ins) |
| `Asm.lean` | assembler (`a5`) | 65 | 22 | YES |
| `Expand.lean` | expander (`e2`) | 28 | 3 | YES |
| `Lex.lean` | lexer + 2a (`l15`) | 110 | 17 | YES |
| `Inl.lean` | inliner, tail-only with a buffer table (`j8`) | 59 | 10 | YES |
| `Parse.lean` | parser 2b (`r16`) | 275 | 34 | YES |
| `Bridge.lean`, `Driver.lean` | proofs / Lean-level chain | 32 / 25 | – | not nano source |

Total stage source: 537 lines (about 24 kB). Names are one letter + digits (`a0..a5`, `e0..e2`, `j0..j8`, `l0..l16`, `r0..r18`,
constants `k*`, `w*`); no `namespace`/`open`/hex/ascriptions/`_`; `;` after each `let`; `len'` for fuel; defs only.
Script: `lake env lean --run Testing/nano/v2self/check.lean FILE...` strips comments/imports, appends a stub `m`, and on
reject adds the defs one by one and prints the FIRST rejected def (files are checked in order, later files see earlier defs).

**All five stages are accepted.** `bpop` is not in the language (decision of the language box and the main session); the parser's scope
and frame stacks carry a top index (`i0`, `m0`) next to the `Buf`: push = `bset` below `bsize` else `bpush`, pop = lower the index.
The state tuple has 15 components. The Lean meaning differs from the V2S stack (`dropLast`) only in dead slots above the top, never read.

## The chained driver (`Nano/V2Self/C/`, Lean namespace `C`, stripped by the acceptance script)
Stage 1 (`l15`) reads the program input and writes a `Buf`; stages 2-5 (`r16`, `j8`, `e2`, `a5`) read the previous `Buf` (`bget`/`bsize`)
and write a `Buf` (`q0 o v` = `bpush o (v &&& 255)`, the meaning of `put`); `m` chains them and `m1` copies the last `Buf` to `put`.
Fuel of stages 2-5 is the numeral 16777216 (they stop on their own conditions). `chain_test.lean`: `C.m = chainS` on 6 good sources and
3000 random strings, 0 mismatches. Acceptance (frontElab, with origin/nano-v2 d19fe00 loop borrowing): ALL of Base, Asm, Expand, Lex, Inl, Parse, Main are accepted, so the whole
compiler incl. the nano driver `C.m` is accepted. (Parser lookups `r5`/`r6` now return only the word, so the Buf stays borrowed.)

## What is NOT done
1. (done) Driver as nano source: `C/Main.lean`, accepted.
2. **Buffer capacity.** The language box's tests use 64 words per buffer (`eccd515`); the parser stacks and the inliner
   table (`kap = 2^24` words) are far larger. The checkpoint is about acceptance; the buffer allocation size is an open design point.
3. **Proofs of the text changes** beyond the assembler and expander (below). Differential tests agree (0 mismatches).
4. Backend proof for buffers (language box, in progress) — compiling these stages to RISC-V is not yet covered by a theorem.
5. Inliner: `inlTV` (tail-only) has no bridge to `inlB` yet (it never had; `inlV`, the non-tail version, has `inlV_eq`).

## Proofs connecting this source to the v1 compiler
- `Bridge.lean` (proved): `a5_eq : a5 x = Nano.V2S.asmV x`, `e2_eq : e2 x = Nano.V2S.mexpV x` (by `rfl`/one simp: renames,
  hex literals as constants, the `a3` `if` hoisted into a `let`). With `Nano.V2S.asmV_eq`, `mexpV_eq` these give `a5 x = asm x`,
  `e2 x = mexp x` for `x.length < 2^32`.
- `Driver.lean`: `chainS_eq`: assuming `l15 = lexV`, `r16 = p2bV`, `j8 = inlTV` (hypotheses), `chainS = asmV ∘ mexpV ∘ inlTV ∘ p2bV ∘ lexV`.
- Existing (Nano/V2S): `lexV_eq`, `p2bV_eq`, `inlV_eq`, `chainV_eq` connect the V2S versions to `lexA`, `stage2b`, `inlB`, `asm ∘ mexp`.
- Differential test `Testing/nano/v2self/diff_test.lean`: lexer 5000 random strings, inliner 2000 record streams, parser 6000 mutated tag
  streams (1055 non-empty results; the index-stack version): 0 mismatches against `Nano.V2S` (the lexer test found, and I fixed, a fuel difference: the
  word loops must carry the remaining token fuel as a word `g`; with `len' x` alone a lone word as whole input differed).
- Semantic (not just textual) differences from `Nano.V2S`, each to be proved: lexer word loops with word fuel `g`; parser
  looks up by buffer position (`bsize S` / `bsize D` instead of `/ 2`, `/ 3`; `findV` returns 3·number), stacks use top indices instead of `bpop`, a new def's number is
  read off the last table entry, `rdW` uses `* 65536 * 65536`, token fuel `16 * len' x + 16` everywhere; inliner is `inlTV`.

## What the front end taught (rules that shaped the text; useful for the self-hosting design)
- Names: one lowercase letter + digits/`_` (`lo`, `ar`, `jj` rejected); a def's FIRST `List UInt8` parameter is the input, so a
  helper that only builds output takes `x` first or the output last.
- A buffer passed to a user function is consumed: lookups return the buffer back (`UInt64 × Buf`); read before moving
  (`let v := bget u i; … u …`). Parenthesised `if` in tail position is rejected; an operator at line end must be followed by a space,
  so long conditions are on one line. `let (a, b) := e` takes pairs only (13-tuple state = 11 nested lets). Tuple components must be
  typed (tags are constants `w0..w13`). Fuel arguments are `len' x`, numerals, `+`, `*` only (not variables).

## HANDOFF (pause, 2026-11-17)
DONE (pushed): five list-based stages `Nano/V2Self/*.lean` (accepted; asm/expand proved equal to V2S; lex/inl/parse diff-tested);
chained Buf version `Nano/V2Self/C/*.lean` with the driver `C.m`, all accepted by frontElab; `C.m = chainS` tested (chain_test.lean).
IN PROGRESS: nothing running. Not done: proofs for lexer / inliner / parser text changes and for the Buf-chained versions
(`C.a5 (b)` vs `asmV` under `b = bytes.map toUInt64`); `inlTV` bridge to `inlB`; the buffer capacity (language box tests use 64 words);
backend proof for buffers; a QEMU run of the compiled `C.m`.
NEXT: (1) run `Testing/nano/v2f/run.lean` / the backend `gen` on `C.m` (needs the capacity decision), (2) bridges: Buf versions vs
list versions (reads `bget b i = rd l i` on `b = l.map toUInt64`, `q0` = `put`), then lexer fuel lemma, parser index-stack invariant,
(3) `inlTV_eq`.

## INTERIM SELF-COMPILE CHECK (resumed session, 2026-11-17; `Testing/nano/v2self/selfcompile.sh`, `sizes.lean`, `selfrun.py`)
Pipeline: strip+concatenate `Nano/V2Self/C/{Base,Asm,Expand,Lex,Inl,Parse,Main}.lean` (22 755 bytes, 90 defs) → `frontElabK κ` + `gen` (native `lean --run`, 37 s)
→ P → QEMU (`qemu-system-riscv64`, bare metal, same harness convention as `v2b_test.py`, QEMU only, no Sail) with the text as input → O.
1. **Front end and back end accept the whole program, driver `m` included.** κ = 65536.
2. **FIRST BLOCKER (source text, fixed): exponential code size.** P was 2 616 288 words (10.5 MB). Cause: `&&` is desugared to nested `if`s that duplicate
   the else branch, and `l4` (keyword classifier, a chain of `else if A && B && ... then` with 4–6 conjuncts each) multiplied: `l4` alone = 821 387 words.
   In P the 21-bit `jal` offset (±1 MiB) wrapped silently (`encJt` takes `bits imm 21`, no range check): QEMU ended at pc = 0 (mcause 1) and never
   halted. FIX in the text: `l4` computes the else-results first (`let r0 := …; let r1 := … else r0; …`), conditions then duplicate only a variable.
   `l4`: 821 387 → 2 104 words; P: **158 439 words = 633 756 bytes** (stages cumulative: lex 48 252, +parse 142 656, +inl 149 111, +expand 155 732, +asm 158 439).
   Applied to `C/Lex.lean` and `Lex.lean` (list version); `diff_test` 0 mismatches, `chain_test` 0 mismatches (3000 strings), both stages still accepted.
   **Back-end gaps to report to the language box** (not fixed here): (a) `Nano.V2B.enc` has no range check: a program > 256 K words can wrap `jal` (and
   `beq/bne/bltu/bgeu` offsets are only safe because every `.br` jumps by 8 over a `jal`); `gen` should return `none` when a jal offset leaves ±2^20; (b) the `&&`/`||`
   desugaring duplicates branches (code size ∝ product of conjunct counts along an else-chain; source text must work around it); (c) calls are inlined (no call/return).
3. **P runs**: 0.2 s of QEMU time on 22 755 bytes of input, status 0, **O = 84 bytes**, and O is byte-identical to the native `C.m` (Lean semantics) on the same text
   (also identical on a small valid program: 340 bytes). So P implements `C.m` exactly on these inputs (QEMU == Lean, differential evidence only; no theorem).
4. **Does nano compile its own source? NO.** O is the 84-byte output nano produces for ANY input its parser rejects (`k255` alone gives 172 bytes; adding the
   second def `q0 (o : Buf) …` already gives 84): the nano LANGUAGE (v1: `UInt64`/`Int64` defs, `let`, `+ - *`, calls, `if` on ==) lacks `List UInt8`, `Buf`, `Nat`
   fuel patterns, `&&`/`||`/`≤`/`≠`, tuples, `rd`/`len`/`bget`… So O ≠ P and no fixed point: the stages are written in the V2 language but compile the V1 language.
   Self-hosting needs the V2 front end (`Nano/V2/Front.lean`, ~1200 lines) rewritten as nano-subset source and its stages (lexer … assembler) changed to the V2 grammar: a new, larger text, not a rerun.
5. **Failure points seen**: jal range (above); buffer capacity (-2, below); work memory (-1, below). Not seen: fuel (stage fuel is 16 777 216 and inputs finish in ≪ that), QEMU time/memory.

## Buffer capacity (measured; `selfrun.py`, synthetic valid v1 programs of 1 kB and 6 kB, `sizes.lean`)
- `bnew` = `mk κ` allocates (κ+2)·8 bytes of the bump heap each time and never frees; ALL buffers share the one κ (`Ex.cap`); `κ < 2^20`.
- Executed allocations of one `C.m` run ≈ 10–11 (QEMU: κ = 65536 (0.5 MB each) needs 5–6 MB of work; 5 MB → status −1, 6 MB ok) incl. the output `[]`.
- Words per stage, per input byte: lex 1.02, parse 0.99 (6029 B → 6150, 5944), inline/expand/asm: small for inputs without calls (inliner expands only the last def).
- κ must exceed the largest buffer: 6029-byte input: κ = 6100 → status −2 (capacity), κ = 6200 ok.
- **Proposal**: for sources up to 32 kB (the V2Self text is 22.7 kB; the larger V2-language text will be ≈ 2×), κ = 2^16 = 65536 (lex/parse ≤ ~1.1 words/byte, ×2 margin), work = 11 × 0.5 MB + stack ≈ 6 MB, set 8 MB;
  if the inlined/expanded output of the real self-hosting text is larger (not measurable until the language covers it) raise to κ = 2^18 (2 MB per buffer, 24 MB work). One κ for all buffers is wasteful (asm output is ~5× smaller than lex): per-buffer capacities would cut work ~3×, but the language has one κ.
  The input length is the real limit: reject (status −2) beyond κ words ≈ 60 kB.

## S = self-language (inventory of the `Nano/V2Self/C` source; `python3 Testing/nano/v2self/inventory.py`)
Stripped text 22.7 kB, 8727 tokens, 90 defs (every def single-line or `| arm` pattern form; Lean namespace/comments stripped).
**Lexical** (count): identifiers (one letter + digits/`_`/`'` only: `len'`), numerals 856 (decimal only; largest 16777216), `( )` 606, `,` 1074, `;` 135, `:` 148, `:=` 203, `=>` 44, `|` 44 (pattern arms),
`→` 97, `×` 154, `==` 195, `+` 176, `-` 53, `*` 14, `<` 24, `≤` 28, `≠` 7, `&&` 56, `||` 23, `&&&` 16, `|||` 18, `<<<` 15, `>>>` 28, `[` `]` 1 (`[]` once, in `m`).
Keywords: `def` 90, `let` 135, `if/then/else` 175 each. Types: `UInt64` 244, `Buf` 116, `Nat` 22, `List` 17 with `UInt8`. No `>`, `≥`, `%`, `/`, hex, strings, `fun`, `match`, `where`, `.1/.2`, ascriptions, `Int64`.
**Grammar forms**: (1) `def n (a : T) … : T := e` (params of type `UInt64`, `Buf`, `List UInt8`, a tuple type); zero-arity constants `def k : UInt64 := 255`;
(2) fuel recursion `def n : Nat → T → … → R | 0, a, … => e | f + 1, a, … => e` (44 arms, 22 defs; the `0` arm first; the recursive call passes `f`, other fuel args are `len' x` or the numeral 16777216);
(3) `let v := e;` 135; (4) `let (a, b, …) := e;` 84, tuples up to 15 components (11 nested lets in the front end's terms); (5) tuple literals 144, tuple types `T × T × …` 154 (pairs `UInt64 × Buf` for borrowed lookups; the parser state: 9 words, 4 Bufs, 2 words);
(6) `if c then e else e` 175 with conditions built from `==`, `<`, `≤`, `≠` joined by `&&` (56) and `||` (23), no parentheses beyond grouping;
(7) calls (606 parens, mostly calls) and the infix operators above with Lean precedence (`<<<`/`>>>` take numerals only).
**Primitives**: `rd` 33, `len` 12, `len'` 9 (fuel only), `put` 1, `bnew` 18, `bsize` 19, `bget` 60, `bpush` 10, `bset` 1 (stack slots). Types of values: `UInt64`, `Nat` (fuel), `List UInt8`, `Buf`, tuples.
**Not in S** (must not be added by the stages): `Int64`, `.1/.2`, `match` on non-fuel, `for`/`do`, arrays, strings, hex, `bpop`.

### Step 2 decision (shrink S): NOT done mechanically; recommendation
`&&`/`||` (79 uses), `≤` (28), `≠` (7) are cheap to ACCEPT in the parser (condition grammar: precedence climbing over 3 levels, desugared at parse time), expensive to remove from the text: eliminating them by hand changes ~110 sites with branch-structure rewriting (a script needs a Lean-expression parser = the thing being built) and risks the 0-mismatch tests. Condition desugaring in the new parser should bind the else result in a fresh `let` (no branch duplication, as with `l4`): `if a && b then X else Y` = `let y := Y; if a then (if b then X else y) else y`, and `≤`/`≠` by swapping then/else of `<`/`==`. So S keeps `&&`, `||`, `≤`, `≠`; `>` / `≥` stay out.
One rewrite WAS needed for size (see above): long `&&` chains with big else-branches must be written with let-bound else results until the parser does it.

### Step 3 plan: stage growth to S (reference: `Nano/V2/Front.lean` `frontElabK`, `Nano.V2B` `gen`; each increment = text change + differential test against the reference on S-like inputs; frontElab acceptance + chain test stay at 0 mismatches)
Order (each stage keeps emitting the v1 record format where possible; new records only where the target needs them):
1. **Lexer** (`l15`): new token kinds for `: , × → | => < ≤ ≠ && || &&& ||| <<< >>> [ ] if then else Nat Buf List UInt8` (tags after the existing 1..16, kept in one constants block shared with the parser); identifiers with `'`; `--` comments not needed. Test: token stream of every `Nano/V2Self/C/*.lean` vs a Lean reference lexer over the same text; plus random mutation.
2. **Parser** (`r16`): expression grammar with the full precedence table (`||`<`&&`<comparisons<`|||`<`&&&`<shifts<`+ -`<`*`<application), `if`, `let`, tuple pattern let, tuple literals, typed params including `A × B × …` and `→`; fuel-pattern defs `| 0, … => e | n + 1, … => e`; output = the tree the inliner/expander consumes (new record tags). Test: record stream vs `Nano/V2/Front.lean` surface AST `S` (printed) on the S text.
3. **Inliner** (`j8`): no inlining of recursive (fuel) defs: they become loops/labels; calls to non-recursive defs inline as now (`let` chains); the table has to know which defs are loops. Test: inlined tree vs `Front.lean`'s `lower`.
4. **Expander + assembler** (`e2`, `a5`): code for loops (`Ex.loop`), buffers (`mk/size/get/set/push`, heap bump with the oom/cap exits), pairs/tuples (value-stack slots), `if`, the I/O prelude, following `Nano.V2B.cE/cT` (Nano/V2/Gen.lean) instruction by instruction; the `jal` range (±1 MiB) has to be respected (or use `lui/jalr`) because the whole compiler is ~158k words and growing. Test: output words vs `Nano.V2B.gen` on the V2f test programs p1..p10 and on S defs, then QEMU.
5. **Fixed point**: C₀ (Lean-compiled by `gen`) compiles the S text → P₁; P₁ compiles the S text → P₂; require P₁ = P₂ bytes, then (if the nano back end differs from `gen`) QEMU-run all of Testing/nano/v2f.
Increment 1 (lexer) has NOT been started in this commit: it needs the token-tag table agreed with the parser first (step 1 and 2 share it); that table is the first thing to write.

### Increment 1 DONE: the S lexer `Nano/V2Self/C/Lex2.lean` (`s10 : List UInt8 → Buf`, 11 defs, accepted by `frontElab`)
Token tag table (shared with the parser): v1 tags unchanged (def 1, let 2, UInt64 3, Int64 4, number 5 + 8 LE bytes, `(` 6, `)` 7, `:` 8, `:=` 9, `+` 10, `-` 11, `*` 12, `;` 13, ident 14 + (1,byte)* + 0)
plus `,` 15, `×` 16, `→` 17, `|` 18, `=>` 19, `<` 20, `≤` 21, `≠` 22, `==` 23, `&&` 24, `||` 25, `&&&` 26, `|||` 27, `<<<` 28, `>>>` 29, `[` 30, `]` 31, `if` 32, `then` 33, `else` 34, `Nat` 35, `Buf` 36, `List` 37, `UInt8` 38.
No type-uniformity pass (v1 `l9`) and no `\n def` rule; reject (any unknown char, lone `=`/`&`/`>`/`>>`, `1a`) = empty Buf. Keyword chain uses let-bound else results (no code blow-up).
Test `Testing/nano/v2self/lex2_test.lean` (independent `List Char` reference): the whole S text (27 772 output words) identical, 20 000 random piece-strings (5 324 valid) 0 mismatches.
Compiled (`selfcompile.lean`, m = copy of `s10 x`): 20 069 words; QEMU on the S text: 27 772 output bytes in 0.2 s. NEXT: parser (increment 2) consuming these tags.

### Increment 2 design: parser → inliner → expander interchange format (PROPOSAL, sent to the Opus box; to be agreed before the parser is written)
Goal: every later stage is a single linear pass over a `Buf` with explicit stacks (nano has no data recursion), so the parser emits **postfix (RPN) with structure markers**, variables already resolved to **stack depths**.
Per def: `DEF n_params kind(0 plain, 1 fuel-loop) name` header, then the body stream, then `END`. Body stream (tag, then operands in following words):
- `LIT v` (UInt64, one word since Buf words are 64-bit), `VAR d` (d = distance from the current value-stack top, 0 = top), `BIN op` (pops 2, pushes 1; ops: + - * == < ≤ ≠ &&& ||| <<< >>> as plain words; `<<<`/`>>>` carry the shift numeral: `SHL k`/`SHR k`),
  `LET` (pops the value, binds it as a new slot; closed by `ENDLET n`, which drops n slots keeping the result), `TUP n` / `PROJ i n` (tuple values are n adjacent slots; `let (a, b, …) := e` = `LET`-style destructuring `SPLIT n`),
- control: `IF` cond-stream `THEN` t-stream `ELSE` e-stream `FI` (`&&`/`||`/`≤`/`≠` are desugared by the PARSER into this form with a let-bound else, so the expander sees only `<`/`==` conditions),
- calls: `CALL defno nargs` (the inliner replaces it by the callee's body with the arguments as `LET`s; recursion only via loops), prims: `RD LEN BNEW BSIZE BGET BSET BPUSH PUT`, `LEN'` only in fuel positions,
- fuel loops (the 22 `Nat →` defs): `DEF … 1`; arms: `ZERO` stream `SUCC` stream; the self call in tail position is `NEXT nargs` (the loop back-edge: new state values on the stack, jump to header); non-tail self calls are rejected (same rule as Front.lean's `Tl`).
The inliner (v1 `j8` style, now over this stream) handles `CALL` only; loops (`NEXT`/`ZERO`/`SUCC`) pass through, the callee loop inlined at a call site becomes a nested `LOOP` block (`LOOPB … ENDLOOP`) as in `Nano.V2B.Ex.loop`. The expander maps each tag to the `Nano.V2B` instruction sequences of `cE`/`cT` (Gen.lean) with the label/offset fix-up and the `jal` range fix.
The differential test for the parser: decode the RPN back to the surface `S` AST of `Nano/V2/Front.lean` (pretty-print) and compare with `Front.lean`'s own parse of the same text.
