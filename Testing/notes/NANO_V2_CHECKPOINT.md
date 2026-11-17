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
