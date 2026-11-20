# SYNTAX_EXP: growing nano's accepted syntax (branch `exp-syntax`, experimental, NOT the release)

Base: `origin/release-434` @ 56e2584. Toolchain: Lean 4.34.1. RISC-V model: `deps-rv-regen434` @ 4cf120c8 (model_hash
`6ac35da9… 161`, checked). Locally the root `lake-manifest.json` was switched to lean-sail v10 to build the regenerated
model (as on `rv-regen-434`); that change is **not committed** (release-434 still pins v5).

## Decision table

| # | construct | status | C delta (lines) | proof delta (lines) | difficulty | next-step estimate |
|---|---|---|---|---|---|---|
| 1 | comments, nested block comments, docstrings, `@[…]`, `namespace`/`open`/`section`/`end`, `private` | **done + proved** (lexer only) | Lex2 +28 −3 | Lex2Sound +417 −56, Lex2Spec +27, MainTokWF +34 −22, SrcLink +115 −27, Sem +55 −21 (regenerated Cert/SrcLink/Tests not counted) | S (≈4 h incl. regen) | — |
| 2 | `match` | design only, see §2 | — | — | M | see §2 |
| 3 | `a[i]!`, `a.size`, `a.push` | not started | — | — | S–M | see §3 |

## 1. Trivia in the lexer

### What is accepted (spec: `LexSpec.step`, `Nano/V2Self/Proof/Lex/Lex2Spec.lean`)
New `step` cases, emitting **no tokens**:
- `--` up to (not including) the newline;
- a block comment from slash-dash to the matching dash-slash, **nested** as in Lean (`blockEnd`, depth counter); this
  covers docstrings and module docs. An unterminated one has no `step`, so the text is rejected;
- `@[` up to and including the first `]` (attributes). Without a `]`, the text is rejected;
- the words `namespace`, `open`, `section`, `end` (whole words, maximal munch) up to the newline;
- the word `private`.
`--` used to lex as two minus tokens. No valid program used that: `a - -b` is not in the grammar, and in Lean it is a comment.

### Semantics caveats (owner decision)
- **Namespaces are flattened.** `namespace A` / `end A` lines are dropped, so `A.f` and `B.f` both become `f`. The
  parser's duplicate-def check then rejects the program. A qualified reference `A.f` is rejected, because `.` is not a
  token. Nothing is silently mis-resolved.
- `open X in` on its own line is dropped, which is harmless. `namespace X def f …` on one line drops the def. Lean
  formatting puts it on its own line, so this is unlikely in practice.
- An all-trivia text lexes to `[]`, which C rejects, as before.
- Not covered: `protected`, `noncomputable`, `partial`, `set_option … in`, `variable`, `universe`, `#eval`. Each is one
  more `kwX` entry and one more `s3'_eq` length case.

### Implementation (C, `Nano/V2Self/C/Lex2.lean`)
- `s3` (keyword chain) gets 5 entries: kind 92 (skip the line) for namespace/open/section/end, kind 93 for private.
- `s4` gets 3 kinds: 94 `--`, 95 slash-dash, 96 `@[`.
- New scanners: `s12 n x i b` gives the first position ≥ i holding byte b, or the end. `s11 n x i d` scans a nested
  block comment and returns the position after its end, or 0 to reject.
- `s9` gets 5 branches. Parser, Own and Gen are untouched.

### Proofs (all local; no parser/Own/Gen/machine proof changed)
- `Lex2Sound`:
  - `kwX` = `kwTable` + the trivia words. `s3'_eq` is extended to 9-byte words (namespace).
  - `s4'_eq`, `kind`, `kind_spec` (+5 disjuncts).
  - `s12_eq`/`s12_drop`, `s11_sound`.
  - `s9_sound` gets 5 cases.
  - The main theorem `s10_sound` is unchanged in statement.
- `MainTokWF.step_tok`: the new steps emit `[]`.
- `Main/Sem.step_len`: the 9-words-per-byte bound, with `blockEnd_len`.
- `SrcLink.step_app`: lexing composes across newline-terminated chunks. New lemmas `blockEnd_app`, `mem_dropWhile`,
  `dw_head`.
- Regenerated as in PERF_NAMES:
  - `Proof/Cert/*` (`dump_pc` + `gen_cert.py`);
  - `Proof/SrcLink/*` chunks (`srclink/gen.lean … 800`; this reproduces the committed chunks byte for byte from the old
    text);
  - `Tests/SelfInPath` and `SelfInQuiet`: def ids ≥ 13 shift by 2 (s11 and s12 are inserted before s9; both are push-free
    and added to `S`).

### Tests
- Fixpoint, with nanorun (no QEMU on this box): B1 (Lean-compiled) → B2 → B3. B3 = B2 = 348,904 B, sha256 `395f0b9d…`.
  The old B2 also compiles the new source to the same bytes. Self-compile costs 664,861,123 instructions (was 641,996,759:
  +3.6 %, for C's 2 extra defs and the larger s3/s9).
- All 8 `examples/*.lean` now compile **with** their `--` header lines. The code is byte-identical to the old compiler's
  code for the stripped files.
- `arm/rv2arm.lean` (45 comment lines) compiles unstripped to the same `rv2arm_rv.bin`.
- New `examples_syntax/trivia.lean` (ROT13) uses every trivia form. `run_syntax.sh` gives `exp:OK`, and real Lean
  `#eval` gives the same bytes.
- 21 probe strings (nested comments, `-/` outside a comment, `@[x` unterminated, `endx`, …): C's `s10` and the spec agree
  on all of them, including the rejections.
- `arm/B2_arm.bin` was regenerated with the nanorun-run translator. The same procedure reproduces the old SHA256SUMS
  entry exactly.

### Surprises
- Lean's block comments nest, so this module's own doc comments must not mention slash-dash literally (it opened a
  nested comment and the file did not parse).
- A third consumer of `LexSpec.step` existed (`Main/Sem.step_len`). It was found only by the full build.
