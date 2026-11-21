# Proof/SrcLink — C's source text lexes and parses to the certified AST

## Files
- `SrcLink.lean` — the only hand-written file: generic lemmas and the per-def checker (below).
- `Data0..Data30.lean` — GENERATED: per source def i, its bytes `x_i`, lexed words `w_i`, tokens `S_i`, parse result `di_i`/`d_i`.
- `Chk0..Chk30.lean` — GENERATED: per def, `lex_i`/`tok_i`/`nl_i`/`chk_i`, each `by decide +kernel`.
- `Chain.lean` — GENERATED: the chained definitions `X_i`, `W_i`, `T_i`, `Ls_i`, and the composition lemmas `lx_i`, `tk_i`, `ch_i`, `len_i`.
- `Top.lean` — GENERATED: the end of the chain and the theorems `parse`, `link`, `ls_pc`, `link_pc`.

All files except `SrcLink.lean` are written by `Testing/nano/v2self/srclink/gen.lean`. Do not hand-edit them;
change the generator and rerun it (usage line at the top of `gen.lean`).

## What it does, where it sits
`SrcGen.X0` is the byte text of C (the self-hosted compiler). The theorems below link it to the AST that `Cert` proves
correct, so the certificate speaks about C's real source text and not only about an AST.
`Main/SelfC.lean` imports `Top` (`hsrc_C`). The `Parser`, `LexSpec` and `Cert.PC` folders supply the definitions.
The text is cut at each line starting with `def`. Each piece is lexed, tokenized and parsed separately,
so every kernel check stays small. The generic lemmas then compose the pieces.

## Decisions
- Per-def kernel checks (`decide +kernel`) instead of one check on the whole text, so each kernel check stays small (see `gen.lean`).
- Composition by lemma: `lexes_app` (lexing, chunks end in newline), `tokens_app`, `pDefs_step` (parsing).
- The AST is compared by a boolean checker (`ndBeq`, `defBeq`, `lsBeq`) with soundness lemmas, so equality with `Cert.PC.all` is one kernel check (`ls_pc`).
- The data is generated from the text, not typed in, and `gen.lean` validates every piece before writing it.

## Main statements (file:name)
- `SrcLink.lean:lexAll_sound` — the reference lexer `lexAll` implies `Lexes`.
- `SrcLink.lean:lexes_app`, `tokens_app`, `pDefs_step`, `refParse_of` — composition of lexing, tokenizing and parsing.
- `SrcLink.lean:chkDef_sound` — one per-def parse check implies the parse step.
- `SrcLink.lean:ndBeq_eq`, `defBeq_eq`, `lsBeq_eq` — boolean AST equality implies `=`.
- `Top.lean:parse` — `refParse W0 = some Ls0`.
- `Top.lean:link` — `Lexes X0 W0 ∧ ParsesProgram W0 Ls0`.
- `Top.lean:link_pc` — `Lexes X0 W0 ∧ ParsesProgram W0 Cert.PC.all`.
- Assumptions: none beyond Lean's kernel. Not in REVIEW's axiom list; `review_axioms.sh` pins the axioms.

## Build / check
`lake build Nano.V2Self.Proof.SrcLink.Top`, then `Testing/scripts/review_axioms.sh`.
Regenerate: `lake env lean --run Testing/nano/v2self/srclink/gen.lean SRC OUTDIR GROUPTOKS`.

## Limits
- `link_pc` is only for the exact text `X0`. Changing C's source requires regenerating the folder.
- The lexer and parser checked are the reference ones (`lexAll`, `refParse`). Relating them to the compiled C lexer and parser is outside this folder.
- The checks are kernel-evaluated (`decide +kernel`), not by `native_decide`.
