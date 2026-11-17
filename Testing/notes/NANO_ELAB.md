# NANO_ELAB: `nanoElab` as byte-level stages for the front end (branch `nano-elab`)

Owner task: `nanoElabB` = `nanoElab` as byte-level state machine(s) the front end accepts, proved equal for ALL inputs,
compiled with machine theorems, tested on QEMU + Sail. Files `Nano/ElabB*.lean`.

## Status
| piece | state |
|---|---|
| stage 1 `Nano.B.lexB` (adjacency check + lexer + type check of `nanoElabT`: bytes → header byte + token bytes) | **proved equal to the spec for every input** (current spec, nano-e2e's lexer): `Nano.B.lexB_eq : decL (lexB xs) = lexT xs`, `lexT xs = (if adjOk xs then lex xs.length xs else none) >>= uniTy` (`Nano/ElabBProof.lean`, axioms propext / Classical.choice / Quot.sound). The first version (old lexer, commit f93dcc2) was also proved, then reworked after the spec changed |
| stage 1 compiled (`Nano.Self.lexBE`, `Nano/ElabBSelf.lean`) | see log below |
| stage 2 (parser: tokens → Prog with inlined calls) | **not started**: analysis below says it cannot be one front-end stage, nor a fixed chain of them, for all inputs |

`lexT xs := (lex xs.length xs).bind fun ts => (uniTy none ts).map (·, ts)`, so
`nanoElabT xs = (lexT xs).bind fun (s, ts) => (pDefs (ts.length + 1) [] ts).map (s, ·)` (by definition): stage 2 needs
only the decoded `(s, ts)`.

## Stage 1 design (`Nano/ElabB.lean`)
* One function `lx (xs o : List UInt8) (m st sp d d0 w ty : UInt64)`; every step consumes one byte and looks at the next
  (`c :: n :: t` / `[c]` / `[]` patterns). Two passes: `m = 0` validates and computes the type, then restarts on the
  bookmark view `o` with `m = 1` and emits. Output = `0` (rejected) or type byte (1 UInt64, 2 Int64) + token bytes:
  punctuation as its ASCII byte (`:=` as `=`), a word as its characters + kind byte (0 name, 1 def, 2 let, 3 UInt64,
  4 Int64), a numeral as `5`, its digits, `6` (the value is decoded with the same fold as `spanNum`).
* Words: name-shape DFA `d` (proved = `nameShape`), packed word `w` (≤ 7 chars behind a sentinel; keyword and reserved
  tests are 28 `==` against constants; proved = `identTok?` via packing injectivity).
* The fuel of `lex xs.length xs` is replicated exactly (`sp`): when every earlier token cost as much fuel as bytes, a word
  or numeral that runs to the end of the input is split before its last character (`"x UInt64x"` lexes as
  `[id x, kty, id x]`; `"12"` alone is rejected). The machine does the same.
* Generated: the step macros `STEPN`/`STEPE` come from `Testing/nano/elabb_{step,end}.tmpl` via `Testing/nano/gen_elabb.py`.

## Proof outline (`Nano/ElabBProof.lean`)
`adjPass` (mode 5 = `adjOk`), `pass1` (= `R1 (lex F xs)`: lex result, then `uniTy`, then the restart), `pass2` (bytes decode
to `lex`'s tokens), both by strong induction on the rest using one lemma `step0`: from state 0, one `lex` step (blank,
newline + column-0 check, punctuation, `:=`, a word) is a fixed run of machine steps (`S0`/`S0g`). Words: `classify`
(`KIND` on the automaton state and packed word = `wordTok`, via `pk_beq`: packing is injective up to 7 characters),
`WordStart`/`WordRun`/`W_last*` (machine runs), `spanId_eq`, `word_ok` (bytes decode to the token, type update =
`uniTy`'s), the fuel split (`W_quirk`, `quirkK`, `lex_last`). Column 0: `C4pos`/`C4neg`.

## Front-end rejections met (and the change made) — evidence for the front-end work
1. `frontx_view`: a recursive call on the same list (`lx xs …` / `lx (c :: t) …`, non-consuming state change) →
   "possibly looping simp theorem `lx.eq_1`", max recursion. Change: every step consumes one byte, with lookahead.
2. `frontx_view`: a recursive call on `[]` in the nil branch (`lx [] o …`) → "a recursive call that is not on a view of
   the list" (`[]` is not folded back to `view B i`). Also `match h : t with` substitutes `t := []`. Change: the end
   of a pass is inlined (no call on `[]`).
3. `t.isEmpty` as a condition → "frontx: unsupported Bool" (an unreduced `match view B (i+1)`). Change: patterns
   `c :: n :: t | [c] | []`.
4. A compound Bool `c == 41 && !(n == 40 || isW n)` inside an `||` chain → obligation `BExp.denote … = if …` not proved.
   Change: separate `if`s.
5. `!(97 ≤ c && c ≤ 122)` → same kind of unproved obligation. Change: `c < 97 || 122 < c`; `!(w == … || …)` rewritten as
   `if (… || …) then 9 else …`.
6. A branch condition that is a constant false after instantiation (`32 == 61` in the end step) or a second test of
   `m == 0` inside an `m == 0` branch → unproved obligation (`rfl` fails on `denote (var 6 == 0)`). Change: the end
   step is its own template; the end-of-pass continuation is specialised per known `m` in the generator.
7. `frontx_compile`: `simp` maximum recursion depth in `lx.view.runs` (the 2-pass, 7-scalar machine, ~17 min) →
   `set_option maxRecDepth 100000`.
8. "could not prove the capacity condition" when a call argument re-tests a condition already on the path (`DSTEP0`
   tested `48 ≤ c` inside the `48 ≤ c` branch: the hypothesis gets simplified, the goal not). Same for `st == 4` tested
   inside `st == 0 || st == 4`. Change: split the branch so arguments do not depend on path conditions (this is
   probably what broke nano-e2e's 15-op `asm`).
9. `frontx_compile` aborts with a native stack overflow on the 3-pass machine; `--tstack` needed (a 4 GB stack next to
   another Lean process got the container killed for memory).
10. (Lean, not the front end) `let` in macros is not allowed by the front end (TINYSELF 4); helper functions cost slots:
   all shared subterms are hygiene-off macros.

## Why the parser (stage 2) cannot be built in this front end for all inputs
The list front end gives a function a constant number of UInt64 scalars, read-only views of the input (bookmarks,
restartable: checked), and a write-only output stream. That is a multi-head two-way automaton with counters (log space).
* `nanoElab`'s output inlines every call: `Ex.call body args` carries the callee's elaborated body. For
  `def f1 (x) := x + x; def fk (x) := f(k-1) (f(k-1) x)` the output is `2^k` copies; for a chain
  `def fk (x) := f(k-1) x + 1` it is linear but the machine must, after emitting `f(k-1)`'s body, return to the call
  site in `fk`, and so on k levels deep: it must remember a path of k call sites (k up to the number of defs), i.e.
  Θ(k · log n) bits. A constant number of 64-bit scalars cannot. Recomputing the path by rescanning needs per-def
  expansion sizes (a table), which a stage cannot read back from its own output.
* A fixed chain of stages does not help: every stage has the same constant memory, and the k-level return path has
  to be produced by some stage.
* Parentheses / precedence alone (postfix order) are possible by rescanning with depth counters (log space), but the
  proof against the fuel-indexed recursive descent of `pDefs`/`pExpr` would be a large separate effort.
* Recommendation (needs the owner / integrator): (a) a non-inlined `Prog` (defs table, calls by index) as the
  elaborator's output, with `inline : Prog' → Prog` proved in Lean and a generator that emits real calls, or
  (b) a front-end feature: a writable work array (stack) in the list path (the paged `wp_compile` path has growing
  arrays but its theorem form is not the `Implements1With` that `Nano.Link` composes).

## Spec findings (for the owner's review of `nanoElab`; nothing changed in `Nano/Elab.lean`)
* Parser fuel = token count + 1 bounds the recursion depth (each paren costs ~4 levels, 2 tokens):
  `def f : UInt64 := ((1))` is REJECTED, but `def f : UInt64 := ((((((((((1)))))))))) + 1 + … + 1` (12 more `+ 1`)
  is accepted. Allowed by the subset rule (nano may reject), but surprising.
* Lexer fuel = byte count: an input whose final word runs to the end with only one-byte tokens before it is lexed with
  the last character split off. Never changes `nanoElab`'s result (a program needs `def` first), but the lexer's token
  list differs; stage 1 replicates it.

## Decisions / log
* 2026-11-16 22:50. Spec = `nanoElab` of `nano-int` (name shape + reserved list, CR only before LF, glued numerals
  rejected). nano-e2e has a different lexer (`wordTok`, `adjOk`, column-0 rule); when it reaches nano-int stage 1 must
  follow (machine + proof).
* Stage boundary chosen at `lexT` (lexer + `uniTy`) because `nanoElabT` factors there by definition.
* Numerals are emitted as their digits (not 8 value bytes): one output byte per step keeps the arms small; the decoder
  computes the value with `spanNum`'s fold.
* Tests: `Testing/nano/elabb_check.lean` (Lean side, 2000 inputs: corpus, boundary mutations, prefixes, random bytes,
  edge cases; 525 pass stage 1; 0 mismatches against `lexT`), `Testing/nano/elabb_test.py` (QEMU + Sail).
* 2026-11-16 23:50. Merged origin/nano-int 4a04370: `Nano/Elab.lean` is now nano-e2e's lexer (`wordTok`, `identOk`,
  global `adjOk`, column-0 rule, CR rejected). The stage-1 machine and proof above (commit f93dcc2, `lexB_eq` for the
  old spec) are reworked for it: an `adjOk` pre-pass (mode 5) restarting on the bookmark, numerals and names as one
  word class (`wordTok`), a column-0 flag `cz` for words right after a newline.
