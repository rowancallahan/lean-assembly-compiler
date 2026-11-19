# NANO_V2_MAIN: the end-to-end statement for C (Opus box D)

File: `Nano/V2Self/Proof/Main.lean` (namespace `NanoMain`), builds in ~2 s. No sorry. Axioms of `compiler_correct`:
propext, Classical.choice, Quot.sound + the Sail extern set (from `Proven.Cfg` / `runsTo` in the statement).

## The statement
- `mC x := C.g41 x (C.y16 (C.s10 x))` — the driver text of `build_self_S.py` (C/Main.lean still has the OLD chain).
- `Sem κ p inp : Except Stop (List UInt8)` — meaning of ParSpec's resolved program `p : List DefA`. Word level: slot values
  `W = w UInt64 | b (List UInt64)`; defs in order, each def's meaning sees the earlier ones (`call i` to a later/missing id
  = `stuck`); fuel loops iterate on slot 0 (zero arm at 0, step arm with slot 0 = fuel − 1, CONTINUE writes slots 1..);
  prims in Gen's numbering; `put`/`bpush` with `l.length ≥ κ` ⇒ `.error .cap`; output = low bytes of main's buffer.
  `.error .stuck` = ill-formed AST (wrong arity/kind, CONTINUE in value position, ...), not reachable for parsed programs
  (lemma to do: `ParsesProgram ts p → Sem κ p inp ≠ .error .stuck`).
  Checked by `#eval` on ParSpec's ex1–ex4 and a buffer/loop program: correct results.
- `ImplementsC B f` — Spec/Implements1 conventions (a0 input, a1 len, a2 work base, a3 output, sp = work top, ra; Cfg;
  Mapped output/work; disjoint regions in RAM; inputs ≤ 2^20 bytes), code = the BYTES `B` at `entry` (|B| % 4 = 0).
  `∃ space : List UInt8 → Nat` such that every run `runsTo` an `Outcome`: PC = ra, abiSavedKept, Cfg, and
  * `f x = ok y`: a0 = (1 if y = [] else 0), a1 = |y|, y at a3, nothing written outside [a3, a3+|y|) ∪ work;
  * `f x = error cap`: a0 = −2, a1 = 0, nothing outside output ∪ work;
  * `f x = error stuck`: no claim;
  * OR out-of-memory (a0 = −1, a1 = 0, nothing outside output ∪ work) — only when `work.len < space x`.
  The existential `space` rules out the always-OOM program.
- Stage hypotheses:
  * lexer: PROVED (`LexSpec.s10_sound`), plus `lexes_len` (≤ 9 words per byte) for the parser's length premise.
  * `ParStage := ∀ ts, ts.length ≤ 16777216 → ParInv.ParserSound ts` (boxes B/C).
  * `GenStage := ∀ c ts p, ParsesProgram ts p → C.g41 c (serialize p) ≠ [] → ImplementsC (C.g41 c (serialize p)) (Sem κC p)`
    with κC = 524288 = `C.g_999` (box A: g41 output = code of the AST; box E: that code on Sail).
- `compiler_correct (HP : ParStage) (HG : GenStage) x (hx : x.length ≤ 2^20) (h : mC x ≠ []) :
   ∃ ts p, LexSpec.Lexes x ts ∧ ParsesProgram ts p ∧ ImplementsC (mC x) (Sem κC p)` — PROVED from HP, HG.

## Non-vacuity (`Nano/V2Self/Proof/MainWitness.lean`, 19 s, 2.4 GB, axioms propext/choice/Quot.sound)
Per stage, `decide +kernel`, for 3 sources (`def m … := []`, ParSpec ex1 (call, RD/PUT/BNEW), ex3 (fuel loop, CONTINUE)):
`C.s10 x = ts` (hence `Lexes x ts`), `refParse ts = some p` with `serialize p = a`, `C.g41 x a ≠ []` (428 / 720 / 796
bytes); so `GenStage`'s premise holds with non-empty code, and `C.y16 ts = a → mC x ≠ []`.  `sem2`/`sem3`: `Sem` gives the
expected outputs ([11], [4]).  The one step NOT kernel-checked: `C.y16 ts = a` (native `#eval` agrees on all three).
Why: Par1's FIXED layout (tokens at word 184,384) — measured: one kernel `bget` at index 184,384 = 28 s / 5.5 GB; a
whole y16 run, or even one `ParInv.step` on a run-length-stated heap, is killed at 9 GB; `List.length` of a 100k list =
11 s / 2.7 GB.  The kernel has no fast path for long lists, so any witness that touches Par1's heap is out of budget.
Options: (a) Par1 layout sized by the token count (offsets d1..d11 as functions of |ts|; compiler change, owner/C);
(b) a representation-change theorem (Par1's code over a compact heap) — large; (c) accept per-stage witnesses.

## Trust / reading notes
- The meaning is ParSpec's resolved AST + `Sem`, both independent of C's code. The link from ParSpec+Sem to Lean's own
  elaboration of the source text is a spec review item (or a later bridge to `Nano.V2` `Prog.eval`).
- Lean `Nat` fuel is a word here (numerals are mod 2^64 already in Lex2Spec; `len' x` < 2^64).
- `put` pushes the whole word, the output keeps the low byte (= Lean's `put` after `toUInt8`); Gen does the same.

## HANDOFF
DONE: statement, `Sem`, `ImplementsC`, stage hypotheses, `compiler_correct` (proved from HP, HG), `lexes_len`, `g41_nil`.
DONE: per-stage non-vacuity witnesses (MainWitness.lean); the parser run itself is not kernel-checkable at Par1's layout.
NEXT: (1) agree `GenStage` / `ImplementsC` with A and E (owner relay; messages sent); (2) `parsed_not_stuck`
(ParsesProgram ts p → Sem κ p inp ≠ .error .stuck); (3) phase 2 parser handlers after C publishes `Rep`.
