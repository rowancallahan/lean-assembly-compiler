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

## Progress: the meaning never gets stuck (`MainTy.lean`, `MainTyP.lean`, ~7 s, propext/choice/Quot.sound)
- `MainTy`: kinds `w`/`b`, judgment `TyN D Γ S e ks` (Γ = known slot kinds, S = allowed CONTINUE payload kinds),
  `TyProg p sigs`; `sem_ok : TyProg p sigs → Sem κ p inp ≠ .error .stuck`.
- `MainTyP`: ParSpec's parser only produces well-kinded programs — fuel induction over the 8 mutual parse functions
  (`p_all`), `bindSlots`/`mkEnv` slot layout (`Lay`, `lay_envT`), `pDef_ok`, `pDefs_ok`, `refParse_ty`;
  `parsed_not_stuck : ParsesProgram ts p → Sem κ p inp ≠ .error .stuck`.
- `compiler_correct'` = `compiler_correct` + `∀ inp, Sem κC p inp ≠ .error .stuck`.

## E's side conditions from the parser (`MainOk.lean`, 4 s, propext/choice/Quot.sound)
- `TyN` tightened: a let's slots must be fresh (`none` in Γ), loops only as def bodies (`TyB`), prims 1/3/5 have no
  argument nodes; MainTyP re-proved (EnvT now also says: slots ≥ nx are fresh).
- `rd_known` (reads hit known slots), `wr_fresh` (let writes hit fresh slots) ⇒ every rd/wr disjointness of `OkV`/`OkT`;
  `wd_ok` (width = kind count), `okV`, `okL`, `okT` (loop arms, CONTINUE width = p − 1), `okBody` (plain body or loop).
- `parsed_ok : ParsesProgram ts p → p[i]? = some d → ∀ K, K.p = d.npw → K.nl = d.nslots → K.nd = i → K.q = d.nres →
   (∀ j < i, p[j] = dj → K.npwOf j = dj.npw ∧ K.nresOf j = dj.nres) → OkV K d.body ∧ wd K d.body = d.nres ∧ d.npw ≤ d.nslots`;
  `parsed_main`: the last def has npw 0, nres 1.

## In the owner's top-level vocabulary (`MainTop.lean`, 13 s; axioms = compiler #1's: Sail extern set + standard)
| | compiler #1 (`Riscv/Back/S3Top.lean`) | C (`Nano/V2Self/Proof/MainTop.lean`) |
|---|---|---|
| theorem | `compile_correctL : CompileCorrectL riscv compile` | `C_correctL : ParStage → GenStage → CompileCorrectL riscv compileC` |
| programs `P` | its source AST | `Src` = source TEXT (bytes) |
| `Program.run` | the AST's evaluator | `srcRun`: Lex2Spec `Lexes`, ParSpec `ParsesProgram`, `Sem κC` (`pOf` by choice; unique: `lexes_det`, refParse is a function); `none` = not a program, or Gen's capacity κ hit |
| `compile` | its code generator | `compileC`: `mC` when non-empty and the text ≤ 2^20 bytes; cellSize 1, events `[alloc (spaceC x inp)]` (the chosen `ImplementsC` bound) |
| conclusion | `CompileCorrectL` (Runs, pc = ra, status ≠ oomFlag, output, a1 = length, frame, kept regs, Cfg) | the same |
Open in this form: `ParStage`, `GenStage` are hypotheses; `CompileRuns(L)` (OOM flag ⇔ out of memory) is NOT claimed (ImplementsC only
allows OOM below the bound); `Computes` holds only for programs whose meaning is defined on every input (capacity never hit).

## Per-program meaning certificates (`MainCert.lean`, 15 s, propext/choice/Quot.sound)
`cert_of` / `cert_of'`: `C.s10 x = ts` (kernel; `s10_sound`), `progEq (refParse ts) P = true` (kernel; Boolean AST
equality `ndEq`/`progEq` with soundness `progEq_eq` — Lean's `rfl` will not unfold refParse), `Sem κC P inp = .ok (f inp)`
for symbolic `inp` ⇒ `srcRun ⟨x⟩ inp = some (f inp)`.
- `Ex1.cert`: ParSpec's `ex1` text means `Ex1.m` (two defs, call, prims) — `Sem` by `rfl`.
- `Ex3.cert`: ParSpec's `ex3` text means `Ex3.m` for inputs < 2^64 bytes (fuel loop): `loop` = induction on the fuel
  against `loopRun`, `f0` = the loop def's meaning, `sem` = main.
With `C_correctL`, for these texts: C's code implements the Lean function `m` (given ParStage, GenStage).
For C itself (186 defs) the `Sem = Lean` part needs one lemma per def (generated, as above); not started.

## FINDING (2026-11-19): C miscompiles non-linear buffer use — the end-to-end statement is FALSE as is
Source `def m (x : List UInt8) : List UInt8 := let b := bnew; let c := bpush b 7; put [] (bsize b)`:
C accepts it (`mC` = 800 bytes); Lean / ParSpec+`Sem` meaning: output `[0]`; QEMU run of C's code: output `[1]`
(Gen's BPUSH/BSET update the buffer in place, so `b` sees the push).  Reproduce: `Testing/asm/ir-words/alias_d.{words,cases}`,
`NOSAIL=1 BIG=16777216 python3 Testing/nano/v2self/cg_test.py alias_d` (fails: qemu output 01, expected 00).
Cause: neither Par1 nor ParSpec has the nano front end's ownership rule (a Buf is consumed when passed / used once per
branch; Nano/V2 Own/OwnP).  So `GenStage` is unprovable for such programs.  Fix options: (a) add a linearity check to
ParSpec and the same rejection to Par1 (compiler change: owner/C); (b) keep C, weaken the theorem to programs with a
`Linear p` predicate checked by ... nothing in C today — (a) is the sound route.

## Trust / reading notes
- The meaning is ParSpec's resolved AST + `Sem`, both independent of C's code. The link from ParSpec+Sem to Lean's own
  elaboration of the source text is a spec review item (or a later bridge to `Nano.V2` `Prog.eval`).
- Lean `Nat` fuel is a word here (numerals are mod 2^64 already in Lex2Spec; `len' x` < 2^64).
- `put` pushes the whole word, the output keeps the low byte (= Lean's `put` after `toUInt8`); Gen does the same.

## HANDOFF
DONE: statement, `Sem`, `ImplementsC`, stage hypotheses, `compiler_correct` (proved from HP, HG), `lexes_len`, `g41_nil`.
DONE: per-stage non-vacuity witnesses (MainWitness.lean); the parser run itself is not kernel-checkable at Par1's layout.
DONE: `parsed_not_stuck`, `compiler_correct'` (MainTy/MainTyP); E's `OkV` from ParSpec (`MainOk.parsed_ok`).
OWNER QUEUE (2026-11-19): (2) bridge Sem ⇐ E's sv — PAUSED on the aliasing finding; (3) DONE (MainTop.C_correctL); (4) small examples DONE (MainCert), C itself not started.
NEXT: (1) agree `GenStage` / `ImplementsC` with A and E (no reply yet); the bridge E's machine-level `sv`/`defS`
(NdSem) ⇒ `Sem` is the natural meeting point — the `TyN` judgment gives the kind facts it needs; E's `OkV` scoping /
width side conditions also have to come from ParSpec (same fuel-induction scheme as `p_all`); (2) phase 2 parser
handlers after C publishes `Rep`.
