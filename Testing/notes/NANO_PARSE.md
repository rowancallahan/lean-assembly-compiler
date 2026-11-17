# NANO_PARSE: the parser stage of the compiled elaborator (branch `nano-parse`)

Owner task: stage 2 = tokens (stage 1's `lexB` bytes) → the micro-op stream, equal to the spec for every input,
compiled with a machine theorem, tested on QEMU + Sail, then the self-hosting composition. Files `Nano/ParseB*.lean`.

## Status (end of this session)
| piece | state |
|---|---|
| layer A: explicit-stack parser machine `Nano.PB.parseA` (`Nano/ParseB.lean`) | done; executable; `Testing/nano/parseb_check.lean`: 3000 inputs (corpus, boundary mutations, prefixes, random bytes, edge cases; 595 lexed, 299 accepted), 0 mismatches against `(nanoElabU x).map serU` |
| layer A = spec, every token list | **proved**: `Nano.PB.parseA_eq` (`Nano/ParseBTop.lean`) |
| stage 1 then layer A = spec, every source | **proved**: `Nano.PB.stage2A_lexB` (gas existential) |
| explicit gas: `stage2` (a fixed Lean function) | **proved exact for every source**: `Nano.PB.stage2_lexB`, `stage2_hfe` (`Nano/ParseBGas.lean`; potential `Φ`, `step_dec`, `run_stable`) |
| composition | **proved**: `Nano.SelfHost.selfHosted_parse` (five stage theorems → target), `selfHosted_parse_asm` (compiled `asm` plugged in) (`Nano/ParseBSelfHost.lean`, Sail axioms) |
| layer B: the same machine on bytes, compiled by `wp_compile` | NOT done (see "What remains") |
| QEMU + Sail tests of stage 2 | NOT done (no compiled stage) |
| self-hosting instance | NOT closed: the remaining hypotheses of `selfHosted_parse_asm` are the machine theorems of stage 1 (`lexBE`, compile parked by the integrator: not confirmed to build), stage 2 (`stage2`, not compiled), `inlB`, `mexp` (both not compiled); everything else is proved |

Axioms of all three theorems: propext, Classical.choice, Quot.sound (`Testing/scripts/axioms_nano-parse.lean`, in
check.sh's loop and in expected-axioms.txt). No sorry, no native_decide.

## The theorems
```
-- EXACT, every source (Nano/ParseBGas.lean)
def stage2 (bs : List UInt8) : List UInt8 :=
  match decL bs with | some (_, ts) => (parseA (gasOf ts) ts).getD [] | none => []     -- gasOf ts = 13·|ts| + 6
theorem stage2_lexB (xs : List UInt8) :
    stage2 (lexB xs) = match nanoElabU xs with | some u => serU u | none => []
theorem stage2_hfe (xs) (u) (h : nanoElabU xs = some u) : stage2 (lexB xs) = serU u
-- composition (Nano/ParseBSelfHost.lean), Sail axioms
theorem selfHosted_parse_asm … (h1 : Implements1With … c1 f1 s1 (2^20) true)   -- stage 1
    (h2 : Implements1With … c2 f2 s2 (2^20) true) (hi : … ci fi …) (hm : … cm fm …)
    (hc2 : c2.length < 2^17) (hci …) (hcm …)
    (hf1 : ∀ x, f1 (ofL x) = lexB x) (hf2 : ∀ x, f2 (ofL x) = stage2 x)
    (hfi : ∀ x, fi (ofL x) = inlB x) (hfm : ∀ x, fm (ofL x) = mexp x) :
    SelfHosted (link (link (link (link c1 c2) ci) cm) nanoAsm.code) (fun _ => …) (Sized5 K …) nanoCompileA
```
Earlier forms (gas existential):
```
-- for every token list
theorem parseA_eq (ts : List Tok) :
    match pDefsU (ts.length + 1) [] [] ts with
    | some u => ∃ n, ∀ g, parseA (g + n) ts = some (serU u)
    | none => ∀ g, parseA g ts = none
-- for every source: stage 1's bytes, decoded, then layer A
def stage2A (g : Nat) (bs : List UInt8) : List UInt8 :=
  match decL bs with | some (_, ts) => (parseA g ts).getD [] | none => []
theorem stage2A_lexB (xs : List UInt8) :
    match nanoElabU xs with
    | some u => ∃ n, ∀ g, stage2A (g + n) (lexB xs) = serU u
    | none => ∀ g, stage2A g (lexB xs) = []
```
`nanoElabU` / `serU` are the integrator's (`Nano/ElabU.lean`, `Nano/SerU.lean`): `nanoElab_eq : nanoElab xs =
(nanoElabU xs).map inlineProg`, `inlB_serU`, `chain_eq`. So `stage2A_lexB` is exactly the `hfe` premise of
`Nano.SelfHost.selfHosted_four` for the Lean function `fun src => stage2A G (lexB src)`, except that the gas is
existential (see "What remains", item 2). Reject code: `[]` (`serU u` is never empty: it ends with `[13, arity]`).

## Design (layer A, `Nano/ParseB.lean`)
* Defunctionalised continuation-passing form of `pDefs`/`pParams`/`pNames`/`pExpr`/`pAdd`/`pMul`/`pMulT`/`pApp`/
  `pArgs`/`pAtom`: a control `Ctl` (which parse function, with its FUEL), a frame stack `List Fr` (what to do on return:
  `letV f x`, `letB`, `exprAdd f`, `addOp f op`, `mulT f`, `mulOp f`, `call j k`, `args f k`, `paren`), state `St`
  (rest of the tokens, output so far, run-time depth `d`, scope `(name, slot)` newest first, defs `(name, arity, number)`,
  current def name / fuel / arity). `step : Ctl → St → Res`, `run` iterates it with gas.
* The fuel of the recursive descent is replicated exactly (every control carries it, frames store the fuel of the
  continuation): `def f : UInt64 := ((1))` is rejected by the spec (fuel = token count + 1) and by the machine.
* Output = `serU u` directly (postfix micro-ops, slots relative to the depth `d`): a variable is
  `[7, d-1-slot] [3, 0]`, a call `args ++ [14, j/256] [15, j%256] [9, k]`, a def ends with `[13, arity]`.
* Not inlining: the machine first emitted the INLINED `ser p` (body bytes copied from the def table, commit 30b1d99,
  0 mismatches too); retargeted to `serU` after the integrator's split (`nanoElabU`, `inlB` as its own stage), so the
  parser stage's output is linear in its input and inlining is the next stage.

## Proof outline
* `Nano/ParseBProof.lean`: `Reach c s c' s'` (∃ n, ∀ g, run (g + n) c s = run g c' s'), `Fails c s` (∀ g, run g c s =
  none), composition lemmas; views (`letV`, `addV`, `starV`, `appV`, …) and, per parse function, two equation lemmas
  putting the spec and the machine on the SAME case split (`pExpr_succ` / `step_expr`, …; proved by exhausting token
  shapes to depth 3, `tcases`); table lemmas `findDef_dsOf`, `lookS_zip` (machine scope = `zip names slots`).
* `Nano/ParseBSim.lean`: `sim : ∀ f, PE f ∧ PA f ∧ PM f ∧ PT f ∧ PP f ∧ PG f ∧ PO f`, by induction on the fuel: for
  each parse function, `some (e, r)` ⇒ the machine goes from the call state to the return state with `serUE scD d e`
  appended (`pAdd`/`pMulT`: with the accumulator already emitted), `none` ⇒ it fails.
* `Nano/ParseBTop.lean`: `names_sim`, `params_sim` (slots `mkSc n 0`), `defs_sim` (defs numbered in order, output
  `serU acc`), `parseA_eq`, `stage2A_lexB` (with nano-elab's `lexB_eq`).

## What remains (exact)
1. **Layer B (the compiled stage).** A `ByteArray → ByteArray` loop for `wp_compile` that simulates `step` on stage 1's
   token bytes, plus `layerB_eq : parseB bs = stage2A G bs` (for every `bs`), plus the `Implements1Pg` theorem and
   `Nano.Link.of_pg` to get `Implements1With`, then `link_stage` with `Nano.Self.lexBE.implements1` gives `he`.
   Front-end constraints known (integrator probes, `Testing/nano/wp_stack_probe.lean`, `wp_copy_probe.lean`;
   NANO_INT.md 00:20/00:30): one tail call per step with every state component a conditional expression; a fixed
   number of pushed bytes per step; the stack inside the work buffer via `set!`; non-consuming steps need a
   lexicographic measure; the loop body is limited (~1000 words on the plain back end, more with `mop`/`compBFC`);
   each probe (one or two branches) took 3–15 min. Layer A needs ~25 transitions plus multi-step modes for name
   comparison (scope lookup, def lookup, duplicate-def check) and numerals (`sLi`: 9 micro-ops): far above the
   probes. My own probe of a 4-branch loop with `if c then go … else go …` shape (before reading the integrator's
   probe) did not finish in 15 min (stopped). Assessment: needs either front-end capacity (larger loop bodies,
   faster `GoodE` proofs) or splitting the parser into several small paged / list stages (e.g. (2a) token bytes →
   fixed-width tokens with def numbers resolved by rescanning, (2b) precedence + scopes with an explicit stack), each
   with its own equality proof against a layer-A-like spec.
2. **Gas: DONE.** `Φ c s = 13·|tokens| + 3·|frames| + κ(c)` drops on every continuing step (`step_dec`), so the run is
   linear: `13·|ts| + 6` steps suffice (`run_stable`, `parseA_gas`). A compiled layer B can use `Φ` (scaled by its
   sub-steps per layer-A step) as its `measure`.
3. Remaining hypotheses of the self-hosting theorem (`selfHosted_parse_asm`): the machine theorems `h1` (stage 1:
   `Nano.Self.lexBE.implements1`, parked in `Testing/nano/pending/ElabBSelf.lean.txt` by the integrator, not confirmed
   to build), `h2` (stage 2 = `stage2`: item 1), `hi` (`inlB`), `hm` (`mexp`), with their code-size bounds; the domain
   `Sized5` (arities < 256, ≤ 65536 defs, every intermediate ≤ 2^20 bytes and ≤ K). No equation hypothesis is left:
   `hfe` is `stage2_hfe`, the rest is `chain_eq` (integrator).

## Front-end rejections met
* (own probe, `Nano/ParseBProbe.lean`, deleted) `wp_compile` on a 4-branch stack loop: default heartbeats exceeded
  (`isDefEq` timeout, 2.5 min); with `maxHeartbeats 0` still running after 15 min of CPU (stopped by the harness
  time limit). The integrator's probe found why branching between different calls fails (`Decidable.rec` in the
  generated step proof); its accepted shape is above.

## Log
* 2026-11-17 00:00–00:30. Setup (build cache, toolchain); read NANO_INT / NANO_ELAB / Ser / Elab / WpCmd.
* 00:30. Layer A (inlining `ser p`), tested 3000 inputs, 0 mismatches. Pushed 30b1d99.
* (session paused by the usage limit 00:35–03:30.)
* 03:30. Merged nano-int (nanoElabU/serU/inlB/selfHosted_four). DECISION: retarget the parser to `serU`
  (non-inlining), because `selfHosted_four`'s `hfe` asks for exactly `serU u`, and inlining is then a separate copying
  stage. Re-tested: 0 mismatches.
* 03:45–04:30. Proofs: views, `sim`, `params_sim`, `defs_sim`, `parseA_eq`, `stage2A_lexB`. Axioms file in check.sh.
* 04:30–05:15. Explicit gas (`Nano/ParseBGas.lean`: `κ`, `Φ`, `step_dec` by exhausting `step`'s matches,
  `run_stable`); `stage2`, `stage2_lexB` (exact), `stage2_hfe`; `Nano/ParseBSelfHost.lean`: `selfHosted_parse`
  (five stages; `link_stage` over the source domain, so the lexer's output bound is only needed on `Sized5`, not for all
  inputs ≤ 2^20 as `selfHosted_four`'s `he` would ask) and `selfHosted_parse_asm` (`nanoAsm.implements1`;
  `nanoAsm.code.length < 2^17` by `decide +kernel`). Tests: `parseb_check.lean` now also checks `stage2 (lexB x)` =
  `serU`/`[]`: seed 7 × 3000 and seed 11 × 2000 inputs, 0 mismatches (551 accepted, 1060 lexed).
* Merged origin/nano-int e122335 (main merged there; check.sh loop now has `round1` and `nano-parse`).
* Note for the integrator: `Testing/nano/regen_nano_axioms.py` lists only nano-{e2e,proof,mvp,int}; if it is rerun,
  add `nano-parse` to its list or the three nano-parse lines are dropped from expected-axioms.txt.
