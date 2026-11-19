# NANO_V2_MAIN: the end-to-end statement for C (Opus box D)

File: `Nano/V2Self/Proof/Main/Main.lean` (namespace `NanoMain`), builds in ~2 s. No sorry. Axioms of `compiler_correct`:
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

## Non-vacuity (`Nano/V2Self/Proof/Tests/MainWitness.lean`, 19 s, 2.4 GB, axioms propext/choice/Quot.sound)
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
- `parsed_sc` (for E's `gen_top`): `ScV K d.body` (via `sc_of_okV`), body reads ⊆ parameters (`rd_body`), npw ≤ nslots.
  NOT derivable from parsing (a parsed program may have 300 parameters or 2^40 let slots): `DB` (fields < 2^32, `NB`),
  npw/nres < 251, npw < 2^20, `(serialize ds).length < 2^31` — these must come from Gen's success checks (A) or input size.

## In the owner's top-level vocabulary (`MainTop.lean`, 13 s; axioms = compiler #1's: Sail extern set + standard)
| | compiler #1 (`Riscv/Back/S3Top.lean`) | C (`Nano/V2Self/Proof/Main/MainTop.lean`) |
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

## HANDOFF (2026-11-19, keep current)
SOURCE LINK (D, 74c831c8): `SrcGen.link_pc : LexSpec.Lexes SrcGen.X0 SrcGen.W0 ∧ ParsesProgram SrcGen.W0 Cert.PC.all`
(axioms propext, Quot.sound).  Generic lemmas: Proof/SrcLink.lean (lexAll ⇒ Lexes, Lexes composes across '\n',
tokens composes, pDefs chain, refParse_of, defBeq/chkDef/lsBeq).  Generated: Proof/Src/{Data,Chk}0..30, Chain, Top by
`lake env lean --run Testing/nano/v2self/srclink/gen.lean Testing/nano/v2self/self_S_input.txt Nano/V2Self/Proof/Src 800`
(per-def text chunks cut before "\ndef "; full refParse in one kernel check runs out of memory, so per def; groups of
~800 tokens; full build ≈ 5 min wall in parallel).  Rerun the generator whenever self_S_input.txt or ParSpec changes.
Files (all no sorry, each ≤ 15 s): Main (statement, Sem, ImplementsC, ParStage/GenStage, compiler_correct), MainWitness
(non-vacuity), MainTy (kind judgment TyN/TyB, sem_ok), MainTyP (parser ⇒ well-kinded, parsed_not_stuck, compiler_correct'),
MainOk (E's OkV/ScV/reads ⊆ params: parsed_ok, parsed_sc, parsed_main), MainTop (C_correctL : ParStage → GenStage →
CompileCorrectL riscv compileC), MainCert (meaning certificates ex1, ex3).
OPEN / NEXT (owner order 2026-11-19):
1. Sem ⇐ sv bridge (E's NdSem `sv`/`defS`/`loopGo`, heap image Hp): soundness direction "sv succeeds ⇒ ev succeeds with
   related values" under a linearity hypothesis.  Value relation: word = word; buffer list ↔ pointer with `bufInfo` =
   (len, κ) and cells.  Matching checked by reading: cmpF 2 = unsigned <, rdF1 = getD, bget/bset out of range as Sem,
   bpush cap check `len < κ` = Sem's `push`, loopGo (env 0 = 0 / decE) = loopRun, len/len' = c29.  Needs the linearity
   interface (asked O whether their ownership rule is on Nd; proposed `LinN` with own/ro/dead flags mirroring Nano/V2 Own).
   Second direction still needed for ImplementsC's `space`: Sem ok ⇒ sv succeeds with enough stack room.
   LINEARITY = O's `OwnSpec.Linear p` (∃ Ks, progOk [] [] Ks p; walk `chk` with dead flags, kinds 0 word / 1 owned /
   2 read-only param; pins in argument lists).  BRIDGE DESIGN (layer 2, to do): ghost abstract heap σ : Nat → Option
   (List UInt64); `AHeap H σ` = every σ-block is `BufAt` in H, σ-blocks pairwise disjoint; value relation .w x ↔ word x,
   .b l ↔ σ addr = some l; slot invariant over Γ-known slots (TyN): kind 0 ⇒ word, kind ≥ 1 ∧ live ⇒ related, owned live
   slots' addresses distinct from every other live buffer slot.  Node theorem (mutual on TyN ∧ chk): sv succeeds ⇒ ev
   succeeds, results related in σ', σ' differs from σ only at blocks of slots consumed by e and at fresh blocks, plain
   kind-1 result entries are fresh/consumed blocks not held by any live slot after; pinned entries = the slot's address.
   Layer 1 (MainBridge.lean): BufAt + per-prim agreement (done).
   Layer 2 (MainBridge2): AHeap σ, VR, σ under BNEW/BPUSH/BSET (done).  Layer 3 (MainBridge3): EnvI, ResI, Ch, Mono,
   consume_spec (done).  MainKeep: static facts of O's walk (value mode) — it kills only kind-1 slots (`chk_keep`),
   tags carry their slot kind; `R2` = read-only slots live.
   `NodeOK cx K oc D e` (MainBridge4) = value-mode claim.  Premises: CtxOK, O's K ≤ 2, R2 F, EnvI, AHeap, tops.
   Conclusions: ev ok, AHeap, ResI, EnvI, Ch, Mono, tops, `Src` (an owned result whose block pre-existed is a slot
   consumed by the node — needed for LET scoping and call results), entry shapes (≤ 1 or tagged).
   DONE, all nodes (`node_all`, MainBridge11; no sorry, propext/choice/Quot.sound):
   const/loc/bin (4), ite (6), letE (7), argument lists `lst_ok` + pair (8), prims (9: own0 / borrow via finB),
   call (10: against the callee contract `DefR`/`CallR`).  Extra premises of node_all: RsOK (rs lengths = D),
   RsW (O's result kinds ≤ 1), CtxR (K.κ = cx.κ, c29 = |inp|, K.inp = inpW inp, |inp| < 2^64), CallR (every callee
   meets DefR: related args ⇒ related results; owned results fresh or owned-arg blocks, distinct; other blocks kept).
   DONE (2026-11-19), all no sorry, propext/choice/Quot.sound, each file ≤ 6 s / 1.7 GB:
   - tail mode `tail_all` (MainBridge12): `TailOK` = exit related as NodeOK, or CONTINUE states `StOK` (ArgsR at the
     state kinds stD + owned-state source + read-only states are read-only slots' blocks); `st_none` (value-mode
     tail template = exitS ∘ sv), `chk_len_tail`, `fin_args`.
   - loop `loop_run` (MainBridge13): E's `loopGo` succeeding ⇒ `Sem`'s `loopRun` with `ResR` (results in the callee
     contract's form) and `Frame0` (blocks existing at the call and not owned arguments' unchanged); invariant `LI`;
     `chk_keep_tail` (tail walk kills only owned slots), `envI_cont`, `envI_slot0`.
   - def `def_ok` (MainBridge14): plain body via node_all, loop body via loop_run ⇒ `DefR` for
     `defS npw nslots (sv K body)` vs `defMean`.  `NodeOK`/`DefR` also carry `Grow` (σ blocks never removed).
   - program (MainBridge15): `prog_ok` — for an O-accepted (progOk [] [] Ks ds, Ks entries ≤ 2), well-kinded (TyProg)
     program every `semAt P ds i` meets `DefR` against `(means inp P.κ [] ds)[i]` (E's PC with c29 = |inp|,
     inp = inpW inp); `main_bridge` — `semAt P ds (|ds|−1) [] sp H = some (vs, H')` (H.top 8-aligned, hb ≤ H.top) ⇒
     vs = [a], `BufAt hb κ H' a l`, `Sem P.κ ds inp = .ok (l.map toUInt8)`.
   OPEN for the end-to-end statement: (a) O's Linear has no slot-kind bound; the bridge needs every Ks entry ≤ 2
   (a kind ≥ 4 would decode tags to the wrong slot) — asked O to add it to defOk or prove it for o41's Ks;
   (b) the machine side from the start routine to `semAt main` (E's DefX chain + start words) — compose with
   main_bridge; (c) MainTop re-point to the o41 driver with subset = parsed ∧ Linear.
   Fuel-margin run on self_S (interpreted `lean --run`): did not finish in 40 min; needs a compiled exe.
   CONVERSE (A, 2026-11-19, MainConv1..7, no sorry, propext/choice/Quot.sound): `Mo` room monotonicity (semAt_mo:
   more stack room ⇒ same result); `Ex S H` = ∃ N, ∀ sp, H.top + N ≤ sp < 2^62 ⇒ S sp H ≠ none; NodeEx/TailEx/DefEx/CallEx
   (ex_all, tex_all, loop_ex, def_ex); `prog_both` (every def meets DefR and DefEx); `main_ex` (MainConv7, 70 s with deps):
   TyProg ∧ progOk (Ks ≤ 2) ∧ c29/inp ∧ κ < 2^40 ∧ H 8-aligned above hb ∧ `Sem P.κ ds inp = .ok y` ⇒ ∃ N, ∀ sp ∈ [H.top+N, 2^62),
   semAt main [] sp H = some ([a], H') ∧ BufAt hb κ H' a l ∧ y = l.map toUInt8.
   `main_room` (MainConv8): E's premise form — ∃ R uniform in the work base and in T (semAt_T: sv never reads K.T;
   unif_fin: finite max over base < 2^32), semAt (P with hb = base+16) main [] ((base+len)/8*8) ⟨base+16, ∅⟩ = some …
   when R ≤ len.
   CAP HALF DONE (MainConvX1..X7, E's SemX: semAtF, Fail = cap | room | stuck): semAtF_mo (non-room outcomes stable
   under more room), ExC/NodeExC/TailExC/DefExC/CallExC mirror of the Ex chain, main_cap, main_capR (uniform R, E's form).
   ALL-ROOM KINDS DONE (MainConvF2..F7): forward failure bridge FailOK f r := f = room ∨ (f = cap ∧ r = cap);
   NodeFail/TailFail/DefFail/CallFail; prog_fail; main_kind; `main_all`: for every sp, semAtF main = ok (BufAt, Sem ok
   agreeing) ∨ room ∨ (cap ∧ Sem = cap) — never stuck.  E assembles ImplementsC (space x from main_room/main_capR).
   DB/Bnd: P64 is FALSE for parsed programs (doubling pair lets: nslots = 2^(k+1) − 1; Testing/nano/v2self/parcap/
   wrap.lean).  Fix approved: O adds a parser cap `nx + w < 2^20` (Par1 + refParse) and proves parsed_bnd; then D
   discharges `BndStage` (Main) and repairs ParSerLen/MainTyP for the new refParse.  hXl DONE: ParSerLen.ser_len
   |serialize p| ≤ 4·|ts| + 1, ser_lt < 2^31; GenStage/BndStage carry ts.length < 2^24.
   STAGES (Main/MainTop): ParStage discharged (parStage = F's parserSound), OwnStage discharged (ownStage = O's
   own_stage); C_correctL : BndStage → GenStage → CompileCorrectL.
2. DONE (caf51274): driver `mC x = g41 x (o41 (y16 (s10 x)))`; `LinearK p := ∃ Ks, progOk [] [] Ks p ∧ Ks ≤ 2`;
   `OwnStage := ∀ p, o41 (serialize p) ≠ [] → LinearK p` (O's lemma, pending); `GenStage` now for parsed ∧ LinearK;
   `compiler_correct HP HO HG` gives `Lexes ∧ ParsesProgram ∧ LinearK ∧ ImplementsC`; `C_correctL : ParStage → OwnStage →
   GenStage → CompileCorrectL riscv compileC` (MainTop 12.6 s / 1.7 GB, axioms = compiler #1's).  `o41_ne`: o41 returns
   its input or []. Witnesses (MainWitness, 36 s / 2.7 GB) now include `C.o41 a = a` and `LinearK p` with explicit Ks
   ([[]], [[0,0],[]], [[0,0],[]]).  GenStage's Sem side is `main_bridge` (MainBridge15); what remains of GenStage is
   the machine run from the start words to `semAt main` (E) and the converse direction for the `space`/cap outcomes.
3. C-wide certificate generator (one Sem = Lean lemma per def) + kernel test of progEq on C's token stream.
   MEASURED (decide +kernel, prefixes of self_S_input.txt + a stub main): 713 bytes → lexer `C.s10` 35 s / 5.9 GB, lexer +
   `refParse` 36 s / 6.0 GB (parse is cheap next to the lexer); 7,714 bytes → killed at 9 GB.  So C's 66,620-byte text
   cannot be lexed in the kernel in one piece; route: lex per chunk (Lexes is compositional at whitespace boundaries:
   prove `Lexes (x₁ ++ x₂) (t₁ ++ t₂)` from both parts when x₁ ends in a newline), then `refParse` on the whole token list.
Gen-side bounds (DB, < 251, < 2^20, serialization < 2^31) are not parser facts: routed to A via owner.

## HANDOFF — C-wide certificate (F, 2026-11-19, keep current)
Goal: `Sem κC P_C inp = .ok y → y = C.m inp` (P_C = refParse of C's text: 234 defs, 46 fuel loops, pairs only in Own,
`List UInt8` results only in g42/g41/m), then the AST ↔ text link (chunked lexing, MAIN item 3).
DONE (pushed, no sorry, axioms propext/Quot.sound):
* `Proof/MainPure.lean` — cap-free evaluator `pev` / `pdefMean` / `pmeans`, `ev_pev`, `sem_pure` (an accepted `Sem` run is
  the cap-free main's value).  Certificates are EQUATIONS in the pev world.
* `Proof/MainCertRules.lean` — `Ev inp ms n env vs` (irreducible) + rules that build the Lean term: bin ops, `ev_ite1/2`
  (`if x == y` / `if x < y`, any encoding), `ev_letW/B` (result is a real `let`, env given explicitly), `ev_call`,
  `ev_callL` (fuel = `len' x`, callee equation in `LenC` form), prims, `pdef_env`.  (`ev_auto` tactic exists but is
  search-based and slow: not used.)
* `Testing/nano/v2self/gen_cert.py` (+ `ast_dump.lean`, usage in its header) — infers node shapes (word/buffer) and emits
  EXPLICIT proof terms.  `Proof/MainCertC0..8.lean` (GENERATED, 872 KB, ≤ 22 s each): for 164 plain defs
  `c<i> : pdefMean inp ms D<i> [args] = .ok [C.f args]` under hypotheses per callee j:
  `h<j> : ms[j]? = some F<j>`, `e<j> : ∀ args, F<j> [..] = .ok [C.f_j ..]` (Nat fuel a ↦ `a.toNat`), and for loop callees
  `l<j>` = the same at fuel `.w inp.length.toUInt64` with Lean fuel `len' inp`.
TODO, in order:
1. the 46 loop defs: tail-mode judgment (`Out`: value or CONTINUE payload) + induction template (MainCert Ex3.loop);
   generator support (kind = 1 in the AST dump).
2. pairs (Own: wide `loc` / `letE` w > 1, `.pair`, results `Buf × Buf`) and the three `List UInt8`-result defs (g42, g41, m:
   `put` pushes the word, value relation `l.map toUInt8`).
3. composition: fold all c<i> along `pmeans inp [] P_C` (needs `inp.length < 2^64` for the `l<j>` forms), `sem_pure`.
4. P_C = refParse of the text (progEq, chunked lexing).
Skipped ids now (loops, pairs, List results, and their callers): printed by gen_cert.py.
G's certificate HANDOFF was never pushed; nothing beyond MainCert ex1/ex3 existed.

## Parser WIDTH CAP (2026-11-19, O)
Par1 / ParSpec / ParRun reject slot counts and shape widths ≥ 2^20 (see NANO_V2_OWN.md "WIDTH CAP"); parserSound stays proved.
MainCertC3 / C4 / C5 (F's abandoned duplicate certificate) no longer build against the new Par1: NOT fixed, per the lead.  They are
imported by nothing, and the `Nano` lib is not a default target.  Canonical certificate: Proof/Cert (PC.lean regenerated with
gen_cert.py; all 46 tracked Cert files build, Defs35 still open as before).  ParSerLen / MainTyP (D) adapted to the pDef cap split.
`ParCapBnd` (O): `parsed_cap` (every parsed def: nslots, nres < 2^20), `parsed_bnd` (OwnWF.Bnd ∧ DB), `bndStage : BndStage`,
`capStage : CapStage`, hence `C_correctLO : CompileCorrectL riscv compileC` with no premises.  Axioms: propext,
Classical.choice, Quot.sound plus the Sail model's opaque platform/float externs (sail-riscv-lean RiscvExtras), no sorryAx.
