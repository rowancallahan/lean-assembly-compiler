
## Soundness / loophole audit of the final statement (box G, 2026-11-19)

Statement read: `NanoMain.C_correctLO : CompileCorrectL riscv compileC` (ParCapBnd.lean), with `Spec/Top.lean`,
`Compiler/AllocSpec.lean`, `Spec/RiscvMachine.lean`, `MainTop.lean` (SrcC, pOf, srcRun, spaceC, compileC), `Main.lean`
(Sem, ImplementsCW/ImplementsC). Read-only; the only new file is `Proof/AuditWitness.lean`.

### 1. Non-vacuity: the theorem instantiated for a real program (`Proof/AuditWitness.lean`, builds, no sorry)
Program: ParSpec's `ex1` (two defs, a call, prims), Lean function `Ex1.m`.
- `Audit.ex1_computes : Computes src Ex1.m id id` — PROVED outright (from `Ex1.cert`). Axioms: propext, choice, Quot.sound.
- `Audit.ex1_compiles : C.y16 (C.s10 x) = a → compileC src = some ⟨mC x, 1, _⟩` — CONDITIONAL on one parser run.
  That run cannot be kernel-checked for ANY program (Par1's fixed heap layout: one `bget` at word 184,384 is 28 s / 5.5 GB,
  MainWitness). It agrees natively. So "compileC p = some c" is not a kernel theorem for any p today.
- `Audit.ex1_applies`: `C_correctLO` applied to it: run to `ra`, status ≠ oomFlag, output = `Ex1.m inp`. Remaining hypotheses:
  the parser run above, `StartCorrect` (abstract, as instructed), output fits, and `spaceC x inp ≤ workLength` (finding A).
  Axioms: the Sail extern set + propext, choice, Quot.sound. No sorryAx.

### 2. Findings, most serious first
**A. `memoryNeeded` is an unconstrained `Classical.choose` — the memory premise cannot be discharged, and the theorem
does not exclude always-out-of-memory code.**
**STATUS: FIXED (339d759, E; recorded by O).** `spaceC x inp := max 16 (Msp p inp)`, where `Msp p x =
(16 + thr p x + 7) / 8 * 8` and `thr p x` is the LEAST number of usable bytes with which main does not run out of room
at any admissible 8-aligned work position (Proof/Machine/RunsDef.lean). So `memoryNeeded` is a definite, minimal
quantity, not an arbitrary choice. Both sides are pinned:
- `C_runs : ShiftInv → CompileRuns riscv compileC` (Proof/Main/RunsTop.lean): OOM is reported exactly below
  `memoryNeeded`, and the output block is untouched on OOM.
- `ShiftInv` is proved by D as `shiftInv` (c771775).
- `Msp_le` / `spaceC_le`: at most D's work bound + 30.

This rules out the always-OOM reading in consequence 1. Consequence 2 is reduced: the bound is minimal and finite, but
not given in closed form, because `gen_R`'s bound is an existential.
`compileC` reports `events inp = [.alloc (spaceC x inp)]`, so `memoryNeeded = spaceC x inp`, and
`spaceC := Classical.choose (h : ImplementsC (mC x) (Sem κC p))` with `ImplementsC B f := ∃ space, ImplementsCW B f space`.
`ImplementsCW` gets WEAKER as `space` grows (`oomOK := work.len < space x` only enables the OOM outcome), and with
`space := fun _ => 2^64` the OOM outcome is always allowed. Consequences:
  1. `ImplementsC B f` holds for any code that always returns a0 = −1, a1 = 0 and touches nothing; the comment in
     Main.lean / NANO_V2_MAIN.md ("the existential `space` rules out the always-OOM program") is not true.
  2. No theorem bounds `spaceC` from above, so for no concrete call can `memoryNeeded ≤ workLength` be proved — not even
     that it is below the RAM size 2^32 that `StartCorrect.inRam` forces on `workLength`. `C_correctLO` is therefore
     consistent with a compiler whose code never produces output. It is true, but its "what comes out" content is
     conditional on a number nobody can compute or bound.
  Not a soundness bug. The proof underneath HAS a concrete bound (`GenImpl.gen_implements` concludes
  `ImplementsCW … (fun x => max 16 (R x))`); it is lost at the `∃`/`choose`. Fix options: (i) define `spaceC` by that
  explicit function (then `memoryNeeded` is a stated quantity and non-vacuity is provable); (ii) keep `choose` but add a
  theorem `spaceC x inp ≤ <explicit bound>`; (iii) prove `CompileRunsL` (flag ⇔ `workLength < memoryNeeded`), which pins
  the value from both sides. I did not check what `R` is or how tight.

**B. Nothing says C accepts anything.** `compileC p = some _` needs `mC text ≠ []`. There is parser SOUNDNESS
(accepts ⇒ reference parse) but no completeness, and no kernel run (see 1). A compiler rejecting every text satisfies
`C_correctLO`. Usual for this shape of theorem; stated so it is not overread.

**C. `Computes` is total: capacity and domain.** `srcRun` is `none` when `Sem` hits Gen's buffer capacity κC = 524,288
(`.error .cap`) or is stuck; `Computes` then fails for that program unless `encodeInput` restricts the domain (it may: α is
arbitrary). Inputs above 2^20 bytes are excluded by `StartCorrect.inputSmall`. Fine, but a program that can reach the
capacity on some admitted input gets no guarantee on ANY input through this theorem.

**D. Meaning is ParSpec + `Sem`, not Lean's elaboration of the text.** The link to the Lean function is per program
(certificates). For C itself: `Cert.sem_C : Ref (Sem κC PC.all inp) (Sh.mLean inp)` (pushed, 234 defs; `Sh.mLean` is `mC`
verbatim), still to be linked to the text (`PC.all` = parse of the lexed source; D). One real Lean-vs-S difference
surfaced there: a `let` bound to numerals only (`let k := if … then 1 else 0`) is a `Nat` for Lean and a word for C. Equal
below 2^64 and only compared in C's source (the certificate proves the bound per occurrence); arithmetic on such a
variable would differ, and the generator would fail on it rather than pass.

### 3. Checked and found in order
- `pOf` (a `Classical.choose`) is unique: `lexes_det`, `refParse` is a function (`pOf_eq`). No freedom there.
- Conclusion not trivially true: zero steps would need pc = `returnAddress`, excluded by `returnOutsideCode` with
  non-empty code (`compileC` requires `mC ≠ []`) and `codeLoaded`; the output equation `readMemory … = some (f a)` and the
  length register are substantive; missing registers read as 0 in `riscvObserve`, but `configured` (Cfg) is also concluded.
- `CompileCorrectL → CompileCorrect` is proved in AllocSpec; `CompileRuns(L)` (OOM flag ⇔ out of memory) is NOT claimed
  for C anywhere.
- `Sem .error .stuck` gives `True` in `Outcome`, harmless: `Computes` forces `.ok`.

### 4. Not determined
- Whether `StartCorrect riscv …` together with `Cfg` is satisfiable (a concrete Sail start state): left abstract as
  instructed. The size constraints (blocks in [0x80000000, 0x100000000), pairwise apart, input ≤ 2^20) are plainly
  compatible; `Cfg` I did not examine.
- Whether `memoryNeeded ≤ workLength` is satisfiable: unknown by construction (finding A).

### B (follow-up, G): acceptance is not kernel-proved — measurements and routes
`compileC src = some _` needs `mC text ≠ []`, i.e. one run of the parser stage `C.y16`. Probe with `decide +kernel`:
- the cost is inside `y16 = v99` alone (lexer, Own and Gen on small inputs already kernel-check in MainWitness);
- v99 builds the fixed 184,384-word heap (`y15 = y5 184384`, one `bpush` per word on a `List`) and then every task reads
  and writes it by index; the heap term is lazy, so each forced cell passes through all pending `bpush`/`bset` layers;
- `(y5 n []).length = n`: n = 4,000 → 2 s / 0.5 GB; 16,000 → 4 s / 0.8 GB; 32,000 → 7 s / 1.2 GB;
  `(y15 []).length = 184384`: not finished in 280 s; one read through one write (`bget (bset (y15 []) 7 3) 7 = 3`): not
  finished in 280 s (D measured 28 s / 5.5 GB for a single read earlier);
- the smallest program (`def m (x : List UInt8) : List UInt8 := []`, 20 token words) needs on the order of 10^3 heap
  operations (estimate): orders of magnitude over 5 min / 8 GB.
What does not help: per-stage intermediate literals (the cost is all in `y16`); a "bounded heap prefix" lemma (the layout
is fixed, tokens sit at word 184,384 whatever the program size).
Routes that would work (not started; lead's decision 2026-11-19: documented as a limit):
- (c) completeness for one program: the converse of each machine handler it uses (`Rep ∧ stepF = some ⇒ status stays 1`);
  the Layer-3 proofs only give "machine did not fail ⇒ spec step". Estimate 1–2 days for one prover.
- (d) symbolic execution by rewriting, the heap kept as `base + finite map of written cells` over y5's closed form
  `h ++ replicate n 0`: ~10^3 rewrites through ~40 tasks of `v96`. Estimate 1 day, moderate risk.
- a representation change (Par1 over a compact heap + equivalence) or a token-count-dependent layout (compiler change, new
  fixpoint): days.
Native runs agree with the reference parser on all tested programs (fuzzer, the full C source).
