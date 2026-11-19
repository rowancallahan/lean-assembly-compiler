
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
