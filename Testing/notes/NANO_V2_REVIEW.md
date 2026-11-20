# NANO v2 self-hosted compiler C: owner review

What has to be trusted in C's correctness theorem. Companion file: `Nano/V2Self/REVIEW.lean`
(`lake build Nano.V2Self.REVIEW`, about 1 min warm), which `#check`s the items below and `#print`s the axioms. No new proofs.
[UNSURE] marks claims the author (O) has not checked against a proof.

## 1. The theorems

**Read this first: what the theorems do NOT say.**
- **Acceptance is not proved for any program.** Every theorem assumes `compileC s = some compiled`, i.e. C emits code
  (`mC s.text ≠ []`). The kernel has not shown this for any text (audit finding B). For C's own text it is shown only by
  running B1, because the kernel cannot evaluate `mC` on the 66 KB text.
- **All inputs or none.** `Computes` must hold for EVERY argument. A program whose meaning can hit a buffer's capacity
  (`cap`) on some input gets no guarantee for any `f` whose domain includes that input. Choose `α` to exclude those
  inputs, as `SelfIn` does for C itself.
- **"OOM exactly below `memoryNeeded`" is close to true by definition.** `memoryNeeded` is defined as the exact
  threshold of the compiled code's own run (`Msp`: the least work size with which main never runs out of room). So what
  `CompileRuns` adds is this: with too little memory, the code RETURNS and REPORTS out-of-memory (a0 = −1, output block
  untouched, kept registers and configuration intact). It never gives a wrong answer and never crashes or runs off.
- `Spec/` is frozen including `Spec/Alloc.lean` (owner, 4dd99338; `Spec/FROZEN.sha256`).

**`NanoMain.C_correctLO : CompileCorrect riscv compileC`**, at `Nano/V2Self/Proof/Main/RvTop.lean:38`. It has no
premises. It is the RISC-V instance of the generic `C_correct_on` (Main/TopOn.lean:76) over a target adapter
(`JTarget` + `Laws`, Machine/Target.lean). The adapter is proved, not trusted.

In plain words: take any source text `s` that C compiles, so `compileC s = some compiled`, and any reading of `s` as a
function `f : α → β`. A reading means `Computes`: for every `a : α`, the text's meaning on the bytes `encodeInput a` is
`some (encodeOutput (f a))`. Load `compiled.code` on the Sail RV64 model and call it according to `StartCorrect`, with
input of at most 2^20 bytes, an output block at least as long as the result, and at least `memoryNeeded compiled input`
bytes of work memory. Then the machine reaches, by retired instructions only, a state where:
- the PC is the return address;
- the status register a0 is not the OOM flag;
- the output block starts with the result, and a1 holds its length;
- the callee-saved registers are unchanged, and `Cfg` holds again;
- no memory outside the work block and the result prefix of the output block has changed.

**`NanoMain.C_runsO : CompileRuns riscv compileC`**, at `Main/RvTop.lean`. It has no premises. With ANY work block,
the code returns. Out of memory (a0 = −1) is reported exactly when `workLength < memoryNeeded`, and then only the work
block changes. `C_runs` (RvTop.lean:49) is the same statement with the former premise `ShiftInv`, which D proved as
`shiftInv`.

**`Cert.sem_C`**, at `Nano/V2Self/Proof/Cert/All.lean:288`. For every input of fewer than 2^64 bytes,
`Ref (Sem κC PC.all inp) (Sh.mLean inp)`. That is, C's own source text, parsed (`PC.all`, generated) and run under
`Sem`, agrees with the Lean function `Sh.mLean` (= `mC`, per E: `rfl`) up to buffer capacity. `Ref r v` (Cert/Rules.lean:12)
is `r = .error .cap ∨ r = .ok v`: either a buffer overflowed, or the result is exactly the Lean function's. `stuck` is
excluded.

**C compiled by itself** (E, `Nano/V2Self/Proof/Main/SelfC.lean`; the generic versions with `hsrc` as a hypothesis are in
`SelfLink.lean`). `SrcGen.X0` is the byte list of `Testing/nano/v2self/self_S_input.txt`: D's generator checks that its
chunks concatenate to exactly those bytes. D's kernel-checked `SrcGen.link_pc` says `X0` lexes and parses to
`Cert.PC.all`.
- `self_meaning_C`: for inputs shorter than 2^64 bytes, the meaning of `X0` either hits `cap` (and `srcRun` is `none`)
  or equals `mC inp`.
- `self_computes_C`: `X0` computes `mC` on `SelfIn`, the inputs whose meaning does not hit `cap`
  (`Main/SelfLink.lean:28`).
- `self_runs_C` (Main/RunsTopO.lean:13): the `CompileRuns` conclusion for C compiled by itself.
- `self_correct_C`: if `compileC ⟨X0⟩ = some compiled`, then for every `a : SelfIn` with a correct start, enough output
  space and at least `memoryNeeded` work bytes, the emitted code returns with `mC a` in the output block. It also gives
  the length register, unchanged memory outside the output and work blocks, the callee-saved registers and `Cfg`.
  Axioms: the same as `C_correctLO`, no `sorryAx`.
- **Not proved:** `compileC ⟨X0⟩ = some compiled`, which is a hypothesis of `self_correct_C`. It holds iff
  `mC X0 ≠ []`, and is shown only by running B1, because the kernel cannot evaluate `mC` on the 66 KB text. Also not
  proved: that the shipped `B2.bin` equals that `compiled.code` (see section 4, "The binary").

## 2. Definitions to trust

### Machine and calling convention (`Spec/`, hash-frozen by `Spec/FROZEN.sha256`)
- `Machine`, `Runs` (Spec/Top.lean:13, :23): states, a partial step function, an observation (PC, registers, byte memory),
  `configured`, a register mapping and a RAM range. `Runs` is zero or more successful steps.
- `Program`, `Computes` (Spec/Top.lean:29, :32): a source program is a partial bytes → bytes function. `Computes p f enc dec`
  says `run p (enc a) = some (dec (f a))` for ALL `a`.
- `Call`, `StartCorrect`, `readMemory`, `Present`, `Apart`, `Outside` (Spec/Top.lean:41–92): the start-state hypotheses.
  They cover: code at the PC; the input loaded at a0 with its length in a1 and at most 2^20 bytes; work base in a2 and
  work top in sp; output address in a3; the return address in ra; alignment (code 4, return 4, work 8); all four blocks
  inside RAM and pairwise disjoint; output and work bytes present.
- `riscv`, `riscvStep`, `riscvObserve` (Spec/RiscvMachine.lean:36, :31, :25): the Sail RV64 model. A step is one
  instruction that retires with `Retire_Success`; any trap or model error is "no step". Missing registers or memory read
  as 0 / `none`. RAM is `[0x80000000, 0x100000000)`.
- `riscvMapping` (Spec/Machines.lean:18): ra = x1; input a0/a1; work a2 and sp; output a3; status a0; output length a1;
  kept = sp, gp, tp, s0–s11.
- `Cfg` (Spec/Riscv.lean:12): the fixed control state. M-mode, hart active, fixed misa and mstatus (MIE = 0), PMP off,
  no HTIF, one rwx PMA region equal to RAM, and the listed registers present.

### Correctness notion (`Spec/Alloc.lean`, moved into Spec/ by owner instruction, adbf2d1)
- `CompileCorrect` (:130): the shape described in section 1. It was formerly `CompileCorrectL` in
  Compiler/AllocSpec.lean; the weaker forms are now `CompileCorrectWeak` (:81) and `CompileRunsWeak` (:65).
- `CompiledA` (:47) is code plus cell size plus memory events. `memoryNeeded` (:53) is cell size × the peak of those
  events. `KeptRegisters` (:108) and `oomFlag` (:57) = all ones.
- `Spec/Alloc.lean` is frozen: the owner re-froze Spec/ with it in `Spec/FROZEN.sha256` (4dd99338).

### Source language: lexer and parser
- `LexSpec.step`, `LexSpec.Lexes` (Nano/V2Self/Proof/Lex/Lex2Spec.lean:49, :65): maximal-munch lexing, one token per step.
  - Spaces and newlines are skipped; tabs and CR are rejected.
  - Operators are matched longest first; words are `[A-Za-z0-9_']+`.
  - Keywords and prims come from a table; other words are identifiers.
  - A digit-led word must be all digits and is a number taken **mod 2^64** (no overflow error).
  - Any other byte is rejected.
- `ParSpec.tokens`, `pDef`, `pDefs`, `refParse`, `ParsesProgram` (Nano/V2Self/Proof/Parser/ParSpec.lean:49, :379, :438, :447,
  :455): the reference grammar. The file header (lines 1–19) is the summary:
  - first-order defs and fuel loops;
  - `UInt64` / `Buf` / `List UInt8` / tuples, where the first `List UInt8` parameter is the implicit input;
  - `let`, `if` with `==` or `<`, binary operators;
  - self-calls only in tail position of a loop's step arm;
  - the program must end with `def m (x : List UInt8) : List UInt8`.
- **Width cap** (pDef, both branches, at ParSpec.lean:410 and :431): a def with `nslots ≥ 2^20` or result width
  `≥ 2^20` is rejected. Before this cap, doubling `let`s could make slot numbers wrap in the 64-bit serialization.
- **Fuel**: `refParse` uses fuel `8·|tokens| + 8` for the expression parser and `|tokens| + 1` for the def list. If it
  ran out, the text would be rejected, not mis-parsed. [UNSURE] The header calls the bound "never reached"; O has not
  seen a proof of that. It only matters for completeness, i.e. whether the theorem covers a text, never for soundness.

### Source language: semantics (Nano/V2Self/Proof/Main/Sem.lean)
- `Stop` (:29): `cap` means a buffer reached capacity κ. `stuck` means an ill-formed AST, which never happens for a
  parsed program (per NANO_V2_MAIN.md).
- `ev`, `evL`, `loopRun`, `prim`, `binop`, `setSlots` (:79, :70, :53, :44, :41): a word-level evaluator over slots.
  - Arithmetic is UInt64, wrapping mod 2^64. Shifts are `<<<` / `>>>` on UInt64, which take the shift amount mod 64.
  - `rd x i` out of range gives 0. `bget` out of range gives 0. `bset` out of range leaves the buffer unchanged.
  - A fuel loop runs the zero arm at fuel 0; otherwise it runs the step arm with slot 0 = fuel − 1, and a CONTINUE
    rewrites the states.
- `defMean`, `means` (:114, :121): each def's meaning uses only earlier defs, so there is no recursion except fuel loops.
- `Sem` (:127): runs the last def (main) with no explicit arguments; the input is implicit. Main must return a buffer.
  The output is the **low byte of each word**.
- `κC = 524288` (:136): buffer capacity in words. Exceeding it gives `.error .cap`.

### The compiler as a function (Nano/V2Self/Proof/Main/Compile.lean)
- `SrcC` (:26) is a text. `pOf` (:31) is the program the text denotes, chosen with `Classical.choose`. It is still
  determined: lexing is deterministic (`lexes_det`) and `refParse` is a function (`pOf_eq`).
- `srcRun` (:43): `pOf`, then `Sem κC`. `.cap` and `.stuck` both become `none`. This is the `Program SrcC` instance (:46).
- `spaceC` (:49): the work-memory bound, `max 16 (Msp p inp)` for the program `p = pOf x` (0 if the text
  is not a program). `Msp` (Machine/RunsDef.lean:48) is `(16 + thr p inp + 7) / 8 * 8`, where `thr p inp` (:45) is
  the LEAST number of usable bytes (above the 16-byte reserve) with which main does not run out of room at ANY
  admissible 8-aligned work-block position (searched up to 2^32). It is defined as a least element, so
  `Classical` decidability is used, but it is a definite number, not an arbitrary choice (audit finding A, fixed in
  339d759).
- `compileC` (:55): `some ⟨mC text, cellSize 1, events = [alloc (spaceC text inp)]⟩` when `mC text ≠ []` and the text
  is at most 2^20 bytes; otherwise `none`. So `memoryNeeded = spaceC text inp`.
- `mC` (Sem.lean:18) is C's driver as Lean code: `g41 x (o41 (y16 (s10 x)))`. It is the implementation, not a
  specification; the theorem covers it.

## 3. Things a reviewer should know
1. **The memory bound is exact but not computed.** `memoryNeeded = max 16 (Msp p inp)` is the least sufficient work
   size (see `spaceC` above), so "OOM iff below `memoryNeeded`" is nearly definitional (see §1). `C_runsO` /
   `C_runs` (Main/RvTop.lean) say the code returns with any work block and reports out-of-memory EXACTLY when
   `workLength < memoryNeeded`. D proved `ShiftInv`
   as `shiftInv` (Bridge/MainShift4.lean; axioms propext, Classical.choice, Quot.sound); `C_runsO` is
   premise-free (Main/RvTop.lean), and `self_runs_C` (Main/RunsTopO.lean) covers C compiled by itself. A concrete value is kernel-checked: `AuditSpace.spaceC_ex1_eq : spaceC Witness.x2 [5] = 4194416`
   (D, Tests/AuditSpace.lean), i.e. the audit example on input [5] needs exactly 4,194,416 work bytes. Upper bound:
   `spaceC_le` (Main/Compile.lean:97) / `Msp_le` give at most D's work bound `gen_R` + 30 bytes. `gen_R`'s bound is itself an existential
   (`Classical.choose`), so there is still no closed-form number per program. [UNSURE] whether a closed form is
   planned.
2. **`Computes` is for all arguments.** If `Sem` hits `cap` or `stuck` on some encoded input, `srcRun` is `none` there.
   Such an `f` cannot satisfy `Computes`, so pick `α` to exclude those inputs. E's SelfLink theorem does exactly this:
   it uses a restricted input type that excludes the inputs that hit `cap`. What the code does on a `cap` input
   (the stub returns a0 = −2) is not part of `CompileCorrect` / `CompileRuns`.
3. **Limits.** Source text at most 2^20 bytes (`compileC`). Program input at most 2^20 bytes (`StartCorrect`). Token
   stream below 2^24 words is internal (it follows from at most 9 words per byte). Defs are capped at
   `nslots < 2^20` and result width `< 2^20`. Buffers hold at most 524288 words.
4. **`Classical.choice`** appears in `pOf` and in `thr` (least-element search), so `compileC`, `srcRun` and `riscv` are noncomputable.
   `compileC`'s code component is the computable `mC`.
5. **Rejections are not errors in the statement.** `compileC = none` whenever `mC` returns `[]`. The theorem says
   nothing about which texts C accepts; there is no completeness theorem.
6. **Numbers and `put`** wrap silently: numerals mod 2^64, arithmetic mod 2^64, and output bytes are word mod 256.

## 4. Axioms and trust base
- `#print axioms NanoMain.C_correctLO` (see REVIEW.lean output): propext, Classical.choice, Quot.sound, plus the opaque
  declarations of the Sail model in `sail-riscv-lean/LeanRV64D/RiscvExtras.lean`:
  - `cancel_reservation`, `load_reservation`, `match_reservation`, `valid_reservation`;
  - `get_16_random_bits`, `plat_term_write`, `sys_enable_experimental_extensions`;
  - the `riscv_f16*/f32*/f64*` float operations, conversions and `riscv_*To*`.

  These are uninterpreted functions with inhabited types; they model platform effects and softfloat. [UNSURE] That C's
  code never executes an instruction whose result depends on them (atomics, floats) is implied by the proof going
  through, but O did not check it separately.
- `#print axioms Cert.sem_C`: propext, Quot.sound.
- **Pinned:** `Testing/scripts/review_axioms.txt` holds the exact `#print axioms` line of each REVIEW theorem (8).
  `Testing/scripts/review_axioms.sh` diffs against it and fails on any change; `--pin` rewrites it after an approved change.
- No `sorry`, no `native_decide`, no `bv_decide`, no `extern` in the proofs.
- Trusted: the Lean kernel; the Sail RV64 model (sail-riscv-lean, from the `build-cache` branch) as a description of
  RISC-V; `Spec/` (frozen, including `Spec/Alloc.lean`); the definitions in section 2.
- **Trusted generator chain** (Python / Lean programs whose OUTPUT the kernel checks, but whose choice of input is not
  checked):
  - `Testing/nano/v2self/build_self_S.py`: concatenates `C/{Base,Lex2,Par1,Own,Gen}.lean` into `self_S.lean` and
    `self_S_input.txt` (C's text). Nothing kernel-checks that this text is "C's source"; the kernel only checks what
    the text means.
  - `SrcGen.X0 = self_S_input.txt` is checked by the GENERATOR (`srclink/gen.lean` refuses to write the modules unless
    its chunks concatenate to exactly the file's bytes), not by the kernel. The kernel checks `link_pc` for `X0` as
    written in the generated modules.
  - `Testing/nano/v2self/cert/gen_cert.py` (+ `dump_pc.lean`): writes `Proof/Cert/`. The kernel checks every certificate
    it writes, so a wrong generator can only produce a failing build, not a false theorem. Its target `Sh.mLean` is
    `mC` by `rfl`.
  - `Testing/nano/v2self/srclink/gen.lean`: writes `Proof/SrcLink/`. Kernel-checked like the certificate.
- **The shipped `B2.bin` = `compiled.code` is NOT proved** (see "The binary" below).
- **The binary.** The theorem is about `mC`, a Lean function. The shipped bytes `B2.bin` (340,296 B, sha256
  `24759aa0f757e50e92e67d498a84f28ec7a0b13da6f2c9fc3d76cd0679699ed4`; before perf-names 337,856 B, `bb5558a5…`) were produced by **B1**: `self_S.lean` compiled by
  the Lean toolchain (`lean -c` + `leanc`) with `BootPrelude.lean`, which uses Array buffers in place of the List
  prelude and is marked TRUSTED in build_B1.py.
  - Kernel-checked: the meaning (`Sem`) of C's source text equals `mC`, the Lean `C.*` definitions. This is `Cert.sem_C`
    plus D's link `pOf text = some PC.all`. `self_S.lean` is a plain concatenation of `Nano/V2Self/C/{Base,Lex2,Par1,
    Own,Gen}.lean` plus the driver line (build_self_S.py).
  - Still trusted for B2 = `mC (C's text)`:
    - the Lean compiler that builds B1;
    - BootPrelude ≡ Prelude (Array vs List buffers), including build_B1.py's textual rewrite of `List UInt8` to
      `Array UInt8` and `[]` to `#[]` in the copy of self_S.lean that B1 is built from.
  - The fixpoint B3 == B2, with B3 = B2 run on QEMU on its own source, is a **test** on QEMU, not on Sail, and not a
    proof.
