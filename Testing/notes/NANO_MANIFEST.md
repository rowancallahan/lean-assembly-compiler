# NANO_MANIFEST: nano v1, every stage (integration branch nano-parse-s3)

Rule (owner, ROADMAP "FREEZE BEFORE THE FULL RUN"): every stage has its source, a bridge `= original` on EVERY
input, a stage theorem with the Sail axioms only, and builds in ≤ 5 min. When every row is done and
`bash Testing/scripts/check.sh` passes, the revision is tagged `nano-v1-rc1`. The full run uses only the tag.

Composition: FIVE stages lexA → 2b → inliner → expander → assembler (`Nano.selfHosted`, Nano/SelfHostFinal.lean;
equivalently `selfHosted_parse5S`, Nano/SelfHostSplit5.lean):
`SelfHosted binary (fun _ => space5 K) (Sized5S … ∧ LeanLimits) nanoCompileA`. `Nano.selfHosted` is its instance once
nano-final's lexA stage theorem lands. Superseded compiles (> 5 min) are in the non-default lib `NanoSlow`
(listCS lexer halves `vBE`/`eBE` + `SelfHostedA`, paged inliners `InlPSelf`/`InlRSelf`/`InlRPSelf`); the 7-stage
composition `selfHosted_parse7` (Nano/SelfHostSplit7.lean) stays as a proved alternative.

| stage | spec function | route | source file | bridge (every input) | stage theorem | build wall | `#print axioms` | status |
|---|---|---|---|---|---|---|---|---|
| front: lexer + parser 2a | `lexA = stage2a ∘ lexB` | S3 (`s3_compileF`) | Nano/LexS3.lean, Nano/LexS3Self.lean (nano-final) | `Nano.LS.lexA_eq` | `Nano.LS.lexA_implements` (Nano/LexS3Stage.lean) | LexS3 5 s, LexS3Self 54 s, LexS3Stage 39 s | Sail set (+ propext, Classical.choice, Quot.sound) | DONE (nano-final) |
| parser 2b (machine) | `stage2b` (`stage2b (stage2a x) = stage2 x`) | S3 (`s3_compileF`) | Nano/ParseS3B.lean, Nano/ParseS3BSelfA/B/C.lean, Nano/ParseS3BSelf.lean | `Nano.PS.stage2b_stage2a` (+ `stage2S_eq`) | `Nano.PS.stage2B_implements` (Nano/ParseS3BAllocA.lean, ParseS3BLow18, ParseS3BAllocB, ParseS3BLayA/B, ParseS3BEmitA/B, Nano/ParseS3BStage.lean) | 12 files, each ≤ 155 s / 6.3 GB cold (table "Build resources") | Sail set + propext, Classical.choice, Quot.sound | DONE (46054 words); QEMU 166/166 ×2 (inputs `stage2a (lexB src)`, expected `stage2`; raw tag bytes vs `stage2b`), Sail 6/6 ×2 |
| inliner | `inlB` | S3 (`s3_compileB`) | Nano/InlS3.lean (`inlBS`), Nano/InlS3Self.lean | `Nano.IS.inlBS_eq` | `Nano.IS.inlS3_implements` (Nano/InlS3Stage.lean) | < 1 min + 12 s | Sail (expected; checked at final build) | DONE; QEMU 146/146 ×2, Sail 6/6 ×2 (here); pool runner: QEMU 871, Sail 5 |
| expander | `mexp` | frontx listCS | Nano/ExpandM.lean (`mx`), Nano/ExpandMSelf.lean | `Nano.MX.mexp_eq_mx` | `Nano.Self.nanoExpM.implements1` | 49 s (nano-final note) | Sail (+ propext, Classical.choice, Quot.sound) | DONE; pool runner: QEMU 1266, Sail 5 |
| assembler | `asm` | frontx | Nano/Asm.lean, Nano/AsmSelfC.lean, Nano/AsmSelf.lean | (verbatim) | `Nano.Self.nanoAsm.implements1` | 125 s + 13 s cold | Sail (+ propext, Classical.choice, Quot.sound) | DONE; pool runner: QEMU 239/239, Sail 5 |
| composition | — | — | Nano/SelfHostFinal.lean (nano-final), Nano/LeanLimits.lean; also Nano/SelfHostSplit5.lean, Nano/SelfHostSplit7.lean | — | **`Nano.selfHosted (K) : SelfHosted binary (fun _ => space5 K) (Domain K) nanoCompileA`**, no hypotheses (domain `SizedL … ∧ LeanLimits`) | < 1 min | exactly the Sail set of `S3.compile_correct` | DONE |

Shared infrastructure (this branch): S3 front-end extensions (`s3_compileB`, `s3_bytes`, `s3_splitB`, `s3.depth`;
Compiler/S3/Front.lean, Cert.lean, SimpAttr.lean), the adapter `Proven.S3.implements1` (Riscv/Back/S3Impl1.lean,
IR stub: a1 = result length), `Nano.S3Stage.stage` + kernel-literal compiler acceptance (Nano/S3Stage.lean).
Tests: `python3 Testing/nano/ps3_test.py R S seed` (S3 stages; QEMU bulk, Sail smoke). Notes: NANO_PARSE_S3.md.

Superseded compiles (> 5 min) are archived in Testing/nano/archive/ (nano-final's layout): the listCS lexer halves,
`SelfHostedA`, the paged inliners.

Gate status (12:16): every row DONE; `bash Testing/scripts/check.sh` at **6a76836**: ALL CHECKS PASSED (1026 s; the only
warning is the statement-fingerprint one, definitions under headline statements changed by the IR stub, statements
unchanged, not re-frozen). Tag `nano-v1-rc1` created on 6a76836; pushing tags is refused by this session's git proxy
(branch pushes work), so the tag must be pushed from another session: `git tag -a nano-v1-rc1 6a76836`.

## nano v1 rc2

Commit **152f05b** (branch nano-parse-s3). `bash Testing/scripts/check.sh` at 152f05b: ALL CHECKS PASSED (1177 s,
peak 4.7 GB; the only warning is the statement-fingerprint one, unchanged since rc1, no Nano declaration listed, not
re-frozen). `Nano.selfHosted` builds; its axioms are the expected-axioms.txt line (77, the Sail set), as
`Nano.PS.stage2B_implements`.

- **Every module builds in ≤ 5 min from scratch** (table below): the slowest is Nano.ParseS3BSelfB, 155 s (`cert18`,
  one theorem; ≈ 230 s on a box 1.5× slower), every other module ≤ 127 s; every module ≤ 6.3 GB peak (rc1: 6 min 26 s,
  6 min 10 s, 10.1 GB).
- **The words of `binary` did not change.** Only proofs and file boundaries moved: (1) `s3_compileF … s3_part a b`
  (Compiler/S3/FrontPart.lean) elaborates the same generated commands of `s3_compileF` in index ranges, so
  `Stage2B.P` is the same definition; (2) the allocation of function 18 goes through its lowered literal
  (`stage2B_g18`, `stage2B_a18'`); (3) `stage2B_hE` (same statement) comes from `emitFsQ` checked in three pieces
  (Nano/EmitSplit.lean: `emitFsQ_append`, `emitFs_of_Q`, `emitP_lt`); (4) AsmSelf's `frontx_compile` moved to
  Nano/AsmSelfC.lean, and `frontx_implements_listC nanoAsm` is written out with the register choice (untrusted,
  kernel-checked by `optB`) as a literal, the same `tbl`/`spl` the macro computed. Checked by evaluation: stage 2b, old monolithic file vs new, 46054 words with equal hash;
  asm, old file vs new, 379 words, equal hash, 23 slots. No new gate needed; the 2b QEMU/Sail tests were not re-run
  (same words).
- Tag: `git tag -a nano-v1-rc2 152f05b` (the owner pushes it; this session's proxy refuses tags).

Build resources (rc2; each module FROM SCRATCH: its .olean removed, then `/usr/bin/time -f '%e s %M KB' timeout 10m
lake build +M`, alone on a 4-core / 15 GB box, imports already built; peak RSS of the lake process tree). Every
module of nano and of the stage-2b chain is listed if it takes > 10 s; the Spec/Compiler/Riscv modules come from the
build cache and were measured in Testing/notes/BUILD_PROFILE.md (slowest Riscv.Steps.GenMem 139 s).

| module | wall | peak RSS | content |
|---|---|---|---|
| Nano.ParseS3BSelfA | 107 s | 3.0 GB | `s3_compileF Stage2B := stage2b s3_part 0 84`: program, oracle, first certificates |
| Nano.ParseS3BSelfB | 155 s | 5.3 GB | commands [84, 88): `cert18` (131 s of kernel/elaboration alone) |
| Nano.ParseS3BSelfC | 89 s | 3.0 GB | commands [88, 172) |
| Nano.ParseS3BSelf | 99 s | 2.4 GB | commands [172, 215): last certificates, `main_good`, `wf`, `computes` |
| Nano.ParseS3BAllocA | 94 s | 4.7 GB | allocation of every function except 18 |
| Nano.ParseS3BLow18 | 44 s | 6.0 GB | `lowFn Stage2B.P 18 = stage2B_G18` (literal) |
| Nano.ParseS3BAllocB | 70 s | 2.5 GB | `Func.alloc1 stage2B_G18 = some stage2B_F18` |
| Nano.ParseS3BLayA | 87 s | 6.3 GB | `stage2B_hQ`, layout rounds `h1`, `h2` |
| Nano.ParseS3BLayB | 46 s | 6.1 GB | layout fixpoint, `hm`, `hL` |
| Nano.ParseS3BEmitA | 18 s | 3.6 GB | `emitFsQ` on functions 0 .. 17 |
| Nano.ParseS3BEmitB | 20 s | 3.8 GB | `emitFsQ` on function 18 (17754 words) |
| Nano.ParseS3BStage | 21 s | 3.8 GB | `emitFsQ` on functions 19 .. 41, `stage2B_hE`, `stage2B_implements` |
| Nano.AsmSelfC | 125 s | 2.4 GB | `frontx_view`, `frontx_compile` of `asm` |
| Nano.AsmSelf | 13 s | 2.7 GB | `frontx_entry`, `frontx_implements_listC` written out, register choice as a literal |
| Riscv.Frontx.S3RecExamplesA | 124 s | 2.5 GB | (not nano) structural entries, split off S3RecExamples (182 s) |
| Riscv.Frontx.S3RecExamples | 53 s | 2.1 GB | (not nano) the other entries |
| Riscv.Frontx.S3Examples | 127 s | 2.5 GB | (not nano) |
| Nano.LexS3Self | 82 s | 2.7 GB | lexA S3 compile |
| Nano.ExpandMSelf | 65 s | 4.7 GB | expander |
| Nano.Agree | 54 s | 4.1 GB | |
| Nano.LexS3Stage | 45 s | 3.2 GB | |
| Nano.SelfHostFinal | 31 s | 4.7 GB | `Nano.selfHosted` |
| Nano.InlS3Self | 21 s | 2.0 GB | |
| Nano.InlS3Stage | 14 s | 2.3 GB | |

Before rc2 (rc1, 6a76836, from scratch): ParseS3BSelf 6 min 26 s / 6.05 GB, ParseS3BStage 6 min 10 s / 10.0 GB,
ParseS3BAllocB 160 s / 10.1 GB, AsmSelf 321 s / 3.4 GB (186 s of it the interpreted register choice `pickListC`),
Riscv.Frontx.S3RecExamples 182 s. The full `lake build Spec Compiler Riscv Arm Frontx Nano`
(4 parallel jobs, 54 modules rebuilt over the cache) peaked at 4.7 GB.

Earlier gate status (11:33, superseded by the 12:16 status above): check.sh ALL CHECKS PASSED at 11:03 and again at 11:33 (head before CertBytes; 1022 s). The tag `nano-v1-rc1` is NOT set: the
front stage (lexA) is the one missing row.

## Self-run (nano-v1-rc1)

Revision 6a76836 (gate commit; `Nano.selfHosted (K) : SelfHosted binary (fun _ => space5 K) (Domain K) nanoCompileA`).
No Lean source under Nano/, Compiler/, Riscv/, Spec/ changed. Files: Testing/nano/selfrun/ (`build.sh` + `build.log`,
`emit_selfrun.lean`, `selfrun_test.py`, `run_summary.log`, `cases_final.txt`). 4 cores, 15 GB RAM + 12 GB swap.

**Build** (`Testing/nano/selfrun/build.sh`): build cache restored (`build-cache` branch: Sail model + `.lake/build` of
main f1cfb76, so Spec/Compiler/Riscv/Frontx came from the cache; every Nano module and the S3 modules newer than
f1cfb76 were compiled). Heavy modules one at a time, each under `/usr/bin/time -v timeout`:
ParseS3BSelf 5:39 (6.1 GB), AllocA 1:26 (4.6 GB), AllocB 2:54 (**10.1 GB**), ParseS3BStage 3:04 (9.6 GB),
LexS3Self 1:11, LexS3Stage 0:43, InlS3Self 0:19, InlS3Stage 0:12, ExpandMSelf 0:59, ParseBSelfHost 4:55,
SelfHostFinal 0:28. **Total wall 1390 s (23 min 10 s); peak system memory 11.0 GB** (RAM + swap used, sampled
every 2 s); largest single process 10.06 GB (ParseS3BAllocB, above the 7.6 GB noted earlier). All steps exit 0.
`#print axioms Nano.selfHosted` = the `Nano.selfHosted` line of expected-axioms.txt (Sail set + propext,
Classical.choice, Quot.sound).

**Words of `binary`: 55529** = stub 18 × 4 + lexA 5958 + 2b 46054 + inliner 2035 + expM 1031 + asm 379.
How: `binary` is noncomputable (`S3.words`). `emit_selfrun.lean` defines a computable `binaryC` (each S3 component
`((rvT.emitP Q L2).map rvT.words).getD []` on the stage files' literal allocation `Q` and layout `L2`, then the
same `link` nesting with `nanoExpM.code` / `nanoAsm.code`) and PROVES `binaryC_eq : binary = binaryC` by rewriting
with `Nano.S3Stage.words_eq'` and the stage files' kernel-checked facts (`*_hQ`: `alloc (lowerP P) = some Q`,
`*_hL`/`*_fix`: layout fixpoint, `*_hm`: `2 ≤ rounds Q`). So the full `rounds` layout is not approximated: the
equality is a theorem (no sorry, no new axioms; checks in 7 s). The words written are `#eval binaryC` (Lean's
compiled evaluator, < 1 s).

**Inputs**: 146 sources = CORPUS (39) + INT_CORPUS (27) + 30 random UInt64 + 30 random Int64 + 20 mid-size random
UInt64 programs (3–6 defs, depth 3–5), seed 11; sources up to 776 bytes, outputs up to 9304 bytes. All 146 in
`Domain K` (elaborator accepts, `nanoCompileA` accepts, `d.1 < 256`, `u.length ≤ 65536`, intermediates ≤ 2^20,
`LeanLimits` checked on the elaborated program). Expected = code of `nanoCompileA (nanoElab src)`, evaluated in Lean
(also asserted equal to `asm (mexp (inlB (serU u)))`).

**K per source**: K = max(intermediate lengths, lexA's memoryNeeded (IR interpreter), W(2b), W(inliner), the
expM/asm spaces); the work is `space5 K`. W(2b), W(inliner) were found on QEMU (the interpreted IR interpreter takes
~110 s per KB for 2b): each stage alone, work doubled until its OOM flag clears, then bisected to within 1/32
(ir_test.py checks the IR stages' flag exactly at memoryNeeded − 1 / memoryNeeded). This is per input, not `spaceP`
(max over all inputs of the length), so the tested work is at most the theorem's. K 17888..2348672 bytes,
`space5 K` up to 601 MB.

**Results** (`python3 Testing/nano/selfrun/selfrun_test.py 30 20 8 11`, 416 s):
- linked `binary`, QEMU: **146/146** — output = expected bytes, a1 = length, a0 ≠ −1 (flag clear), gp/sp restored,
  guards around input / output / work intact.
- linked `binary`, Sail: **8/8** (4 smallest works, 4 largest sources ≤ 400 B: 362–386 B) — QEMU == Sail == Lean,
  every Sail write inside the output or work block.
- 2b alone 146/146 and inliner alone 146/146 on QEMU (every flag-clear run checked against `serU u` / `inlB`).
- lexA alone (`nano_lexA`, the first component of `binaryC`, expected `stage2a (lexB src)`, exact memoryNeeded):
  QEMU 146 × 2 (output at memoryNeeded, flag at memoryNeeded − 1), Sail 8 × 2.
- **Mismatches: none.**

Notes:
- The OOM flag of the linked binary is only the LAST stage's a0: the link stub does not pass an inner stage's flag on
  (`Implements1With` states nothing about a0). A too-small K therefore shows as wrong output, not as a flag; that
  is why K comes from per-stage runs and not from retrying the linked binary.
- `space5` gives the first stage W/256 of the work, so the linked binary needs ~256× the largest stage need: on a
  1312-byte random program (6–11 defs, depth 4–6; trial run) the inliner alone needed 11.3 MB, `space5 K` ≈ 2.9 GB, beyond the
  harness's 1 GB QEMU; such sources are reported as "not run linked" (none in the final run).
- ROADMAP sections "FREEZE BEFORE THE FULL RUN", "ONE GATE", "GATE REACHED" are not present at 6a76836.

## nano v2-design: all stages on S3 ("B on S3", branch nano-s3-all)

ROADMAP ORDER step 2: every stage of B compiled by the S3 compiler (proved once); per stage only a Lean bridge
(`= original` on every input) and kernel evaluation of the IR compiler on the program (`irLit%`/`layLit%` literals). No
frontx certificate is left in the composition.

| stage | spec | source / S3 compile | bridge (every input) | stage theorem | cold build (file, wall, peak) |
|---|---|---|---|---|---|
| lexer + parser 2a | `stage2a ∘ lexB` | (unchanged) Nano/LexS3.lean, LexS3Self.lean | `Nano.LS.lexA_eq` | `Nano.LS.lexA_implements` | (v1 table) |
| parser 2b | `stage2b` | (unchanged) | `Nano.PS.stage2b_stage2a` | `Nano.PS.stage2B_implements` | (v1 table) |
| inliner | `inlB` | (unchanged) | `Nano.IS.inlBS_eq` | `Nano.IS.inlS3_implements` | (v1 table) |
| **expander** | `mexp` | `mexp` VERBATIM: Nano/ExpS3Self.lean (`s3_compileF ExpS3 := Nano.mexp`) | `rfl` | `Nano.XS.expS3_implements` (Nano/ExpS3Stage.lean) | ExpS3Self 35.9 s / 3.8 GB, ExpS3Stage 15.1 s / 2.6 GB |
| **assembler** | `asm` | Nano/AsmS3.lean (`asmS`: bytes computed as `UInt64` words then `toUInt8`, S3 has no `UInt8` arithmetic; same op case split), Nano/AsmS3Self.lean (`s3_compileF`, `s3.depth 24`: the op chain is 12 deep) | `Nano.AS.asmS_eq` (9 single-byte piece lemmas, each `decide +kernel` over the 256 bytes) | `Nano.AS.asmS3_implements` (Nano/AsmS3Stage.lean) | AsmS3 2.2 s, AsmS3Self 11.8 s / 2.0 GB, AsmS3Stage 10.4 s / 2.3 GB |
| composition | — | Nano/SelfHostS3.lean | — | **`Nano.selfHostedS3 (K) : SelfHosted binaryS3 (fun _ => space5 K) (DomainS3 K) nanoCompileA`**, no hypotheses; `DomainS3 K src := SizedL K sLex s2bF siF smS saS src ∧ LeanLimits src` (smS/saS = `spaceP` of the S3 expander/assembler) | 1.3 s / 1.8 GB |

Cold = the module's .olean removed, `/usr/bin/time -f '%e s %M KB' timeout 10m lake build +M`, imports built.
`Nano.selfHosted` (v1, frontx expander/assembler) is unchanged and still builds; `selfHostedS3` reuses its composition
lemma `selfHosted_lexA` with the two S3 stage theorems.

Axioms (Testing/scripts/axioms_nano-s3-all.lean, in check.sh): `Nano.selfHostedS3` = exactly the `Nano.selfHosted` set
(Sail set + propext, Classical.choice, Quot.sound); `ExpS3.computes`, `AsmS3.computes` ⊆ {propext, Classical.choice,
Quot.sound}; `asmS_eq` ⊆ {propext, Quot.sound}.

Tests (before merging origin/main at 1cdf8f8):
- per stage, `python3 Testing/nano/bs3_test.py 20 6 7` (expected = `mexp` / `asm` executed in Lean; inputs from the
  corpus/random/mutated sources through the spec chain, plus 40 raw micro-op strings and 40 raw record strings with
  non-nano ops and odd lengths): expander 3147 words, QEMU 146 × 2 (output at memoryNeeded, flag at memoryNeeded − 1),
  Sail 6 × 2; assembler 1838 words, QEMU 146 × 2, Sail 6 × 2. Mismatches: none.
- self-run of the linked binary, `python3 Testing/nano/selfrun_s3/selfrun_s3_test.py 30 20 8 11` (log
  Testing/nano/selfrun_s3/run_summary.log, 316 s): `binaryS3C_eq : binaryS3 = binaryS3C` PROVED (words_eq' on the five
  stage files' literals); **59104 words** = stub + lexA 5958 + 2b 46054 + inliner 2035 + expander 3147 + assembler 1838;
  146 sources, all in DomainS3; stage 2b alone and inliner alone 146/146 (QEMU, work found by doubling/bisection);
  **linked binaryS3: QEMU 146/146, Sail 8/8** (QEMU == Sail == Lean `nanoCompileA`, a1 = length, flag clear, gp/sp,
  guards, Sail writes only in output + work). K 17888..2348672, `space5 K` up to 601 MB. Mismatches: none.

After merging origin/main (1cdf8f8, IR strong stub from ir-strong): `bash Testing/scripts/check.sh` **ALL CHECKS PASSED**
(1910 s, peak 6.3 GB, 4 jobs; `ok 'Nano.selfHostedS3' 77 axioms`; only the pre-existing statement-fingerprint WARNING,
not re-frozen). The words are unchanged by the merge: expander, assembler and the linked `binaryS3C` (59104 words)
byte-identical to the tested ones; `bs3_test.py 20 6 7` re-run after the merge: same results (QEMU 146 × 2, Sail 6 × 2
per stage).
