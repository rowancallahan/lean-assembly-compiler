# NANO_MANIFEST: nano v1, every stage (integration branch nano-parse-s3)

Rule (owner, ROADMAP "FREEZE BEFORE THE FULL RUN"): every stage has its source, a bridge `= original` on EVERY
input, a stage theorem with the Sail axioms only, and builds in ≤ 5 min. When every row is done and
`bash Testing/scripts/check.sh` passes, the revision is tagged `nano-v1-rc1`. The full run uses only the tag.

Composition: FIVE stages lexA → 2b → inliner → expander → assembler (`selfHosted_parse5S`, Nano/SelfHostSplit5.lean;
`selfHosted_s3`, Nano/SelfHostS3.lean, whose only hypothesis is lexA's stage theorem):
`SelfHosted binary (fun _ => space5 K) (Sized5S … ∧ LeanLimits) nanoCompileA`. `Nano.selfHosted` is its instance once
nano-final's lexA stage theorem lands. Superseded compiles (> 5 min) are in the non-default lib `NanoSlow`
(listCS lexer halves `vBE`/`eBE` + `SelfHostedA`, paged inliners `InlPSelf`/`InlRSelf`/`InlRPSelf`); the 7-stage
composition `selfHosted_parse7` (Nano/SelfHostSplit7.lean) stays as a proved alternative.

| stage | spec function | route | source file | bridge (every input) | stage theorem | build wall | `#print axioms` | status |
|---|---|---|---|---|---|---|---|---|
| front: lexer + parser 2a | `lexA = stage2a ∘ lexB` | S3 | Nano/LexS3.lean (nano-final 7a9f662), NanoSlow/LexS3Self.lean | `Nano.LS.lexA_eq` (every input) | `Nano.LS.lexA_implements` (NanoSlow/LexS3Stage.lean, written) | Nano/LexS3.lean 34 s; S3 compile > 10 min (`s3_compileF`, timed out) | — | MISSING: 3 failing certificates (le8, uniTyS, encTok φ; Testing/nano/ps3/lexA_d4.lean); OWNER BOX nano-final |
| parser 2b (machine) | `stage2b` (`stage2b (stage2a x) = stage2 x`) | S3 (`s3_compileF`) | Nano/ParseS3B.lean, Nano/ParseS3BSelf.lean | `Nano.PS.stage2b_stage2a` (+ `stage2S_eq`) | `Nano.PS.stage2B_implements` (Nano/ParseS3BAllocA.lean, Nano/ParseS3BAllocB.lean, Nano/ParseS3BStage.lean) | 268 s alone (311 s on a busy box) + 87 s + 177 s + 184 s | Sail set + propext, Classical.choice, Quot.sound | DONE (46054 words); QEMU 166/166 ×2 (inputs `stage2a (lexB src)`, expected `stage2`; raw tag bytes vs `stage2b`), Sail 6/6 ×2 |
| inliner | `inlB` | S3 (`s3_compileB`) | Nano/InlS3.lean (`inlBS`), Nano/InlS3Self.lean | `Nano.IS.inlBS_eq` | `Nano.IS.inlS3_implements` (Nano/InlS3Stage.lean) | < 1 min + 12 s | Sail (expected; checked at final build) | DONE; QEMU 146/146 ×2, Sail 6/6 ×2 (here); pool runner: QEMU 871, Sail 5 |
| expander | `mexp` | frontx listCS | Nano/ExpandM.lean (`mx`), Nano/ExpandMSelf.lean | `Nano.MX.mexp_eq_mx` | `Nano.Self.nanoExpM.implements1` | 49 s (nano-final note) | Sail (+ propext, Classical.choice, Quot.sound) | DONE; pool runner: QEMU 1266, Sail 5 |
| assembler | `asm` | frontx | Nano/Asm.lean, Nano/AsmSelf.lean | (verbatim) | `Nano.Self.nanoAsm.implements1` | to measure | Sail (+ propext, Classical.choice, Quot.sound) | DONE; pool runner: QEMU 239/239, Sail 5 |
| composition | — | — | Nano/SelfHostSplit5.lean, Nano/SelfHostS3.lean, NanoSlow/SelfHosted.lean | — | `selfHosted_parse5S`, `selfHosted_s3` (built; only hypothesis: the front stage); `Nano.selfHosted` (NanoSlow/SelfHosted.lean, written) | Nano/SelfHostS3.lean < 1 min | Sail set (same as `S3.compile_correct`) | WAITS ON the front stage |

Shared infrastructure (this branch): S3 front-end extensions (`s3_compileB`, `s3_bytes`, `s3_splitB`, `s3.depth`;
Compiler/S3/Front.lean, Cert.lean, SimpAttr.lean), the adapter `Proven.S3.implements1` (Riscv/Back/S3Impl1.lean,
IR stub: a1 = result length), `Nano.S3Stage.stage` + kernel-literal compiler acceptance (Nano/S3Stage.lean).
Tests: `python3 Testing/nano/ps3_test.py R S seed` (S3 stages; QEMU bulk, Sail smoke). Notes: NANO_PARSE_S3.md.

Gate status (11:33): check.sh ALL CHECKS PASSED at 11:03 and again at 11:33 (head before CertBytes; 1022 s). The tag `nano-v1-rc1` is NOT set: the
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
