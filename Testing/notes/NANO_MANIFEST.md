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
| assembler | `asm` | frontx | Nano/Asm.lean, Nano/AsmSelfC.lean, Nano/AsmSelf.lean | (verbatim) | `Nano.Self.nanoAsm.implements1` | 125 s + 198 s cold | Sail (+ propext, Classical.choice, Quot.sound) | DONE; pool runner: QEMU 239/239, Sail 5 |
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
| Nano.AsmSelf | 198 s | 2.6 GB | `frontx_entry`, `frontx_implements_listC` |
| Riscv.Frontx.S3RecExamples | 182 s | 2.7 GB | (not nano; slowest non-nano module rebuilt here) |
| Riscv.Frontx.S3Examples | 127 s | 2.5 GB | (not nano) |
| Nano.LexS3Self | 82 s | 2.7 GB | lexA S3 compile |
| Nano.ExpandMSelf | 65 s | 4.7 GB | expander |
| Nano.Agree | 54 s | 4.1 GB | |
| Nano.LexS3Stage | 45 s | 3.2 GB | |
| Nano.SelfHostFinal | 31 s | 4.7 GB | `Nano.selfHosted` |
| Nano.InlS3Self | 21 s | 2.0 GB | |
| Nano.InlS3Stage | 14 s | 2.3 GB | |

Before rc2 (rc1, 6a76836, from scratch): ParseS3BSelf 6 min 26 s / 6.05 GB, ParseS3BStage 6 min 10 s / 10.0 GB,
ParseS3BAllocB 160 s / 10.1 GB, AsmSelf 321 s / 3.4 GB. The full `lake build Spec Compiler Riscv Arm Frontx Nano`
(4 parallel jobs, 54 modules rebuilt over the cache) peaked at 4.7 GB.
