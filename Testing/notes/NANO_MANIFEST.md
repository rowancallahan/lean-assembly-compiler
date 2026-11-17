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
