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
| parser 2b (machine) | `stage2b` (`stage2b (stage2a x) = stage2 x`) | S3 (`s3_compileF`) | Nano/ParseS3B.lean, Nano/ParseS3BSelf.lean | `Nano.PS.stage2b_stage2a` (+ `stage2S_eq`) | `Nano.PS.stage2B_implements` (Nano/ParseS3BAllocA.lean, Nano/ParseS3BAllocB.lean, Nano/ParseS3BStage.lean) | 268 s alone (311 s on a busy box) + 87 s + 177 s + 184 s | Sail set + propext, Classical.choice, Quot.sound | DONE (46054 words); QEMU 166/166 ×2 (inputs `stage2a (lexB src)`, expected `stage2`; raw tag bytes vs `stage2b`), Sail 6/6 ×2 |
| inliner | `inlB` | S3 (`s3_compileB`) | Nano/InlS3.lean (`inlBS`), Nano/InlS3Self.lean | `Nano.IS.inlBS_eq` | `Nano.IS.inlS3_implements` (Nano/InlS3Stage.lean) | < 1 min + 12 s | Sail (expected; checked at final build) | DONE; QEMU 146/146 ×2, Sail 6/6 ×2 (here); pool runner: QEMU 871, Sail 5 |
| expander | `mexp` | frontx listCS | Nano/ExpandM.lean (`mx`), Nano/ExpandMSelf.lean | `Nano.MX.mexp_eq_mx` | `Nano.Self.nanoExpM.implements1` | 49 s (nano-final note) | Sail (+ propext, Classical.choice, Quot.sound) | DONE; pool runner: QEMU 1266, Sail 5 |
| assembler | `asm` | frontx | Nano/Asm.lean, Nano/AsmSelf.lean | (verbatim) | `Nano.Self.nanoAsm.implements1` | to measure | Sail (+ propext, Classical.choice, Quot.sound) | DONE; pool runner: QEMU 239/239, Sail 5 |
| composition | — | — | Nano/SelfHostFinal.lean (nano-final), Nano/LeanLimits.lean; also Nano/SelfHostSplit5.lean, Nano/SelfHostSplit7.lean | — | **`Nano.selfHosted (K) : SelfHosted binary (fun _ => space5 K) (Domain K) nanoCompileA`**, no hypotheses (domain `SizedL … ∧ LeanLimits`) | < 1 min | exactly the Sail set of `S3.compile_correct` | DONE |

Shared infrastructure (this branch): S3 front-end extensions (`s3_compileB`, `s3_bytes`, `s3_splitB`, `s3.depth`;
Compiler/S3/Front.lean, Cert.lean, SimpAttr.lean), the adapter `Proven.S3.implements1` (Riscv/Back/S3Impl1.lean,
IR stub: a1 = result length), `Nano.S3Stage.stage` + kernel-literal compiler acceptance (Nano/S3Stage.lean).
Tests: `python3 Testing/nano/ps3_test.py R S seed` (S3 stages; QEMU bulk, Sail smoke). Notes: NANO_PARSE_S3.md.

Superseded compiles (> 5 min) are archived in Testing/nano/archive/ (nano-final's layout): the listCS lexer halves,
`SelfHostedA`, the paged inliners.

Gate status (12:00): every row DONE. `Nano.selfHosted` kernel-checked, exactly the Sail axioms. check.sh running at
6a76836; the tag `nano-v1-rc1` follows if it passes.
