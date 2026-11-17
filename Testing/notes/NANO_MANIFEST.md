# NANO_MANIFEST: nano v1, every stage (integration branch nano-parse-s3)

Rule (owner, ROADMAP "FREEZE BEFORE THE FULL RUN"): every stage has its source, a bridge `= original` on EVERY
input, a stage theorem with the Sail axioms only, and builds in ≤ 5 min. When every row is done and
`bash Testing/scripts/check.sh` passes, the revision is tagged `nano-v1-rc1`. The full run uses only the tag.

Composition: SEVEN stages (`selfHosted_parse7`, Nano/SelfHostSplit7.lean; `selfHosted_s3`, Nano/SelfHostS3.lean, with
stage 2a as the remaining hypothesis): `SelfHosted binary (fun _ => space7 K) (Sized7 … ∧ LeanLimits) nanoCompileA`;
`Nano.selfHosted` is added there once 2a (and the S3 lexer, if it replaces vB/eB) land.

| stage | spec function | route | source file | bridge (every input) | stage theorem | build wall | `#print axioms` | status |
|---|---|---|---|---|---|---|---|---|
| lexer 1a (validator) | `vB` | frontx listCS → moving to S3 | Nano/ElabBSplit.lean | `eB_vB` (with 1b) | `Nano.Self.vBE.implements1` | 57+ min (listCS) | Sail | OWNER BOX nano-final (moving to S3) |
| lexer 1b (emitter) | `eB` | frontx listCS → moving to S3 | Nano/ElabBSplitE.lean | `eB_vB` | `Nano.Self.eBE.implements1` | 57+ min (listCS) | Sail | OWNER BOX nano-final (moving to S3) |
| parser 2a (decoder) | `stage2a = encT ∘ decL` | S3 | (box session_01MfKuVd8zxJmc6ZVj9VyJmH, branch parse-dec) | `stage2aS = stage2a` (theirs) | (theirs) | decoder probe 36.6 s (`s3_compileF`) | — | OWNER BOX session_01MfKuVd8zxJmc6ZVj9VyJmH |
| parser 2b (machine) | `stage2b` (`stage2b (stage2a x) = stage2 x`) | S3 (`s3_compileF`) | Nano/ParseS3B.lean, Nano/ParseS3BSelf.lean | `Nano.PS.stage2b_stage2a` (+ `stage2S_eq`) | `Nano.PS.stage2B_implements` (Nano/ParseS3BAllocA.lean, Nano/ParseS3BAllocB.lean, Nano/ParseS3BStage.lean) | 311 s (compile, ≈ 270 s alone) + 87 s + 177 s + 184 s | Sail set + propext, Classical.choice, Quot.sound | DONE (46054 words); tests running |
| inliner | `inlB` | S3 (`s3_compileB`) | Nano/InlS3.lean (`inlBS`), Nano/InlS3Self.lean | `Nano.IS.inlBS_eq` | `Nano.IS.inlS3_implements` (Nano/InlS3Stage.lean) | < 1 min + 12 s | Sail (expected; checked at final build) | DONE; QEMU 146/146 ×2, Sail 6/6 ×2 (here); pool runner: QEMU 871, Sail 5 |
| expander | `mexp` | frontx listCS | Nano/ExpandM.lean (`mx`), Nano/ExpandMSelf.lean | `Nano.MX.mexp_eq_mx` | `Nano.Self.nanoExpM.implements1` | 49 s (nano-final note) | Sail (+ propext, Classical.choice, Quot.sound) | DONE; pool runner: QEMU 1266, Sail 5 |
| assembler | `asm` | frontx | Nano/Asm.lean, Nano/AsmSelf.lean | (verbatim) | `Nano.Self.nanoAsm.implements1` | to measure | Sail (+ propext, Classical.choice, Quot.sound) | DONE; pool runner: QEMU 239/239, Sail 5 |
| composition | — | — | Nano/SelfHostS3.lean | — | `Nano.selfHosted` | to measure | Sail | WRITTEN; builds once the parser stage lands |

Shared infrastructure (this branch): S3 front-end extensions (`s3_compileB`, `s3_bytes`, `s3_splitB`, `s3.depth`;
Compiler/S3/Front.lean, Cert.lean, SimpAttr.lean), the adapter `Proven.S3.implements1` (Riscv/Back/S3Impl1.lean,
IR stub: a1 = result length), `Nano.S3Stage.stage` + kernel-literal compiler acceptance (Nano/S3Stage.lean).
Tests: `python3 Testing/nano/ps3_test.py R S seed` (S3 stages; QEMU bulk, Sail smoke). Notes: NANO_PARSE_S3.md.
