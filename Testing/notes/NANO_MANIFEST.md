# NANO_MANIFEST: nano v1, every stage (integration branch nano-parse-s3)

Rule (owner, ROADMAP "FREEZE BEFORE THE FULL RUN"): every stage has its source, a bridge `= original` on EVERY
input, a stage theorem with the Sail axioms only, and builds in ≤ 5 min. When every row is done and
`bash Testing/scripts/check.sh` passes, the revision is tagged `nano-v1-rc1`. The full run uses only the tag.

Composition: `Nano.selfHosted` (Nano/SelfHostS3.lean): `SelfHosted binary (fun _ => space6 K) (Domain K) nanoCompileA`,
with `binary` = link of the six stages and `Domain K` = `Sized6 …` ∧ `LeanLimits` (the elaborator limits as a stated
predicate). Through `selfHosted_closeA` → `selfHosted_parse6` (Nano/SelfHostSplit.lean) → `link_stage`.

| stage | spec function | route | source file | bridge (every input) | stage theorem | build wall | `#print axioms` | status |
|---|---|---|---|---|---|---|---|---|
| lexer 1a (validator) | `vB` | frontx listCS → moving to S3 | Nano/ElabBSplit.lean | `eB_vB` (with 1b) | `Nano.Self.vBE.implements1` | 57+ min (listCS) | Sail | OWNER BOX nano-final (moving to S3) |
| lexer 1b (emitter) | `eB` | frontx listCS → moving to S3 | Nano/ElabBSplitE.lean | `eB_vB` | `Nano.Self.eBE.implements1` | 57+ min (listCS) | Sail | OWNER BOX nano-final (moving to S3) |
| parser 2 | `stage2` | S3 (`s3_compileB`) | Nano/ParseS3.lean (`stage2S`), Nano/ParseS3Self.lean | `Nano.PS.stage2S_eq` | `Nano.PS.stage2S3_implements` (Nano/ParseS3Stage.lean) | measuring (> 5 min so far) | Sail (expected) | IN PROGRESS: split 2a decoder (session_01MfKuVd8zxJmc6ZVj9VyJmH) / 2b machine (here) if > 5 min |
| inliner | `inlB` | S3 (`s3_compileB`) | Nano/InlS3.lean (`inlBS`), Nano/InlS3Self.lean | `Nano.IS.inlBS_eq` | `Nano.IS.inlS3_implements` (Nano/InlS3Stage.lean) | < 1 min + 12 s | Sail (expected; checked at final build) | DONE; QEMU 146/146 ×2, Sail 6/6 ×2 |
| expander | `mexp` | frontx listCS | Nano/ExpandM.lean (`mx`), Nano/ExpandMSelf.lean | `Nano.MX.mexp_eq_mx` | `Nano.Self.nanoExpM.implements1` | 49 s (nano-final note) | Sail | DONE (nano-closeA / nano-final) |
| assembler | `asm` | frontx | Nano/Asm.lean, Nano/AsmSelf.lean | (verbatim) | `Nano.Self.nanoAsm.implements1` | to measure | Sail | DONE (nano-proof) |
| composition | — | — | Nano/SelfHostS3.lean | — | `Nano.selfHosted` | to measure | Sail | WRITTEN; builds once the parser stage lands |

Shared infrastructure (this branch): S3 front-end extensions (`s3_compileB`, `s3_bytes`, `s3_splitB`, `s3.depth`;
Compiler/S3/Front.lean, Cert.lean, SimpAttr.lean), the adapter `Proven.S3.implements1` (Riscv/Back/S3Impl1.lean,
IR stub: a1 = result length), `Nano.S3Stage.stage` + kernel-literal compiler acceptance (Nano/S3Stage.lean).
Tests: `python3 Testing/nano/ps3_test.py R S seed` (S3 stages; QEMU bulk, Sail smoke). Notes: NANO_PARSE_S3.md.
