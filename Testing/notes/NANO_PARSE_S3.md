# NANO_PARSE_S3: the parser stage `stage2` through S3 (branch nano-parse-s3)

## Setup
- Branch = origin/s3-rec + nano-closeB + nano-closeA + nano-s3 (merged one by one; the octopus merge conflicted).
  Conflicts: check.sh axiom loop and expected-axioms.txt (unions, ir-s3 block before the nano blocks), NANO_CLOSE.md
  (both sections kept).
- Toolchain: elan from elan.lean-lang.org worked (no denial). Build cache restored per build-cache README.
- Testing/notes/S3_REC.md does not exist on s3-rec; the recursion support is read from Compiler/S3/Front.lean and
  Riscv/Frontx/S3RecExamples.lean.

## Findings
- S3's machine theorems (`CompileCorrect`/`CompileRuns`, Compiler/AllocSpec.lean) do NOT imply `Implements1With`:
  missing (1) `a1` = result length (`retLen`), (2) `abiSavedKept`, (3) `Cfg` after the run, (4) bytes of the output
  block past the result unchanged (AllocSpec frames only outside the whole output block). The IR back end's
  `Ctx.Fin` (Compiler/Ir/EmitStep.lean) states `Cfg` but not (1), (2), (4). So the adapter needs a stronger IR
  emission theorem, not a restatement.

## Log
- Front end on stage2's pieces (probes Testing/nano/ps3/): `mo` ok; `UInt64.toUInt8` failed in the certificates
  (byte decoded from a word vs `toUInt8`): fixed by three `s3_norm` lemmas in Compiler/S3/Cert.lean (`u8_mk_sw`,
  `u8_ofBitVec_sw`, `u64_toUInt8_ofNat`, one normal form `UInt8.ofNat x.toNat`).
- More `s3_norm` lemmas (Cert.lean): `nat_beq_decide`, `list_u8_beq` (`List.beq` on bytes = `decide (=)`),
  `u8_ofNat_u64_sw`, `u8_ofNat_bv_sw`; Front.lean's certificate simp set drops `UInt8.ofNat_uInt64ToNat` (it loops
  against the new normal form). With these, `mo`, `sLi`, `lookS`, `findD` compile verbatim.
- DECISION: `stage2` is not compiled verbatim as a whole. The S3 front end fails on: `Nat.toUInt8` and `Nat`
  subtraction ("invalid instantiateForall"), `Option.map` with lambdas capturing run-time values (`dec`), `UInt8`
  subtraction (`dec`), `UInt8` literal patterns (`decL`: the matcher contains `Eq.symm`), the literal pattern
  `some (0, j)`, `gasOf`'s multiplication. `Nano/ParseS3.lean` defines `stage2S` = the same machine with those
  constructs replaced (`natW`/`u8N`/`subN`, `consO`/`pairO`, `if b == 1`, nested `match k`, `gasS`); every other
  function and all datatypes are the originals. PROVED: `Nano.PS.stage2S_eq : stage2S bs = stage2 bs` (all inputs).
- Main-session messages (06:32, 06:35): (1) a composed `Nano.selfHosted` must state, in its domain, the
  elaborator-depth limits (nesting ≤ 400, chains ≤ 2500; NANO.md "RESOURCE LIMITS" on nano-e2e); nanoElab unchanged.
  (2) the parser compile is owned here (close B: inliner only); if the `stage2S` compile runs > ~30 min, split it
  into smaller S3 stages, each with its own bridge, linked by `link_stage`, with timings recorded here.
