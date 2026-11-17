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
- TIMING: probe `gs` (decoder `decLS`/`decS` + `gasS` + `u8N`, S3 compile with certificates): OK, 22 min 48 s
  wall (13 min 17 s user; another Lean build ran in parallel). The certificates dominate (s3_solve on decS's
  if-chain).
- Regression found by the adapter box: the byte lemmas as global `s3_norm` broke Riscv/Frontx/S3Examples (and
  S3RecExamples). DECISION: opt-in. New simp set `s3_bytes` (SimpAttr.lean), command `s3_compileB` (certificates by
  `s3_solveB` = `s3_solve` with `s3_bytes` in every simp call, and `s3_splitB`). `s3_compile` and the existing
  examples are unchanged (both example files build).
- WHY the machine compile did not finish (> 27 min for `stepS`, > 10 min for the 3-case `stParams`): the parser's
  state is a 9-field structure and the machine matches on its projections (`s.ts`); `s3_split` never destructs a
  one-constructor variable, so those branches never close and `s3_solve` exhausts its depth (12) splitting `Nat`s
  (~2^12 branches) before failing. FIX (`s3_splitB`): first destruct a structure variable used inside `Enc.enc`
  (no branching), then split a variable that blocks evaluation (`match some (Enc.enc x)`), else `s3_split`.
  Option `s3.depth` (default 12) for diagnosis. Also: `st0 ts` inlined as a record literal in `stage2S` (a call
  returning a structure cannot be split). Result: `stParams` probe 34 s (was > 10 min, failing).
- Adapter (box nano-parse-s3-adapter, merged): `Proven.S3.implements1` / `implements1_spaceOf`
  (Riscv/Back/S3Impl1.lean, notes Testing/notes/S3_IMPL1.md): S3's compiled code meets `Implements1With` with
  `retLen = true`. IR change: the stub moves `main`'s return value into a1 (`stub3`), S3's `main` returns its output
  count; `Ctx.Fin` gains `keepC`/frame facts; the frame of the output block is obtained by instantiating the
  emission context with the RESULT length. All existing theorem statements unchanged.
- `Nano/S3Stage.lean`: `stage`: from `computes` (generated), `smallB P.S = true`, main arity 1 and the IR compiler's
  acceptance, the machine theorem in the linker's form (`spaceP P` = `spaceOf` of the compiled program).
- FINDING: kernel evaluation of `Ir.compileW` (`decide +kernel`) blows up (> 9.5 GB on the 2035-word inliner):
  `layout`'s accumulator is re-evaluated lazily at every use. DECISION: materialize the allocated program and the
  layouts as literal terms (`irLit%`, `layLit%`: elaborated by evaluation with derived `ToExpr`; untrusted, every
  use is an equation the kernel checks by `decide +kernel`): `alloc (lowerP P) = some Q`, `layStep Q init = L1`,
  `layStep Q L1 = L2`, `layStep Q L2 = L2` (fixpoint; `layout_fix`, `layout_add`), `emitP Q L2` succeeds
  (`compileW_isSome`), code length (`words_eq'`). Inliner: 12 s, 2.3 GB.
- Files: `Nano/ParseS3Self.lean` / `Nano/InlS3Self.lean` (S3 compile + certificates only),
  `Nano/ParseS3Stage.lean` / `Nano/InlS3Stage.lean` (the stage theorems).
- INLINER through S3 (`Nano/InlS3.lean`: `inlBS`, bridge `inlBS_eq : inlBS xs = inlB xs` for EVERY input, so the
  stage needs no `inlFits` condition): compile < 1 min; `Nano.IS.inlS3_implements` checks.
