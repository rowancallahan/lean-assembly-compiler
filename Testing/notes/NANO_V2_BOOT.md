# NANO_V2_BOOT: B₁ from the nano v2 stage sources via compiler 1 (S3)

Branch `nano-v2-boot` (worker 4, bootstrap half). Pattern: v1-S3 (NANO_MANIFEST "nano v2-design").

## Status
| stage | v2 source (worker 3, Nano/V2S) | S3 twin + bridge (Nano/V2Boot) | S3 compile | stage theorem |
|---|---|---|---|---|
| lexA | `lexV` | `lexVS`, `lexVS_eq` (len < 2^64) — LexS3.lean | LexS3Self (`LexB`) | `lexB_implements` (LexS3Stage) |
| 2b | `Nano/V2S/Parse.lean` (no bridge yet) | — | — | v1 `Nano.PS.stage2B_implements` still used |
| inliner | `inlV` | `inlVS`, `inlVS_eq` (len < 2^31) — InlS3.lean | InlS3Self (`InlB`) | `inlB_implements` |
| expander | `mexpV` | `mexpVS`, `mexpVS_eq` (len < 2^64) — ExpandS3.lean | ExpandS3Self (`ExpB`) | `expB_implements` |
| assembler | `asmV` | `asmVS`, `asmVS_eq` (len < 2^64) — AsmS3.lean | AsmS3Self (`AsmB`) | `asmB_implements` |

Stage theorems: `Implements1With (·.data.toList) id (S3.words P) (V2 function ∘ ·.data.toList) (spaceP P) (2^20) true`
(transported from the twin by `implements_congr`, Nano/V2Boot/Stage.lean). Axioms: exactly the v1 S3 stage set (77,
compared with `Nano.XS.expS3_implements`).

**Composition (hybrid B₁)**: `Nano.selfHostedB1 (K) : SelfHosted binaryB1 (fun _ => space5 K) (DomainB1 K) nanoCompileA`
(Nano/V2Boot/SelfHostB1.lean): v1 `selfHosted_lexA` with the v2 lexer, v1 2b, v2 inliner/expander/assembler, through
the v2→v1 bridges of worker 3. Builds; no sorry. It is stated in v1's contract (SelfHosted), NOT yet `ImplementsBytes`.

## Why twins (S3 cannot take the v2 prelude as is)
- `rd`/`len` use `Nat`↔`UInt64` (S3: "dependent result type of BitVec.ofNat"). Twins: `rdS`/`lenS` by list recursion.
- `put o b = o ++ [b]` copies `o` (quadratic allocation, no GC). Twins keep the output reversed (`putR`), reverse once.
- `Nat` fuel is unary in S3; `(len+1)^2` fuel (inliner) would allocate (len+1)^2 cells. Twins use `UInt64` fuel (wf).
- S3 certificate search limits found and handled in twins: no `let`-bound word used in an `if` condition inside a
  recursive function (inline the read); no compound `&&`/`||` loop conditions (nested `if` or a 0/1 helper function);
  `if` as a call argument → helper function; sign fill in `ax3` as arithmetic (`sgn8`, checked on all 256 bytes).
- Cost: `rdS` is O(i), so B₁ is quadratic-ish in input length. Fine for a bootstrap, measure on the real source.

## S3 front-end changes (Compiler/S3/Front.lean, untrusted build tooling)
`s3_hyps` handles BitVec `<`/`≤` and their negations; `s3_contra` closes premises by assumption and prints the goal on
failure; `s3_solveF` normalizes `UInt64.toBitVec_{add,sub,mul,ofNat}` in hypotheses and has a last-resort
`s3_hyps; s3_contra` alternative. All v1 S3 stage modules (Lex, ParseS3B*, Inl, Exp, Asm, SelfHostS3) rebuilt OK
after the change (11 min, 4 jobs).

## Measurements (`/usr/bin/time lake env lean`, deps built; S3 compile of the twin)
asm 10.8 s / 2.0 GB; expand 14 s / 2.1 GB; inliner 16 s / 2.2 GB; lexer 89 s / 3.2 GB. Stage files (layout/emit by
`decide +kernel`) built in seconds. Cold per-module table NOT yet measured.

## Products (round 3, point 4)
The v2 sources use no products, so the 7-argument limit was not hit (max arity 6: `inlBodyS`). Not tested on nested
products; Parse.lean (state tuple) will be the first test.

## HANDOFF
Done: twins + bridges + S3 compiles + stage theorems for lexV, inlV, mexpV, asmV; hybrid B₁ theorem `Nano.selfHostedB1`.
Next:
1. Parser 2b: when worker 3 has the bridge for Nano/V2S/Parse.lean, write `Nano/V2Boot/ParseS3.lean` (same twin rules)
   — first check whether S3 flattens its state tuple within the 7-arg IR limit. Then swap it into SelfHostB1.
2. QEMU/Sail: `Testing/nano/selfrun_b1/` (copy of selfrun_s3 with the v2 stages) is written but NOT RUN:
   `python3 Testing/nano/selfrun_b1/selfrun_b1_test.py 30 20 8 11`. Emitter still names `LS.lexA_Q` for lexA: switch
   `wLex` to `Nano.V2B.lexB_Q/lexB_L2` and `binaryS3C_eq` to `lexB_*` first.
3. `ImplementsBytes`: asked worker 1 (session_01MfKuVaecMPtighd5kbQ58u) for the exact statement; no answer yet. Note:
   `link`'s stub does not propagate an inner stage's OOM/status.
4. Cold build table per module (≤ 5 min, ≤ 8 GB); merge origin/main; `bash Testing/scripts/check.sh`; add an axioms
   file for `Nano.selfHostedB1` to check.sh.
Commands that worked:
- restore cache: see build-cache README (sail-riscv-lean, sailsim, repo-build parts), elan 4.29.0.
- `lake build Nano.V2Boot.SelfHostB1` (builds everything here).
- debug a failing S3 certificate: run the twin through `s3_compileF` in a scratch file with output to a FILE (not a
  pipe), then the `s3_contra` error prints the goal; regenerate one cert with `trace_state` to see the real goal.
