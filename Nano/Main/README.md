# Nano/Main: the compiler C assembled, and the final theorems

## Where to start
`REVIEW.lean`: the final theorems, their `#print axioms`, every definition to trust (`lake build Nano.Main.REVIEW`, notes `Testing/notes/NANO_V2_REVIEW.md`). `Testing/scripts/review_axioms.sh` checks the axioms against the pin.

## Contents
| file | what |
|---|---|
| `Prelude.lean` | buffers and prims of the self-language (the nano subset) |
| `Chain.lean` | the chained stages' shared definitions (was `C/Base`) |
| `Sem.lean` | driver `mC x = g41 x (o41 (y16 (s10 x)))`, the meaning `Sem`, stage props |
| `Compile.lean` | `compileC`, `spaceC` (work bound) |
| `TopOn.lean` | generic top theorems over a `JTarget`: `C_correct_on`, `C_runs_on` |
| `RvTop.lean`, `ArmTop.lean` | RISC-V (`C_correctLO`, `C_runsO`) and AArch64 instances (`C_correct_rv2arm`, `C_runs_rv2arm`) |
| `SelfC.lean`, `SelfLink.lean`, `RunsTopO.lean` | C compiled by itself (`self_correct_C`, `self_runs_C`) |
| `ParCapBnd.lean`, `DBStageE.lean` | parser width cap ⇒ Gen's field bounds |

## Role
Composes `Nano/Lexer`, `Parser`, `Ownership`, `Codegen` through `Run`/`SelfHost` into `CompileCorrect` / `CompileRuns` for C (namespace `NanoMain`). Anything built on C starts here.

## Decisions
Top theorems are target-generic (`TopOn`), instances thin; the final theorem is on Sail for RISC-V, interim abstract-step for ARM. Fixpoint is a test (`Testing/nano/v2self/boot/fixpoint.sh`), not a proof.

## Rebuild
Everything: `lake build $(find Nano/{Lexer,Parser,Ownership,Codegen,Run,SelfHost,Main,Tests} -name '*.lean' | sed 's|/|.|g; s|\.lean$||')` (~12 min cold). Rules: no `sorry`, no new axioms, no `native_decide`/`bv_decide`/`extern`; module ≤ 5 min, ≤ 8 GB; `Spec/` is the owner's.

## Limits
See `REVIEW.lean` for what is trusted; ARM final theorem is modulo `A64Sem` for now.
