# Nano/Codegen: AST → machine-code bytes (stage 4), code and soundness on success

## Contents
| file | what |
|---|---|
| `Gen.lean` | **code**: the fused code generator `g41` (expand + assemble, width pre-pass `g53`, fixups `g19/g20`) in the nano subset (was `C/Gen`) |
| `BufL.lean` | `Buf` read/write lemmas used by the stage proofs |
| `GenRef.lean` | work-item invariant of Gen's main loop `g39`: `Reach`, `CG/CT` code relation |
| `Fixup.lean` | jump emission/patching lemma |
| `GenWidth.lean` | width pass: every def satisfies the width relation `W` |
| `GenTop.lean` | def and program level: `def_run`, g39, then `g42/g41` |
| `GenAll.lean` | Gen soundness on success with the width facts |
| `DBNode.lean` | node bounds `NB` from kind typing |

## Role
Takes the ownership-checked AST, emits RV64 words (`Nano/Run` shows these are the J-program templates and runs them on the machine). Last stage of `mC`.

## Decisions
One fused generator instead of expand+assemble stages: one fuel loop, one invariant. Target-specific re-encoding (ARM) is not here but in `Nano/Run` (`ArmTarget`, `ArmRA*`) and `Arm/`.

## Check
`lake build Nano.Codegen.GenAll`.

## Limits
Soundness is "on success"; failure exits (`cap`, `room`) are in `Nano/Run`.
