# Nano/Run: Gen's code on the abstract machine J, and the lift to real targets

## Contents (81 files, by prefix)
| prefix | what |
|---|---|
| `Call`, `Expr*`, `Templates`, `Loop`, `Heap*`, `HeapEV`, `TmGood`, `JLay`, `JNorm` | the abstract machine `CallProbe.J` and Gen's templates on it (leaves, IF, LOOP, calls, heap prims) |
| `EVX*`, `Nd*`, `NdCG*`, `MachExact`, `GenRun`, `GenMain*` | node / def / program theorems: Gen's code = the templates (`NdCGm`), `gen_words` (`NdTop2`) |
| `EVS*`, `SafeRun`, `SimW`, `SimX*`, `Start*`, `GenRunS` | the Sail-safe versions and the start code; `gen_runS` = Gen's program on Sail |
| `Cap*`, `RoomRun`, `SemCases`, `RunsDef`, `RunsShift`, `NoW` | capacity / out-of-memory exits and the exact work bound (`Msp`) |
| `Host*`, `Target`, `RvTarget`, `RvEnc`, `RvStep` | the generic host lift over any `JTarget` and its RISC-V adapter |
| `ArmEnc*`, `ArmRA*`, `ArmTarget`, `A64Sem` | the AArch64 adapter (abstract `A64Sem`; real ARM steps are in `Arm/`) |
| `Bridge` | Gen's word encoders = nano-v2 `I.enc` |

## Role
Machine-side half of the correctness proof: connects `Nano/Codegen` to a `Machine` (RISC-V via Sail, ARM via `A64Sem`). Feeds `Nano/SelfHost` (Bridge) and `Nano/Main` (`TopOn`, `RvTop`, `ArmTop`). Target-generic by design; RISC-V-only parts to move to `Riscv/` in the per-target pass.

## Decisions
Everything target-generic is stated over a `JTarget` with `Laws`; each target is a small adapter (`Target.lean`). Safe-run retrofit (`EVS*`) duplicates the success-path files to carry Sail-safety; merging them is a known cleanup (`Testing/notes/CLEANUP_PLAN.md`).

## Check
`lake build Nano.Run.GenRunS Nano.Run.HostOom`.

## Limits
ARM adapter encodings (`ArmEnc`) are unproven against Sail here; see `Arm/`.
