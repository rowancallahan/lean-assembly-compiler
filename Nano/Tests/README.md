# Proof/Tests — non-vacuity tests and audit witnesses

Not imported by the final theorems; each file is named in `REVIEW.lean` or `Testing/notes/NANO_V2_AUDIT.md`.

| file | contents |
|---|---|
| `OwnNV.lean` | `pOk` accepted by `o41` and linear; `pAlias` (read after consume) rejected: non-vacuity of `o41_sound` |
| `MainWitness.lean` | three small sources pass lexer, parser spec, `o41`, `g41` in the kernel (`stages`, `x1..`): `OwnStage`/`GenStage` premises hold |
| `MainCert.lean` | per-program meaning certificates: `srcRun ⟨x⟩ inp = some (f inp)` via `progEq`, `sem`, `cert` |
| `AuditSpace.lean` | audit A2: `spaceC_ex1_eq : spaceC Witness.x2 [5] = 4194416` (kernel run + `shiftInv`) |
| `AuditWitness.lean` | `C_correctLO` instantiated for `ex1` (`ex1_computes`, `ex1_compiles`, `ex1_applies`) |
| `SelfInCapFree.lean` | step A: push-free defs never report `cap` (`ev_nocap`, `Quiet`) |
| `SelfInQuiet.lean` | step B: the 171 push-free defs of C are quiet on all inputs (`S`, `quiet`) |
| `SelfInPath.lean` | step C: on `[]` no def reports `cap` (13 push-reaching defs by hand, `X<i>`; `CapFree.sem_nil`) |
| `SelfInWitness.lean` | `selfIn_nonempty : Nonempty SelfIn` (the self-application theorems are not vacuous) |

Decisions: witnesses are kernel-checked (`decide +kernel`) where feasible; the parser run `C.y16 ts = a` is checked
natively only (Par1's layout puts tokens at word 184,384; one kernel `bget` there costs 28 s / 5.5 GB).
Hence `ex1_compiles` takes that run as a hypothesis, and `ex1_applies` takes `memoryNeeded ≤ workLength` (the
audit-finding-1 premise, discharged for `[5]` by `spaceC_ex1_eq`).
Check: `lake build Nano.Tests.SelfInWitness Nano.Tests.AuditWitness` (+ the rest of the folder).
