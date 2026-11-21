# Nano/Tests: non-vacuity tests and audit witnesses

| file | what |
|---|---|
| `MainWitness.lean` | non-vacuity of `compiler_correct` per stage on three small sources (`decide +kernel`) |
| `MainCert.lean` | per-program meaning certificates (`srcRun ⟨x⟩ inp = some (f inp)`) |
| `AuditWitness.lean`, `AuditSpace.lean` | `C_correctLO` instantiated on `ex1`; a concrete `spaceC` bound (≤ 4,194,416 bytes) |
| `OwnNV.lean` | `o41_sound` accepts `pOk`, rejects aliasing `pAlias` |
| `SelfInCapFree`, `SelfInQuiet`, `SelfInPath`, `SelfInWitness` | steps A–C: `SelfIn` (input for the self-application theorems) is inhabited by the empty input |

Role: guards against vacuous hypotheses in `Nano/Main`; nothing imports these except `REVIEW`-adjacent scripts (`Testing/scripts/deadcode.lean`). Check: `lake build Nano.Tests.AuditWitness Nano.Tests.SelfInWitness`. Limit: concrete instances only, not coverage.
