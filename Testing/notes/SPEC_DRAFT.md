# Top-level theorem: agreed draft (owner, 2026-11-14)

Not yet compiled. Supporting definitions (`StartCorrect`, `Runs`, `readMemory`, `Computes`, `Call`,
`MachineState`, `Machine`, register mappings) to be added by the owner; a second theorem with the same
hypotheses will carry the frame facts (work zeroed, nothing else changed, kept registers, status/length).

```lean
theorem compile_correct
    (compiles : compile machine program = some compiled)
    (computes : Computes program f encodeInput encodeOutput)
    (startsRight : StartCorrect machine startState call compiled.code (encodeInput argument))
    (outputFits : (encodeOutput (f argument)).length ≤ call.outputLength)
    (enoughWorkSpace : compiled.space (encodeInput argument).length ≤ call.workLength) :
    ∃ finishState,
      Runs machine startState finishState ∧
      finishState.programCounter = call.returnAddress ∧
      readMemory finishState call.outputAddress (encodeOutput (f argument)).length
        = some (encodeOutput (f argument))
```

## Compiled (2026-11-15): `Spec/Top.lean`, `Spec/Machines.lean`, `Spec/RiscvMachine.lean`, `Riscv/Back/Top.lean`

**Design of `Machine` / `Runs`.** The Sail state does not factor through `MachineState` (CSRs, privilege,
PMA are lost), so `MachineState` cannot be stepped. `Machine` carries its own `State`, a partial `step`
(RISC-V: `riscvStep` = one `Retire_Success` instruction via `run_hart_active`/`try_step`, else `none`) and
`observe : State → MachineState`; `Runs` is on machine states and conclusions read `machine.observe`.
`configured` (RISC-V: `Cfg`), `mapping`, `ramStart`/`ramEnd` are fields, so `StartCorrect` is machine-generic.

Changes to the draft: `Program` is a class (`run`); `Compiled` = code bytes + `space`; `compile` has no machine
argument (`Proven.Top.compile : XPipe → Option Compiled`, the `compileX1` list front end, the only total
compiler function with a general `Implements1` theorem); the theorems are stated for `riscv`; `compile_frame`
also gives `Cfg` again. One adapter `implements1_top` (any `Implements1With` code, loaded as `wordBytes code`).
Non-vacuity: `Proven.Vacuity.startCorrect_nonvacuous` (`Riscv/Examples/VacuityTop.lean`), a concrete Sail state.

**What a boot stub must establish (all concrete on a Sail state, no opaque predicates):** `Cfg` (fixed
control-register values, present registers), code/input bytes in `mem`, the six argument registers, alignment,
blocks in RAM `[2^31, 2^32)` and disjoint, every output/work byte present in Sail's memory map. Possible
gaps for a stub run from Sail's reset state: `Cfg.pma` fixes ONE PMA region `[0x80000000, +0x80000000)` rwx and
`Cfg.mstatus`/`misa` fixed values, which may differ from what Sail's own reset/platform init leaves (to check
against the model's init); `Present` needs every work/output byte to exist in the finite map, so the stub (or
the loader) must write them (e.g. zero them) first. Everything else a stub sets with ordinary instructions.
