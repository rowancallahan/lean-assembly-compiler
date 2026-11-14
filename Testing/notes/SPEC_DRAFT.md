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
