# Nano/Base/Compiler

Model-free middle layer of the verified compiler: source languages (expressions, statements, byte/word
arrays, spill slots, calls) → abstract machine operations, proved from interface laws only (no Sail model
imported). Targets (RV64, ARM) instantiate the interfaces elsewhere (`Nano/Base/Riscv`, `Arm/`). Namespaces
`Proven.Mach`, `Proven` (Front).

## Files
Interface
- `Iface.lean`: `Machine` (state, `runsTo`, 15 abstract regs, byte memory, PC, `AOp` encoding, one law per op)
- `Logic.lean`: reasoning rules over `Core` laws (`next_add`, run composition)
- `Mem.lean`: regions, `n`-byte reads, byte writes, separation facts
- `Frame.lean`: `MachineF` = Iface + frame register, spill slots, 8-byte loads/stores (`XOp`)
- `Call.lean`: `MachineC` = MachineF + call/return through the link register
- `Wide.lean`: `Wide`/`WideF` = Iface with arbitrary-register, immediate, compare-branch ops (`WOp`) for the optimiser
- `MOp.lean`: multiply/divide ops (compiler side only; `Spec` `Op` is unchanged)
- `AllocSpec.lean`: lemmas about `Spec/Alloc.lean`
Plain compiler (one source language per layer)
- `Exp.lean`: `Exp`/`AExp` → ops, `compE_ok`-style theorems; `Stmt.lean`: `while` statements; `Arr.lean`: `AStmt` byte arrays
- `BLang.lean`: model-free `BExp`/`BStmt`/`BExec` (byte + word arrays, spill slots); `BExp.lean`, `BStmt.lean`: their compilers (`execB_ok`, `compBF_ok`)
- `CLang.lean`, `CStmt.lean`: functions/programs (`CStmt`, `Fn`, `Prog`) and call compilation; `CProg.lean`: function table layout, entry stub, `compP_ok`
Optimising back end (`Opt/`; IR over virtual registers, untrusted choices checked by decidable tests)
- `IR.lean` (IR + big-step semantics), `Sel.lean`/`BSel.lean` (selection), `Flow.lean`, `Peep.lean`, `SR.lean`, `Hoist.lean` (IR→IR passes),
  `Live.lean` (liveness check `chk`), `Color.lean` (untrusted allocator), `Alloc.lean` (renaming `map_ok`), `Lower.lean` (IR→`Wide` ops),
  `Fn.lean` (`fn_ok`), `Exp.lean`/`Stmt.lean`/`Arr.lean`/`BFn.lean` (`optE_ok`, `optS_ok`, `optA_ok`, spill-slot variant)
Front end (`Front/`: `Pipe` combinator language for `List UInt8 → List UInt8`)
- `Pipe.lean` (language, `Pipe.prog`), `PipeSrc.lean` (source-level correctness, view invariant `InvE`), `PipeEncode.lean` (result = `Spec.enc`)
- `PipeMachine.lean`: `compileP_ok`; `PipeStd.lean`/`PipeStdSrc.lean`/`PipeStdMachine.lean`: `XPipe` (std-lib stages), `compileXA_ok`
- `PipeStdB.lean`/`PipeStdBMachine.lean`: pipes with `List.mergeSort` via `BStmt`; `PipeI.lean`/`PipeIMachine.lean`: working space in WORK block, `compileX1_ok`

## Decisions
- Interfaces are laws on an abstract `Machine`, not the Sail model: layers are target-independent and cheap to check; copies of the Sail-side languages (`Stmt`, `BStmt`) are kept here because the originals import the model, with mappings on the target side.
- Layers are stacked by extension (Iface → Frame → Call; Wide separate for the optimiser) so a target proves only the laws of the layer it uses.
- Optimiser passes are IR→IR with the untrusted search (allocation, colouring, spill choice) outside the proof and a decidable checker inside (`injOn`, `chk`, `wf`, `allocOK`); rejected: proving the heuristics.

## Main results
`BStmt.lean:execB_ok`, `BStmt.lean:compBF_ok`, `CProg.lean:compP_ok`, `Opt/Fn.lean:fn_ok`, `Opt/Exp.lean:optE_ok`, `Opt/Arr.lean:optA_ok`,
`Front/PipeMachine.lean:compileP_ok`, `Front/PipeStdMachine.lean:compileXA_ok`, `Front/PipeIMachine.lean:compileX1_ok`.
Assumptions: the target's laws (range side conditions `bzOK`/`jmpOK`, region layout, RAM bounds); guarantee: run of the emitted words matches the source semantics.

## Build/check
`lake build Nano.Base.Compiler.<Module>` (whole folder: build the REVIEW target); `Testing/scripts/review_axioms.sh` must print `OK: 8 theorems, axioms as pinned`.

## Limits
Pure Lean core (no `Std`) in the interface files; no multi-register-class or non-uniform-block targets; `Spec/Code.lean` `Op` has no mul/div (`MOp.lean`).
