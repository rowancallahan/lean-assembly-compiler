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

## Bare metal (2026-11-15): `Riscv/Back/BootReset.lean`, `BootV.lean`, `Boot.lean`, `Riscv/Examples/BootEx.lean`

`boot_correct`: from `bootStart` (the model's `sail_model_init`, a board config, the model's `reset`; verbatim
copy `resetWith`, `reset_eq`) a 21-word stub runs to `StartCorrect` (`boot_start`), then `compile_correct`.
Trusted assumptions, all explicit: (1) board config `board`: reset vector `0x80000000`, PMA regions = the default
config's main-memory region only (the default also has boot-ROM/CLINT regions; `Cfg.pma` wants exactly one);
(2) `cancel_reservation` (a declared axiom with no body, called by `reset`) leaves the Sail state alone
(`hcancel`; `boot_correct_with` takes any such hook, `pure ()` discharges it); (3) loaded image `Image`: stub at
`0x80000000`, code at `0x80001000` (< `0xFF000` B), input length (8 B LE) at `0x80100000`, input at `0x80200000`
(≤ 2^20 B); output ≤ `0x100000` B.  Work space fits automatically.  Not a gap after all: the model's reset sets
`misa.V` (Cfg wants it clear): the stub clears it (`csrrc`, proved in `BootV.lean` from `CfgV`); zeroing makes
output/work `Present`.  `init_model`'s `config_is_valid` assertion is not evaluated (the start uses `reset`).
Non-vacuity: `boot_example` (concrete `incCode1`, no hypotheses); `boot_revinc5` (XPipe) keeps only `codeFits`:
the kernel cannot evaluate the optimiser's `List.mergeSort` (62 words by `#eval`).  QEMU: `Testing/asm/boot_test.py`.

## Sketch: out of memory as a machine step (owner, 2026-11-15; the owner will fix the exact details)

```lean
inductive Step (State : Type) where
  | next (state : State) | halted | outOfMemory

structure Machine where
  State : Type
  step : State → Step State
  observe : State → MachineState
  inUse : State → Address → Bool      -- live work-block cells; the rest are free

inductive Ending (machine : Machine) where
  | done (state : machine.State) | outOfMemory   -- outOfMemory is final

inductive Runs (machine : Machine) : machine.State → Ending machine → Prop
  | halt {s}     : machine.step s = .halted → Runs machine s (.done s)
  | oom  {s}     : machine.step s = .outOfMemory → Runs machine s .outOfMemory
  | step {s t e} : machine.step s = .next t → Runs machine t e → Runs machine s e
```

- A step is `outOfMemory` when it needs a new cell and every work-block cell is in use; freeing marks a cell not
  in use. No step leaves `outOfMemory`.
- `compile_runs` (no memory hypothesis): every run ends `done` with the right output, or `outOfMemory`.
- `compile_correct` (sub-theorem): hypothesis `memoryNeeded machine start ≤ call.workLength` (`memoryNeeded` = most
  cells in use during the run with unlimited space; defined, not calculated) → ends `done` with the right output.
- Adapter: today's `step : State → Option State` embeds as `some t ↦ .next t`, `none ↦ .halted`, never
  `outOfMemory`, so current theorems carry over.
- Open (owner): the Sail RISC-V model has no in-use/free. Either (a) an allocator layer is part of the trusted
  machine (like an OS malloc; RISC-V machine = Sail + that layer), or (b) the allocator is our proved code and
  out of memory is defined over the compiler's abstract run. The owner's description matches (a).
