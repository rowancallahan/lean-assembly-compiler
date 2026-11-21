# Nano/Base/Riscv — RISC-V step lemmas and early compilers

Layer between the Sail RV64 model (`Lean_RV64D`, `../deps/sail-riscv-lean`) and the compilers/proofs above it
(`Nano/V2Self/Proof`, `Arm`). Four folders, each importing the previous ones in this order:

| folder | role |
|---|---|
| `Steps/` | one-instruction lemmas: running the model's `step` on an encoded word gives `Next s s' pc' rd v mem` |
| `Direct/` | first compilers (Loop, byte-array, memory/region forms) proved directly on `Steps`, plus sorts |
| `Back/` | the same compilers re-derived through an abstract machine interface (`Iface`), then optimised/wide variants and top-level theorems |
| `Examples/` | programs compiled and proved with the above (crc, tree eval, merge sort, …); leaves, not imported by the compiler proofs |

## Files
Steps: `Step` sail_eval normal forms; `SailEval` the `sail_eval` simp/decision tactic helpers; `Regs` register-file
`xval/xset`; `Imm12` 12-bit immediates; `Branch`/`GenBranch` branch words and offsets; `GenALU`/`GenMul`/`GenMem`/`GenRegs`
word encodings as `concrete ||| symbolic` fields, arithmetic, alignment, register presence; `GenTac`/`GenUse` field masks and
per-`Op` step lemmas (`step_rop`); `MemStep`/`MemSteps`/`Arr2Step`/`CompatArr2` ld/sd/lbu steps; `Compat` older names; `WordsBase` word ite forms.
Direct: `Compiler` `codeAt`, running code; `Loop`/`LoopRule` Loop language, `runsTo`; `Arr`/`ArrExp` byte-array compiler (`compileA`);
`Arr2*` block-heap compiler (`HeapRel`, `KeepX`); `Mem*` memory-model form; `SortIns`/`SortMachine` insertion sort; `SortMerge*` merge sort.
Back: `Iface` `ofNext` (Next → abstract effects); `Keep`/`Frame`/`LinkL` frame, ABI, linking; `Exp`/`BStmt`/`Arr`/`Call`/`Calls` source mapping;
`Implements1(Opt)`/`OptArr`/`OptB`/`Wide` optimised and wide-constant compilers (`compileOptA`, `rvwF`); `SortMerge` `msortCode_ok_m`; `Top` bytes of code (`wordBytes`).

## Decisions
* Step lemmas are phrased by `Next` (ret/cfg/pc/x/mem) instead of a full state equation, so the frame is derived once.
* `Back/` re-derives `Direct/` results through an interface rather than editing them, so the original statements stay valid.
* `@[simp]` normal-form lemmas in `Steps/Step.lean`, `GenMem.lean`, `GenTac.lean`, `GenUse.lean`, `WordsBase.lean` are used implicitly by
  `sail_eval`; a textual reference count says nothing for them, so the dead sweep keeps them.

## Check
`lake build` (needs `../deps/sail-riscv-lean`), then `Testing/scripts/review_axioms.sh` → "OK: 8 theorems, axioms as pinned".

## Limits
Sail model pinned to Lean 4.34.1 build; code must sit in `0x80000000 ≤ pc`, `pc+4 ≤ 2^32`, aligned; no RVC (`isRVC = false` required in the fetch lemma).
