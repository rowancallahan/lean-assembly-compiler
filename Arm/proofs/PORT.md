# ARM port status (full machine steps, loops, memory)

## Done (kernel-checked, axioms `propext, Classical.choice, Quot.sound`)
- F1 `full_word` (Arm/Full.lean): every emitted word is one full `stepModel` step under `ArmFull`.
- F2 `full_ret`, `compile_ok` (Arm/Machine.lean): `ret` as a full step; the expression backend
  `Arm.compile e` runs to `PC = x30` with `x0 = e.denote`, memory unchanged (`armRunsTo`).
- The generic step theorem `step_ok` (Arm/Step.lean) is word-independent: any instruction whose decode+execute
  result `s1` keeps `Pins`, leaves the bookkeeping registers alone and sets `__BranchTaken`/`_PC` is a full step.
  `full_ret` is the first branch-taken instance (bt = true).
- F3 (partial) Arm/Branch.lean: `b_exec`, `cbz_taken`/`cbz_not`, `cbnz_taken`/`cbnz_not` at the decode
  function + execute layer for symbolic register `t < 31` and symbolic immediate, under `Pins`.

- F3 (2026-11-15) Arm/SymDec.lean, Arm/BrFull.lean: branch words through `__DecodeA64` with symbolic immediates
  (decided from the opcode bits), full steps for `b`, `bl`, `cbz`, `cbnz`, `b.cond` (taken / not taken), `movz`,
  `movk`, `add`/`sub` immediate, `mov`. F4 (partial) Arm/Mem.lean: data accesses (MMU off), full steps for `ldrb`,
  `strb`, 8-aligned `ldr`/`str`/`stur`. Items 1, 2 and 4 below are done in this form; the bridge to DeepMind's
  model and runs (`gcd_sail`, `sort_sail`) are in `Arm/apc/Bridge{Br,Run,Mem}.lean`.

## Not done, and what each piece needs
1. **Branch words through `__DecodeA64`.** `dec_*` lemmas (as in Arm/Words.lean) for `cbz x9, #imm` and
   `b #imm` with the immediate symbolic (the loop compiler's offsets depend on code length). The Words
   generator proves dispatch for concrete words only; for symbolic immediates the decoder's bit-slice tests on
   `0xB4000009 ||| imm19 <<< 5` must evaluate on the fixed opcode bits (untried). Alternative: generate
   concrete words for every offset the loop examples need.
2. **Branch full steps.** Instantiate `step_ok` as `full_ret` does: taken branch ⇒ `bt = true`, `pc1 = target`,
   `Branchtypetaken := DIR` (≠ RESET, so `ArmFull` is kept); not taken ⇒ like `full_word` with PC + 4.
3. **`Stmt`/`compileS` for ARM.** Needs `mov x_v, x9` for v = 1..3 (only `mov x0, x9` is in `emitted`):
   extend `gen/gen_words.py` with those three words and rebuild Words (~13 min). Then `compileS` = RISC-V's with
   `cbz x9` for `beq t0, x0` and `b` for `jal x0`. `Exec`, `Exec.loop_of`, `LoopRule` are pure Lean and port
   verbatim with `runsTo` → `armRunsTo` (`ArmSteps.append` is the `Steps.trans` analogue).
4. **F4 memory.** `ldrb/strb/ldr/str` (register base, zero offset): data translation is the same MMU-off path
   as `fetch_ok` but with `CreateAccDescGPR` (needs an `accGPR` analogue of `accIF`, `mpam_ok` for
   `AccessType_GPR`), `AArch64_CheckDebug` with the data-side watchpoint path (off under `Pins`), alignment
   (`SCTLR_EL3.A = 0`), and the store path `AArch64_MemSingle_set` (`writeBytes`). `MemModel` is pure Lean.
5. **F5 arrays** builds on 3 and 4.
