/- OWNER REVIEW FILE: what to read and what to trust.  No new proofs.  Notes: Testing/notes/NANO_V2_REVIEW.md.
Build: `lake build Nano.V2Self.REVIEW`.  The #print axioms output is the authoritative axiom list. -/
import Nano.V2Self.Proof.Parser.ParCapBnd
import Nano.V2Self.Proof.Cert.All
import Nano.V2Self.Proof.Main.SelfC
import Nano.V2Self.Proof.Main.RunsTop

open LeanRV64D Proven Proven.Top Proven.Top.Alloc NanoMain ParSpec

/-! ## 1. the main theorem
For every source text `s` that C compiles (`compileC s = some compiled`: C's driver `mC` emits non-empty code and the
text is at most 2^20 bytes), and every way of reading the text as a function `f : α → β` (`Computes`: the text's
meaning `srcRun` returns `encodeOutput (f a)` on `encodeInput a`, for EVERY `a`), the bytes `compiled.code`, loaded and
called on the Sail RV64 model per `StartCorrect` (input ≤ 2^20 bytes), with an output block big enough and at least
`memoryNeeded` bytes of work memory, return to the caller with the output, length register, no OOM flag, callee-saved
registers kept, configuration kept, and memory changed only in the work block and the output prefix. -/
#check @NanoMain.C_correctLO
#print axioms NanoMain.C_correctLO

/-! ## 2. the certificate: C's own source text means C's Lean function (needed for the self-compilation link) -/
#check @Cert.sem_C
#print axioms Cert.sem_C

/-! ## 2b. C compiled by itself (E, Proof/SelfC.lean; generic versions in Proof/SelfLink.lean).  `SrcGen.X0` = the bytes
of Testing/nano/v2self/self_S_input.txt (D's generator refuses to write the modules unless its chunks concatenate to
exactly those bytes).  `SelfIn` = inputs shorter than 2^64 bytes on which `Sem κC Cert.PC.all` does not hit `cap`.
NOT proved: `compileC ⟨X0⟩ = some compiled` (it is a hypothesis of self_correct_C; holds iff `mC X0 ≠ []`, shown only
by running B1), nor that the shipped B2.bin is `compiled.code`. -/
#check @NanoMain.self_meaning_C
#check @NanoMain.self_computes_C
#check @NanoMain.self_correct_C
#check @NanoMain.SelfIn
#print axioms NanoMain.self_correct_C

/-! ## 2c. memory (E, Proof/Main/RunsTop.lean, Proof/Machine/RunsDef.lean, RunsThr.lean).  `memoryNeeded` of `compileC`
is `spaceC x inp = max 16 (Msp p inp)`: `thr p x` = the LEAST number of usable bytes (above the 16-byte reserve) with
which main does not run out of room at ANY admissible 8-aligned work position; `Msp` rounds `16 + thr` up to 8 bytes.
`C_runs`: `CompileRuns` (the owner's run statement: any work block; OOM flag exactly below `memoryNeeded`), given
`ShiftInv` (D proved it as `shiftInv`, c771775; E's premise-free `C_runsO` / `self_runs_C` are pending). `Msp_le` /
`spaceC_le`: the bound is at most D's work bound `gen_R` (an existential) + 30 bytes. -/
#check @NanoMain.C_runs
#print axioms NanoMain.C_runs
#check @NanoMain.Msp
#check @NanoMain.thr
#check @NanoMain.Msp_le
#check @NanoMain.spaceC_le
-- PENDING (E): #check @NanoMain.C_runsO, @NanoMain.self_runs_C

/-! ## 3. definitions the statement depends on (see NANO_V2_REVIEW.md for summaries) -/
-- machine / calling convention (Spec/, frozen by Spec/FROZEN.sha256)
#check @Proven.Top.Machine
#check @Proven.Top.Runs
#check @Proven.Top.Program
#check @Proven.Top.Computes
#check @Proven.Top.StartCorrect
#check @Proven.Top.readMemory
#check @Proven.Top.riscv
#check @Proven.Top.riscvStep
#check @Proven.Top.riscvObserve
#check @Proven.Top.riscvMapping
#check @Proven.Cfg
-- top-level correctness notion (Spec/Alloc.lean; not listed in Spec/FROZEN.sha256 as of 3ec5c4e)
#check @Proven.Top.Alloc.CompileCorrect
#check @Proven.Top.Alloc.CompiledA
#check @Proven.Top.Alloc.memoryNeeded
#check @Proven.Top.Alloc.KeptRegisters
-- source language
#check @LexSpec.step
#check @LexSpec.Lexes
#check @ParSpec.tokens
#check @ParSpec.pDef
#check @ParSpec.pDefs
#check @ParSpec.refParse
#check @ParSpec.ParsesProgram
#check @NanoMain.Stop
#check @NanoMain.prim
#check @NanoMain.loopRun
#check @NanoMain.ev
#check @NanoMain.defMean
#check @NanoMain.Sem
#check @NanoMain.κC
-- the compiler as a `P → Option CompiledA`
#check @NanoMain.SrcC
#check @NanoMain.pOf
#check @NanoMain.srcRun
#check @NanoMain.spaceC
#check @Proven.Top.Alloc.CompileRuns
#check @NanoMain.compileC
#check @NanoMain.mC
