/- OWNER REVIEW FILE: what to read and what to trust.  No new proofs.  Notes: Testing/notes/NANO_V2_REVIEW.md.
Build: `lake build Nano.V2Self.REVIEW`.  The #print axioms output is the authoritative axiom list. -/
import Nano.V2Self.Proof.ParCapBnd
import Nano.V2Self.Proof.Cert.All

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
-- PENDING (E): the SelfLink final theorem (compileC on C's own text) is not on the branch yet; add its #check here.

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
-- top-level correctness notion (Compiler/AllocSpec.lean: NOT in Spec/, not covered by FROZEN.sha256)
#check @Proven.Top.Alloc.CompileCorrectL
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
#check @NanoMain.compileC
#check @NanoMain.mC
