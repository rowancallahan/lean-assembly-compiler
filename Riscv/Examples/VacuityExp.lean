/- Non-vacuity, part 2: the hypotheses of `compile_ok` and `gcd_ok` are jointly satisfiable, on an explicit
state, and the theorems then give the expected concrete result.  Plus (V2) a concrete execution of `1 + 1`
that does NOT use `compile_ok`: nine step lemmas of the Sail model applied to the witness state. -/
import Riscv.Examples.MutationBase
import Riscv.Examples.LoopExamples
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Proven.Vacuity

/-- where the code goes -/
def pc0 : BitVec 64 := 0x80000000#64
/-- the return address: a `jal x0, 0` ("park") sits there -/
def ra0 : BitVec 64 := 0x80001000#64
def sp0 : BitVec 64 := 0x80002000#64

/-- memory: `code` at `pc0`, `park` at `ra0` -/
def memC (code : List (BitVec 32)) : Mem :=
  loadBytes (loadBytes ∅ ra0.toNat (codeBytes8 [park])) pc0.toNat (codeBytes8 code)

/-- the witness for a register-in/register-out program: `a0`, `a1` given, everything else `0` -/
def sC (code : List (BitVec 32)) (a0 a1 : BitVec 64) : St := witness pc0 ra0 sp0 a0 a1 0 0 (memC code)

theorem sC_cfg (code a0 a1) : Cfg (sC code a0 a1) := witness_cfg ..
theorem sC_pc (code a0 a1) : (sC code a0 a1).regs.get? .PC = some pc0 := witness_pc ..
theorem sC_x (code a0 a1) (i : Fin 32) : getX (sC code a0 a1) i =
    if i = 1 then ra0 else if i = 2 then sp0 else if i = 10 then a0 else if i = 11 then a1 else 0 := by
  rw [sC, witness_getX]; by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;> by_cases h3 : i = 10 <;>
    by_cases h4 : i = 11 <;> simp_all
theorem sC_ra (code a0 a1) : getX (sC code a0 a1) 1 = ra0 := by rw [sC_x]; rfl
theorem sC_ra_even (code a0 a1) : (getX (sC code a0 a1) 1).toNat % 2 = 0 := by rw [sC_ra]; decide

theorem codeOK_pc0 {n : Nat} (hn : n ≤ 1000) : codeOK pc0 n := by
  refine ⟨by decide, by decide, ?_⟩; have : pc0.toNat = 0x80000000 := rfl; omega

theorem sC_code {code : List (BitVec 32)} (hn : code.length ≤ 1000) (a0 a1) : codeAt (sC code a0 a1) pc0 code :=
  codeAt_load _ code (codeOK_pc0 hn) rfl

theorem sC_park {code : List (BitVec 32)} (hn : code.length ≤ 1000) (a0 a1) : instrAt (sC code a0 a1) ra0 park := by
  have hp : instrAt { sC code a0 a1 with mem := loadBytes ∅ ra0.toNat (codeBytes8 [park]) } ra0 park :=
    codeAt_one (codeAt_load ∅ [park] (by refine ⟨by decide, by decide, by decide⟩) rfl)
  refine instrAt_of_mem (fun i hi => ?_) hp
  show (memC code)[_]? = _
  rw [memC, load_get_other]
  rw [codeBytes8_length]; simp only [pc0, ra0]; simp; omega

theorem pcOK_ra0 : pcOK ra0 := ⟨by decide, by decide, by decide⟩

/-! ## `compile_ok`: `1 + 1` -/

def e11 : Exp := .bin .add (.const 1) (.const 1)

theorem compile_e11 : compile e11 = [iZero 0, iShl 0, iInc 0, iZero 1, iShl 1, iInc 1, iOp .add 0, iRes, iRet] := by
  decide +kernel

/-- **All hypotheses of `compile_ok` hold at once** on the explicit state `sC (compile e11) 0 0`. -/
theorem compile_ok_hyps :
    e11.depth < 11 ∧ Cfg (sC (compile e11) 0 0) ∧ (sC (compile e11) 0 0).regs.get? .PC = some pc0 ∧
    codeAt (sC (compile e11) 0 0) pc0 (compile e11) ∧ codeOK pc0 (compile e11).length ∧
    (getX (sC (compile e11) 0 0) 1).toNat % 2 = 0 := by
  have hn : (compile e11).length ≤ 1000 := by rw [compile_e11]; decide
  exact ⟨by decide, sC_cfg .., sC_pc .., sC_code hn 0 0, codeOK_pc0 hn, sC_ra_even ..⟩

/-- **`compile_ok` applied**: the machine returns to `ra0` with `a0 = 2`. -/
theorem compile_ok_concrete :
    runsTo (sC (compile e11) 0 0) fun s' => s'.regs.get? .PC = some ra0 ∧ getX s' 10 = 2#64 ∧ Cfg s' := by
  obtain ⟨hd, h, hpc, hc, hok, hra⟩ := compile_ok_hyps
  refine runsTo_mono (compile_ok e11 hd h hpc hc hok hra) fun s' ⟨p1, p2, p3, _⟩ => ⟨?_, ?_, p3⟩
  · rw [p1, sC_ra]
  · rw [p2]; decide

/-! ## `gcd_ok`: gcd 12 18 = 6 -/

theorem gcd_12_18 : gcdSub 12#64 18#64 = 6#64 := by
  repeat (rw [gcdSub]; simp)

theorem gcd_len : (compileF gcdProg).length ≤ 1000 := by decide +kernel

/-- **All hypotheses of `gcd_ok` hold at once** on `sC (compileF gcdProg) 12 18`. -/
theorem gcd_ok_hyps :
    Cfg (sC (compileF gcdProg) 12 18) ∧ (sC (compileF gcdProg) 12 18).regs.get? .PC = some pc0 ∧
    codeAt (sC (compileF gcdProg) 12 18) pc0 (compileF gcdProg) ∧ codeOK pc0 (compileF gcdProg).length ∧
    (getX (sC (compileF gcdProg) 12 18) 1).toNat % 2 = 0 :=
  ⟨sC_cfg .., sC_pc .., sC_code gcd_len 12 18, codeOK_pc0 gcd_len, sC_ra_even ..⟩

/-- **`gcd_ok` applied**: returns to `ra0` with `a0 = 6`. -/
theorem gcd_ok_concrete :
    runsTo (sC (compileF gcdProg) 12 18) fun s' => s'.regs.get? .PC = some ra0 ∧ getX s' 10 = 6#64 := by
  obtain ⟨h, hpc, hc, hok, hra⟩ := gcd_ok_hyps
  refine runsTo_mono (gcd_ok h hpc hc hok hra) fun s' ⟨p1, p2, _⟩ => ⟨?_, ?_⟩
  · rw [p1, sC_ra]
  · rw [p2, sC_x, sC_x]; exact gcd_12_18

/-! ## V2: a concrete execution of `1 + 1`, without the compiler theorem -/

theorem step_on {s : St} {pc : BitVec 64} {w : BitVec 32} {ws : List (BitVec 32)}
    (hc : codeAt s pc (w :: ws)) (hok : codeOK pc (w :: ws).length) : pcOK pc ∧ instrAt s pc w :=
  ⟨codeOK_pcOK hok (by simp), by simpa using hc 0 (by simp)⟩

theorem after {s s' : St} {pc : BitVec 64} {rd v} {w : BitVec 32} {ws : List (BitVec 32)}
    (hn : Next s s' (pc + 4) rd v s.mem) (hc : codeAt s pc (w :: ws)) (hok : codeOK pc (w :: ws).length) :
    codeAt s' (pc + 4) ws ∧ codeOK (pc + 4) ws.length := by
  have hc' : codeAt s pc ([w] ++ ws) := hc
  rw [codeAt_append] at hc'
  have hok' := (codeOK_append (a := 1) (b := ws.length) (by simpa [Nat.add_comm] using hok)).2
  exact ⟨codeAt_mem hn.mem (by simpa using hc'.2), by simpa using hok'⟩

/-- **Execution witness**: from `sC (compile e11) 0 0`, nine retired instructions reach a state with
`PC = ra0` and `a0 = 2`.  Each step is a step lemma of the Sail model (`step_zero`, `step_shl`, `step_inc`,
`step_op`, `step_res`, `step_ret`, proved by symbolic evaluation of `run_hart_active`); the proof does not use
`compile_ok`, `gen_ok` or any compiler lemma. -/
set_option maxHeartbeats 0 in
theorem exec_e11 : ∃ s', Steps 9 (sC (compile e11) 0 0) s' ∧ s'.regs.get? .PC = some ra0 ∧
    getX s' 10 = 2#64 ∧ s'.mem = (sC (compile e11) 0 0).mem := by
  have h0 := sC_cfg (compile e11) 0 0
  have hpc0 := sC_pc (compile e11) 0 0
  have hn : (compile e11).length ≤ 1000 := by rw [compile_e11]; decide
  have hc0 := sC_code hn 0 0
  have hok0 := codeOK_pc0 hn
  rw [compile_e11] at hc0 hok0
  obtain ⟨ok, hi⟩ := step_on hc0 hok0
  obtain ⟨s1, n1⟩ := step_zero h0 hpc0 ok 0 (by decide) hi
  obtain ⟨hc, hok⟩ := after n1 hc0 hok0; obtain ⟨ok, hi⟩ := step_on hc hok
  obtain ⟨s2, n2⟩ := step_shl n1.cfg n1.pc ok 0 (by decide) hi
  obtain ⟨hc, hok⟩ := after n2 hc hok; obtain ⟨ok, hi⟩ := step_on hc hok
  obtain ⟨s3, n3⟩ := step_inc n2.cfg n2.pc ok 0 (by decide) hi
  obtain ⟨hc, hok⟩ := after n3 hc hok; obtain ⟨ok, hi⟩ := step_on hc hok
  obtain ⟨s4, n4⟩ := step_zero n3.cfg n3.pc ok 1 (by decide) hi
  obtain ⟨hc, hok⟩ := after n4 hc hok; obtain ⟨ok, hi⟩ := step_on hc hok
  obtain ⟨s5, n5⟩ := step_shl n4.cfg n4.pc ok 1 (by decide) hi
  obtain ⟨hc, hok⟩ := after n5 hc hok; obtain ⟨ok, hi⟩ := step_on hc hok
  obtain ⟨s6, n6⟩ := step_inc n5.cfg n5.pc ok 1 (by decide) hi
  obtain ⟨hc, hok⟩ := after n6 hc hok; obtain ⟨ok, hi⟩ := step_on hc hok
  obtain ⟨s7, n7⟩ := step_op n6.cfg n6.pc ok .add 0 (by decide) hi
  obtain ⟨hc, hok⟩ := after n7 hc hok; obtain ⟨ok, hi⟩ := step_on hc hok
  obtain ⟨s8, n8⟩ := step_res n7.cfg n7.pc ok hi
  obtain ⟨hc, hok⟩ := after n8 hc hok; obtain ⟨ok, hi⟩ := step_on hc hok
  have hra : getX s8 1 = ra0 := by
    simp only [n8.x, n7.x, n6.x, n5.x, n4.x, n3.x, n2.x, n1.x]; simp [T, sC_x]
  obtain ⟨s9, n9⟩ := step_ret n8.cfg n8.pc ok hi (by rw [hra]; decide)
  refine ⟨s9, ⟨s1, n1.ret, s2, n2.ret, s3, n3.ret, s4, n4.ret, s5, n5.ret, s6, n6.ret, s7, n7.ret, s8, n8.ret,
    s9, n9.ret, rfl⟩, by rw [n9.pc, hra], ?_, ?_⟩
  · simp only [n9.x, n8.x, n7.x, n6.x, n5.x, n4.x, n3.x, n2.x, n1.x]; simp [T, Op.raw, Op.eval]; decide
  · rw [n9.mem, n8.mem, n7.mem, n6.mem, n5.mem, n4.mem, n3.mem, n2.mem, n1.mem]

end Proven.Vacuity
