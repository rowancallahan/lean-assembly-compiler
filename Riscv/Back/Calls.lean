/- Programs with calls on the Sail model: the statement `ImplementsW` (bytes in, one 64-bit word out,
ONE resource bound `space`) and its proof for every well-formed program from a source-level run
(`callsCode_implements`), through `MachineC.compP_ok`.

Conventions of the generated code (`callsCode P main`): global 0 (`a0`) = input base (byte block 0),
global 1 (`a1`) = input length, global 3 (`a3`) = output base (word block 0: one 8-aligned word), global 4
(`a4`) receives `main`'s result; the stack lives in the block below `sp` (the `stack` region). -/
import Compiler.CProg
import Riscv.Back.Call
import Riscv.Back.BStmt
import Riscv.Direct.SortMergeMachine
import Spec.Encode
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven

/-- `code`, placed anywhere, computes the word `f x` from the bytes `x` (for inputs satisfying `pre`):
called with `a0 = input, a1 = length, a2 = scratch, a3 = output, sp = top of the work block, ra`, it runs to
`ra` with `enc (f x)` (8 bytes, little-endian) in `output`, other memory and callee-saved registers
unchanged, `Cfg` kept.  Resources: the work block `stack` must have `space |x|` bytes; `output` is 8 bytes,
8-aligned and present in the memory map. -/
def ImplementsW (code : List (BitVec 32)) (f : List UInt8 → BitVec 64) (pre : List UInt8 → Prop)
    (space : Nat → Nat) : Prop :=
  ∀ (x : List UInt8) (s : St) (entry ra : BitVec 64) (input scratch output stack : Region),
    let codeR : Region := ⟨entry.toNat, 4 * code.length⟩
    pre x → Cfg s → s.regs.get? .PC = some entry → entry.toNat % 4 = 0 →
    bytesAt s entry.toNat (4 * code.length) = codeBytes code →
    s.regs.get? .x10 = some (BitVec.ofNat 64 input.base) →
    s.regs.get? .x11 = some (BitVec.ofNat 64 x.length) →
    s.regs.get? .x12 = some (BitVec.ofNat 64 scratch.base) →
    s.regs.get? .x13 = some (BitVec.ofNat 64 output.base) →
    s.regs.get? .x2 = some (BitVec.ofNat 64 (stack.base + stack.len)) →
    s.regs.get? .x1 = some ra → ra.toNat % 4 = 0 →
    bytesAt s input.base x.length = x.map (some ·.toBitVec) →
    input.len = x.length → output.len = 8 → output.base % 8 = 0 → space x.length ≤ stack.len →
    (∀ r ∈ [input, scratch, output, stack, codeR], r.inRAM) →
    [input, scratch, output, stack, codeR].Pairwise disjoint →
    (∀ i < 8, (s.mem[output.base + i]?).isSome) →
    runsTo s fun s' => s'.regs.get? .PC = some ra ∧
      bytesAt s' output.base 8 = (enc (f x)).map (some ·.toBitVec) ∧
      unchangedOutside s s' [input, scratch, output, stack] ∧ calleeSavedKept s s' ∧ Cfg s'

end Proven

namespace Proven.Mach.Riscv

theorem le8_byte (w : BitVec 64) (j : Nat) :
    w.extractLsb' (8 * j) 8 = (UInt8.ofNat (w.toNat / 256 ^ j % 256)).toBitVec := by
  apply BitVec.eq_of_toNat_eq
  show _ = (UInt8.ofNat (w.toNat / 256 ^ j % 256)).toNat
  rw [UInt8.toNat_ofNat', Nat.mod_mod_of_dvd _ (by decide), BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    Nat.pow_mul]

/-- the bytes of a word are its spec encoding -/
theorem le8_enc (w : BitVec 64) : le8 w = (Bytes.enc w).map (·.toBitVec) := by
  show _ = (leN 8 w.toNat).map (·.toBitVec)
  simp only [le8, List.range, List.range.loop, List.map, leN, le8_byte]
  simp [Nat.div_div_eq_div_mul]

theorem uncons {α : Type} {l : List α} {n : Nat} (h : l.length = n + 1) : ∃ a t, l = a :: t ∧ t.length = n := by
  cases l with
  | nil => exact absurd h (by simp)
  | cons a t => exact ⟨a, t, rfl, by simpa using h⟩

/-- any 8 bytes are the bytes of a word -/
theorem exists_le8 (l0 : List (BitVec 8)) (h0 : l0.length = 8) : ∃ w : BitVec 64, le8 w = l0 := by
  obtain ⟨b0, l1, rfl, h1⟩ := uncons h0
  obtain ⟨b1, l2, rfl, h2⟩ := uncons h1
  obtain ⟨b2, l3, rfl, h3⟩ := uncons h2
  obtain ⟨b3, l4, rfl, h4⟩ := uncons h3
  obtain ⟨b4, l5, rfl, h5⟩ := uncons h4
  obtain ⟨b5, l6, rfl, h6⟩ := uncons h5
  obtain ⟨b6, l7, rfl, h7⟩ := uncons h6
  obtain ⟨b7, l8, rfl, h8⟩ := uncons h7
  obtain rfl := List.eq_nil_of_length_eq_zero h8
  refine ⟨BitVec.ofNat 64 (b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 * (b4.toNat +
    256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat))))))), ?_⟩
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
  have := b4.isLt; have := b5.isLt; have := b6.isLt; have := b7.isLt
  simp only [le8, List.range, List.range.loop, List.map]
  refine congr (congrArg _ ?_) (congr (congrArg _ ?_) (congr (congrArg _ ?_) (congr (congrArg _ ?_)
    (congr (congrArg _ ?_) (congr (congrArg _ ?_) (congr (congrArg _ ?_) (congr (congrArg _ ?_) rfl))))))) <;>
  (apply BitVec.eq_of_toNat_eq
   simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
   omega)

/-! ## Checking well-formedness of a concrete program -/

/-- the length of `genConst k n`, by structural recursion on fuel (so that it evaluates) -/
def glF : Nat → Nat → Nat
  | 0, _ => 1
  | f + 1, n => if n = 0 then 1 else glF f (n / 2) + 1 + (if n % 2 = 1 then 1 else 0)

theorem glF_eq (k : Nat) : ∀ (f n : Nat), n ≤ f → (genConst k n).length = glF f n
  | 0, n, h => by
    obtain rfl : n = 0 := by omega
    rw [genConst]; rfl
  | f + 1, n, h => by
    rw [genConst, glF]
    by_cases h0 : n = 0
    · rw [if_pos h0, if_pos h0]; rfl
    · rw [if_neg h0, if_neg h0, List.length_append, List.length_append, glF_eq k f (n / 2) (by omega)]
      by_cases h1 : n % 2 = 1
      · rw [if_pos h1, if_pos h1]; rfl
      · rw [if_neg h1, if_neg h1]; rfl

theorem gcLen (k n : Nat) : (genConst k n).length = glF n n := glF_eq k n n (Nat.le_refl _)

/-- `wf_calls [defs]`: prove `wfF` / `wfC` of a concrete function for `rvC` by evaluation -/
syntax "wf_calls" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| wf_calls [$ls,*]) => `(tactic|
    (simp [$ls,*, MachineC.wfF, MachineC.wfC, MachineF.wfB, Mach.BExp.depth, Mach.BExp.vlt, nlOf,
      MachineC.progOff, MachineC.offs, MachineC.lenF, MachineC.lenC, MachineC.lenStub, MachineC.posS,
      MachineC.lenArgs, MachineC.lenLi, argsC, padArgs, mgenB, Mach.setV, MachineF.compB, MachineF.codeF,
      MachineC.codeC, MachineC.encY, MachineF.encF, rvC, rvF, rv, core, base, Riscv.enc, encX, encC, prologue,
      opCode, selCode, Mach.addrB, Mach.addrW, rk, avar, List.replicate, gcLen, NS] <;> decide))

/-- the source-level specification of a program: on input `x` (with `pre x`) the entry call runs within
`need |x|` bytes of stack and leaves `f x` in the output word -/
def Computes (P : Prog) (main : Nat) (f : List UInt8 → BitVec 64) (pre : List UInt8 → Prop) (need : Nat → Nat) :
    Prop :=
  ∀ (x : List UInt8) (env : BEnv) (w0 : BitVec 64), pre x → env 1 = BitVec.ofNat 64 x.length →
    ∃ σ', CExec P (need x.length) (.call 4 main []) ⟨env, [x.map (·.toBitVec)], [[w0]]⟩ σ' ∧ σ'.wheap = [[f x]]

/-- the machine code of a program with calls -/
def callsCode (P : Prog) (main : Nat) : List (BitVec 32) := rvC.codeC (rvC.compP P [0] [3] 4 main)

/-- well-formedness of a program for the RISC-V target -/
def WfProg (P : Prog) (main : Nat) : Prop :=
  (∀ f (hf : f < P.length), rvC.wfF P [0] [3] (rvC.progOff P [0] [3] 4 main) (rvC.progOff P [0] [3] 4 main f) P[f]) ∧
  rvC.wfC P [0] [3] (rvC.progOff P [0] [3] 4 main) 0 rvC.posS (.call 4 main [])

/-- **Programs with calls on the Sail model.**  A well-formed program whose source run computes `f`
within `need n` bytes of stack is implemented by its code with the single bound `space n = need n + 24`. -/
theorem callsCode_implements {P : Prog} {main : Nat} {f : List UInt8 → BitVec 64} {pre : List UInt8 → Prop}
    {need : Nat → Nat} (hwf : WfProg P main) (hsrc : Computes P main f pre need) :
    ImplementsW (callsCode P main) f pre (fun n => need n + 24) := by
  intro x s entry ra input scratch output stack codeR hpre h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hx
    hil hol hoal hstk hram hdis hmap
  have hin : ∀ r ∈ [input, scratch, output, stack, codeR], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14, d15⟩, ⟨d23, d24, d25⟩, ⟨d34, d35⟩, d45⟩ := hdis
  obtain ⟨ri, rs, ro, rst, rc⟩ := hin
  unfold Region.inRAM at ri rs ro rst rc
  unfold Proven.disjoint at d12 d13 d14 d15 d23 d24 d25 d34 d35 d45
  simp only [codeR] at d15 d25 d35 d45 rc
  have hsp : getX s 2 = BitVec.ofNat 64 (stack.base + stack.len) := getX_of (h.x2.symm.trans h2) rfl
  have hspn : (getX s 2).toNat = stack.base + stack.len := by rw [hsp]; exact toNat_ofNat' (by omega)
  have hfb : frameBase 0 (getX s 2) = (stack.base + stack.len) / 8 * 8 - 8 := by unfold frameBase; rw [hspn]
  have hstk' : need x.length + 24 ≤ stack.len := hstk
  have hok : codeOK entry (callsCode P main).length := ⟨hal, rc.1, rc.2⟩
  obtain ⟨w0, hw0⟩ := exists_le8 ((bytesAt s output.base 8).map (·.getD 0)) (by simp [bytesAt])
  have hout : bytesAt s output.base 8 = (le8 w0).map some := by rw [hw0]; exact bytesAt_hosted hmap
  let env : BEnv := fun i => if hi : i < 8 then getX s (A8 ⟨i, hi⟩) else 0
  obtain ⟨σ', hex, hres⟩ := hsrc x env w0 hpre (getX_of (h.x11.symm.trans h11) rfl)
  have hen : rvC.enterOK s 0 := (⟨by rw [hfb]; omega, by rw [hfb]; omega, by rw [hfb]; omega, by decide⟩ :
    FrOK 0 (frameBase 0 (getX s 2)))
  have hfA : rvC.frameAt s 0 = (stack.base + stack.len) / 8 * 8 - 8 := hfb
  have hL : rvC.PLay entry (rvC.codeC (rvC.compP P [0] [3] 4 main)).length [⟨input.base, x.length⟩]
      [⟨output.base, 8⟩] stack.base (rvC.frameAt s 0 + 8) := by
    rw [hfA]
    refine ⟨fun r hr => ?_, fun r hr => ?_, List.pairwise_singleton _ _, List.pairwise_singleton _ _,
      fun r hr w hw => ?_, fun w hw => ?_, ?_, fun r hr => ?_, fun r hr => ?_, fun r hr a h1 h2 _ _ => ?_,
      fun w hw a h1 h2 _ _ => ?_, fun a h1 h2 _ _ => ?_⟩
    · rw [List.mem_singleton] at hr; subst hr; show 0x80000000 ≤ _ ∧ _ ≤ 0x100000000; dsimp only; omega
    · rw [List.mem_singleton] at hr; subst hr; show 0x80000000 ≤ _ ∧ _ ≤ 0x100000000; dsimp only; omega
    · rw [List.mem_singleton] at hr hw; subst hr; subst hw; unfold disjoint; dsimp only; omega
    · rw [List.mem_singleton] at hw; subst hw; exact hoal
    · show 0x80000000 ≤ _ ∧ _ ≤ 0x100000000; omega
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with rfl | rfl <;> (unfold disjoint; dsimp only; omega)
    · have hcl : (rvC.codeC (rvC.compP P [0] [3] 4 main)).length = (callsCode P main).length := rfl
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with (rfl | rfl) | rfl <;> (unfold disjoint; dsimp only; rw [hcl]; omega)
    · rw [List.mem_singleton] at hr; subst hr; show 0x80000000 ≤ a ∧ a + 1 ≤ 0x100000000
      dsimp only at h1 h2; omega
    · rw [List.mem_singleton] at hw; subst hw; show 0x80000000 ≤ a ∧ a + 1 ≤ 0x100000000
      dsimp only at h1 h2; omega
    · show 0x80000000 ≤ a ∧ a + 1 ≤ 0x100000000; omega
  have hheap : rvC.HeapB [0] [3] [⟨input.base, x.length⟩] [⟨output.base, 8⟩]
      ⟨env, [x.map (·.toBitVec)], [[w0]]⟩ s := by
    refine ⟨rfl, rfl, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, rfl, rfl, fun b hb => ?_, fun b hb => ?_,
      fun b hb => ?_⟩ <;> obtain rfl : b = 0 := (by simp only [List.length_singleton] at hb; omega)
    · exact getX_of (h.x10.symm.trans h10) rfl
    · exact List.length_map _
    · show bytes (rv.mem s) input.base x.length = (x.map (·.toBitVec)).map some
      rw [bytes_eq, hx, List.map_map]; rfl
    · exact getX_of (h.x13.symm.trans h13) rfl
    · rfl
    · show bytes (rv.mem s) output.base 8 = (le8 w0 ++ []).map some
      rw [bytes_eq, hout, List.append_nil]
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  refine runsTo_mono (rvC.compP_ok hex ⟨h, hpc, codeAt_of_codeBytes hok hcode, hok⟩ hwf.1 hwf.2 (by decide) (by decide)
    hen (by rw [hfA]; omega) hL (fun i => by
      show getX s (phys (avar i)) = _; rw [phys_avar]; show _ = dite _ _ _; rw [dite_pos' i.2]) hheap
    (by show (getX s 1).toNat % 2 = 0; rw [hra']; omega)) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  refine ⟨by rw [p1]; exact congrArg some hra', ?_, fun a ha => p4 a fun r hr => ?_, keep_calleeSaved h p5 p6, p5⟩
  · have := p3.wbyts 0 Nat.zero_lt_one
    rw [hres] at this
    rw [← bytes_eq, show bytes (rv.mem s') output.base 8 = _ from this]
    show (le8 (f x) ++ []).map some = _
    rw [List.append_nil, le8_enc, List.map_map]; rfl
  · have a1 := ha input (by simp); have a2 := ha scratch (by simp); have a3 := ha output (by simp)
    have a4 := ha stack (by simp)
    rw [hfA] at hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (rfl | rfl) | rfl <;> (dsimp only; omega)

end Proven.Mach.Riscv
