/- Programs with calls on DeepMind's AArch64 semantics: the statement `ImplementsA` (bytes in, one 64-bit word out,
ONE resource bound `space`) and its proof for every well-formed program from a source-level run
(`callsCode_implements_apc`), through `MachineC.compP_ok` and `apcC`; then the call clients of
`Riscv/Examples/{CallExamples,TreeEval}.lean` (source proofs staged unchanged) on ARM.

Conventions (as on RISC-V): global 0 (x0) = input base (byte block 0), global 1 (x1) = input length, global 3 (x3) =
output base (word block 0: one 8-aligned word), global 4 receives `main`'s result; the wk is the block below
`sp` (the `wk` region, `sp` 8-aligned). -/
import Apc.Call
import Apc.Stack
import Apc.Src.TreeEval
namespace Proven.Apc
open Proven Proven.Mach Proven.Mach.Riscv

/-- `code`, placed at the PC inside the executable range of `L`, computes the word `f x` from the bytes `x` (for
inputs satisfying `pre`): called with x0 = input, x1 = length, x3 = output, sp = top of the work block, it runs to
x30 with `enc (f x)` (8 bytes, little-endian) in `output`, other memory, `sp` and every register outside x0..x15
unchanged, status `Running`.  Resources: the work block `wk` must have `space |x|` bytes; input, output and
wk lie in the writable data range of `L`. -/
def ImplementsA (L : Lay) (code : List (BitVec 32)) (f : List UInt8 → BitVec 64) (pre : List UInt8 → Prop)
    (space : Nat → Nat) : Prop :=
  ∀ (x : List UInt8) (s : Arm64.State) (input output wk : Region),
    pre x → (apcC L).At s s.pc code →
    s.regs.read 0#5 = BitVec.ofNat 64 input.base → s.regs.read 1#5 = BitVec.ofNat 64 x.length →
    s.regs.read 3#5 = BitVec.ofNat 64 output.base →
    s.sp.toNat = wk.base + wk.len → s.sp.toNat % 8 = 0 →
    bytes (memV s) input.base x.length = x.map (some ·.toBitVec) →
    input.len = x.length → output.len = 8 → output.base % 8 = 0 → space x.length ≤ wk.len →
    (∀ r ∈ [input, output, wk], L.dLo ≤ r.base ∧ r.base + r.len ≤ L.dHi) → L.dHi < 2 ^ 64 →
    [input, output, wk, ⟨s.pc.toNat, 4 * code.length⟩].Pairwise disjoint →
    ∃ s', Arm64.Steps P s s' ∧ s'.pc = s.regs.read 30#5 ∧
      bytes (memV s') output.base 8 = (Bytes.enc (f x)).map (some ·.toBitVec) ∧
      Out [input, output, wk] (memV s) (memV s') ∧ s'.status = .Running ∧ s'.sp = s.sp ∧
      ∀ y : BitVec 5, (∀ r, xr r ≠ y) → s'.regs.read y = s.regs.read y

/-- the machine code of a program with calls -/
def callsCode (L : Lay) (P : Prog) (main : Nat) : List (BitVec 32) := (apcC L).codeC ((apcC L).compP P [0] [3] 4 main)

/-- well-formedness of a program for this target -/
def WfProg (L : Lay) (P : Prog) (main : Nat) : Prop :=
  (∀ f (hf : f < P.length), (apcC L).wfF P [0] [3] ((apcC L).progOff P [0] [3] 4 main)
    ((apcC L).progOff P [0] [3] 4 main f) P[f]) ∧
  (apcC L).wfC P [0] [3] ((apcC L).progOff P [0] [3] 4 main) 0 (apcC L).posS (.call 4 main [])

/-- **Programs with calls on DeepMind's AArch64 semantics.**  A well-formed program whose source run computes `f`
within `need n` bytes of wk is implemented by its code with the single bound `space n = need n + 16`. -/
theorem callsCode_implements_apc {L : Lay} {P : Prog} {main : Nat} {f : List UInt8 → BitVec 64}
    {pre : List UInt8 → Prop} {need : Nat → Nat} (hwf : WfProg L P main) (hsrc : Computes P main f pre need) :
    ImplementsA L (callsCode L P main) f pre (fun n => need n + 16) := by
  intro x s input output wk hpre hA h0 h1 h3 hsp hsp8 hx hil hol hoal hstk hdat hd hdis
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hdis
  unfold disjoint at d12 d13 d14 d23 d24 d34
  unfold callsCode at d14 d24 d34; dsimp only at d14 d24 d34
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hdat
  obtain ⟨ri, ro, rs⟩ := hdat
  have hstk' : need x.length + 16 ≤ wk.len := hstk
  have hfA : (apcC L).frameAt s 0 = wk.base + wk.len - 8 := by show s.sp.toNat - 8 * (0 + 1) = _; omega
  -- the output word, as some `w0`
  have hrd : ∀ i, i < 8 → ∃ b, memV s (output.base + i) = some b := fun i hi => by
    have := (hA.ok.2.2 (output.base + i) (by omega) (by omega)).1
    exact ⟨_, by unfold memV; rw [if_pos ⟨by omega, this⟩]⟩
  obtain ⟨w0, hw0⟩ := exists_le8 ((bytes (memV s) output.base 8).map (·.getD 0)) (by simp [length_bytes])
  have hout : bytes (memV s) output.base 8 = (le8 w0).map some := by
    rw [hw0]
    apply List.ext_getElem (by simp [length_bytes])
    intro i h1 h2
    rw [length_bytes] at h1
    simp only [List.getElem_map, bytes_getElem]
    obtain ⟨b, hb⟩ := hrd i h1; rw [hb]; rfl
  let env : BEnv := fun i => if hi : i < 8 then (apcC L).get s (avar ⟨i, hi⟩) else 0
  obtain ⟨σ', hex, hres⟩ := hsrc x env w0 hpre (by simp only [env]; rw [dite_eq_left_of_eq_true (by decide)]; exact h1)
  have hen : (apcC L).enterOK s 0 := ⟨by decide, hsp8, by omega, by show _ ≤ s.sp.toNat - 8 * (0 + 1); omega,
    by show s.sp.toNat - 8 * (0 + 1) + 8 * (0 + 1) ≤ _; omega, hd⟩
  have hL : (apcC L).PLay s.pc ((apcC L).codeC ((apcC L).compP P [0] [3] 4 main)).length [⟨input.base, x.length⟩]
      [⟨output.base, 8⟩] wk.base ((apcC L).frameAt s 0 + 8) := by
    rw [hfA]
    refine ⟨fun r hr => ?_, fun r hr => ?_, List.pairwise_singleton _ _, List.pairwise_singleton _ _,
      fun r hr w hw => ?_, fun w hw => ?_, ?_, fun r hr => ?_, fun r hr => ?_, fun r hr a h1 h2 _ _ => ?_,
      fun r hr a h1 h2 _ _ => ?_, fun a h1 h2 _ _ => ?_⟩
    · rw [List.mem_singleton] at hr; subst hr; exact ⟨Nat.zero_le _, by show _ ≤ 2 ^ 64 - 1; dsimp only; omega⟩
    · rw [List.mem_singleton] at hr; subst hr; exact ⟨Nat.zero_le _, by show _ ≤ 2 ^ 64 - 1; dsimp only; omega⟩
    · rw [List.mem_singleton] at hr hw; subst hr; subst hw; unfold disjoint; dsimp only; omega
    · rw [List.mem_singleton] at hw; subst hw; exact hoal
    · exact ⟨Nat.zero_le _, by show _ ≤ 2 ^ 64 - 1; omega⟩
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with rfl | rfl <;> (unfold disjoint; dsimp only; omega)
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with (rfl | rfl) | rfl <;> (unfold disjoint; dsimp only; omega)
    · rw [List.mem_singleton] at hr; subst hr; dsimp only at h1 h2; exact ⟨by omega, by omega⟩
    · rw [List.mem_singleton] at hr; subst hr; dsimp only at h1 h2; exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  have hheap : (apcC L).HeapB [0] [3] [⟨input.base, x.length⟩] [⟨output.base, 8⟩]
      ⟨env, [x.map (·.toBitVec)], [[w0]]⟩ s := by
    refine ⟨rfl, rfl, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, rfl, rfl, fun b hb => ?_, fun b hb => ?_,
      fun b hb => ?_⟩ <;> obtain rfl : b = 0 := (by simp only [List.length_singleton] at hb; omega)
    · exact h0
    · exact List.length_map _
    · show bytes (memV s) input.base x.length = (x.map (·.toBitVec)).map some
      rw [hx, List.map_map]; rfl
    · exact h3
    · rfl
    · show bytes (memV s) output.base 8 = (le8 w0 ++ []).map some
      rw [hout, List.append_nil]
  obtain ⟨s', hst, p1, -, p3, p4, p5, p6⟩ := (apcC L).compP_ok hex hA hwf.1 hwf.2 (by decide) (by decide) hen
    (by rw [hfA]; omega) hL (fun i => by simp only [env]; rw [dite_eq_left_of_eq_true (by simp)]) hheap trivial
  refine ⟨s', hst, p1, ?_, fun a ha => p4 a fun r hr => ?_, p5.1, p6.2, fun y hy => p6.1 y hy id⟩
  · have := p3.wbyts 0 Nat.zero_lt_one
    rw [hres] at this
    show bytes ((apcC L).mem s') output.base 8 = _
    rw [show bytes ((apcC L).mem s') output.base 8 = _ from this]
    show (le8 (f x) ++ []).map some = _
    rw [List.append_nil, le8_enc, List.map_map]; rfl
  · have a1 := ha input (by simp); have a2 := ha output (by simp); have a4 := ha wk (by simp)
    rw [hfA] at hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (rfl | rfl) | rfl <;> (dsimp only; omega)

/-! ## Checking well-formedness of a concrete program -/

/-- `wf_apc [defs]`: prove `wfF` / `wfC` of a concrete function for `apcC L` by evaluation -/
syntax "wf_apc" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| wf_apc [$ls,*]) => `(tactic|
    (simp [$ls,*, MachineC.wfF, MachineC.wfC, MachineF.wfB, Mach.BExp.depth, Mach.BExp.vlt, nlOf,
      MachineC.progOff, MachineC.offs, MachineC.lenF, MachineC.lenC, MachineC.lenStub, MachineC.posS,
      MachineC.lenArgs, MachineC.lenLi, argsC, padArgs, mgenB, Mach.setV, MachineF.compB, MachineF.codeF,
      MachineC.codeC, MachineC.encY, MachineF.encF, apcC, apcF, apc, core, base, Proven.Apc.enc, encX, encC, opW, gc,
      zs, Mach.addrB, Mach.addrW, rk, avar, List.replicate] <;> decide))

theorem sumToProg_wf (L : Lay) : WfProg L sumToProg 0 := by
  refine ⟨fun f hf => ?_, ?_⟩
  · have : f = 0 ∨ f = 1 := by simp [sumToProg] at hf; omega
    rcases this with rfl | rfl <;> wf_apc [sumToProg, mainFn, sumFn]
  · wf_apc [sumToProg, mainFn, sumFn]

/-- **`sumTo` on ARM**: one input byte `n`, output `enc (sumTo n)`; recursion depth `n`. -/
theorem sumTo_apc (L : Lay) : ImplementsA L (callsCode L sumToProg 0) (fun x => sumTo (x.headD 0).toNat)
    (fun x => x.length = 1) (fun _ => 16 + (24 + 24 * 255) + 16) :=
  callsCode_implements_apc (sumToProg_wf L) sumToProg_computes

theorem fibProg_wf (L : Lay) : WfProg L fibProg 0 := by
  refine ⟨fun f hf => ?_, ?_⟩
  · have : f = 0 ∨ f = 1 := by simp [fibProg] at hf; omega
    rcases this with rfl | rfl <;> wf_apc [fibProg, mainFn, fibFn]
  · wf_apc [fibProg, mainFn, fibFn]

/-- **`fib` (doubly recursive) on ARM** -/
theorem fib_apc (L : Lay) : ImplementsA L (callsCode L fibProg 0) (fun x => fibW (x.headD 0).toNat)
    (fun x => x.length = 1) (fun _ => 16 + (32 + 32 * 255) + 16) :=
  callsCode_implements_apc (fibProg_wf L) fibProg_computes

theorem evenProg_wf (L : Lay) : WfProg L evenProg 0 := by
  refine ⟨fun f hf => ?_, ?_⟩
  · have : f = 0 ∨ f = 1 ∨ f = 2 := by simp [evenProg] at hf; omega
    rcases this with rfl | rfl | rfl <;> wf_apc [evenProg, mainFn, evenFn, oddFn]
  · wf_apc [evenProg, mainFn, evenFn, oddFn]

/-- **mutually recursive `isEven` / `isOdd` on ARM** -/
theorem isEven_apc (L : Lay) : ImplementsA L (callsCode L evenProg 0) (fun x => bw (isEven (x.headD 0).toNat))
    (fun x => x.length = 1) (fun _ => 16 + (24 + 24 * 255) + 16) :=
  callsCode_implements_apc (evenProg_wf L) evenProg_computes

theorem treeProg_wf (L : Lay) : WfProg L treeProg 0 := by
  refine ⟨fun f hf => ?_, ?_⟩
  · have : f = 0 ∨ f = 1 := by simp [treeProg] at hf; omega
    rcases this with rfl | rfl <;> wf_apc [treeProg, mainT, evFn, stepB]
  · wf_apc [treeProg, mainT, evFn, stepB]

/-- **The tree evaluator on ARM.**  For every tree `t`, with `enc t` (`n` bytes) as the input, the code leaves
`enc (t.eval)` in the output word, using at most `space n = 32 n + 64` bytes of the work block. -/
theorem treeEval_apc (L : Lay) : ImplementsA L (callsCode L treeProg 0) treeF
    (fun x => (∃ t : Tree, x = Bytes.enc t) ∧ x.length < 2 ^ 64) (fun n => 16 + (32 + 32 * n) + 16) :=
  callsCode_implements_apc (treeProg_wf L) treeProg_computes

end Proven.Apc
