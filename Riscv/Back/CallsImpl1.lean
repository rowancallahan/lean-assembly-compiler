/- Programs with calls (`MachineC`, plain back end `compP`) in `Implements1` form.

`implements1_of_cexec`: a well-formed program `P` whose entry call `res := main()` (source run `CExec`, stack
need `need n` bytes for an input of `n` bytes) writes the result bytes into the output block is implemented by
its code with the single bound `space n = need n + 24`.  Byte blocks: `0` = input (`a0`), `1` = output (`a3`);
no word blocks.  The stack is the work block (top in `sp`; 16 bytes for the stub's two cells, up to 7 for
aligning `sp`). -/
import Riscv.Back.Calls
import Riscv.Back.Implements1
import Riscv.Back.Keep

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv
open LeanRV64D

/-- the code of a program with calls; byte blocks in `a0` (input) and `a3` (output) -/
def callsCode1 (P : Prog) (res main : Nat) : List (BitVec 32) := rvC.codeC (rvC.compP P [0, 3] [] res main)

/-- well-formedness for `callsCode1` -/
def WfProg1 (P : Prog) (res main : Nat) : Prop :=
  (∀ f (hf : f < P.length), rvC.wfF P [0, 3] [] (rvC.progOff P [0, 3] [] res main)
    (rvC.progOff P [0, 3] [] res main f) P[f]) ∧
  rvC.wfC P [0, 3] [] (rvC.progOff P [0, 3] [] res main) 0 rvC.posS (.call res main [])

/-- **Programs with calls ⇒ `Implements1`.** -/
theorem implements1_of_cexec {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (f : α → β)
    (P : Prog) (res main : Nat) (hwf : WfProg1 P res main) (hres : res < 8) (need : Nat → Nat) (maxLen : Nat)
    (retLen : Bool)
    (hex : ∀ (a : α) (out : List (BitVec 8)) (env : BEnv),
      env 1 = BitVec.ofNat 64 (encA a).length → (encA a).length ≤ maxLen → (encA a).length < 2 ^ 32 →
      (encB (f a)).length ≤ out.length → out.length < 2 ^ 32 →
      ∃ σ' out', CExec P (need (encA a).length) (.call res main []) ⟨env, [(encA a).map (·.toBitVec), out], []⟩ σ' ∧
        σ'.heap = [(encA a).map (·.toBitVec), out'] ∧
        out'.take (encB (f a)).length = (encB (f a)).map (·.toBitVec) ∧
        out'.drop (encB (f a)).length = out.drop (encB (f a)).length ∧
        (retLen = true → σ'.env 1 = BitVec.ofNat 64 (encB (f a)).length)) :
    Implements1With encA encB (callsCode1 P res main) f (fun n => need n + 24) maxLen retLen := by
  intro a s entry ra input output work x y codeR hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx
    hil hol hws hwal hram hdis hmapO hmapW
  have hin : ∀ r ∈ [input, output, work, codeR], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hdis
  obtain ⟨ri, ro, rw', rc⟩ := hin
  unfold Region.inRAM at ri ro rw' rc
  unfold Proven.disjoint at d12 d13 d14 d23 d24 d34
  simp only [codeR] at d14 d24 d34 rc
  have hil' : input.len = x.length := hil
  have hol' : y.length ≤ output.len := hol
  have hws' : need (encA a).length + 24 ≤ work.len := hws
  have hsp : getX s 2 = BitVec.ofNat 64 (work.base + work.len) := getX_of (h.x2.symm.trans h2) rfl
  have hspn : (getX s 2).toNat = work.base + work.len := by rw [hsp]; exact toNat_ofNat' (by omega)
  have hfb : frameBase 0 (getX s 2) = (work.base + work.len) / 8 * 8 - 8 := by unfold frameBase; rw [hspn]
  have hok : codeOK entry (callsCode1 P res main).length := ⟨hal, rc.1, rc.2⟩
  obtain ⟨out0, hout0l, ho⟩ : ∃ out0 : List (BitVec 8), out0.length = output.len ∧
      bytesAt s output.base output.len = out0.map some :=
    ⟨_, by simp [bytesAt], bytesAt_hosted fun i hi => hmapO i hi⟩
  obtain ⟨σ', out', hexec, hh, htk, hdr, hrl⟩ := hex a out0 (envOf s)
    (by simpa [envOf] using getX_of (h.x11.symm.trans h11) rfl) hmax (by show x.length < 2 ^ 32; omega)
    (by show y.length ≤ out0.length; omega) (by omega)
  have hen : rvC.enterOK s 0 := (⟨by rw [hfb]; omega, by rw [hfb]; omega, by rw [hfb]; omega, by decide⟩ :
    FrOK 0 (frameBase 0 (getX s 2)))
  have hfA : rvC.frameAt s 0 = (work.base + work.len) / 8 * 8 - 8 := hfb
  let R : List Region := [⟨input.base, x.length⟩, ⟨output.base, output.len⟩]
  have hL : rvC.PLay entry (rvC.codeC (rvC.compP P [0, 3] [] res main)).length R [] work.base
      (rvC.frameAt s 0 + 8) := by
    have hcl : (rvC.codeC (rvC.compP P [0, 3] [] res main)).length = (callsCode1 P res main).length := rfl
    rw [hfA, hcl]
    refine ⟨fun r hr => ?_, fun r hr => (nomatch hr), ?_, List.Pairwise.nil, fun r _ w hw => (nomatch hw),
      fun w hw => (nomatch hw), ?_, fun r hr => ?_, fun r hr => ?_, fun r hr q h1 h2 _ _ => ?_,
      fun w hw => (nomatch hw), fun q h1 h2 _ _ => ?_⟩
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (show 0x80000000 ≤ _ ∧ _ ≤ 0x100000000; dsimp only; omega)
    · simp only [R, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
        and_true, false_implies, implies_true]
      unfold Mach.disjoint; dsimp only; omega
    · show 0x80000000 ≤ _ ∧ _ ≤ 0x100000000; omega
    · simp only [R, List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold Mach.disjoint; dsimp only; omega)
    · simp only [R, List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> (unfold Mach.disjoint; dsimp only; omega)
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      show 0x80000000 ≤ q ∧ q + 1 ≤ 0x100000000
      rcases hr with rfl | rfl <;> (dsimp only at h1 h2; omega)
    · show 0x80000000 ≤ q ∧ q + 1 ≤ 0x100000000; omega
  have hheap : rvC.HeapB [0, 3] [] R [] ⟨envOf s, [x.map (·.toBitVec), out0], []⟩ s := by
    refine ⟨rfl, rfl, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, rfl, rfl, fun b hb => (nomatch hb),
      fun b hb => (nomatch hb), fun b hb => nomatch hb⟩
    · obtain _ | _ | b := b
      · simpa [envOf] using getX_of (h.x10.symm.trans h10) rfl
      · simpa [envOf] using getX_of (h.x13.symm.trans h13) rfl
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega)
    · obtain _ | _ | b := b
      · simp [R]
      · simpa [R] using hout0l
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega)
    · obtain _ | _ | b := b
      · show bytes (rv.mem s) input.base x.length = _
        exact (bytes_eq s _ _).trans (by simpa [List.map_map, Function.comp_def] using hx)
      · show bytes (rv.mem s) output.base output.len = _
        exact (bytes_eq s _ _).trans (by simpa using ho)
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega)
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  refine runsTo_mono (rvC.compP_ok hexec ⟨h, hpc, codeAt_of_codeBytes hok hcode, hok⟩ hwf.1 hwf.2
    (by intro x hx; simp at hx; omega) (by intro x hx; simp at hx)
    hen (by rw [hfA]; omega) hL (fun i => by
      show getX s (phys (avar i)) = _; rw [phys_avar]; simp [envOf]) hheap
    (by show (getX s 1).toNat % 2 = 0; rw [hra']; omega)) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  have e0 := p3.rbytes 0 (by simp [R]); have e1 := p3.rbytes 1 (by simp [R])
  simp only [hh] at e0 e1
  have e0' : bytesAt s' input.base x.length = (x.map (·.toBitVec)).map some := by
    have := (bytes_eq s' _ _).symm.trans e0; simpa using this
  have e1' : bytesAt s' output.base output.len = out'.map some := by
    have := (bytes_eq s' _ _).symm.trans e1; simpa using this
  refine ⟨by rw [← hra']; exact p1, ?_, ?_, abi_of_keep h p5 p6, p5, fun hr => ?_⟩
  · rw [← bytesAt_take' s' output.base hol', e1', ← List.map_take, htk]; simp [List.map_map, y]
  · intro q hq
    have a2 := hq ⟨output.base, y.length⟩ (by simp); have a3 := hq work (by simp)
    dsimp only at a2
    by_cases hqi : input.base ≤ q ∧ q < input.base + input.len
    · have e0x : bytesAt s' input.base x.length = bytesAt s input.base x.length := by
        rw [e0', hx, List.map_map]; rfl
      have := congrArg (·[q - input.base]?) e0x
      simp only [bytesAt, List.getElem?_map, List.getElem?_range (show q - input.base < x.length by omega),
        Option.map_some, Option.some.injEq] at this
      rwa [Nat.add_sub_cancel' hqi.1] at this
    by_cases hqo : output.base ≤ q ∧ q < output.base + output.len
    · have e1x : (bytesAt s' output.base output.len)[q - output.base]? =
          (bytesAt s output.base output.len)[q - output.base]? := by
        rw [e1', ho, List.getElem?_map, List.getElem?_map]
        have := congrArg (·[q - output.base - y.length]?) hdr
        simp only [List.getElem?_drop] at this
        rw [show y.length + (q - output.base - y.length) = q - output.base by omega] at this
        rw [this]
      simp only [bytesAt, List.getElem?_map, List.getElem?_range (show q - output.base < output.len by omega),
        Option.map_some, Option.some.injEq] at e1x
      rwa [Nat.add_sub_cancel' hqo.1] at e1x
    · apply p4 q
      intro r hr
      rw [hfA] at hr
      simp only [R, List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega
  · have := p2 ⟨1, by decide⟩
    rw [show rvC.get s' (avar ⟨1, by decide⟩) = getX s' 11 from rfl, hrl hr] at this
    rw [p5.x11, this]

end Proven.Mach.Riscv
