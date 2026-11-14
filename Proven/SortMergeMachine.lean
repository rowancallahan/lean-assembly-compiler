/- The bottom-up merge sort (`Proven/SortMergeSrc.lean`) on the Sail model: `msortCode_ok` (region form)
and `msortCode_implements` (the `Implements` form of `Proven/Spec.lean` with stack frame `stackLen = 71` and
two hosting hypotheses: the output and scratch bytes are present in the memory map). -/
import Proven.Arr2F
import Proven.SortMergeSrc
import Proven.SortMachine
import Proven.ArrExamples

set_option linter.unusedVariables false

namespace Proven

set_option maxRecDepth 100000 in
theorem msortProg_wf : msortProg.wf 7 [0, 2, 3] := by
  simp [msortProg, mainBody, passM, runM, innerM, takeE, minE, addE, ltE, BStmt.wf, BExp.depth, BExp.vlt, compileB,
    genB, addrB, opCode, selCode, genConst]

/-- the merge sort: 7 spill slots, blocks input / scratch / output with bases in `a0`, `a2`, `a3` -/
def msortCode : List (BitVec 32) := compileBF 7 [0, 2, 3] msortProg

/-- the initial source state: registers as in `s`, slots `0` -/
def envOf (s : St) : BEnv := fun i => if h : i < 8 then getX s (A8 ⟨i, h⟩) else 0

/-- **Merge sort** (memory/region form): input `xs` at `a0` (length in `a1`), scratch and output blocks of
`|xs|` bytes at `a2`, `a3` (any contents), the 64-byte frame below `sp` in RAM and disjoint from the blocks and
the code: returns to `ra` with the output block holding `xs.mergeSort leB`, the input unchanged, memory
outside the frame, the scratch and the output unchanged, callee-saved registers, `gp` and `Cfg` kept. -/
theorem msortCode_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc msortCode) (hok : codeOK pc msortCode.length) (hra : (getX s 1).toNat % 2 = 0)
    {xs scr out : List (BitVec 8)} {inb scb outb : Nat}
    (hR : RegOK [⟨inb, xs.length⟩, ⟨scb, xs.length⟩, ⟨outb, xs.length⟩])
    (hf : FrOK 7 (frameBase 7 (getX s 2)))
    (hfd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨scb, xs.length⟩, ⟨outb, xs.length⟩],
      disjoint ⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ r)
    (hcd : ∀ r ∈ [(⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ : Region), ⟨inb, xs.length⟩, ⟨scb, xs.length⟩,
      ⟨outb, xs.length⟩], disjoint ⟨pc.toNat, 4 * msortCode.length⟩ r)
    (h0 : getX s 10 = BitVec.ofNat 64 inb) (h1 : getX s 11 = BitVec.ofNat 64 xs.length)
    (h2 : getX s 12 = BitVec.ofNat 64 scb) (h3 : getX s 13 = BitVec.ofNat 64 outb)
    (hx : bytesAt s inb xs.length = xs.map some) (hs : bytesAt s scb xs.length = scr.map some)
    (ho : bytesAt s outb xs.length = out.map some) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      bytesAt s' outb xs.length = (xs.mergeSort leB).map some ∧ bytesAt s' inb xs.length = xs.map some ∧
      unchangedOutside s s' [⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩, ⟨scb, xs.length⟩, ⟨outb, xs.length⟩] ∧
      Cfg s' ∧ calleeSavedKept s s' ∧ getX s' 3 = getX s 3 := by
  have hn : xs.length < 2 ^ 32 := by
    have := hR.1 _ (List.mem_cons_self ..); unfold Region.inRAM at this; dsimp only at this; omega
  have hsl : scr.length = xs.length := by simpa [bytesAt] using (congrArg List.length hs).symm
  have hol : out.length = xs.length := by simpa [bytesAt] using (congrArg List.length ho).symm
  obtain ⟨σ', hex, scr', hh⟩ := msortProg_mergeSort xs scr out ⟨envOf s, [xs, scr, out]⟩ rfl
    (by simpa [envOf] using h1) hn hsl hol
  have hheap : HeapRel [0, 2, 3] [⟨inb, xs.length⟩, ⟨scb, xs.length⟩, ⟨outb, xs.length⟩]
      ⟨envOf s, [xs, scr, out]⟩ s :=
    ⟨rfl, rfl, fun b hb => by
        obtain _ | _ | _ | b := b
        · simpa [envOf] using h0
        · simpa [envOf] using h2
        · simpa [envOf] using h3
        · simp at hb; omega,
      fun b hb => by
        obtain _ | _ | _ | b := b
        · rfl
        · simpa using hsl
        · simpa using hol
        · simp at hb; omega,
      fun b hb => by
        obtain _ | _ | _ | b := b
        · simpa using hx
        · simpa using hs
        · simpa using ho
        · simp at hb; omega⟩
  refine runsTo_mono (compileBF_ok 7 [0, 2, 3] (by decide) msortProg_wf hR hex h hpc hc hok hf hfd hcd
    (fun i => by simp [envOf]) (fun j hj => by simp [envOf]; omega) hheap hra) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6, p7⟩
  have e0 := p3.bytes 0 (by simp); have e2 := p3.bytes 2 (by simp)
  simp only [hh] at e0 e2
  have e0' : bytesAt s' inb xs.length = xs.map some := by simpa using e0
  have hu : unchangedOutside s s' ((⟨inb, xs.length⟩ : Region) :: [⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩,
      ⟨scb, xs.length⟩, ⟨outb, xs.length⟩]) := fun a ha => p4 a fun r hr => ha r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with e | e | e | e <;> simp [e])
  exact ⟨p1, by simpa using e2, e0', unchanged_drop hu (by rw [e0', hx]), p5, p6, p7⟩

/-! ## `Implements` form -/

/-- `Implements` (`Proven/Spec.lean`) plus two hosting hypotheses: the output bytes
`[output.base, output.base + |f x|)` and the scratch bytes `[scratch.base, scratch.base + |x|)` are present in the
memory map (`s.mem[_]?` is `some _`). -/
def ImplementsMapped2 (code : List (BitVec 32)) (f : List UInt8 → List UInt8)
    (maxLen : Nat := 2 ^ 20) (stackLen : Nat := 0) : Prop :=
  ∀ (x : List UInt8) (s : St) (entry ra : BitVec 64) (input scratch output stack : Region),
    let codeR : Region := ⟨entry.toNat, 4 * code.length⟩
    x.length ≤ maxLen → Cfg s → s.regs.get? .PC = some entry → entry.toNat % 4 = 0 →
    bytesAt s entry.toNat (4 * code.length) = codeBytes code →
    s.regs.get? .x10 = some (BitVec.ofNat 64 input.base) →
    s.regs.get? .x11 = some (BitVec.ofNat 64 x.length) →
    s.regs.get? .x12 = some (BitVec.ofNat 64 scratch.base) →
    s.regs.get? .x13 = some (BitVec.ofNat 64 output.base) →
    s.regs.get? .x2 = some (BitVec.ofNat 64 (stack.base + stack.len)) →
    s.regs.get? .x1 = some ra → ra.toNat % 4 = 0 → disjoint ⟨ra.toNat, 4⟩ codeR →
    bytesAt s input.base x.length = x.map (some ·.toBitVec) →
    input.len = x.length → x.length ≤ scratch.len → (f x).length ≤ output.len →
    stackLen ≤ stack.len → (∀ r ∈ [input, scratch, output, stack, codeR], r.inRAM) →
    [input, scratch, output, stack, codeR].Pairwise disjoint →
    (∀ i < (f x).length, (s.mem[output.base + i]?).isSome) →
    (∀ i < x.length, (s.mem[scratch.base + i]?).isSome) →
    runsTo s fun s' => s'.regs.get? .PC = some ra ∧
      bytesAt s' output.base (f x).length = (f x).map (some ·.toBitVec) ∧
      unchangedOutside s s' [input, scratch, output, stack] ∧ calleeSavedKept s s' ∧ Cfg s'

/-- present bytes are the `some`s of their values -/
theorem bytesAt_hosted {s : St} {a n : Nat} (h : ∀ i < n, (s.mem[a + i]?).isSome) :
    bytesAt s a n = ((bytesAt s a n).map (·.getD 0)).map some := by
  rw [List.map_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [bytesAt, List.getElem_map, List.getElem_range, Function.comp]
  have := h i (by simpa [bytesAt] using h1)
  cases e : s.mem[a + i]? with
  | none => rw [e] at this; simp at this
  | some b => rfl

/-- **The merge sort implements `List.mergeSort`** in the sense of `ImplementsMapped2`, with a stack frame of
71 bytes (64 bytes for `gp` and 7 slots, plus up to 7 bytes of alignment). -/
theorem msortCode_implements : ImplementsMapped2 msortCode (fun x => x.mergeSort leU) (stackLen := 71) := by
  intro x s entry ra input scratch output stack codeR hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx
    hil hsl hol hstk hram hdis hmap hmapS
  simp only [List.length_mergeSort] at hol hmap ⊢
  have hin : ∀ r ∈ [input, scratch, output, stack, codeR], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14, d15⟩, ⟨d23, d24, d25⟩, ⟨d34, d35⟩, d45⟩ := hdis
  obtain ⟨ri, rs, ro, rst, rc⟩ := hin
  unfold Region.inRAM at ri rs ro rst rc
  unfold disjoint at d12 d13 d14 d15 d23 d24 d25 d34 d35 d45
  simp only [codeR] at d15 d25 d35 d45 rc
  have hxl : (x.map (·.toBitVec)).length = x.length := by simp
  have hol' : x.length ≤ output.len := hol
  have hil' : input.len = x.length := hil
  have hsp : getX s 2 = BitVec.ofNat 64 (stack.base + stack.len) := getX_of (h.x2.symm.trans h2) rfl
  have hspn : (getX s 2).toNat = stack.base + stack.len := by rw [hsp]; exact toNat_ofNat' (by omega)
  have hfb : frameBase 7 (getX s 2) = (stack.base + stack.len) / 8 * 8 - 64 := by unfold frameBase; rw [hspn]
  have hf : FrOK 7 (frameBase 7 (getX s 2)) := ⟨by rw [hfb]; omega, by rw [hfb]; omega, by rw [hfb]; omega, by decide⟩
  have hR : RegOK [⟨input.base, (x.map (·.toBitVec)).length⟩, ⟨scratch.base, (x.map (·.toBitVec)).length⟩,
      ⟨output.base, (x.map (·.toBitVec)).length⟩] := by
    rw [hxl]
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> (unfold Region.inRAM; dsimp only; omega)
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        List.Pairwise.nil, and_true, false_implies, implies_true]
      unfold disjoint; dsimp only; omega
  have hok : codeOK entry msortCode.length := ⟨hal, rc.1, rc.2⟩
  have hfd : ∀ r ∈ [(⟨input.base, (x.map (·.toBitVec)).length⟩ : Region), ⟨scratch.base, (x.map (·.toBitVec)).length⟩,
      ⟨output.base, (x.map (·.toBitVec)).length⟩], disjoint ⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ r := by
    rw [hxl, hfb]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hcd : ∀ r ∈ [(⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ : Region), ⟨input.base, (x.map (·.toBitVec)).length⟩,
      ⟨scratch.base, (x.map (·.toBitVec)).length⟩, ⟨output.base, (x.map (·.toBitVec)).length⟩],
      disjoint ⟨entry.toNat, 4 * msortCode.length⟩ r := by
    rw [hxl, hfb]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  refine runsTo_mono (msortCode_ok h hpc (codeAt_of_codeBytes hok hcode) hok (by rw [hra']; omega) hR hf hfd hcd
    (getX_of (h.x10.symm.trans h10) rfl) (by rw [getX_of (h.x11.symm.trans h11) rfl, hxl])
    (getX_of (h.x12.symm.trans h12) rfl) (getX_of (h.x13.symm.trans h13) rfl)
    (by simpa [List.map_map, Function.comp_def] using hx) (bytesAt_hosted (by rw [hxl]; exact hmapS))
    (bytesAt_hosted (by rw [hxl]; exact hmap))) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6, p7⟩
  refine ⟨by rw [p1, hra'], ?_, ?_, p6, p5⟩
  · rw [← hxl, p2, ← mergeSort_toBitVec]; simp [List.map_map]
  · intro a ha
    apply p4 a
    intro r hr
    have a1 := ha input (by simp); have a2 := ha scratch (by simp); have a3 := ha output (by simp)
    have a4 := ha stack (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hxl, hfb] at hr
    rcases hr with rfl | rfl | rfl <;> (dsimp only; omega)

end Proven
