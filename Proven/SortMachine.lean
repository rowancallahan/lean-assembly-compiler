/- The insertion sort (`Proven/SortIns.lean`) on the Sail model: `sortCode_ok` (memory/region form) and
`sortCode_implements` (the `Implements` form of `Proven/Spec.lean`, with one extra hosting hypothesis:
the output bytes are present in the memory map). -/
import Proven.SortIns

set_option linter.unusedVariables false

namespace Proven

theorem sortProg_wf : sortProg.wf [0, 3] := by
  simp [sortProg, insProg, outerBody, innerBody, mapProg, idxE, cE, valE, AStmt.wf, AExp.depth, compileA, gen8,
    addrE, opCode, selCode, genConst]

def sortCode : List (BitVec 32) := compileAF [0, 3] sortProg

/-- **Insertion sort** (memory/region form): input `xs` at `a0` (length in `a1`), an output block of
`|xs|` bytes at `a3` (any contents): returns to `ra` with the output block holding
`xs.mergeSort` (computed by insertion sort), the input unchanged, all memory outside the output block
unchanged, callee-saved registers and `Cfg` kept. -/
theorem sortCode_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc sortCode) (hok : codeOK pc sortCode.length) (hra : (getX s 1).toNat % 2 = 0)
    {xs out : List (BitVec 8)} {inb outb : Nat} (hR : RegOK [⟨inb, xs.length⟩, ⟨outb, xs.length⟩])
    (hcd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨outb, xs.length⟩], disjoint ⟨pc.toNat, 4 * sortCode.length⟩ r)
    (h0 : getX s 10 = BitVec.ofNat 64 inb) (h1 : getX s 11 = BitVec.ofNat 64 xs.length)
    (h3 : getX s 13 = BitVec.ofNat 64 outb)
    (hx : bytesAt s inb xs.length = xs.map some) (ho : bytesAt s outb xs.length = out.map some) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      bytesAt s' outb xs.length = (xs.mergeSort leB).map some ∧
      bytesAt s' inb xs.length = xs.map some ∧ unchangedOutside s s' [⟨outb, xs.length⟩] ∧
      Cfg s' ∧ calleeSavedKept s s' := by
  have hn : xs.length < 2 ^ 63 := by
    have := hR.1 _ (List.mem_cons_self ..); unfold Region.inRAM at this; dsimp only at this; omega
  have hout : out.length = xs.length := by simpa [bytesAt] using (congrArg List.length ho).symm
  obtain ⟨σ', hex, hh⟩ := sortProg_mergeSort xs out ⟨fun i => getX s (A8 i), [xs, out]⟩ rfl h1 hn hout
  have hrel : Rel [0, 3] [⟨inb, xs.length⟩, ⟨outb, xs.length⟩] ⟨fun i => getX s (A8 i), [xs, out]⟩ s :=
    ⟨fun _ => rfl, rfl, rfl, fun b hb => by obtain _ | _ | b := b; exact h0; exact h3; simp at hb; omega,
      fun b hb => by obtain _ | _ | b := b; rfl; exact hout; simp at hb; omega,
      fun b hb => by obtain _ | _ | b := b; exact hx; exact ho; simp at hb; omega⟩
  refine runsTo_mono (compileAF_ok [0, 3] sortProg_wf hR hex h hpc hc hok hcd hrel hra) ?_
  rintro s' ⟨p1, p2, p3, p4, p5⟩
  have e0 := p2.bytes 0 (by simp); have e1 := p2.bytes 1 (by simp)
  simp only [hh] at e0 e1
  exact ⟨p1, by simpa using e1, by simpa using e0, unchanged_drop p3 (by simpa [hx] using e0), p4, p5⟩

/-! ## `Implements` form -/

theorem bytesAt_append (s : St) (a m n : Nat) : bytesAt s a (m + n) = bytesAt s a m ++ bytesAt s (a + m) n := by
  simp [bytesAt, List.range_add, List.map_append, Nat.add_assoc]

theorem codeAt_of_codeBytes {s : St} : ∀ {code : List (BitVec 32)} {pc : BitVec 64}, codeOK pc code.length →
    bytesAt s pc.toNat (4 * code.length) = codeBytes code → codeAt s pc code
  | [], _, _, _ => fun i hi => absurd hi (by simp)
  | w :: ws, pc, hok, hb => by
    rw [show 4 * (w :: ws).length = 4 + 4 * ws.length by simp; omega, bytesAt_append] at hb
    simp only [codeBytes, List.flatMap_cons] at hb
    obtain ⟨hb1, hb2⟩ := List.append_inj hb (by simp [bytesAt])
    have g := fun i (hi : i < 4) => mem_of_bytesAt hb1 (i := i) (by simpa using hi)
    have hi : instrAt s pc w :=
      ⟨by simpa using g 0 (by omega), by simpa using g 1 (by omega), by simpa using g 2 (by omega),
        by simpa using g 3 (by omega)⟩
    have hok' := (codeOK_append (a := 1) (b := ws.length) (by simpa [Nat.add_comm] using hok)).2
    have e := pc_toNat hok (a := 1) (by simp)
    have ih := codeAt_of_codeBytes hok' (by rw [e]; simpa using hb2)
    exact (codeAt_append (l₁ := [w])).2 ⟨fun k hk => by simp at hk; subst hk; simpa using hi, ih⟩

/-- `Implements` (`Proven/Spec.lean`) plus one hosting hypothesis: the output bytes are present in the
memory map (`s.mem[output.base + i]?` is `some _` for `i < (f x).length`). -/
def ImplementsMapped (code : List (BitVec 32)) (f : List UInt8 → List UInt8)
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
    runsTo s fun s' => s'.regs.get? .PC = some ra ∧
      bytesAt s' output.base (f x).length = (f x).map (some ·.toBitVec) ∧
      unchangedOutside s s' [input, scratch, output, stack] ∧ calleeSavedKept s s' ∧ Cfg s'

def leU (a b : UInt8) : Bool := decide (a ≤ b)

theorem mergeSort_toBitVec (x : List UInt8) : (x.mergeSort leU).map (·.toBitVec) = (x.map (·.toBitVec)).mergeSort leB := by
  refine sorted_perm_eq ?_ (sorted_mergeSort _) (((List.mergeSort_perm x leU).map _).trans
    (List.mergeSort_perm _ leB).symm)
  have := List.pairwise_mergeSort (le := leU)
    (fun a b c h1 h2 => by simp only [leU, decide_eq_true_eq] at *; exact UInt8.le_trans h1 h2)
    (fun a b => by simp only [leU, Bool.or_eq_true, decide_eq_true_eq]; exact UInt8.le_total a b) x
  rw [Sorted, List.pairwise_map]
  exact this.imp fun h => by simpa [leU, UInt8.le_iff_toBitVec_le] using h

theorem getX_of {s : St} {r : Fin 32} {v w : BitVec 64} (h : some w = some v) (e : getX s r = w) : getX s r = v := by
  rw [e]; exact Option.some.inj h

/-- **Insertion sort implements `List.mergeSort`** in the sense of `ImplementsMapped`. -/
theorem sortCode_implements : ImplementsMapped sortCode (fun x => x.mergeSort leU) := by
  intro x s entry ra input scratch output stack codeR hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx
    hil hsl hol hstk hram hdis hmap
  simp only [List.length_mergeSort] at hol hmap ⊢
  have hin : ∀ r ∈ [input, scratch, output, stack, codeR], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14, d15⟩, ⟨d23, d24, d25⟩, ⟨d34, d35⟩, d45⟩ := hdis
  obtain ⟨ri, rs, ro, rst, rc⟩ := hin
  unfold Region.inRAM at ri ro rc
  unfold disjoint at d13 d15 d35
  simp only [codeR] at d15 d35
  have hxl : (x.map (·.toBitVec)).length = x.length := by simp
  have hol' : x.length ≤ output.len := hol
  have hil' : input.len = x.length := hil
  have hR : RegOK [⟨input.base, (x.map (·.toBitVec)).length⟩, ⟨output.base, (x.map (·.toBitVec)).length⟩] := by
    rw [hxl]
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold Region.inRAM; dsimp only; (try simp only [List.length_map]); omega)
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
        and_true, false_implies, implies_true]
      unfold disjoint; dsimp only; (try simp only [List.length_map]); omega
  have hok : codeOK entry sortCode.length := ⟨hal, rc.1, rc.2⟩
  have hcd : ∀ r ∈ [(⟨input.base, (x.map (·.toBitVec)).length⟩ : Region), ⟨output.base, (x.map (·.toBitVec)).length⟩],
      disjoint ⟨entry.toNat, 4 * sortCode.length⟩ r := by
    rw [hxl]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold disjoint; dsimp only; (try simp only [List.length_map]); omega)
  -- the output's initial bytes
  have ho : bytesAt s output.base (x.map (·.toBitVec)).length =
      ((bytesAt s output.base (x.map (·.toBitVec)).length).map (·.getD 0)).map some := by
    rw [List.map_map]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [bytesAt, List.getElem_map, List.getElem_range, Function.comp]
    have := hmap i (by simpa [bytesAt, hxl] using h1)
    cases e : s.mem[output.base + i]? with
    | none => rw [e] at this; simp at this
    | some b => rfl
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  refine runsTo_mono (sortCode_ok h hpc (codeAt_of_codeBytes hok hcode) hok
    (by rw [hra']; omega) hR hcd (getX_of (h.x10.symm.trans h10) rfl) (by rw [getX_of (h.x11.symm.trans h11) rfl, hxl])
    (getX_of (h.x13.symm.trans h13) rfl) (by simpa [List.map_map, Function.comp_def] using hx) ho) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  refine ⟨by rw [p1, hra'], ?_, ?_, p6, p5⟩
  · rw [← hxl, p2, ← mergeSort_toBitVec]; simp [List.map_map]
  · intro a ha
    apply p4 a
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    have := ha output (by simp)
    dsimp only; omega

end Proven
