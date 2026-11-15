/- The branchy merge sort `msortProgB` (`Riscv/Examples/MsortB.lean`) through the optimising back end:
`msortCodeO2 = compileBFO 7 [0, 2, 3] msortProgB` and `msortCodeO2_implements1` (the statement of
`msortCode_implements1O`, same `space n = n + 71`). The proofs are those of `msortCodeO` with the program swapped. -/
import Riscv.Examples.Implements1Opt
import Riscv.Examples.MsortB

set_option linter.unusedVariables false

namespace Proven

set_option maxRecDepth 100000 in
theorem msortProgB_wf : msortProgB.wf 7 [0, 2, 3] := by
  simp [msortProgB, mainBodyB, passB, runB, mergeB, mergeA, tailL, tailR, condA, lt98, one, minE, addE, ltE,
    BStmt.wf, BExp.depth, BExp.vlt, compileB, genB, addrB, opCode, selCode, genConst]

/-- the branchy merge sort, optimised: 7 spill slots, blocks input / scratch / output with bases in `a0`, `a2`, `a3` -/
def msortCodeO2 : List (BitVec 32) := compileBFO 7 [0, 2, 3] msortProgB

/-- `msortCodeO_ok_m` with the full register frame `keep` -/
theorem msortCodeO2_ok_k {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc msortCodeO2) (hok : codeOK pc msortCodeO2.length) (hra : (getX s 1).toNat % 2 = 0)
    {xs scr out : List (BitVec 8)} {inb scb outb : Nat}
    (hR : RegOK [⟨inb, xs.length⟩, ⟨scb, xs.length⟩, ⟨outb, xs.length⟩])
    (hf : FrOK 7 (frameBase 7 (getX s 2)))
    (hfd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨scb, xs.length⟩, ⟨outb, xs.length⟩],
      disjoint ⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ r)
    (hcd : ∀ r ∈ [(⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ : Region), ⟨inb, xs.length⟩, ⟨scb, xs.length⟩,
      ⟨outb, xs.length⟩], disjoint ⟨pc.toNat, 4 * msortCodeO2.length⟩ r)
    (h0 : getX s 10 = BitVec.ofNat 64 inb) (h1 : getX s 11 = BitVec.ofNat 64 xs.length)
    (h2 : getX s 12 = BitVec.ofNat 64 scb) (h3 : getX s 13 = BitVec.ofNat 64 outb)
    (hx : bytesAt s inb xs.length = xs.map some) (hs : bytesAt s scb xs.length = scr.map some)
    (ho : bytesAt s outb xs.length = out.map some) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      bytesAt s' outb xs.length = (xs.mergeSort leB).map some ∧ bytesAt s' inb xs.length = xs.map some ∧
      unchangedOutside s s' [⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩, ⟨scb, xs.length⟩, ⟨outb, xs.length⟩] ∧
      Cfg s' ∧ Mach.Riscv.rv.keep s s' := by
  have hn : xs.length < 2 ^ 32 := by
    have := hR.1 _ (List.mem_cons_self ..); unfold Region.inRAM at this; dsimp only at this; omega
  have hsl : scr.length = xs.length := by simpa [bytesAt] using (congrArg List.length hs).symm
  have hol : out.length = xs.length := by simpa [bytesAt] using (congrArg List.length ho).symm
  obtain ⟨σ', hex, scr', hh⟩ := msortProgB_mergeSort xs scr out ⟨envOf s, [xs, scr, out]⟩ rfl
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
  refine runsTo_mono (compileBFO_okK 7 [0, 2, 3] (by decide) msortProgB_wf hR hex h hpc hc hok hf hfd hcd
    (fun i => by simp [envOf]) (fun j hj => by simp [envOf]; omega) hheap hra) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  have e0 := p3.bytes 0 (by simp); have e2 := p3.bytes 2 (by simp)
  simp only [hh] at e0 e2
  have e0' : bytesAt s' inb xs.length = xs.map some := by simpa using e0
  have hu : unchangedOutside s s' ((⟨inb, xs.length⟩ : Region) :: [⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩,
      ⟨scb, xs.length⟩, ⟨outb, xs.length⟩]) := fun a ha => p4 a fun r hr => ha r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with e | e | e | e <;> simp [e])
  exact ⟨p1, by simpa using e2, e0', unchanged_drop hu (by rw [e0', hx]), p5, p6⟩

/-- **Merge sort, branchy merge** (`msortProgB` through the optimising back end) in `Implements1` form, the
statement of `msortCode_implements1O` for `msortCodeO2`: `space n = n + 71` (an `n`-byte scratch block at the bottom of the
work block, the 64-byte frame below `sp` at its top, up to 7 bytes of alignment) -/
theorem msortCodeO2_implements1 : Implements1Raw msortCodeO2 (fun x => x.mergeSort leU) (fun n => n + 71) := by
  intro a s entry ra input output work
  dsimp only [encRaw]
  intro hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx hil hol hws hwal hram hdis hmapO hmapW
  simp only [List.length_mergeSort] at hol ⊢
  have hin : ∀ r ∈ [input, output, work, (⟨entry.toNat, 4 * msortCodeO2.length⟩ : Region)], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hdis
  obtain ⟨ri, ro, rw', rc⟩ := hin
  unfold Region.inRAM at ri ro rw' rc
  unfold disjoint at d12 d13 d14 d23 d24 d34
  dsimp only at d12 d13 d14 d23 d24 d34 ri ro rw' rc
  have hxl : (a.map (·.toBitVec)).length = a.length := by simp
  have hil' : input.len = a.length := hil
  have hol' : a.length ≤ output.len := hol
  have hws' : a.length + 71 ≤ work.len := hws
  have hsp : getX s 2 = BitVec.ofNat 64 (work.base + work.len) := getX_of (h.x2.symm.trans h2) rfl
  have hspn : (getX s 2).toNat = work.base + work.len := by rw [hsp]; exact toNat_ofNat' (by omega)
  have hfb : frameBase 7 (getX s 2) = (work.base + work.len) / 8 * 8 - 64 := by unfold frameBase; rw [hspn]
  have hf : FrOK 7 (frameBase 7 (getX s 2)) := ⟨by rw [hfb]; omega, by rw [hfb]; omega, by rw [hfb]; omega, by decide⟩
  have hR : RegOK [⟨input.base, (a.map (·.toBitVec)).length⟩, ⟨work.base, (a.map (·.toBitVec)).length⟩,
      ⟨output.base, (a.map (·.toBitVec)).length⟩] := by
    rw [hxl]
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> (unfold Region.inRAM; dsimp only; omega)
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        List.Pairwise.nil, and_true, false_implies, implies_true]
      unfold disjoint; dsimp only; omega
  have hok : codeOK entry msortCodeO2.length := ⟨hal, rc.1, rc.2⟩
  have hfd : ∀ r ∈ [(⟨input.base, (a.map (·.toBitVec)).length⟩ : Region), ⟨work.base, (a.map (·.toBitVec)).length⟩,
      ⟨output.base, (a.map (·.toBitVec)).length⟩], disjoint ⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ r := by
    rw [hxl, hfb]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hcd : ∀ r ∈ [(⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ : Region), ⟨input.base, (a.map (·.toBitVec)).length⟩,
      ⟨work.base, (a.map (·.toBitVec)).length⟩, ⟨output.base, (a.map (·.toBitVec)).length⟩],
      disjoint ⟨entry.toNat, 4 * msortCodeO2.length⟩ r := by
    rw [hxl, hfb]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  refine runsTo_mono (msortCodeO2_ok_k h hpc (codeAt_of_codeBytes hok hcode) hok (by rw [hra']; omega) hR hf hfd hcd
    (getX_of (h.x10.symm.trans h10) rfl) (by rw [getX_of (h.x11.symm.trans h11) rfl, hxl])
    (getX_of (h.x12.symm.trans h12) rfl) (getX_of (h.x13.symm.trans h13) rfl)
    (by simpa [List.map_map, Function.comp_def] using hx)
    (bytesAt_hosted (fun i hi => hmapW i (by rw [hxl] at hi; omega)))
    (bytesAt_hosted (fun i hi => hmapO i (by rw [hxl] at hi; omega)))) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  refine ⟨by rw [p1, hra'], ?_, ?_, Mach.Riscv.abi_of_keep h p5 p6, p5, fun h => nomatch h⟩
  · rw [← hxl, p2, ← mergeSort_toBitVec]; simp [List.map_map]
  · intro q hq
    apply p4 q
    intro r hr
    have a2 := hq ⟨output.base, a.length⟩ (by simp); have a3 := hq work (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hxl, hfb] at hr
    rcases hr with rfl | rfl | rfl <;> (dsimp only; omega)

end Proven
