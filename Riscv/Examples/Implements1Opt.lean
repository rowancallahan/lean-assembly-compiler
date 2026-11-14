/- Optimised versions of the direct `Implements1` examples: the same programs and source-level proofs,
compiled by the optimising back end (`compBFO`, `compileAFO`, `compileBFO`; `Riscv/Back/Implements1Opt.lean`),
each with its `Implements1` theorem re-proved for the optimised words (statements: those of
`Riscv/Examples/Implements1Ex.lean` and `Riscv/Examples/Crc.lean` with the code names suffixed `O`).
A separate module: `Riscv.Back.OptArr` imports `Riscv.Back.Arr`, which imports the direct sorts. -/
import Riscv.Back.Implements1Opt
import Riscv.Examples.Crc

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv

open Proven (ult_ne toNat_inc toNat_ofNat_lt map_take_set setWidth_setWidth8)

def takeCodeO (k : Nat) : List (BitVec 32) := compBFO 0 [0, 3] [2] (takeP k)
def incCodeO : List (BitVec 32) := compBFO 0 [0, 3] [2] (mapK (.var 1) (.bin .add (.var 6) (.const 1)))
def sumCodeO : List (BitVec 32) := compBFO 0 [0, 3] [2] sumP

/-- **`List.take k`** in `Implements1` form: 15 bytes of work space (the frame cell saving `gp`, plus
alignment); a variable-length result, so its length is returned in `a1` (`retLen = true`). -/
theorem take_implements1O (k : Nat) (hk : k < 2 ^ 64) :
    Implements1Raw (takeCodeO k) (fun xs => xs.take k) (fun _ => 15) (retLen := true) := by
  refine implements1_of_execO encRaw encRaw _ 0 (by omega) _ (take_wf k) (fun _ => 0) (fun _ => 15)
    (fun n => by dsimp only; omega) _ true ?_
  intro a out tbl env h1 h8 hmax hlt hout hol htl
  simp only [encRaw] at h1 hlt hout ⊢
  have hK : (Mach.BExp.denote env (.const (BitVec.ofNat 64 k))).toNat = k := by
    simp [Mach.BExp.denote]; omega
  obtain ⟨σ', hex, hh, h4, h1'⟩ := mapK_exec (.const (BitVec.ofNat 64 k)) (.var 6) id
    (fun env x he => by simp [Mach.BExp.denote, he]) ⟨env, [a.map (·.toBitVec), out], [tbl]⟩
    (a.map (·.toBitVec)) out rfl (by simpa using h1) (by simp at hlt ⊢; omega)
    (by rw [hK]; simp at hout ⊢; omega)
  rw [hK] at hh h4
  simp only [List.length_map] at hh h4
  refine ⟨_, _, .seq hex (BExec.assign' (v := 1) (e := .var 4) rfl), hh, ?_, ?_, fun _ => ?_⟩
  · simp only [List.map_id, List.length_take]
    rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp), List.map_take]
  · simp only [List.map_id, List.length_take]
    exact drop_tail _ (by simp)
  · show Mach.BEnv.set σ'.env 1 ((Mach.BExp.var 4).denote σ'.env) 1 = _
    simp only [Mach.BEnv.set, if_pos, Mach.BExp.denote, List.length_take]
    apply BitVec.eq_of_toNat_eq; rw [h4, BitVec.toNat_ofNat]; omega

/-- **`List.map (· + 1)`** in `Implements1` form -/
theorem inc_implements1O : Implements1Raw incCodeO (List.map (· + 1)) (fun _ => 15) := by
  refine implements1_of_execO encRaw encRaw _ 0 (by omega) _ inc_wf (fun _ => 0) (fun _ => 15)
    (fun n => by dsimp only; omega) _ false ?_
  intro a out tbl env h1 h8 hmax hlt hout hol htl
  simp only [encRaw] at h1 hlt hout ⊢
  have hK : (Mach.BExp.denote env (.var 1)).toNat = a.length := by
    simp only [Mach.BExp.denote, h1, BitVec.toNat_ofNat]; omega
  obtain ⟨σ', hex, hh, -⟩ := mapK_exec (.var 1) (.bin .add (.var 6) (.const 1)) (· + 1)
    (fun env x he => by simp only [Mach.BExp.denote, Op.eval, he]; exact Proven.setWidth_inc x)
    ⟨env, [a.map (·.toBitVec), out], [tbl]⟩ (a.map (·.toBitVec)) out rfl (by simpa using h1) (by simp; omega)
    (by rw [hK]; simp at hout ⊢; omega)
  rw [hK] at hh
  simp only [List.length_map] at hout hh
  refine ⟨σ', _, hex, hh, ?_, ?_, fun h => nomatch h⟩
  · simp only [List.length_map]
    rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp),
      List.take_of_length_le (by simp), List.map_map, List.map_map]
    apply List.map_congr_left; intro u _; simp
  · simp only [List.length_map, Nat.min_self]
    exact drop_tail _ (by simp)

/-- **The byte sum** (a 64-bit word, `enc` = 8 little-endian bytes) in `Implements1` form -/
theorem sum_implements1O : Implements1With encRaw Proven.enc sumCodeO sumBytesU (fun _ => 15) := by
  refine implements1_of_execO encRaw Proven.enc _ 0 (by omega) _ sum_wf (fun _ => 0) (fun _ => 15)
    (fun n => by dsimp only; omega) _ false ?_
  intro a out tbl env h1 h8 hmax hlt hout hol htl
  simp only [encRaw, length_enc64] at h1 hlt hout ⊢
  obtain ⟨σ', out', hex, hh, ht, hd⟩ := sumP_exec ⟨env, [a.map (·.toBitVec), out], [tbl]⟩ (a.map (·.toBitVec)) out
    rfl (by simpa using h1) (by simp; omega) hout
  exact ⟨σ', out', hex, hh, by rw [ht, enc64, sumBytesU_eq], hd, fun h => nomatch h⟩

end Proven.Mach.Riscv

namespace Proven.Crc
open Proven.Mach Proven.Mach.Riscv

def crcCodeO : List (BitVec 32) := compBFO 0 [0, 3] [2] crcP

/-- **CRC-32 on RV64**, `Implements1` form: input = the raw bytes, output = the 4 little-endian bytes of
`crc32`, work space `2048 + 15` bytes (the table, the frame cell saving `gp`, alignment). -/
theorem crc32_implements1O : Implements1With encRaw enc32 crcCodeO crc32 (fun _ => 2063) := by
  refine implements1_of_execO encRaw enc32 crc32 0 (by omega) crcP crc_wf (fun _ => 256) (fun _ => 2063)
    (fun n => by dsimp only; omega) _ false ?_
  intro a out tbl env h1 h8 hmax hlt hout hol htl
  have hl4 : (enc32 (crc32 a)).length = 4 := leN_length 4 _
  simp only [encRaw, hl4] at h1 hlt hout htl ⊢
  obtain ⟨σ', out', hex, hh, ht, hd⟩ := crcP_exec ⟨env, [a.map (·.toBitVec), out], [tbl]⟩ a out tbl rfl rfl htl
    h1 hlt hout
  exact ⟨σ', out', hex, hh, ht, hd, fun h => nomatch h⟩

end Proven.Crc

namespace Proven

def sortCodeO : List (BitVec 32) := compileAFO [0, 3] sortProg
def msortCodeO : List (BitVec 32) := compileBFO 7 [0, 2, 3] msortProg

theorem sortCodeO_ok_k {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc sortCodeO) (hok : codeOK pc sortCodeO.length) (hra : (getX s 1).toNat % 2 = 0)
    {xs out : List (BitVec 8)} {inb outb : Nat} (hR : RegOK [⟨inb, xs.length⟩, ⟨outb, xs.length⟩])
    (hcd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨outb, xs.length⟩], disjoint ⟨pc.toNat, 4 * sortCodeO.length⟩ r)
    (h0 : getX s 10 = BitVec.ofNat 64 inb) (h1 : getX s 11 = BitVec.ofNat 64 xs.length)
    (h3 : getX s 13 = BitVec.ofNat 64 outb)
    (hx : bytesAt s inb xs.length = xs.map some) (ho : bytesAt s outb xs.length = out.map some) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      bytesAt s' outb xs.length = (xs.mergeSort leB).map some ∧
      bytesAt s' inb xs.length = xs.map some ∧ unchangedOutside s s' [⟨outb, xs.length⟩] ∧
      Cfg s' ∧ Mach.Riscv.rv.keep s s' := by
  have hn : xs.length < 2 ^ 63 := by
    have := hR.1 _ (List.mem_cons_self ..); unfold Region.inRAM at this; dsimp only at this; omega
  have hout : out.length = xs.length := by simpa [bytesAt] using (congrArg List.length ho).symm
  obtain ⟨σ', hex, hh⟩ := sortProg_mergeSort xs out ⟨fun i => getX s (A8 i), [xs, out]⟩ rfl h1 hn hout
  have hrel : Rel [0, 3] [⟨inb, xs.length⟩, ⟨outb, xs.length⟩] ⟨fun i => getX s (A8 i), [xs, out]⟩ s :=
    ⟨fun _ => rfl, rfl, rfl, fun b hb => by obtain _ | _ | b := b; exact h0; exact h3; simp at hb; omega,
      fun b hb => by obtain _ | _ | b := b; rfl; exact hout; simp at hb; omega,
      fun b hb => by obtain _ | _ | b := b; exact hx; exact ho; simp at hb; omega⟩
  refine runsTo_mono (compileAFO_okK [0, 3] sortProg_wf hR hex h hpc hc hok hcd hrel hra) ?_
  rintro s' ⟨p1, p2, p3, p4, p5⟩
  have e0 := p2.bytes 0 (by simp); have e1 := p2.bytes 1 (by simp)
  simp only [hh] at e0 e1
  exact ⟨p1, by simpa using e1, by simpa using e0, unchanged_drop p3 (by simpa [hx] using e0), p4, p5⟩

/-- `msortCodeO_ok_m` with the full register frame `keep` -/
theorem msortCodeO_ok_k {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc msortCodeO) (hok : codeOK pc msortCodeO.length) (hra : (getX s 1).toNat % 2 = 0)
    {xs scr out : List (BitVec 8)} {inb scb outb : Nat}
    (hR : RegOK [⟨inb, xs.length⟩, ⟨scb, xs.length⟩, ⟨outb, xs.length⟩])
    (hf : FrOK 7 (frameBase 7 (getX s 2)))
    (hfd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨scb, xs.length⟩, ⟨outb, xs.length⟩],
      disjoint ⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ r)
    (hcd : ∀ r ∈ [(⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ : Region), ⟨inb, xs.length⟩, ⟨scb, xs.length⟩,
      ⟨outb, xs.length⟩], disjoint ⟨pc.toNat, 4 * msortCodeO.length⟩ r)
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
  refine runsTo_mono (compileBFO_okK 7 [0, 2, 3] (by decide) msortProg_wf hR hex h hpc hc hok hf hfd hcd
    (fun i => by simp [envOf]) (fun j hj => by simp [envOf]; omega) hheap hra) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  have e0 := p3.bytes 0 (by simp); have e2 := p3.bytes 2 (by simp)
  simp only [hh] at e0 e2
  have e0' : bytesAt s' inb xs.length = xs.map some := by simpa using e0
  have hu : unchangedOutside s s' ((⟨inb, xs.length⟩ : Region) :: [⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩,
      ⟨scb, xs.length⟩, ⟨outb, xs.length⟩]) := fun a ha => p4 a fun r hr => ha r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with e | e | e | e <;> simp [e])
  exact ⟨p1, by simpa using e2, e0', unchanged_drop hu (by rw [e0', hx]), p5, p6⟩

/-- **Insertion sort** in `Implements1` form: no work space (`space n = 0`) -/
theorem sortCode_implements1O : Implements1Raw sortCodeO (fun x => x.mergeSort leU) (fun _ => 0) := by
  intro a s entry ra input output work
  dsimp only [encRaw]
  intro hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx hil hol hws hwal hram hdis hmapO hmapW
  simp only [List.length_mergeSort] at hol ⊢
  have hin : ∀ r ∈ [input, output, work, (⟨entry.toNat, 4 * sortCodeO.length⟩ : Region)], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hdis
  obtain ⟨ri, ro, rw', rc⟩ := hin
  unfold Region.inRAM at ri ro rc
  unfold disjoint at d12 d14 d24
  dsimp only at d12 d14 d24 ri ro rc
  have hxl : (a.map (·.toBitVec)).length = a.length := by simp
  have hil' : input.len = a.length := hil
  have hol' : a.length ≤ output.len := hol
  have hR : RegOK [⟨input.base, (a.map (·.toBitVec)).length⟩, ⟨output.base, (a.map (·.toBitVec)).length⟩] := by
    rw [hxl]
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold Region.inRAM; dsimp only; omega)
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
        and_true, false_implies, implies_true]
      unfold disjoint; dsimp only; omega
  have hok : codeOK entry sortCodeO.length := ⟨hal, rc.1, rc.2⟩
  have hcd : ∀ r ∈ [(⟨input.base, (a.map (·.toBitVec)).length⟩ : Region), ⟨output.base, (a.map (·.toBitVec)).length⟩],
      disjoint ⟨entry.toNat, 4 * sortCodeO.length⟩ r := by
    rw [hxl]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  refine runsTo_mono (sortCodeO_ok_k h hpc (codeAt_of_codeBytes hok hcode) hok (by rw [hra']; omega) hR hcd
    (getX_of (h.x10.symm.trans h10) rfl) (by rw [getX_of (h.x11.symm.trans h11) rfl, hxl])
    (getX_of (h.x13.symm.trans h13) rfl) (by simpa [List.map_map, Function.comp_def] using hx)
    (bytesAt_hosted (fun i hi => hmapO i (by rw [hxl] at hi; omega)))) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  refine ⟨by rw [p1, hra'], ?_, ?_, Mach.Riscv.abi_of_keep h p5 p6, p5, fun h => nomatch h⟩
  · rw [← hxl, p2, ← mergeSort_toBitVec]; simp [List.map_map]
  · intro q hq
    apply p4 q
    intro r hr
    have a2 := hq ⟨output.base, a.length⟩ (by simp)
    simp only [List.mem_singleton] at hr; subst hr; dsimp only; rw [hxl]; omega

/-- **Merge sort** in `Implements1` form: `space n = n + 71` (an `n`-byte scratch block at the bottom of the
work block, the 64-byte frame below `sp` at its top, up to 7 bytes of alignment) -/
theorem msortCode_implements1O : Implements1Raw msortCodeO (fun x => x.mergeSort leU) (fun n => n + 71) := by
  intro a s entry ra input output work
  dsimp only [encRaw]
  intro hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx hil hol hws hwal hram hdis hmapO hmapW
  simp only [List.length_mergeSort] at hol ⊢
  have hin : ∀ r ∈ [input, output, work, (⟨entry.toNat, 4 * msortCodeO.length⟩ : Region)], r.inRAM := hram
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
  have hok : codeOK entry msortCodeO.length := ⟨hal, rc.1, rc.2⟩
  have hfd : ∀ r ∈ [(⟨input.base, (a.map (·.toBitVec)).length⟩ : Region), ⟨work.base, (a.map (·.toBitVec)).length⟩,
      ⟨output.base, (a.map (·.toBitVec)).length⟩], disjoint ⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ r := by
    rw [hxl, hfb]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hcd : ∀ r ∈ [(⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ : Region), ⟨input.base, (a.map (·.toBitVec)).length⟩,
      ⟨work.base, (a.map (·.toBitVec)).length⟩, ⟨output.base, (a.map (·.toBitVec)).length⟩],
      disjoint ⟨entry.toNat, 4 * msortCodeO.length⟩ r := by
    rw [hxl, hfb]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  refine runsTo_mono (msortCodeO_ok_k h hpc (codeAt_of_codeBytes hok hcode) hok (by rw [hra']; omega) hR hf hfd hcd
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
