/- The branchy merge sort `msortProgB` (`Riscv/Examples/MsortB.lean`, source proof `msortProgB_mergeSort`, staged
unchanged) on DeepMind's AArch64 semantics, through `MachineF.compBF_ok` and `apcF`. -/
import Apc.Frame
import Apc.Stack
import Compiler.BStmt
import Apc.Src.MsortB
import Apc.Src.ToM
namespace Proven.Apc
open Proven Proven.Mach

/-- the program, in the middle layer's `BStmt` -/
def msortB : Mach.BStmt := Riscv.toMS msortProgB

set_option maxRecDepth 100000 in
theorem msortB_wf0 : (apcF L0).wfB 7 [0, 2, 3] [] msortB := by
  simp only [msortB, Riscv.toMS, Riscv.toMB, msortProgB, mainBodyB, passB, runB, mergeB, mergeA, tailL, tailR, condA,
    lt98, one, minE, addE, ltE, MachineF.wfB, Mach.BExp.depth, Mach.BExp.vlt]
  repeat' apply And.intro
  all_goals first | decide | (show _ < 2 ^ 18; decide +kernel) | (show 0 < _ ∧ _ ≤ 2 ^ 25; decide +kernel)
set_option maxRecDepth 100000 in
theorem msortB_wf (L : Lay) : (apcF L).wfB 7 [0, 2, 3] [] msortB := msortB_wf0

/-- the compiled merge sort for this target (7 slots; blocks input / scratch / output at x0, x2, x3; n in x1) -/
def msortCode : List (BitVec 32) := (apcF L0).codeF ((apcF L0).compBF 7 [0, 2, 3] [] msortB)

/-- **Merge sort on DeepMind's AArch64 user-mode semantics** (memory/region form).  Code at `pc` (executable code
range); input `xs` at x0 (length in x1), a scratch block at x2 and an output block at x3 (`|xs|` bytes each, any
contents), all inside the writable data range, pairwise disjoint, disjoint from the frame `[sp - 64, sp)` (which
must lie in the data range, `sp` 8-aligned); code disjoint from all four.  The run returns to x30 with the output
block holding `xs.mergeSort`, the input unchanged, every byte outside the scratch / output blocks and the frame
unchanged, status `Running`, `sp` and x28 (and every register outside x0..x15) unchanged. -/
theorem msort_apc (L : Lay) {s : Arm64.State} {pc : BitVec 64} (hA : (apcF L).At s pc ((apcF L).codeF ((apcF L).compBF 7 [0, 2, 3] [] msortB)))
    (hen : enterOK L s 7) {xs scr out : List (BitVec 8)} {inb scb outb : Nat} (hn : xs.length < 2 ^ 32)
    (hi : L.dLo ≤ inb ∧ inb + xs.length ≤ L.dHi) (hs' : L.dLo ≤ scb ∧ scb + xs.length ≤ L.dHi)
    (ho' : L.dLo ≤ outb ∧ outb + xs.length ≤ L.dHi)
    (hdis : [(⟨inb, xs.length⟩ : Region), ⟨scb, xs.length⟩, ⟨outb, xs.length⟩].Pairwise disjoint)
    (hfd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨scb, xs.length⟩, ⟨outb, xs.length⟩], disjoint ⟨frameAt s 7, 64⟩ r)
    (hcd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨scb, xs.length⟩, ⟨outb, xs.length⟩, ⟨frameAt s 7, 64⟩],
      disjoint ⟨pc.toNat, 4 * ((apcF L).codeF ((apcF L).compBF 7 [0, 2, 3] [] msortB)).length⟩ r)
    (h0 : s.regs.read 0#5 = BitVec.ofNat 64 inb) (h1 : s.regs.read 1#5 = BitVec.ofNat 64 xs.length)
    (h2 : s.regs.read 2#5 = BitVec.ofNat 64 scb) (h3 : s.regs.read 3#5 = BitVec.ofNat 64 outb)
    (hx : bytes (memV s) inb xs.length = xs.map some) (hs : bytes (memV s) scb xs.length = scr.map some)
    (ho : bytes (memV s) outb xs.length = out.map some) :
    ∃ s', Arm64.Steps P s s' ∧ s'.pc = s.regs.read 30#5 ∧
      bytes (memV s') outb xs.length = (xs.mergeSort leB).map some ∧ bytes (memV s') inb xs.length = xs.map some ∧
      Out [⟨inb, xs.length⟩, ⟨scb, xs.length⟩, ⟨outb, xs.length⟩, ⟨frameAt s 7, 64⟩] (memV s) (memV s') ∧
      s'.status = .Running ∧ s'.sp = s.sp ∧ s'.regs.read 28#5 = s.regs.read 28#5 ∧
      ∀ x : BitVec 5, (∀ r, xr r ≠ x) → s'.regs.read x = s.regs.read x := by
  have hd := hen.2.2.2.2.2
  have hsl : scr.length = xs.length := by simpa [length_bytes] using (congrArg List.length hs).symm
  have hol : out.length = xs.length := by simpa [length_bytes] using (congrArg List.length ho).symm
  let env : BEnv := fun i => if h : i < 8 then (apcF L).get s (avar ⟨i, h⟩) else 0
  obtain ⟨σ', hex, scr', hh⟩ := msortProgB_mergeSort xs scr out ⟨env, [xs, scr, out]⟩ rfl
    (by simp only [env]; rw [dite_eq_left_of_eq_true (by decide)]; exact h1) hn hsl hol
  have R3 : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨scb, xs.length⟩, ⟨outb, xs.length⟩],
      L.dLo ≤ r.base ∧ r.base + r.len ≤ L.dHi := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  have hL : (apcF L).Lay 7 (frameAt s 7) [⟨inb, xs.length⟩, ⟨scb, xs.length⟩, ⟨outb, xs.length⟩] [] :=
    { ram := fun r hr => ⟨Nat.zero_le _, by have := R3 r hr; show _ ≤ 2 ^ 64 - 1; omega⟩
      wram := fun r hr => by simp at hr
      rp := hdis
      wp := List.Pairwise.nil
      rw := fun r _ w hw => by simp at hw
      fr := hfd
      fw := fun w hw => by simp at hw
      wal := fun w hw => by simp at hw
      wr := fun r hr a h1 h2 _ _ => by have := R3 r hr; exact ⟨by omega, by omega⟩
      wwr := fun w hw => by simp at hw }
  have hheap : (apcF L).HeapB [0, 2, 3] [] [⟨inb, xs.length⟩, ⟨scb, xs.length⟩, ⟨outb, xs.length⟩] []
      (Riscv.toMSt ⟨env, [xs, scr, out]⟩) s :=
    { hlen := rfl, bvlen := rfl,
      base := fun b hb => by
        obtain _ | _ | _ | b := b
        · exact h0
        · exact h2
        · exact h3
        · simp at hb; omega
      blen := fun b hb => by
        obtain _ | _ | _ | b := b
        · rfl
        · exact hsl
        · exact hol
        · simp at hb; omega
      rbytes := fun b hb => by
        obtain _ | _ | _ | b := b
        · exact hx
        · exact hs
        · exact ho
        · simp at hb; omega
      whlen := rfl, wvlen := rfl, wbase := fun b hb => by simp at hb, wblen := fun b hb => by simp at hb,
      wbyts := fun b hb => by simp at hb }
  obtain ⟨s', hst, p1, -, p3, p4, p5, p6⟩ := (apcF L).compBF_ok 7 [0, 2, 3] [] (by decide) (by simp) (msortB_wf L)
    (Riscv.exec_toM hex) hA hen hL hcd (fun i => by simp [env, Riscv.toMSt])
    (fun j hj => by simp [env, Riscv.toMSt]; omega) hheap trivial
  have e0 := p3.rbytes 0 (by simp); have e2 := p3.rbytes 2 (by simp)
  simp only [Riscv.toMSt, hh] at e0 e2
  have e2' : bytes ((apcF L).mem s') outb xs.length = (xs.mergeSort leB).map some := by simpa using e2
  have e0' : bytes ((apcF L).mem s') inb xs.length = xs.map some := by simpa using e0
  have p4' : Out [⟨inb, xs.length⟩, ⟨scb, xs.length⟩, ⟨outb, xs.length⟩, ⟨(apcF L).frameAt s 7, 64⟩]
      ((apcF L).mem s) ((apcF L).mem s') := by simpa using p4
  exact ⟨s', hst, p1, e2', e0', p4', p5.1, p6.2,
    (apcF L).keep_fr p6, fun x hx => p6.1 x hx id⟩

end Proven.Apc
