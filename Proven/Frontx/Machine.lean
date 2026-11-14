/- A generated program on the machine: the CRC-32 loop compiled by the existing `compileBF` and run on the
Sail RISC-V model.  The only hand-written steps are the ones every `compileBF_ok` client has (building the
initial source state from the registers and the heap relation from `bytesAt`). -/
import Proven.Arr2F
import Proven.Frontx.Examples

namespace Proven.Frontx.Ex
open Proven LeanRV64D

/-! ## `BStmt.wf` is decidable (so that well-formedness of a generated program is one `decide`) -/

def vltDec (m : Nat) : (e : BExp) → Decidable (e.vlt m)
  | .var i => inferInstanceAs (Decidable (i < m))
  | .const _ => isTrue trivial
  | .bin _ a b => @instDecidableAnd _ _ (vltDec m a) (vltDec m b)
  | .ite c a b => @instDecidableAnd _ _ (vltDec m c) (@instDecidableAnd _ _ (vltDec m a) (vltDec m b))

instance (m : Nat) (e : BExp) : Decidable (e.vlt m) := vltDec m e

def wfDec (N : Nat) (bv : List Nat) : (p : BStmt) → Decidable (p.wf N bv)
  | .assign v e => inferInstanceAs (Decidable (e.depth < 7 ∧ e.vlt (8 + N) ∧ v < 8 + N ∧ v ∉ bv))
  | .load v b i => inferInstanceAs (Decidable (i.depth < 6 ∧ i.vlt (8 + N) ∧ v < 8 + N ∧ v ∉ bv ∧ b < bv.length))
  | .store b i e =>
    inferInstanceAs (Decidable (i.depth < 6 ∧ e.depth < 6 ∧ i.vlt (8 + N) ∧ e.vlt (8 + N) ∧ b < bv.length))
  | .seq p q => @instDecidableAnd _ _ (wfDec N bv p) (wfDec N bv q)
  | .loop _ body =>
    @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ (wfDec N bv body) inferInstance))

instance (N : Nat) (bv : List Nat) (p : BStmt) : Decidable (p.wf N bv) := wfDec N bv p

/-- the initial source state: registers as in `s`, slots `0` -/
def envOf (s : St) : BEnv := fun i => if h : i < 8 then getX s (A8 ⟨i, h⟩) else 0

/-- the loop of `crcGo`, result in `a2`; 20 variables: `a0..a7` and 12 slots -/
def crcProg : BStmt := prog crcGo.lay crcGo.tree 2

theorem crcProg_wf : crcProg.wf 12 [0] := by decide +kernel

def crcCode : List (BitVec 32) := compileBF 12 [0] crcProg

/-- **CRC-32 loop on the machine**: with the array at `a0` (length in `a1`), the index in `a2` and the running
CRC in `a3`, the code returns to `ra` with `a2 = crcGo xs i c`, the array unchanged. -/
theorem crcCode_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc crcCode) (hok : codeOK pc crcCode.length) (hra : (getX s 1).toNat % 2 = 0)
    (xs : ByteArray) (i : Nat) (c : UInt32) {inb : Nat} (hR : RegOK [⟨inb, xs.size⟩])
    (hf : FrOK 12 (frameBase 12 (getX s 2)))
    (hfd : ∀ r ∈ [(⟨inb, xs.size⟩ : Region)], disjoint ⟨frameBase 12 (getX s 2), 8 * (12 + 1)⟩ r)
    (hcd : ∀ r ∈ [(⟨frameBase 12 (getX s 2), 8 * (12 + 1)⟩ : Region), ⟨inb, xs.size⟩],
      disjoint ⟨pc.toNat, 4 * crcCode.length⟩ r)
    (h0 : getX s 10 = BitVec.ofNat 64 inb) (h1 : getX s 11 = rN xs.size)
    (h2 : getX s 12 = rN i) (hi : i < 2 ^ 64) (h3 : getX s 13 = r32 c)
    (hx : bytesAt s inb xs.size = (blk xs).map some) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ getX s' 12 = r32 (crcGo xs i c) ∧
      bytesAt s' inb xs.size = (blk xs).map some ∧
      unchangedOutside s s' [⟨frameBase 12 (getX s 2), 8 * (12 + 1)⟩, ⟨inb, xs.size⟩] ∧
      Cfg s' ∧ calleeSavedKept s s' ∧ getX s' 3 = getX s 3 := by
  have hn : xs.size < 2 ^ 64 := by
    have := hR.1 _ (List.mem_cons_self ..); unfold Region.inRAM at this; dsimp only at this; omega
  obtain ⟨σ', hex, hv, hh⟩ := crcGo.exec xs i c ⟨envOf s, [blk xs]⟩
    ⟨rfl, by simpa [envOf] using h1, hn, by simpa [envOf] using h2, hi, by simpa [envOf] using h3⟩
  have hheap : HeapRel [0] [⟨inb, xs.size⟩] ⟨envOf s, [blk xs]⟩ s :=
    ⟨rfl, rfl, fun b hb => by
        obtain _ | b := b
        · simpa [envOf] using h0
        · simp at hb,
      fun b hb => by
        obtain _ | b := b
        · simp
        · simp at hb,
      fun b hb => by
        obtain _ | b := b
        · simpa using hx
        · simp at hb⟩
  refine runsTo_mono (compileBF_ok 12 [0] (by decide) crcProg_wf hR hex h hpc hc hok hf hfd hcd
    (fun i => by simp [envOf]) (fun j hj => by simp [envOf]; omega) hheap hra) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6, p7⟩
  have e0 := p3.bytes 0 (by simp)
  simp only [hh] at e0
  exact ⟨p1, (p2 2).trans hv, by simpa using e0, p4, p5, p6, p7⟩

end Proven.Frontx.Ex
