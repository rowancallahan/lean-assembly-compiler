/- Generated programs on the machine: `prog f.lay f.tree out` compiled by the existing `compileBF` and run on
the Sail RISC-V model.  `ro1_ok` is the glue, once, for functions over one read-only byte array (block 0, base in
`a0`): it builds the initial source state from the registers and the heap relation from `bytesAt`.  Each machine
theorem below is then `f.exec` plus `decide` for `BStmt.wf`. -/
import Proven.Arr2F
import Proven.Frontx.Examples

namespace Proven.Frontx
open Proven LeanRV64D

/-! ## `BStmt.wf` is decidable (well-formedness of a generated program is one `decide`) -/

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

/-- **One read-only byte array.**  If the program, started with the registers of `s` and the array as block 0,
ends with `r` in variable `out` (a register) and the heap unchanged, then the compiled code, called with the
array at `a0`, returns to `ra` with `r` in that register, the array unchanged, memory outside the frame
unchanged, callee-saved registers and `gp` kept. -/
theorem ro1_ok {N : Nat} {p : BStmt} (hp : p.wf N [0]) (out : Fin 8) (xs : ByteArray) (r : BitVec 64)
    {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileBF N [0] p)) (hok : codeOK pc (compileBF N [0] p).length)
    (hra : (getX s 1).toNat % 2 = 0) {inb : Nat} (hR : RegOK [⟨inb, xs.size⟩])
    (hf : FrOK N (frameBase N (getX s 2)))
    (hfd : ∀ r ∈ [(⟨inb, xs.size⟩ : Region)], disjoint ⟨frameBase N (getX s 2), 8 * (N + 1)⟩ r)
    (hcd : ∀ r ∈ [(⟨frameBase N (getX s 2), 8 * (N + 1)⟩ : Region), ⟨inb, xs.size⟩],
      disjoint ⟨pc.toNat, 4 * (compileBF N [0] p).length⟩ r)
    (h0 : getX s 10 = BitVec.ofNat 64 inb) (hx : bytesAt s inb xs.size = (blk xs).map some)
    (hex : ∃ σ', BExec p ⟨envOf s, [blk xs]⟩ σ' ∧ σ'.env out.val = r ∧ σ'.heap = [blk xs]) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ getX s' (A8 out) = r ∧
      bytesAt s' inb xs.size = (blk xs).map some ∧
      unchangedOutside s s' [⟨frameBase N (getX s 2), 8 * (N + 1)⟩, ⟨inb, xs.size⟩] ∧
      Cfg s' ∧ calleeSavedKept s s' ∧ getX s' 3 = getX s 3 := by
  obtain ⟨σ', hex, hv, hh⟩ := hex
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
  refine runsTo_mono (compileBF_ok N [0] (by simp; omega) hp hR hex h hpc hc hok hf hfd hcd
    (fun i => by simp [envOf]) (fun j hj => by simp [envOf]; omega) hheap hra) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6, p7⟩
  have e0 := p3.bytes 0 (by simp)
  simp only [hh] at e0
  exact ⟨p1, (p2 out).trans hv, by simpa using e0, p4, p5, p6, p7⟩

theorem size_lt {inb : Nat} {xs : ByteArray} (hR : RegOK [⟨inb, xs.size⟩]) : xs.size < 2 ^ 64 := by
  have := hR.1 _ (List.mem_cons_self ..); unfold Region.inRAM at this; dsimp only at this; omega

namespace Ex

/-! ## CRC-32 -/

def crcProg : BStmt := prog crcGo.lay crcGo.tree 2
theorem crcProg_wf : crcProg.wf crcGo.slots [0] := by decide +kernel
def crcCode : List (BitVec 32) := compileBF crcGo.slots [0] crcProg

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
      Cfg s' ∧ calleeSavedKept s s' ∧ getX s' 3 = getX s 3 :=
  ro1_ok crcProg_wf 2 xs _ h hpc hc hok hra hR hf hfd hcd h0 hx
    (crcGo.exec xs i c ⟨envOf s, [blk xs]⟩
      ⟨rfl, by simpa [envOf] using h1, size_lt hR, by simpa [envOf] using h2, hi, by simpa [envOf] using h3⟩)

/-! ## A loop in lean-svg style (`at'`, `b64Digit`, fuel): needs the automatic expression splitting -/

def b64Prog : BStmt := prog b64Sum.lay b64Sum.tree 2
theorem b64Prog_wf : b64Prog.wf b64Sum.slots [0] := by decide +kernel
def b64Code : List (BitVec 32) := compileBF b64Sum.slots [0] b64Prog

/-- array at `a0` (length in `a1`), `i` in `a2`, `fuel` in `a3`, `n` in `a4`: returns `a2 = b64Sum bs i fuel n` -/
theorem b64Code_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc b64Code) (hok : codeOK pc b64Code.length) (hra : (getX s 1).toNat % 2 = 0)
    (bs : ByteArray) (i fuel : Nat) (n : UInt32) {inb : Nat} (hR : RegOK [⟨inb, bs.size⟩])
    (hf : FrOK b64Sum.slots (frameBase b64Sum.slots (getX s 2)))
    (hfd : ∀ r ∈ [(⟨inb, bs.size⟩ : Region)],
      disjoint ⟨frameBase b64Sum.slots (getX s 2), 8 * (b64Sum.slots + 1)⟩ r)
    (hcd : ∀ r ∈ [(⟨frameBase b64Sum.slots (getX s 2), 8 * (b64Sum.slots + 1)⟩ : Region), ⟨inb, bs.size⟩],
      disjoint ⟨pc.toNat, 4 * b64Code.length⟩ r)
    (h0 : getX s 10 = BitVec.ofNat 64 inb) (h1 : getX s 11 = rN bs.size)
    (h2 : getX s 12 = rN i) (h3 : getX s 13 = rN fuel) (hb : i + fuel < 2 ^ 64) (h4 : getX s 14 = r32 n)
    (hx : bytesAt s inb bs.size = (blk bs).map some) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ getX s' 12 = r32 (b64Sum bs i fuel n) ∧
      bytesAt s' inb bs.size = (blk bs).map some ∧
      unchangedOutside s s' [⟨frameBase b64Sum.slots (getX s 2), 8 * (b64Sum.slots + 1)⟩, ⟨inb, bs.size⟩] ∧
      Cfg s' ∧ calleeSavedKept s s' ∧ getX s' 3 = getX s 3 :=
  ro1_ok b64Prog_wf 2 bs _ h hpc hc hok hra hR hf hfd hcd h0 hx
    (b64Sum.exec bs i fuel n ⟨envOf s, [blk bs]⟩
      ⟨rfl, by simpa [envOf] using h1, size_lt hR, by simpa [envOf] using h2, by omega,
        by simpa [envOf] using h3, by omega, by simpa [envOf] using h4, hb⟩)

end Ex
end Proven.Frontx
