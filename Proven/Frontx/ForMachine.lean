/- Machine theorems (Sail RISC-V model, through `compileBF_ok`) for a `for` loop and a non-recursive function
of lean-svg.  Each is `ro1_ok` applied to the generated `exec` theorem; `BStmt.wf` by `decide`. -/
import Proven.Frontx.Machine
import Proven.Frontx.ForExamples

namespace Proven.Frontx.Ex
open Proven LeanRV64D

/-! ## lean-svg `Bytes.findByte` -/

def findProg : BStmt := initS findByte.inits (prog findByte.lay findByte.tree 2)
theorem findProg_wf : findProg.wf findByte.slots [0] := by decide +kernel
def findCode : List (BitVec 32) := compileBF findByte.slots [0] findProg

/-- array at `a0` (length in `a1`), start index in `a2`, the byte in `a3`: returns `a2 = findByte bs i c` -/
theorem findCode_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc findCode) (hok : codeOK pc findCode.length) (hra : (getX s 1).toNat % 2 = 0)
    (bs : ByteArray) (i : Nat) (c : UInt8) {inb : Nat} (hR : RegOK [⟨inb, bs.size⟩])
    (hf : FrOK findByte.slots (frameBase findByte.slots (getX s 2)))
    (hfd : ∀ r ∈ [(⟨inb, bs.size⟩ : Region)],
      disjoint ⟨frameBase findByte.slots (getX s 2), 8 * (findByte.slots + 1)⟩ r)
    (hcd : ∀ r ∈ [(⟨frameBase findByte.slots (getX s 2), 8 * (findByte.slots + 1)⟩ : Region), ⟨inb, bs.size⟩],
      disjoint ⟨pc.toNat, 4 * findCode.length⟩ r)
    (h0 : getX s 10 = BitVec.ofNat 64 inb) (h1 : getX s 11 = rN bs.size)
    (h2 : getX s 12 = rN i) (hi : i < 2 ^ 64) (h3 : getX s 13 = r8 c)
    (hx : bytesAt s inb bs.size = (blk bs).map some) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ getX s' 12 = rN (findByte bs i c) ∧
      bytesAt s' inb bs.size = (blk bs).map some ∧
      unchangedOutside s s' [⟨frameBase findByte.slots (getX s 2), 8 * (findByte.slots + 1)⟩, ⟨inb, bs.size⟩] ∧
      Cfg s' ∧ calleeSavedKept s s' ∧ getX s' 3 = getX s 3 :=
  ro1_ok findProg_wf 2 bs _ h hpc hc hok hra hR hf hfd hcd h0 hx
    (findByte.exec bs i c ⟨envOf s, [blk bs]⟩
      ⟨rfl, by simpa [envOf] using h1, size_lt hR, by simpa [envOf] using h2, hi, by simpa [envOf] using h3⟩)

/-! ## lean-svg `PngDecode.be32` -/

def be32Prog : BStmt := prog be32.lay be32.tree 2
theorem be32Prog_wf : be32Prog.wf be32.slots [0] := by decide +kernel
def be32Code : List (BitVec 32) := compileBF be32.slots [0] be32Prog

/-- array at `a0` (length in `a1`), offset in `a2`: returns `a2 = be32 b i` (bytes past the end read as 0) -/
theorem be32Code_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc be32Code) (hok : codeOK pc be32Code.length) (hra : (getX s 1).toNat % 2 = 0)
    (b : ByteArray) (i : Nat) {inb : Nat} (hR : RegOK [⟨inb, b.size⟩])
    (hf : FrOK be32.slots (frameBase be32.slots (getX s 2)))
    (hfd : ∀ r ∈ [(⟨inb, b.size⟩ : Region)], disjoint ⟨frameBase be32.slots (getX s 2), 8 * (be32.slots + 1)⟩ r)
    (hcd : ∀ r ∈ [(⟨frameBase be32.slots (getX s 2), 8 * (be32.slots + 1)⟩ : Region), ⟨inb, b.size⟩],
      disjoint ⟨pc.toNat, 4 * be32Code.length⟩ r)
    (h0 : getX s 10 = BitVec.ofNat 64 inb) (h1 : getX s 11 = rN b.size)
    (h2 : getX s 12 = rN i) (hi : i + 3 < 2 ^ 64)
    (hx : bytesAt s inb b.size = (blk b).map some) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ getX s' 12 = rN (be32 b i) ∧
      bytesAt s' inb b.size = (blk b).map some ∧
      unchangedOutside s s' [⟨frameBase be32.slots (getX s 2), 8 * (be32.slots + 1)⟩, ⟨inb, b.size⟩] ∧
      Cfg s' ∧ calleeSavedKept s s' ∧ getX s' 3 = getX s 3 :=
  ro1_ok be32Prog_wf 2 b _ h hpc hc hok hra hR hf hfd hcd h0 hx
    (be32.exec b i ⟨envOf s, [blk b]⟩
      ⟨rfl, by simpa [envOf] using h1, size_lt hR, by simpa [envOf] using h2, by omega, hi⟩)

end Proven.Frontx.Ex
