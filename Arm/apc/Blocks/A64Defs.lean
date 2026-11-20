/- VERBATIM copies (check_copy.sh): `wbyte`/`cbyte` of `Nano/V2Self/Proof/Machine/Target.lean` and the helper
definitions of `Nano/V2Self/Proof/Machine/A64Sem.lean` (before the structure), so that the armDM facts elaborate on
Lean 4.34 without Target's 4.29-only import closure. -/
import Spec.Top
import Nano.V2Self.Proof.Machine.ArmEnc
namespace JT
open Proven.Top

/-- byte `k` (0..3) of a 32-bit word, little-endian -/
def wbyte (w : BitVec 32) (k : Nat) : UInt8 := UInt8.ofBitVec (w.extractLsb' (8 * k) 8)

/-- byte `k` (0..7) of a J memory cell, little-endian -/
def cbyte (v : UInt64) (k : Nat) : UInt8 := (v >>> (8 * k).toUInt64).toUInt8

/-- the 32-bit word `w` is stored little-endian at byte address `a` -/
def WordAt (o : MachineState) (a w : Nat) : Prop :=
  ∀ k < 4, o.memory (UInt64.ofNat (a + k)) = some (wbyte (BitVec.ofNat 32 w) k)

/-- the pc is a 4-aligned word address in RAM (what a model needs to fetch) -/
def PcOK (M : Machine) (o : MachineState) : Prop :=
  o.programCounter.toNat % 4 = 0 ∧ M.ramStart ≤ o.programCounter.toNat ∧ o.programCounter.toNat + 4 ≤ M.ramEnd

/-- the machine runs from `s` to a configured state that shows `o` -/
def Goes (M : Machine) (s : M.State) (o : MachineState) : Prop :=
  ∃ s', Runs M s s' ∧ M.configured s' ∧ M.observe s' = o

/-- `o` after an instruction that writes register `d` with `v` and falls through -/
def setReg (o : MachineState) (d : Nat) (v : UInt64) : MachineState :=
  ⟨o.programCounter + 4, fun r => if r = d then v else o.register r, o.memory⟩

/-- `o` after a jump to `t` that writes no register -/
def jumpTo (o : MachineState) (t : UInt64) : MachineState := ⟨t, o.register, o.memory⟩

/-- the register ALU values (ArmEnc.aluC numbering): add, sub, madd (+ x17), and, orr, lslv, lsrv, eor -/
def aluV (op : Nat) (a b z : UInt64) : UInt64 :=
  if op = 1 then a + b else if op = 2 then a - b else if op = 3 then z + a * b else if op = 4 then a &&& b
  else if op = 5 then a ||| b else if op = 6 then a <<< b else if op = 7 then a >>> b else a ^^^ b

/-- the b.cond conditions the blocks use, after `subs x16, xa, xb`: EQ 0, NE 1, HS 2, LO 3 -/
def condV (c : Nat) (a b : UInt64) : Bool :=
  if c = 0 then a == b else if c = 1 then a != b else if c = 2 then decide (b.toNat ≤ a.toNat) else decide (a.toNat < b.toNat)

/-- `movk`'s new register value -/
def movkV (old : UInt64) (i h : Nat) : UInt64 :=
  (old &&& ~~~((0xFFFF : UInt64) <<< (16 * h).toUInt64)) ||| ((UInt64.ofNat i) <<< (16 * h).toUInt64)

/-- `o`'s memory after an 8-byte store of `v` at `a` -/
def store8 (o : MachineState) (a : Nat) (v : UInt64) : MachineState :=
  ⟨o.programCounter + 4, o.register,
    fun u => if a ≤ u.toNat ∧ u.toNat < a + 8 then some (cbyte v (u.toNat - a)) else o.memory u⟩

/-- `o`'s memory after a byte store of `v`'s low byte at `a` -/
def store1 (o : MachineState) (a : Nat) (v : UInt64) : MachineState :=
  ⟨o.programCounter + 4, o.register, fun u => if u.toNat = a then some v.toUInt8 else o.memory u⟩

end JT
