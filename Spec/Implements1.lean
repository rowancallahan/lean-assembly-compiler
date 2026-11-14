/- Specification with ONE resource bound: what it means for RV64 machine code to implement a function
`f : α → β` (bytes in, bytes out through `Spec/Encode.lean`) using at most `space n` bytes of work memory
for an input of `n` bytes.

Calling convention (RV64, `Spec/Riscv.lean`): `a0` = input base, `a1` = input length (bytes),
`a2` = work base, `a3` = output base, `sp` = work base + work length (the TOP of the work block: the code
may use the work block as its stack, growing down from `sp`, and as scratch from `a2` up), `ra` = return
address.  The work block is 8-aligned (`work.base % 8 = 0`); input, output, work block and code are in
RAM and pairwise disjoint; the output and work bytes are present in the memory map.  The run reaches `ra`
with `enc (f a)` in the first bytes of the output block, NOTHING outside output ∪ work changed (the input
in particular), callee-saved registers and `Cfg` kept. -/
import Spec.Riscv
import Spec.Encode

namespace Proven

/-- `Implements1` for explicit encodings of the argument and the result -/
def Implements1With {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (code : List (BitVec 32))
    (f : α → β) (space : Nat → Nat) (maxLen : Nat := 2 ^ 20) : Prop :=
  ∀ (a : α) (s : St) (entry ra : BitVec 64) (input output work : Region),
    let x := encA a
    let y := encB (f a)
    let codeR : Region := ⟨entry.toNat, 4 * code.length⟩
    x.length ≤ maxLen → Cfg s → s.regs.get? .PC = some entry → entry.toNat % 4 = 0 →
    bytesAt s entry.toNat (4 * code.length) = codeBytes code →
    s.regs.get? .x10 = some (BitVec.ofNat 64 input.base) →
    s.regs.get? .x11 = some (BitVec.ofNat 64 x.length) →
    s.regs.get? .x12 = some (BitVec.ofNat 64 work.base) →
    s.regs.get? .x13 = some (BitVec.ofNat 64 output.base) →
    s.regs.get? .x2 = some (BitVec.ofNat 64 (work.base + work.len)) →
    s.regs.get? .x1 = some ra → ra.toNat % 4 = 0 → disjoint ⟨ra.toNat, 4⟩ codeR →
    bytesAt s input.base x.length = x.map (some ·.toBitVec) →
    input.len = x.length → y.length ≤ output.len → space x.length ≤ work.len → work.base % 8 = 0 →
    (∀ r ∈ [input, output, work, codeR], r.inRAM) → [input, output, work, codeR].Pairwise disjoint →
    (∀ i < output.len, (s.mem[output.base + i]?).isSome) → (∀ i < work.len, (s.mem[work.base + i]?).isSome) →
    runsTo s fun s' => s'.regs.get? .PC = some ra ∧
      bytesAt s' output.base y.length = y.map (some ·.toBitVec) ∧
      unchangedOutside s s' [output, work] ∧ calleeSavedKept s s' ∧ Cfg s'

/-- **The user-facing statement**: `code` implements `f` (through the `Bytes` encodings) with work space
`space n` for inputs of `n ≤ maxLen` bytes. -/
def Implements1 {α β : Type} [Bytes α] [Bytes β] (code : List (BitVec 32)) (f : α → β) (space : Nat → Nat)
    (maxLen : Nat := 2 ^ 20) : Prop :=
  Implements1With enc enc code f space maxLen

/-- raw byte lists in and out (the identity encoding `encRaw`) -/
def Implements1Raw (code : List (BitVec 32)) (f : List UInt8 → List UInt8) (space : Nat → Nat)
    (maxLen : Nat := 2 ^ 20) : Prop :=
  Implements1With encRaw encRaw code f space maxLen

end Proven
