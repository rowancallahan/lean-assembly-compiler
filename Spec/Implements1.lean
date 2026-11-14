/- Specification with ONE resource bound (supersedes `Implements` of `Spec/Riscv.lean`): what it means for
RV64 machine code to implement a function `f : α → β` (bytes in, bytes out through `Spec/Encode.lean`)
using at most `space n` bytes of work memory for an input of `n` bytes.  Plain-words explanation of every
clause: `Testing/notes/SPEC.md`.

Calling convention: `a0` = input base, `a1` = input length (bytes), `a2` = work base, `a3` = output base,
`sp` = work base + work length (the TOP of the work block: the code may use the work block as its stack,
growing down from `sp`, and as scratch from `a2` up), `ra` = return address.  The work block is 8-aligned.
Input, output, work block and code are in RAM and pairwise disjoint; output and work block are `Mapped`
(hosting hypothesis).  Inputs are at most `maxLen` bytes (default `2^20`).

Result: the run reaches `ra` (no trap); the first `|enc (f a)|` bytes of the output block are
`enc (f a)`; memory outside those bytes and the work block is unchanged (the input, the rest of the output
block, everything else; present or absent addresses alike); the ABI-preserved integer registers
(`abiSavedKept`: `sp`, `gp`, `tp`, `s0..s11`) are unchanged; `Cfg` holds again (the pinned control state:
privilege, `misa`, `mstatus`, `mcountinhibit`, `minstretcfg`, `pmpcfg`, HTIF, `elp`, `mseccfg`, the PMA
region — equal before and after because `Cfg` fixes their values); for variable-length results
(`retLen = true`) `a1` holds the result length.  NOT stated: the other CSRs (`mscratch`, `mtvec`, `mepc`,
`mcause`, `mie`, `mip`, `satp`, `pmpaddr*`, counters) and the caller-saved registers `ra`, `t0..t6`,
`a0..a7` (the ABI lets a callee clobber them). -/
import Spec.Riscv
import Spec.Encode
open LeanRV64D

namespace Proven

/-- the integer registers the RISC-V psABI requires a callee to preserve: `sp`, `gp`, `tp`, `s0 .. s11` -/
def abiSavedKept (s s' : St) : Prop :=
  ∀ r ∈ [Register.x2, .x3, .x4, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
    s'.regs.get? r = s.regs.get? r

/-- **Hosting hypothesis**: every byte of region `r` is present in the model's memory map (`s.mem` is a
finite map; an absent address faults on access).  The OS / loader that hosts the code provides the output
and work blocks as present memory. -/
def Mapped (s : St) (r : Region) : Prop := ∀ i < r.len, (s.mem[r.base + i]?).isSome

/-- `Implements1` for explicit encodings of the argument and the result -/
def Implements1With {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (code : List (BitVec 32))
    (f : α → β) (space : Nat → Nat) (maxLen : Nat := 2 ^ 20) (retLen : Bool := false) : Prop :=
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
    Mapped s output → Mapped s work →
    runsTo s fun s' => s'.regs.get? .PC = some ra ∧
      bytesAt s' output.base y.length = y.map (some ·.toBitVec) ∧
      unchangedOutside s s' [⟨output.base, y.length⟩, work] ∧ abiSavedKept s s' ∧ Cfg s' ∧
      (retLen = true → s'.regs.get? .x11 = some (BitVec.ofNat 64 y.length))

/-- **The user-facing statement**: `code` implements `f` (through the `Bytes` encodings) with work space
`space n` for inputs of `n ≤ maxLen` bytes. -/
def Implements1 {α β : Type} [Bytes α] [Bytes β] (code : List (BitVec 32)) (f : α → β) (space : Nat → Nat)
    (maxLen : Nat := 2 ^ 20) (retLen : Bool := false) : Prop :=
  Implements1With enc enc code f space maxLen retLen

/-- raw byte lists in and out (the identity encoding `encRaw`) -/
def Implements1Raw (code : List (BitVec 32)) (f : List UInt8 → List UInt8) (space : Nat → Nat)
    (maxLen : Nat := 2 ^ 20) (retLen : Bool := false) : Prop :=
  Implements1With encRaw encRaw code f space maxLen retLen

end Proven
