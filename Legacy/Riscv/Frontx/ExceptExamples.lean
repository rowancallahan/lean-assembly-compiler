/- Round 7: `Except` / `Option` results with compound payloads, `do` / `bind` / early `throw`, structures with a
`ByteArray` field (`BitReader`). Library and book code copied verbatim (provenance per definition). -/
import Legacy.Riscv.Frontx.PairExamples

/-! ## lean-zip-common `BitReader` (github.com/kim-em/lean-zip-common @ 6b7d018, `ZipCommon/BitReader.lean:10-61`),
verbatim (the module docstring dropped) -/

namespace ZipCommon

structure BitReader where
  data : ByteArray
  pos : Nat       -- byte position
  bitOff : Nat    -- bit offset within current byte (0 = LSB)
namespace BitReader

/-- Read a single bit. Returns (bit, updatedReader). -/
def readBit (br : BitReader) : Except String (UInt32 × BitReader) :=
  if br.pos ≥ br.data.size then
    .error "BitReader: unexpected end of input"
  else
    let byte := br.data[br.pos]!
    let bit : UInt32 := ((byte.toUInt32 >>> br.bitOff.toUInt32) &&& 1)
    if br.bitOff + 1 ≥ 8 then
      .ok (bit, { br with pos := br.pos + 1, bitOff := 0 })
    else
      .ok (bit, { br with bitOff := br.bitOff + 1 })

/-- Read `n` bits (n ≤ 25), LSB first. Returns the value as UInt32. -/
def readBits (br : BitReader) (n : Nat) : Except String (UInt32 × BitReader) :=
  go br 0 0 n
where
  go (br : BitReader) (acc : UInt32) (shift : Nat) : Nat → Except String (UInt32 × BitReader)
    | 0 => .ok (acc, br)
    | k + 1 => do
      let (bit, br') ← br.readBit
      go br' (acc ||| (bit <<< shift.toUInt32)) (shift + 1) k

/-- Align to the next byte boundary. Discards remaining bits in the current byte. -/
def alignToByte (br : BitReader) : BitReader :=
  if br.bitOff == 0 then br
  else { br with pos := br.pos + 1, bitOff := 0 }

/-- Read a UInt16 in little-endian from the byte-aligned position. -/
def readUInt16LE (br : BitReader) : Except String (UInt16 × BitReader) :=
  let br := br.alignToByte
  if br.pos + 2 > br.data.size then
    .error "BitReader: unexpected end of input reading UInt16"
  else
    let lo := br.data[br.pos]!.toUInt16
    let hi := br.data[br.pos + 1]!.toUInt16
    .ok (lo ||| (hi <<< 8), { br with pos := br.pos + 2 })

end BitReader
end ZipCommon

/-! ## lean-zip `readBitsFast` (github.com/kim-em/lean-zip @ 7e10583, `Zip/Native/Inflate.lean:28-41`), verbatim -/

namespace Zip.Native

open ZipCommon (BitReader)

def readBitsFast (br : BitReader) (n : Nat) : Except String (UInt32 × BitReader) :=
  go br.pos br.bitOff 0 0 n
where
  go (pos bitOff : Nat) (acc : UInt32) (shift : Nat) :
      Nat → Except String (UInt32 × BitReader)
    | 0 => .ok (acc, { br with pos := pos, bitOff := bitOff })
    | k + 1 =>
      if h : pos ≥ br.data.size then .error "BitReader: unexpected end of input"
      else
        let bit : UInt32 := (((br.data[pos]'(by omega)).toUInt32 >>> bitOff.toUInt32) &&& 1)
        if bitOff + 1 ≥ 8 then
          go (pos + 1) 0 (acc ||| (bit <<< shift.toUInt32)) (shift + 1) k
        else
          go pos (bitOff + 1) (acc ||| (bit <<< shift.toUInt32)) (shift + 1) k

end Zip.Native

namespace Proven.Frontx.Exc
open Proven Proven.Frontx ZipCommon

frontx_compile BitReader.readBit requires fun br => br.bitOff < 8
frontx_compile BitReader.alignToByte
frontx_compile BitReader.readUInt16LE requires fun br => br.pos + 3 < 2 ^ 64
frontx_compile BitReader.readBits.go with fun br _ shift k => br.bitOff < 8 ∧ shift + k < 2 ^ 64
frontx_compile Zip.Native.readBitsFast.go with fun _ _ bitOff _ shift k => bitOff < 8 ∧ shift + k < 2 ^ 64

end Proven.Frontx.Exc

namespace Proven.Frontx.Exc
open Proven Proven.Frontx ZipCommon Proven.Frontx.Book

/-! Entry points (glue, not library code). Non-recursive functions read the reader's `pos`, `bitOff` from the
input (`readBitAt`); the loops start from constants (`from` an `rfl` equation: `readBits br n = go br 0 0 n`). -/

def readBitAt (xs : ByteArray) (i : Nat) : Except String (UInt32 × BitReader) :=
  BitReader.readBit ⟨xs, (byteAt xs i &&& 31).toNat, (byteAt xs i >>> 5).toNat⟩
frontx_compile readBitAt requires fun _ i => i + 8 < 2 ^ 64
def readBitE (xs : ByteArray) : Except String (UInt32 × BitReader) := readBitAt xs 0
frontx_entry readBitE
frontx_implements_bytes readBitE

def readBitsE (xs : ByteArray) : Except String (UInt32 × BitReader) := BitReader.readBits ⟨xs, 1, 3⟩ 20
theorem readBitsE_eq (xs : ByteArray) : readBitsE xs = BitReader.readBits.go ⟨xs, 1, 3⟩ 0 0 20 := rfl
frontx_entry readBitsE from readBitsE_eq
frontx_implements_bytes readBitsE

def readBits2E (xs : ByteArray) : Except String (UInt32 × BitReader) := BitReader.readBits ⟨xs, 0, 0⟩ 25
theorem readBits2E_eq (xs : ByteArray) : readBits2E xs = BitReader.readBits.go ⟨xs, 0, 0⟩ 0 0 25 := rfl
frontx_entry readBits2E from readBits2E_eq
frontx_implements_bytes readBits2E

def readBitsFastE (xs : ByteArray) : Except String (UInt32 × BitReader) := Zip.Native.readBitsFast ⟨xs, 1, 3⟩ 20
theorem readBitsFastE_eq (xs : ByteArray) :
    readBitsFastE xs = Zip.Native.readBitsFast.go ⟨xs, 1, 3⟩ 1 3 0 0 20 := rfl
frontx_entry readBitsFastE from readBitsFastE_eq
frontx_implements_bytes readBitsFastE

def alignAt (xs : ByteArray) (i : Nat) : BitReader :=
  BitReader.alignToByte ⟨xs, (byteAt xs i).toNat % 32, (byteAt xs i).toNat / 32⟩
frontx_compile alignAt requires fun _ i => i + 8 < 2 ^ 64
def alignE (xs : ByteArray) : BitReader := alignAt xs 0
frontx_entry alignE
frontx_implements_bytes alignE

/-- `pos` from the input, `bitOff` 0 resp. 5 (`alignToByte` moves to the next byte) -/
def readUInt16LEAt (xs : ByteArray) (i : Nat) : Except String (UInt16 × BitReader) :=
  BitReader.readUInt16LE ⟨xs, (byteAt xs i).toNat % 32, 0⟩
def readUInt16LE5At (xs : ByteArray) (i : Nat) : Except String (UInt16 × BitReader) :=
  BitReader.readUInt16LE ⟨xs, (byteAt xs i).toNat % 32, 5⟩
frontx_compile readUInt16LEAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile readUInt16LE5At requires fun _ i => i + 8 < 2 ^ 64
def readUInt16LEE (xs : ByteArray) : Except String (UInt16 × BitReader) := readUInt16LEAt xs 0
frontx_entry readUInt16LEE
frontx_implements_bytes readUInt16LEE
def readUInt16LE5E (xs : ByteArray) : Except String (UInt16 × BitReader) := readUInt16LE5At xs 0
frontx_entry readUInt16LE5E
frontx_implements_bytes readUInt16LE5E

/-! ## `do` with an early `throw` (this repo): one bit from an aligned reader -/

def readAligned (br : BitReader) : Except String (UInt32 × BitReader) := do
  if br.bitOff ≠ 0 then throw "unaligned"
  let (b, br) ← br.readBit
  return (b + 1, br)
frontx_compile readAligned requires fun br => br.bitOff < 8

def readAlignedAt (xs : ByteArray) (i : Nat) : Except String (UInt32 × BitReader) :=
  readAligned ⟨xs, (byteAt xs i).toNat % 32, (byteAt xs i).toNat / 32⟩
frontx_compile readAlignedAt requires fun _ i => i + 8 < 2 ^ 64
def readAlignedE (xs : ByteArray) : Except String (UInt32 × BitReader) := readAlignedAt xs 0
frontx_entry readAlignedE
frontx_implements_bytes readAlignedE

end Proven.Frontx.Exc
