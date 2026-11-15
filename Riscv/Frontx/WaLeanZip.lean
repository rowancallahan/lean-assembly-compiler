/- Word arrays (NOTES section 20): lean-zip code compiled verbatim by `wa_compile` (`WaCmd.lean`).

Source: github.com/rowancallahan/lean-zip @ 7e10583 (Lean 4.34.0), definitions copied VERBATIM with
`file:line` per block; doc comments and proofs are not copied, nothing else is changed (the same text compiles on
Lean 4.29.0).  The entry points (`…E : ByteArray → β`) fix the other arguments; they are not library code. -/
import Riscv.Frontx.WaCmd

/-! ## CRC-32, table-driven -/

namespace Crc32.Spec
-- Zip/Spec/Crc32.lean:25@7e10583
def POLY : UInt32 := 0xEDB88320
-- Zip/Spec/Crc32.lean:30@7e10583
def crcBit (crc : UInt32) : UInt32 :=
  if crc &&& 1 == 1 then
    (crc >>> 1) ^^^ POLY
  else
    crc >>> 1
-- Zip/Spec/Crc32.lean:78@7e10583
def mkTable : Array UInt32 :=
  Array.ofFn fun (i : Fin 256) =>
    let crc := UInt32.ofNat i.val
    crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (crcBit crc)))))))
-- Zip/Spec/Crc32.lean:84@7e10583
def crcByteTable (table : Array UInt32) (crc : UInt32) (byte : UInt8) : UInt32 :=
  let index := ((crc ^^^ UInt32.ofNat byte.toNat) &&& 0xFF).toNat
  if h : index < table.size then
    (crc >>> 8) ^^^ table[index]
  else
    crc -- unreachable for a 256-entry table
end Crc32.Spec

namespace Crc32.Native
-- Zip/Native/Crc32.lean:14@7e10583
def table : Array UInt32 := Spec.mkTable
-- Zip/Native/Crc32.lean:17@7e10583
def updateBytes (crc : UInt32) (data : ByteArray) : UInt32 :=
  data.data.foldl (Spec.crcByteTable table) crc
-- Zip/Native/Crc32.lean:22@7e10583
def crc32 (init : UInt32 := 0) (data : ByteArray) : UInt32 :=
  let raw := if init == 0 then 0xFFFFFFFF else init ^^^ 0xFFFFFFFF
  let result := updateBytes raw data
  result ^^^ 0xFFFFFFFF
end Crc32.Native

/-! ## Code-length histogram (mutable `Array Nat` in the work block) -/

namespace Zip.Native
-- Zip/Native/Inflate.lean:536@7e10583
def countLengthsFast (lengths : Array UInt8) (maxBits : Nat) : Array Nat :=
  go lengths maxBits 0 (Array.replicate (maxBits + 1) 0)
where
  go (lengths : Array UInt8) (maxBits i : Nat) (count : Array Nat) : Array Nat :=
    if h : i < lengths.size then
      let ln := lengths[i].toNat
      let count := if 0 < ln ∧ ln ≤ maxBits then count.set! ln (count[ln]! + 1) else count
      go lengths maxBits (i + 1) count
    else count
  termination_by lengths.size - i
end Zip.Native

namespace Proven.WA.LeanZip
open Proven.WA

/-- zlib's `crc32(0, xs)` -/
def crc32E (xs : ByteArray) : UInt32 := Crc32.Native.crc32 0 xs
wa_compile crc32E

/-- the running state from `0xFFFFFFFF` (`Crc32.Native.updateBytes`, no final complement) -/
def crcUpdateE (xs : ByteArray) : UInt32 := Crc32.Native.updateBytes 0xFFFFFFFF xs
wa_compile crcUpdateE

/-- the histogram of the input bytes as code lengths, `maxBits = 15` (DEFLATE's literal/length and distance codes):
16 counts, 8 bytes each -/
def countLengthsE (xs : ByteArray) : Array Nat := Zip.Native.countLengthsFast xs.data 15
wa_compile countLengthsE
  invariant fun (lengths : Array UInt8) (maxBits i : Nat) (count : Array Nat) =>
    i ≤ lengths.size ∧ lengths.size < 2 ^ 32 ∧ maxBits = 15 ∧ count.size = 16
  measure fun (lengths : Array UInt8) (_maxBits i : Nat) (_count : Array Nat) => lengths.size - i

/-- the same with `maxBits = 7` (code-length alphabet) -/
def countLengths7E (xs : ByteArray) : Array Nat := Zip.Native.countLengthsFast xs.data 7
wa_compile countLengths7E
  invariant fun (lengths : Array UInt8) (maxBits i : Nat) (count : Array Nat) =>
    i ≤ lengths.size ∧ lengths.size < 2 ^ 32 ∧ maxBits = 7 ∧ count.size = 8
  measure fun (lengths : Array UInt8) (_maxBits i : Nat) (_count : Array Nat) => lengths.size - i

end Proven.WA.LeanZip
