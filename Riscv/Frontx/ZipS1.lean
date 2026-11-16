/- ZipS1: lean-zip inflate helpers marked "possibly unblocked" by NOTES §22 (variable `*`), retried VERBATIM with
`wa_compile` (`Testing/notes/LEANZIP_TARGETS.md` §1, rows 12–19). Source: github.com/rowancallahan/lean-zip @ 7e10583;
each block copied from the file line range named in its comment (doc comments and proofs not copied). Entries are
new names; the existing `kraftE`/`nextCodesE`/`countLengthsE` are in `WaMul.lean`/`WaLeanZip.lean` and not imported here. -/
import Riscv.Frontx.WaCmd

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
-- Zip/Native/Inflate.lean:555@7e10583
def kraftSumFast (count : Array Nat) (maxBits : Nat) : Nat :=
  go count maxBits 0 0
where
  go (count : Array Nat) (maxBits b acc : Nat) : Nat :=
    if h : b ≤ maxBits then
      go count maxBits (b + 1) (acc + count[b]! * (1 <<< (maxBits - b)))
    else acc
  termination_by maxBits + 1 - b
-- Zip/Native/Inflate.lean:587@7e10583
def nextCodesFast (count : Array Nat) (maxBits : Nat) : Array UInt32 :=
  go count maxBits 1 0 (Array.replicate (maxBits + 1) 0)
where
  go (count : Array Nat) (maxBits bits code : Nat) (nc : Array UInt32) : Array UInt32 :=
    if h : bits ≤ maxBits then
      let code := (code + count[bits - 1]!) * 2
      go count maxBits (bits + 1) code (nc.set! bits code.toUInt32)
    else nc
  termination_by maxBits + 1 - bits
end Zip.Native

namespace Proven.WA.ZipS1
open Proven.WA

/-- the histogram of the code lengths `xs` (`maxBits = 15`) -/
def s1countlengths (xs : ByteArray) : Array Nat := Zip.Native.countLengthsFast xs.data 15
wa_compile s1countlengths
  invariant fun (lengths : Array UInt8) (maxBits i : Nat) (count : Array Nat) =>
    i ≤ lengths.size ∧ lengths.size < 2 ^ 32 ∧ maxBits = 15 ∧ count.size = 16
  measure fun (lengths : Array UInt8) (_maxBits i : Nat) (_count : Array Nat) => lengths.size - i

/-- the Kraft sum of `xs` (`maxBits = 15`) -/
def s1kraft (xs : ByteArray) : Nat := Zip.Native.kraftSumFast (Zip.Native.countLengthsFast xs.data 15) 15
wa_compile s1kraft
  invariant fun (lengths : Array UInt8) (maxBits i : Nat) (count : Array Nat) =>
    i ≤ lengths.size ∧ lengths.size < 2 ^ 32 ∧ maxBits = 15 ∧ count.size = 16
  measure fun (lengths : Array UInt8) (_maxBits i : Nat) (_count : Array Nat) => lengths.size - i
  invariant fun (_count : Array Nat) (maxBits b _acc : Nat) => maxBits = 15 ∧ b ≤ 16
  measure fun (_count : Array Nat) (maxBits b _acc : Nat) => maxBits + 1 - b

/-- the first canonical code per length of `xs` (`maxBits = 15`) -/
def s1nextcodes (xs : ByteArray) : Array UInt32 := Zip.Native.nextCodesFast (Zip.Native.countLengthsFast xs.data 15) 15
wa_compile s1nextcodes
  invariant fun (lengths : Array UInt8) (maxBits i : Nat) (count : Array Nat) =>
    i ≤ lengths.size ∧ lengths.size < 2 ^ 32 ∧ maxBits = 15 ∧ count.size = 16
  measure fun (lengths : Array UInt8) (_maxBits i : Nat) (_count : Array Nat) => lengths.size - i
  invariant fun (_count : Array Nat) (maxBits bits _code : Nat) (nc : Array UInt32) =>
    maxBits = 15 ∧ 1 ≤ bits ∧ bits ≤ 16 ∧ nc.size = 16
  measure fun (_count : Array Nat) (maxBits bits _code : Nat) (_nc : Array UInt32) => maxBits + 1 - bits

end Proven.WA.ZipS1
