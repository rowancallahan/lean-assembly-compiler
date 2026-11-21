/- Paged front end (NOTES section 35): lean-zip ARR rows on the paged back end through `wp_compile` (`WpCmd.lean`).
The lean-zip definitions are those copied VERBATIM in `WaLeanZip.lean` / `WaMul.lean` (github.com/rowancallahan/lean-zip
@ 7e10583, `file:line` there); the entry points fix the other arguments. -/
import Legacy.Riscv.Frontx.WpCmd
import Legacy.Riscv.Frontx.WaMul

namespace Zip.Native.HuffTree
-- Zip/Native/Inflate.lean:144@7e10583
def fastBits : Nat := 11
-- Zip/Native/InflateTreeFree.lean:94@7e10583
def countLongCodes (count : Array Nat) (maxBits : Nat) : Nat :=
  go count maxBits (fastBits + 1) 0
where
  go (count : Array Nat) (maxBits len acc : Nat) : Nat :=
    if len > maxBits then acc
    else go count maxBits (len + 1) (acc + count[len]!)
  termination_by maxBits + 1 - len
end Zip.Native.HuffTree

namespace Huffman.Spec
-- Zip/Spec/Huffman.lean:83@7e10583
def nextCodes (blCount : Array Nat) (maxBits : Nat) : Array Nat :=
  let init := Array.replicate (maxBits + 1) 0
  go init 1 0
where
  go (arr : Array Nat) (bits code : Nat) : Array Nat :=
    if h : bits > maxBits then arr
    else
      let code := (code + blCount[bits - 1]!) * 2
      go (arr.set! bits code) (bits + 1) code
  termination_by maxBits + 1 - bits
end Huffman.Spec

namespace Proven.WA.LeanZip3
open Proven.WA

/-- `kraftSumFast (countLengthsFast xs.data 15) 15` (Inflate.lean:555, :536) -/
def kraftPE (xs : ByteArray) : Nat := Zip.Native.kraftSumFast (Zip.Native.countLengthsFast xs.data 15) 15
wp_compile kraftPE max 1048576
  invariant fun (lengths : Array UInt8) (maxBits i : Nat) (count : Array Nat) =>
    i ≤ lengths.size ∧ lengths.size < 2 ^ 32 ∧ maxBits = 15 ∧ count.size = 16
  measure fun (lengths : Array UInt8) (_maxBits i : Nat) (_count : Array Nat) => lengths.size - i
  invariant fun (_count : Array Nat) (maxBits b _acc : Nat) => maxBits = 15 ∧ b ≤ 16
  measure fun (_count : Array Nat) (maxBits b _acc : Nat) => maxBits + 1 - b

/-- `nextCodesFast (countLengthsFast xs.data 15) 15` (Inflate.lean:587, :536) -/
def nextCodesPE (xs : ByteArray) : Array UInt32 :=
  Zip.Native.nextCodesFast (Zip.Native.countLengthsFast xs.data 15) 15
wp_compile nextCodesPE max 1048576
  invariant fun (lengths : Array UInt8) (maxBits i : Nat) (count : Array Nat) =>
    i ≤ lengths.size ∧ lengths.size < 2 ^ 32 ∧ maxBits = 15 ∧ count.size = 16
  measure fun (lengths : Array UInt8) (_maxBits i : Nat) (_count : Array Nat) => lengths.size - i
  invariant fun (_count : Array Nat) (maxBits bits _code : Nat) (nc : Array UInt32) =>
    maxBits = 15 ∧ 1 ≤ bits ∧ bits ≤ 16 ∧ nc.size = 16
  measure fun (_count : Array Nat) (maxBits bits _code : Nat) (_nc : Array UInt32) => maxBits + 1 - bits

/-- `countLongCodes (countLengthsFast xs.data 15) 15` (InflateTreeFree.lean:94; `fastBits` Inflate.lean:144) -/
def longCodesE (xs : ByteArray) : Nat :=
  Zip.Native.HuffTree.countLongCodes (Zip.Native.countLengthsFast xs.data 15) 15
wp_compile longCodesE max 1048576
  invariant fun (lengths : Array UInt8) (maxBits i : Nat) (count : Array Nat) =>
    i ≤ lengths.size ∧ lengths.size < 2 ^ 32 ∧ maxBits = 15 ∧ count.size = 16
  measure fun (lengths : Array UInt8) (_maxBits i : Nat) (_count : Array Nat) => lengths.size - i
  invariant fun (_count : Array Nat) (maxBits len _acc : Nat) => maxBits = 15 ∧ len ≤ 16
  measure fun (_count : Array Nat) (maxBits len _acc : Nat) => maxBits + 1 - len

/-- the reference `Huffman.Spec.nextCodes` (Huffman.lean:83) of the histogram `countLengthsFast xs.data 15` -/
def specNextCodesE (xs : ByteArray) : Array Nat :=
  Huffman.Spec.nextCodes (Zip.Native.countLengthsFast xs.data 15) 15
wp_compile specNextCodesE max 1048576
  invariant fun (lengths : Array UInt8) (maxBits i : Nat) (count : Array Nat) =>
    i ≤ lengths.size ∧ lengths.size < 2 ^ 32 ∧ maxBits = 15 ∧ count.size = 16
  measure fun (lengths : Array UInt8) (_maxBits i : Nat) (_count : Array Nat) => lengths.size - i
  invariant fun (_blCount : Array Nat) (maxBits : Nat) (arr : Array Nat) (bits _code : Nat) =>
    maxBits = 15 ∧ 1 ≤ bits ∧ bits ≤ 16 ∧ arr.size = 16
  measure fun (_blCount : Array Nat) (maxBits : Nat) (_arr : Array Nat) (bits _code : Nat) => maxBits + 1 - bits

end Proven.WA.LeanZip3
