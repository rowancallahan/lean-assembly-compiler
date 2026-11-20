/- Multiply, divide, remainder, shift by a variable in the word-array front end (NOTES section 22): library code
compiled verbatim by `wa_compile` (`WaCmd.lean`), through `BStmt.mop` (the RISC-V M extension).

Sources, copied VERBATIM with `file:line` per block (doc comments and proofs not copied):
* lean-zip github.com/rowancallahan/lean-zip @ 7e10583 (`countLengthsFast` is in `WaLeanZip.lean`);
* Lean 4 v4.29.0 core (`Nat.gcd`, `Nat.lcm` are used directly from core, not copied).
The entry points (`…E : ByteArray → β`) fix the other arguments; they are not library code. -/
import Riscv.Frontx.WaLeanZip

set_option backward.isDefEq.respectTransparency false
namespace Zip.Native
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

namespace Proven.WA.LeanZip
open Proven.WA

/-- the Kraft sum of the code lengths `xs` (as `validateLengths` computes it, `maxBits = 15`) -/
def kraftE (xs : ByteArray) : Nat := Zip.Native.kraftSumFast (Zip.Native.countLengthsFast xs.data 15) 15
wa_compile kraftE
  invariant fun (lengths : Array UInt8) (maxBits i : Nat) (count : Array Nat) =>
    i ≤ lengths.size ∧ lengths.size < 2 ^ 32 ∧ maxBits = 15 ∧ count.size = 16
  measure fun (lengths : Array UInt8) (_maxBits i : Nat) (_count : Array Nat) => lengths.size - i
  invariant fun (_count : Array Nat) (maxBits b _acc : Nat) => maxBits = 15 ∧ b ≤ 16
  measure fun (_count : Array Nat) (maxBits b _acc : Nat) => maxBits + 1 - b

end Proven.WA.LeanZip

namespace Proven.WA.LeanZip
open Proven.WA

/-- the first canonical code per length of the code lengths `xs` (`maxBits = 15`), as `buildTable` computes it -/
def nextCodesE (xs : ByteArray) : Array UInt32 := Zip.Native.nextCodesFast (Zip.Native.countLengthsFast xs.data 15) 15
wa_compile nextCodesE
  invariant fun (lengths : Array UInt8) (maxBits i : Nat) (count : Array Nat) =>
    i ≤ lengths.size ∧ lengths.size < 2 ^ 32 ∧ maxBits = 15 ∧ count.size = 16
  measure fun (lengths : Array UInt8) (_maxBits i : Nat) (_count : Array Nat) => lengths.size - i
  invariant fun (_count : Array Nat) (maxBits bits _code : Nat) (nc : Array UInt32) =>
    maxBits = 15 ∧ 1 ≤ bits ∧ bits ≤ 16 ∧ nc.size = 16
  measure fun (_count : Array Nat) (maxBits bits _code : Nat) (_nc : Array UInt32) => maxBits + 1 - bits

end Proven.WA.LeanZip

namespace WaGlue
/-- a little-endian 32-bit number from bytes `o .. o + 3` (entry glue, outside `Proven` so that `wa_compile`
unfolds it) -/
def rd32 (xs : ByteArray) (o : Nat) : Nat :=
  xs[o]!.toNat + 256 * xs[o + 1]!.toNat + 65536 * xs[o + 2]!.toNat + 16777216 * xs[o + 3]!.toNat
end WaGlue

namespace Proven.WA.Core
open Proven.WA WaGlue

/-- core `Nat.gcd` (`Init/Data/Nat/Gcd.lean:35`, Lean 4 v4.29.0) of two 32-bit numbers -/
def gcdE (xs : ByteArray) : Nat := Nat.gcd (rd32 xs 0) (rd32 xs 4)
wa_compile gcdE
  invariant fun (m n : Nat) => m < 2 ^ 32 ∧ n < 2 ^ 32
  measure fun (m _n : Nat) => m

end Proven.WA.Core

namespace WaGlue
/-- little-endian 8 bytes from `o` as a `UInt64` (entry glue) -/
def rd64 (xs : ByteArray) (o : Nat) : UInt64 :=
  xs[o]!.toUInt64 ||| xs[o + 1]!.toUInt64 <<< 8 ||| xs[o + 2]!.toUInt64 <<< 16 ||| xs[o + 3]!.toUInt64 <<< 24 |||
    xs[o + 4]!.toUInt64 <<< 32 ||| xs[o + 5]!.toUInt64 <<< 40 ||| xs[o + 6]!.toUInt64 <<< 48 |||
    xs[o + 7]!.toUInt64 <<< 56
/-- little-endian 4 bytes from `o` as a `UInt32` -/
def rd32u (xs : ByteArray) (o : Nat) : UInt32 :=
  xs[o]!.toUInt32 ||| xs[o + 1]!.toUInt32 <<< 8 ||| xs[o + 2]!.toUInt32 <<< 16 ||| xs[o + 3]!.toUInt32 <<< 24
end WaGlue

namespace Proven.WA.Ops
open Proven.WA WaGlue

/-- every variable operation on `UInt64` (operands: words at bytes 0 and 8; `b = 0` when the input is short) -/
def ops64E (xs : ByteArray) : UInt64 :=
  let a := rd64 xs 0
  let b := rd64 xs 8
  (a * b) ^^^ (a / b) ^^^ (a % b) ^^^ (a <<< b) ^^^ (a >>> b)
wa_compile ops64E

/-- the same on `UInt32` (the results are masked to 32 bits) -/
def ops32E (xs : ByteArray) : UInt32 :=
  let a := rd32u xs 0
  let b := rd32u xs 4
  (a * b) ^^^ (a / b) ^^^ (a % b) ^^^ (a <<< b) ^^^ (a >>> b)
wa_compile ops32E

/-- the same on `Nat` (32-bit operands; the shift amount below 64) -/
def opsNE (xs : ByteArray) : Nat :=
  let a := rd32 xs 0
  let b := rd32 xs 4
  (a * b) ^^^ (a / b) ^^^ (a % b) ^^^ (a <<< (b % 64)) ^^^ (a >>> b)
wa_compile opsNE

end Proven.WA.Ops

