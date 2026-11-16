/- Paged front end (NOTES section 35): lean-zip ARR rows on the paged back end through `wp_compile` (`WpCmd.lean`).
The lean-zip definitions are those copied VERBATIM in `WaLeanZip.lean` / `WaMul.lean` (github.com/rowancallahan/lean-zip
@ 7e10583, `file:line` there); the entry points fix the other arguments. -/
import Riscv.Frontx.WpCmd
import Riscv.Frontx.WaMul

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

end Proven.WA.LeanZip3
