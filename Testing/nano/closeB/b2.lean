import Nano.InlP
import Riscv.Frontx.WpCmd
namespace Nano.IP
open Proven.WA
def inlE (xs : ByteArray) : ByteArray :=
  let ob := Array.replicate (CAP + 0 * xs.size) 0
  let ls := ob[HD]! / 16777216 % 16777216
  let le := ob[HD]! % 16777216
  em (xs.extract 0 0) ob 0 ls (le - 1 - ls) (if le == 0 then 0 else ob[BASE + (le - 1)]! % 256)
set_option maxHeartbeats 0 in
wp_compile inlE max 1048576
  invariant fun (out : ByteArray) (_ob : Array Nat) (t ls len k : Nat) =>
    out.size = t ∧ t ≤ 20 * k + len + 38 ∧ ls < 16777216 ∧ len < 16777216 ∧ k < 256
  measure fun (_out : ByteArray) (_ob : Array Nat) (t ls len k : Nat) => 20 * k + len + 38 - t
#check @inlE.compiles
end Nano.IP
