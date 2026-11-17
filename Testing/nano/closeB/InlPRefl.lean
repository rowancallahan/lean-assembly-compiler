import Nano.InlP
import Riscv.Frontx.WpCmd
namespace Nano.IP
open Proven.WA

set_option maxHeartbeats 0 in
wp_compile inlP reflect_only max 1048576
  invariant fun (ob : Array Nat) (src : ByteArray) (i ph m w n hi cp rem cs : Nat) =>
    ob.size = 327680 ∧ i ≤ src.size ∧ src.size < 2 ^ 32 ∧ ph ≤ 1 ∧ m < 256 ∧ w ≤ 262136 ∧ n ≤ i ∧ hi < 256 ∧
      cp + rem ≤ 524272 ∧ rem ≤ 262136 ∧ cs ≤ 262136
  measure fun (_ob : Array Nat) (src : ByteArray) (i _ph _m _w _n _hi _cp rem _cs : Nat) =>
    (src.size - i) * 262137 + rem
  invariant fun (out : ByteArray) (_ob : Array Nat) (t ls len k : Nat) =>
    out.size = t ∧ t ≤ 20 * k + len + 38 ∧ ls < 16777216 ∧ len < 262144 ∧ k < 256
  measure fun (_out : ByteArray) (_ob : Array Nat) (t ls len k : Nat) => 20 * k + len + 38 - t

#print inlP.wa
end Nano.IP
