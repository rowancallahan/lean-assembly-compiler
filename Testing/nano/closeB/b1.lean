import Legacy.Nano.InlP
import Legacy.Riscv.Frontx.WpCmd
namespace Nano.IP
open Proven.WA
def inlM (xs : ByteArray) : Array Nat := mn (Array.replicate (CAP + 0 * xs.size) 0) xs 0 0 0 0 0 0 0 0 0
set_option maxHeartbeats 0 in
wp_compile inlM max 1048576
  invariant fun (ob : Array Nat) (src : ByteArray) (i ph m w n hi cp rem cs : Nat) =>
    ob.size = 327680 ∧ i ≤ src.size ∧ src.size < 2 ^ 32 ∧ ph ≤ 1 ∧ m < 256 ∧ w ≤ 262136 ∧ n ≤ i ∧ hi < 256 ∧
      cp + rem ≤ 524272 ∧ rem ≤ 262136 ∧ cs ≤ 262136
  measure fun (_ob : Array Nat) (src : ByteArray) (i _ph _m _w _n _hi _cp rem _cs : Nat) =>
    (src.size - i) * 262137 + rem
#check @inlM.compiles
end Nano.IP
