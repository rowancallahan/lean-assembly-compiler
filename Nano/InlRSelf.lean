/- The inliner's paged stage `Q` (`Nano.IR.inlQ`, Nano/InlR.lean) compiled by OUR paged front end (`wp_compileS`,
spill-first register choice), branch nano-final. -/
import Nano.InlR
import Nano.PgStage
import Riscv.Frontx.WpBridge
import Nano.WpSpill

namespace Nano.IR
open Proven Proven.WA Proven.WP Proven.Top.Alloc Nano.IP

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
wp_compileS inlQ max 1048576
  invariant fun (ob : Array UInt64) (src : ByteArray) (i w cs cp rem : Nat) =>
    ob.size = 327680 ∧ i ≤ src.size ∧ src.size ≤ 1048576 ∧ w + (src.size - i) * 1048576 + rem ≤ 2 ^ 41 ∧
      cs ≤ w ∧ cp + rem ≤ 2 ^ 45
  measure fun (_ob : Array UInt64) (src : ByteArray) (i _w _cs _cp rem : Nat) => (src.size - i) * 1048576 + rem
  invariant fun (out : Array UInt8) (_ob : Array UInt64) (t ls len : Nat) =>
    out.size = len ∧ t ≤ len ∧ ls < 2 ^ 40 ∧ len < 1048576
  measure fun (_out : Array UInt8) (_ob : Array UInt64) (t _ls len : Nat) => len - t



#print axioms inlQ.pgGood
#print axioms inlQ.computes
end Nano.IR
