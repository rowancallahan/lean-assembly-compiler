import Nano.InlQ
import Nano.WpSpill
open Proven Proven.WA Proven.Mach Proven.Mach.Riscv
namespace Nano.IP
set_option maxHeartbeats 0 in
wp_compileS inlQ reflect_only max 1048576
  invariant fun (ob : Array Nat) (src : ByteArray) (i ph m w n hi cp rem cs : Nat) =>
    ob.size = 327680 ∧ i ≤ src.size ∧ src.size < 2 ^ 32 ∧ ph ≤ 4 ∧ m < 256 ∧ w ≤ 262136 ∧ n ≤ i ∧ hi < 256 ∧
      cp + rem ≤ 524272 ∧ rem ≤ 262136 ∧ cs ≤ 262136
  measure fun (_ob : Array Nat) (src : ByteArray) (i ph _m _w _n _hi _cp rem _cs : Nat) =>
    (src.size - i) * (5 * 262136 + 5) + 5 * rem + (4 - ph)
  invariant fun (out : Array UInt8) (_ob : Array Nat) (t ls len k : Nat) =>
    out.size = 20 * k + len + 38 ∧ t ≤ 20 * k + len + 38 ∧ ls < 16777216 ∧ len < 262144 ∧ k < 256
  measure fun (_out : Array UInt8) (_ob : Array Nat) (t ls len k : Nat) => 20 * k + len + 38 - t
def probeC (mode : Nat) : Nat × Bool :=
  let N := pgNA inlQ.wa; let p := pgProgA inlQ.wa; let spl := List.range N
  let sp := fun j => spl.contains j
  let c := IR.Code.seq (initL sp (List.range N)) (irB sp [0,3] [2] p)
  match colorB N [0,3] [2] p spl mode with
  | some g => let f := fB (tblG (tabulate g 4096)); let cm := IR.dropMov (c.map f)
     ((rvwF.toWide.W scB cm).length, rvwF.toWide.wf scB cm)
  | none => (0, false)
#eval pgNA inlQ.wa
#eval probeC 0
