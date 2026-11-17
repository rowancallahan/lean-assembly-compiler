import Nano.InlR
import Nano.WpSpill
open Proven Proven.WA Proven.Mach Proven.Mach.Riscv
namespace Nano.IR
open Nano.IP
def probeC (N : Nat) (p : Mach.BStmt) : Nat × Bool :=
  let spl := List.range N
  let sp := fun j => spl.contains j
  let c := IR.Code.seq (initL sp (List.range N)) (irB sp [0,3] [2] p)
  match colorB N [0,3] [2] p spl 0 with
  | some g => let f := fB (tblG (tabulate g 4096)); let cm := IR.dropMov (c.map f)
     ((rvwF.toWide.W scB cm).length, rvwF.toWide.wf scB cm)
  | none => (0, false)
set_option maxHeartbeats 0 in
wp_compileS inlQ reflect_only max 1048576
  invariant fun (ob : Array Nat) (src : ByteArray) (i w cs cp rem : Nat) =>
    ob.size = 327680 ∧ i ≤ src.size ∧ src.size ≤ 1048576 ∧ w + (src.size - i) * 1048576 + rem ≤ 2 ^ 41 ∧
      cs ≤ w ∧ cp + rem ≤ 2 ^ 44
  measure fun (_ob : Array Nat) (src : ByteArray) (i _w _cs _cp rem : Nat) => (src.size - i) * 1048576 + rem
  invariant fun (out : Array UInt8) (_ob : Array Nat) (t ls len : Nat) =>
    out.size = len ∧ t ≤ len ∧ ls < 2 ^ 43 ∧ len < 2097152
  measure fun (_out : Array UInt8) (_ob : Array Nat) (t _ls len : Nat) => len - t
#eval (pgNA inlQ.wa, probeC (pgNA inlQ.wa) (pgProgA inlQ.wa))
