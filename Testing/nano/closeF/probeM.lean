import Nano.InlQ
import Nano.WpSpill
open Proven Proven.WA Proven.Mach Proven.Mach.Riscv
namespace Nano.IP
def onlyM (xs : ByteArray) : Array Nat := mnQ (Array.replicate (CAP + 0 * xs.size) 0) xs 0 0 0 0 0 0 0 0 0
def fz (out : Array UInt8) (ob : Array Nat) (t n : Nat) : Array UInt8 :=
  if t < n then fz (out.set! t (UInt8.ofNat ob[t]!)) ob (t + 1) n else out
termination_by n - t
def onlyZ (xs : ByteArray) : Array UInt8 := fz (Array.replicate (xs.size) 0) (Array.replicate (CAP + 0 * xs.size) 0) 0 xs.size
def onlyE (xs : ByteArray) : Array UInt8 :=
  em (Array.replicate (20 * xs.size + 38) 0) (Array.replicate (CAP + 0 * xs.size) 0) 0 0 xs.size xs.size
set_option maxHeartbeats 0 in
wp_compileS onlyM reflect_only max 1048576
  invariant fun (ob : Array Nat) (src : ByteArray) (i ph m w n hi cp rem cs : Nat) =>
    ob.size = 327680 ∧ i ≤ src.size ∧ src.size < 2 ^ 32 ∧ ph ≤ 4 ∧ m < 256 ∧ w ≤ 262136 ∧ n ≤ i ∧ hi < 256 ∧
      cp + rem ≤ 524272 ∧ rem ≤ 262136 ∧ cs ≤ 262136
  measure fun (_ob : Array Nat) (src : ByteArray) (i ph _m _w _n _hi _cp rem _cs : Nat) =>
    (src.size - i) * (5 * 262136 + 5) + 5 * rem + (4 - ph)
set_option maxHeartbeats 0 in
wp_compileS onlyE reflect_only max 1048576
  invariant fun (out : Array UInt8) (_ob : Array Nat) (t ls len k : Nat) =>
    out.size = 20 * k + len + 38 ∧ t ≤ 20 * k + len + 38 ∧ ls < 16777216 ∧ len < 262144 ∧ k < 256
  measure fun (_out : Array UInt8) (_ob : Array Nat) (t ls len k : Nat) => 20 * k + len + 38 - t
set_option maxHeartbeats 0 in
wp_compileS onlyZ reflect_only max 1048576
  invariant fun (out : Array UInt8) (_ob : Array Nat) (t n : Nat) => out.size = n ∧ t ≤ n
  measure fun (_out : Array UInt8) (_ob : Array Nat) (t n : Nat) => n - t
def probeC (N : Nat) (p : Mach.BStmt) : Nat × Bool :=
  let spl := List.range N
  let sp := fun j => spl.contains j
  let c := IR.Code.seq (initL sp (List.range N)) (irB sp [0,3] [2] p)
  match colorB N [0,3] [2] p spl 0 with
  | some g => let f := fB (tblG (tabulate g 4096)); let cm := IR.dropMov (c.map f)
     ((rvwF.toWide.W scB cm).length, rvwF.toWide.wf scB cm)
  | none => (0, false)
#eval (pgNA onlyM.wa, probeC (pgNA onlyM.wa) (pgProgA onlyM.wa))
#eval (pgNA onlyE.wa, probeC (pgNA onlyE.wa) (pgProgA onlyE.wa))
#eval (pgNA onlyZ.wa, probeC (pgNA onlyZ.wa) (pgProgA onlyZ.wa))
