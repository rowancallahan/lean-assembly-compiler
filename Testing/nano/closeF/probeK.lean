import Nano.InlQ
import Legacy.Nano.WpSpill
open Proven Proven.WA Proven.Mach Proven.Mach.Riscv
namespace Nano.IP
def probeC (N : Nat) (p : Mach.BStmt) : Nat × Bool :=
  let spl := List.range N
  let sp := fun j => spl.contains j
  let c := IR.Code.seq (initL sp (List.range N)) (irB sp [0,3] [2] p)
  match colorB N [0,3] [2] p spl 0 with
  | some g => let f := fB (tblG (tabulate g 4096)); let cm := IR.dropMov (c.map f)
     ((rvwF.toWide.W scB cm).length, rvwF.toWide.wf scB cm)
  | none => (0, false)
-- A: no array access in loop
def fA (ob : Array Nat) (t n : Nat) : Array Nat := if t < n then fA ob (t + 1) n else ob
termination_by n - t
def gA (xs : ByteArray) : Array Nat := fA (Array.replicate (CAP + 0 * xs.size) 0) 0 xs.size
-- B: one read
def fB' (ob : Array Nat) (t n a : Nat) : Array Nat := if t < n then fB' ob (t + 1) n ob[t]! else ob
termination_by n - t
def gB (xs : ByteArray) : Array Nat := fB' (Array.replicate (CAP + 0 * xs.size) 0) 0 xs.size 0
-- C: one set!
def fC (ob : Array Nat) (t n : Nat) : Array Nat := if t < n then fC (ob.set! t t) (t + 1) n else ob
termination_by n - t
def gC (xs : ByteArray) : Array Nat := fC (Array.replicate (CAP + 0 * xs.size) 0) 0 xs.size
-- D: src read
def fD (ob : Array Nat) (src : ByteArray) (t a : Nat) : Array Nat :=
  if t < src.size then fD ob src (t + 1) (src.get! t).toNat else ob
termination_by src.size - t
def gD (xs : ByteArray) : Array Nat := fD (Array.replicate (CAP + 0 * xs.size) 0) xs 0 0
-- E: 10 if tests
def fE (ob : Array Nat) (t n a b : Nat) : Array Nat := if t < n then fE ob (t + 1) n
  (if a == 1 then 3 else if a == 2 then 4 else if a == 3 then 5 else if a == 4 then 7 else if a == 5 then 9 else 0)
  (if b == 1 then 3 else if b == 2 then 4 else if b == 3 then 5 else if b == 4 then 7 else if b == 5 then 9 else 0) else ob
termination_by n - t
def gE (xs : ByteArray) : Array Nat := fE (Array.replicate (CAP + 0 * xs.size) 0) 0 xs.size 0 0
def fF (ob : Array Nat) (t n a b : Nat) : Array Nat := if t < n then
  (if a == 1 then fF ob (t + 1) n 3 b else if a == 2 then fF ob (t + 1) n 4 b else if a == 3 then fF ob (t + 1) n 5 b
   else if a == 4 then fF ob (t + 1) n 7 b else if a == 5 then fF ob (t + 1) n 9 b else fF ob (t + 1) n 0 b) else ob
termination_by n - t
def gF (xs : ByteArray) : Array Nat := fF (Array.replicate (CAP + 0 * xs.size) 0) 0 xs.size 0 0
def fG (ob : Array Nat) (t n a b : Nat) : Array Nat := if t < n then fG ob (t + 1) n (a + 3) (b - a) else ob
termination_by n - t
def gG (xs : ByteArray) : Array Nat := fG (Array.replicate (CAP + 0 * xs.size) 0) 0 xs.size 0 0
def fH (ob : Array Nat) (t n a b : Nat) : Array Nat := if t < n then fH ob (t + 1) n (if a < b then a else b) b else ob
termination_by n - t
def gH (xs : ByteArray) : Array Nat := fH (Array.replicate (CAP + 0 * xs.size) 0) 0 xs.size 0 0
set_option maxHeartbeats 0
wp_compileS gF reflect_only max 1048576 invariant fun (ob : Array Nat) (t n a b : Nat) => ob.size = 327680 ∧ t ≤ n measure fun (_ob : Array Nat) (t n _a _b : Nat) => n - t
wp_compileS gG reflect_only max 1048576 invariant fun (ob : Array Nat) (t n a b : Nat) => ob.size = 327680 ∧ t ≤ n ∧ a < 2^40 measure fun (_ob : Array Nat) (t n _a _b : Nat) => n - t
wp_compileS gH reflect_only max 1048576 invariant fun (ob : Array Nat) (t n a b : Nat) => ob.size = 327680 ∧ t ≤ n measure fun (_ob : Array Nat) (t n _a _b : Nat) => n - t
wp_compileS gA reflect_only max 1048576 invariant fun (ob : Array Nat) (t n : Nat) => ob.size = 327680 ∧ t ≤ n measure fun (_ob : Array Nat) (t n : Nat) => n - t
wp_compileS gB reflect_only max 1048576 invariant fun (ob : Array Nat) (t n a : Nat) => ob.size = 327680 ∧ t ≤ n measure fun (_ob : Array Nat) (t n _a : Nat) => n - t
wp_compileS gC reflect_only max 1048576 invariant fun (ob : Array Nat) (t n : Nat) => ob.size = 327680 ∧ t ≤ n measure fun (_ob : Array Nat) (t n : Nat) => n - t
wp_compileS gD reflect_only max 1048576 invariant fun (ob : Array Nat) (src : ByteArray) (t a : Nat) => ob.size = 327680 ∧ t ≤ src.size measure fun (_ob : Array Nat) (src : ByteArray) (t _a : Nat) => src.size - t
wp_compileS gE reflect_only max 1048576 invariant fun (ob : Array Nat) (t n a b : Nat) => ob.size = 327680 ∧ t ≤ n measure fun (_ob : Array Nat) (t n _a _b : Nat) => n - t
#eval (probeC (pgNA gF.wa) (pgProgA gF.wa), probeC (pgNA gG.wa) (pgProgA gG.wa), probeC (pgNA gH.wa) (pgProgA gH.wa))
#eval (probeC (pgNA gA.wa) (pgProgA gA.wa), probeC (pgNA gB.wa) (pgProgA gB.wa), probeC (pgNA gC.wa) (pgProgA gC.wa), probeC (pgNA gD.wa) (pgProgA gD.wa), probeC (pgNA gE.wa) (pgProgA gE.wa))
