/- `compile%` examples: ordinary Lean list functions, their machine code, and the theorem that the code
implements the function on the Sail model.  Failing examples are checked with `#guard_msgs`.
Tested on QEMU and the Sail C emulator by `asm/pipe_test.py` (words emitted by `asm/emit_pipe.lean`). -/
import Compiler.Front.PipeFront

namespace Proven.PipeEx

/-! ## Accepted -/

def revinc5 := compile% fun xs : List UInt8 => ((xs.take 5).map (· + 1)).reverse

/-- the machine-code theorem is about the function as written -/
theorem revinc5_ok : ImplementsPipe revinc5.code (fun xs => ((xs.take 5).map (· + 1)).reverse)
    (Pipe.space revinc5.pipe) := revinc5.implements

def mapsum := compile% fun xs : List UInt8 =>
  (xs.map fun x => if x < 10 then x ^^^ 0x20 else x - 1).foldl (· + ·) 0

theorem mapsum_ok : ImplementsPipe mapsum.code
    (fun xs => [(xs.map fun x => if x < 10 then x ^^^ 0x20 else x - 1).foldl (· + ·) 0]) (Pipe.space mapsum.pipe) :=
  mapsum.ok

def revtake5 := compile% fun xs : List UInt8 => xs.reverse.take 5

def mapsort := compile% fun xs : List UInt8 => (xs.map (· &&& 0x7f)).mergeSort

theorem mapsort_ok : ImplementsPipe mapsort.code (fun xs => (xs.map (· &&& 0x7f)).mergeSort)
    (Pipe.space mapsort.pipe) := mapsort.implements

def sort := compile% fun xs : List UInt8 => xs.mergeSort

/-- sum of the bytes as a 64-bit word (8 little-endian output bytes) -/
def sum64 := compile% fun xs : List UInt8 => xs.foldl (fun (a : BitVec 64) x => a + x.toBitVec.setWidth 64) 0

theorem sum64_ok : ImplementsPipe sum64.code
    (fun xs => leBytes (xs.foldl (fun (a : BitVec 64) x => a + x.toBitVec.setWidth 64) 0) 8) (Pipe.space sum64.pipe) :=
  sum64.ok

/-- a 64-bit hash: `a := (a ^ x) + (a << 5)`, from 5381 -/
def hash64 := compile% fun xs : List UInt8 =>
  xs.foldl (fun (a : BitVec 64) x => (a ^^^ x.toBitVec.setWidth 64) + (a <<< ((5 : BitVec 64).toNat % 64))) 5381

/-- descending sort, drop the two largest, replace 3 by 0 (in-place reversal of the sorted buffer) -/
def sortdesc := compile% fun xs : List UInt8 =>
  (xs.mergeSort.reverse.drop 2).map fun x => if x ≠ 3 then x else 0

/-- elements 1..3 of the sorted list -/
def mid := compile% fun xs : List UInt8 => (xs.mergeSort.drop 1).take 3

/-- a fold over a reversed window of the sorted buffer -/
def foldsorted := compile% fun xs : List UInt8 =>
  (xs.mergeSort.reverse.take 4).foldl (fun a x => (a - x) ^^^ 1) 7

/-- two sorts, with `drop`, `reverse` and `map` in between -/
def twosort := compile% fun xs : List UInt8 =>
  (((xs.drop 3).mergeSort.take 10).reverse.map fun x => if x ≥ 0x80 then x ||| 1 else 0xff - x).mergeSort

/-! ### `ImplementsMapped` (output block of exactly the result size) where no intermediate is longer -/

theorem revinc5_mapped : ImplementsMapped revinc5.code (fun xs => ((xs.take 5).map (· + 1)).reverse) :=
  revinc5.mapped_view (by decide)

theorem revtake5_mapped : ImplementsMapped revtake5.code (fun xs => xs.reverse.take 5) :=
  revtake5.mapped_view (by decide)

theorem mapsort_mapped : ImplementsMapped mapsort.code (fun xs => (xs.map (· &&& 0x7f)).mergeSort) :=
  mapsort.mapped fun n => by
    simp [mapsort, Pipe.space, Pipe.need, Pipe.len, stageC, Stage.space, Stage.len, CS.clean, cs0, csClean]

/-! ### The syntactic success condition holds for these pipes -/

example : Pipe.ok revinc5.pipe = true := by decide
example : Pipe.ok mapsum.pipe = true := by decide
example : Pipe.ok hash64.pipe = true := by decide
example : Pipe.ok twosort.pipe = true := by decide

/-! ## Rejected, with the reason -/

/--
error: compile%: unsupported list expression (use map, take, drop, reverse, mergeSort, foldl on the argument)
  List.filter (fun x => x>b3) xs
-/
#guard_msgs in
example := compile% fun xs : List UInt8 => xs.filter (· > 3)

/--
error: compile%: unsupported byte expression (use + - &&& ||| ^^^, if-then-else, literals)
  x✝ * 3
-/
#guard_msgs in
example := compile% fun xs : List UInt8 => xs.map (· * 3)

/--
error: compile%: the take count must not depend on the input:
  xs.length
-/
#guard_msgs in
example := compile% fun xs : List UInt8 => xs.take xs.length

/--
error: compile%: the pipe
  [Stage.map
      (BExp.bin BOp.add BExp.x
        (BExp.bin BOp.add BExp.x
          (BExp.bin BOp.add BExp.x
            (BExp.bin BOp.add BExp.x
              (BExp.bin BOp.add BExp.x
                (BExp.bin BOp.add BExp.x (BExp.bin BOp.add BExp.x (BExp.bin BOp.add BExp.x BExp.x))))))))]
is rejected by compileP: assignment to a6: expression needs 9 temporaries (limit 7), or a6 is a block base
-/
#guard_msgs in
example := compile% fun xs : List UInt8 => xs.map fun x => x + (x + (x + (x + (x + (x + (x + (x + x)))))))

/--
error: compile%: the pipe
  [Stage.take (2 ^ 64)]
is rejected by compileP: take: count 18446744073709551616 does not fit 64 bits
-/
#guard_msgs in
example := compile% fun xs : List UInt8 => xs.take (2 ^ 64)

/--
error: compile%: mergeSort is supported only with the default order `fun a b => a ≤ b`, got
  fun a b => a≥bb
-/
#guard_msgs in
example := compile% fun xs : List UInt8 => xs.mergeSort (fun a b => a ≥ b)

end Proven.PipeEx
