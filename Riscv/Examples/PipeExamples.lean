/- `compile%` examples: ordinary Lean list functions, their machine code, and the theorem that the code
implements the function on the Sail model.  Failing examples are checked with `#guard_msgs`.
Tested on QEMU and the Sail C emulator by `asm/pipe_test.py` (words emitted by `asm/emit_pipe.lean`). -/
import Compiler.Front.PipeFront

namespace Proven.PipeEx

/-! ## Accepted -/

def revinc5 := compile% fun xs : List UInt8 => ((xs.take 5).map (· + 1)).reverse

/-- the machine-code theorem is about the function as written -/
theorem revinc5_ok : ImplementsPipe revinc5.code (fun xs => ((xs.take 5).map (· + 1)).reverse)
    (XPipe.space revinc5.pipe) := revinc5.implements

def mapsum := compile% fun xs : List UInt8 =>
  (xs.map fun x => if x < 10 then x ^^^ 0x20 else x - 1).foldl (· + ·) 0

theorem mapsum_ok : ImplementsPipe mapsum.code
    (fun xs => [(xs.map fun x => if x < 10 then x ^^^ 0x20 else x - 1).foldl (· + ·) 0]) (XPipe.space mapsum.pipe) :=
  mapsum.ok

def revtake5 := compile% fun xs : List UInt8 => xs.reverse.take 5

def mapsort := compile% fun xs : List UInt8 => (xs.map (· &&& 0x7f)).mergeSort

theorem mapsort_ok : ImplementsPipe mapsort.code (fun xs => (xs.map (· &&& 0x7f)).mergeSort)
    (XPipe.space mapsort.pipe) := mapsort.implements

def sort := compile% fun xs : List UInt8 => xs.mergeSort

/-- sum of the bytes as a 64-bit word (8 little-endian output bytes) -/
def sum64 := compile% fun xs : List UInt8 => xs.foldl (fun (a : BitVec 64) x => a + x.toBitVec.setWidth 64) 0

theorem sum64_ok : ImplementsPipe sum64.code
    (fun xs => enc (xs.foldl (fun (a : BitVec 64) x => a + x.toBitVec.setWidth 64) 0)) (XPipe.space sum64.pipe) :=
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

/-! ## Standard-library functions (`Compiler/Front/PipeStd.lean`) -/

/-! ### Reductions: `Bytes` encodings of `Spec/Encode.lean` (`BitVec 64`: 8 bytes, `UInt8`/`Bool`: 1 byte) -/

def len := compile% fun xs : List UInt8 => BitVec.ofNat 64 xs.length

theorem len_ok : ImplementsPipe len.code (fun xs => enc (BitVec.ofNat 64 xs.length)) (XPipe.space len.pipe) := len.ok

def sum8 := compile% fun xs : List UInt8 => xs.sum
def sumNat := compile% fun xs : List UInt8 => BitVec.ofNat 64 (xs.map UInt8.toNat).sum
def countLt := compile% fun xs : List UInt8 => BitVec.ofNat 64 (xs.countP fun x => x < 10)
def count7 := compile% fun xs : List UInt8 => BitVec.ofNat 64 (xs.count 7)
def any3 := compile% fun xs : List UInt8 => xs.any fun x => x == 3
def allRange := compile% fun xs : List UInt8 => xs.all fun x => x ≥ 3 && x != 9
def has5 := compile% fun xs : List UInt8 => xs.contains 5
def empty := compile% fun xs : List UInt8 => xs.isEmpty

theorem any3_ok : ImplementsPipe any3.code (fun xs => enc (xs.any fun x => x == 3)) (XPipe.space any3.pipe) := any3.ok

/-! ### `Option UInt8` results (tag byte, then the value) -/

def head := compile% fun xs : List UInt8 => xs.head?
def last := compile% fun xs : List UInt8 => xs.getLast?
def get3 := compile% fun xs : List UInt8 => xs[3]?
def findBig := compile% fun xs : List UInt8 => xs.find? fun x => x > 100
def min := compile% fun xs : List UInt8 => xs.min?
def max := compile% fun xs : List UInt8 => xs.max?
def idxZero := compile% fun xs : List UInt8 => BitVec.ofNat 64 (xs.findIdx fun x => x == 0)
def idx42 := compile% fun xs : List UInt8 => BitVec.ofNat 64 (xs.idxOf 42)

theorem min_ok : ImplementsPipe min.code (fun xs => enc xs.min?) (XPipe.space min.pipe) := min.ok

/-! ### Data-dependent lengths: the result length is returned in `a1` (`ImplementsPipeLen`) -/

def evens := compile% fun xs : List UInt8 => xs.filter fun x => x &&& 1 == 0
def ascii := compile% fun xs : List UInt8 => xs.takeWhile fun x => x < 128
def unpad := compile% fun xs : List UInt8 => xs.dropWhile fun x => x == 0
def suffix := compile% fun xs : List UInt8 => xs ++ [1, 2, 3]
def prefixRev := compile% fun xs : List UInt8 => [9, 8] ++ xs.reverse
def filtmap := compile% fun xs : List UInt8 => ((xs.filter (· > 3)).map (· + 1)).reverse
def filtsort := compile% fun xs : List UInt8 => (xs.filter (· > 3)).mergeSort
def countBig := compile% fun xs : List UInt8 => BitVec.ofNat 64 ((xs.dropWhile (· < 5)).filter (· > 200)).length

theorem evens_ok : ImplementsPipeLen evens.code (fun xs => xs.filter fun x => x &&& 1 == 0)
    (XPipe.space evens.pipe) := evens.implementsLen

/-! ### `ImplementsMapped` (output block of exactly the result size) where no intermediate is longer -/

theorem revinc5_mapped : ImplementsMapped revinc5.code (fun xs => ((xs.take 5).map (· + 1)).reverse) :=
  revinc5.mapped fun x => by
    simp [revinc5, XPipe.space, XPipe.need, xstageC, XStage.space, XStage.len, stageC, Stage.space, Stage.len,
      CS.clean, cs0, csClean]

theorem revtake5_mapped : ImplementsMapped revtake5.code (fun xs => xs.reverse.take 5) :=
  revtake5.mapped fun x => by
    simp [revtake5, XPipe.space, XPipe.need, xstageC, XStage.space, XStage.len, stageC, Stage.space, Stage.len,
      CS.clean, cs0, csClean]

theorem mapsort_mapped : ImplementsMapped mapsort.code (fun xs => (xs.map (· &&& 0x7f)).mergeSort) :=
  mapsort.mapped fun x => by
    simp [mapsort, XPipe.space, XPipe.need, xstageC, XStage.space, XStage.len, stageC, Stage.space, Stage.len,
      CS.clean, cs0, csClean, List.length_mergeSort]

/-! ## Rejected, with the reason -/

/--
error: compile%: unsupported byte expression (use + - &&& ||| ^^^, if-then-else, literals)
  x✝ % 3
-/
#guard_msgs in
example := compile% fun xs : List UInt8 => xs.filter (· % 3 == 0)

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
  [XStage.base
      (Stage.map
        (BExp.bin BOp.add BExp.x
          (BExp.bin BOp.add BExp.x
            (BExp.bin BOp.add BExp.x
              (BExp.bin BOp.add BExp.x
                (BExp.bin BOp.add BExp.x
                  (BExp.bin BOp.add BExp.x (BExp.bin BOp.add BExp.x (BExp.bin BOp.add BExp.x BExp.x)))))))))]
is rejected by the compiler: assignment to a6: expression needs 9 temporaries (limit 7), or a6 is a block base
-/
#guard_msgs in
example := compile% fun xs : List UInt8 => xs.map fun x => x + (x + (x + (x + (x + (x + (x + (x + x)))))))

/--
error: compile%: the pipe
  [XStage.base (Stage.take (2 ^ 64))]
is rejected by the compiler: take: count 18446744073709551616 does not fit 64 bits
-/
#guard_msgs in
example := compile% fun xs : List UInt8 => xs.take (2 ^ 64)

/--
error: compile%: mergeSort is supported only with the default order `fun a b => a ≤ b`, got
  fun a b => a≥bb
-/
#guard_msgs in
example := compile% fun xs : List UInt8 => xs.mergeSort (fun a b => a ≥ b)

/--
error: compile%: `++` is supported with one constant side only
  xs +++ xs
-/
#guard_msgs in
example := compile% fun xs : List UInt8 => xs ++ xs

/--
error: compile%: unsupported list expression (use map, take, drop, reverse, mergeSort, filter, takeWhile, dropWhile, ++ a constant list, foldl on the argument)
  List.zipWith (fun x1 x2 => x1 + x2) xs xs.reverse
-/
#guard_msgs in
example := compile% fun xs : List UInt8 => List.zipWith (· + ·) xs xs.reverse

end Proven.PipeEx
