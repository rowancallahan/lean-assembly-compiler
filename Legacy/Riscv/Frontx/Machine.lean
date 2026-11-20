/- Generated programs on the machine, in the single-bound form `Implements1` (`Spec/Implements1.lean`).

For each entry point `g : ByteArray → T` (`g xs := f xs constants…`, `f` compiled by `frontx_compile`):
`frontx_entry g` adds the program `g.prog` and its source-level theorem `g.exec`; `frontx_implements g` adds
`g.code` (through the optimised entry point `compBFO`, `Riscv/Back/Implements1Opt.lean`) and

  `g.implements1 : Implements1With (fun xs => xs.data.toList) Res.enc g.code g (fun _ => 8 * (g.slots + 1) + 7)`.

Nothing in this file is proved by hand. -/
import Legacy.Riscv.Frontx.Impl1
import Legacy.Riscv.Frontx.ForExamples
import Legacy.Riscv.Frontx.ListExamples
import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.BookExamples
import Legacy.Riscv.Frontx.CallExamples

namespace Proven.Frontx.Ex
open Proven Proven.Frontx

/-- CRC-32 without the final complement (tail recursion over the index, 8 unrolled bit steps per byte) -/
def crcRaw (xs : ByteArray) : UInt32 := crcGo xs 0 0xFFFFFFFF
frontx_entry crcRaw
frontx_implements crcRaw

/-- lean-svg style: `at'`, `b64Digit`, fuel -/
def b64All (xs : ByteArray) : UInt32 := b64Sum xs 0 xs.size 0
frontx_entry b64All
frontx_implements b64All

/-- `for` loop with early return (lean-svg `findByte`): index of the first newline -/
def findNL (xs : ByteArray) : Nat := findByte xs 0 10
frontx_entry findNL
frontx_implements findNL

/-- straight-line code with guarded loads (lean-svg `be32`) -/
def be32At0 (xs : ByteArray) : Nat := be32 xs 0
frontx_entry be32At0
frontx_implements be32At0

/-! ## Book list functions ("Functional Programming in Lean", `ListExamples.lean`) on the input bytes -/

open Proven.Frontx.BookList in
frontx_implements tailSum
open Proven.Frontx.BookList in
frontx_implements nonTailSum
open Proven.Frontx.BookList in
frontx_implements tailLength
open Proven.Frontx.BookList in
frontx_implements bookLength

/-! ## Book functions returning a list (`ListOutExamples.lean`): the bytes in the output block, the length in `a1`

`g.implements1 : Implements1With (fun xs => xs.data.toList) (fun l => l) g.code g (fun _ => 8 * (g.slots + 1) + 7)
(retLen := true)` -/

open Proven.Frontx.BookOut in
frontx_implements_list take5
open Proven.Frontx.BookOut in
frontx_implements_list drop5
open Proven.Frontx.BookOut in
frontx_implements_list matchDrop3
open Proven.Frontx.BookOut in
frontx_implements_list filterAll
open Proven.Frontx.BookOut in
frontx_implements_list incEach
open Proven.Frontx.BookOut in
frontx_implements_list twice

/-! `Option UInt8` results (`head?`, `final?`, `findFirst?`): two bytes, tag and payload (`Res (Option UInt8)`) -/

open Proven.Frontx.BookOut in
frontx_implements headOf
open Proven.Frontx.BookOut in
frontx_implements finalOf
open Proven.Frontx.BookOut in
frontx_implements findFirstGt3

/-! ## Book functions over `Nat` (`BookExamples.lean`): arguments are 16-bit little-endian numbers in the input

`fE xs := fAt xs 0`; `fAt` calls the compiled book function (a sub-program, `Tree.sub`, for the recursive ones). -/

namespace BookNat
open Proven.Frontx.Book
def add1E (xs : ByteArray) := add1At xs 0
frontx_entry add1E
frontx_implements add1E
def maximumE (xs : ByteArray) := maximumAt xs 0
frontx_entry maximumE
frontx_implements maximumE
def isZeroE (xs : ByteArray) := isZeroAt xs 0
frontx_entry isZeroE
frontx_implements isZeroE
def predE (xs : ByteArray) := predAt xs 0
frontx_entry predE
frontx_implements predE
def evenE (xs : ByteArray) := evenAt xs 0
frontx_entry evenE
frontx_implements evenE
def plusE (xs : ByteArray) := plusAt xs 0
frontx_entry plusE
frontx_implements plusE
def timesE (xs : ByteArray) := timesAt xs 0
frontx_entry timesE
frontx_implements timesE
def minusE (xs : ByteArray) := minusAt xs 0
frontx_entry minusE
frontx_implements minusE
def doubleE (xs : ByteArray) := doubleAt xs 0
frontx_entry doubleE
frontx_implements doubleE
def natDoubleE (xs : ByteArray) := natDoubleAt xs 0
frontx_entry natDoubleE
frontx_implements natDoubleE
def tripleE (xs : ByteArray) := tripleAt xs 0
frontx_entry tripleE
frontx_implements tripleE
def quadrupleE (xs : ByteArray) := quadrupleAt xs 0
frontx_entry quadrupleE
frontx_implements quadrupleE
def timesTwelveE (xs : ByteArray) := timesTwelveAt xs 0
frontx_entry timesTwelveE
frontx_implements timesTwelveE
def divE (xs : ByteArray) := divAt xs 0
frontx_entry divE
frontx_implements divE
def halveE (xs : ByteArray) := halveAt xs 0
frontx_entry halveE
frontx_implements halveE
def matchEvenE (xs : ByteArray) := matchEvenAt xs 0
frontx_entry matchEvenE
frontx_implements matchEvenE
def explicitHalveE (xs : ByteArray) := explicitHalveAt xs 0
frontx_entry explicitHalveE
frontx_implements explicitHalveE
end BookNat

/-! ## Nested loops through a call (`CallExamples.lean`) -/

open Proven.Frontx.Calls in
frontx_implements dupCount
open Proven.Frontx.Calls in
frontx_implements sameLen
open Proven.Frontx.BookList in
frontx_implements nonTailLength

end Proven.Frontx.Ex
