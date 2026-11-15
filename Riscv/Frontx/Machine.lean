/- Generated programs on the machine, in the single-bound form `Implements1` (`Spec/Implements1.lean`).

For each entry point `g : ByteArray → T` (`g xs := f xs constants…`, `f` compiled by `frontx_compile`):
`frontx_entry g` adds the program `g.prog` and its source-level theorem `g.exec`; `frontx_implements g` adds
`g.code` (through the optimised entry point `compBFO`, `Riscv/Back/Implements1Opt.lean`) and

  `g.implements1 : Implements1With (fun xs => xs.data.toList) Res.enc g.code g (fun _ => 8 * (g.slots + 1) + 7)`.

Nothing in this file is proved by hand. -/
import Riscv.Frontx.Impl1
import Riscv.Frontx.ForExamples
import Riscv.Frontx.ListExamples
import Riscv.Frontx.ListOutExamples

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

end Proven.Frontx.Ex
