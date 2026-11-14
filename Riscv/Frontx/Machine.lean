/- Generated programs on the machine, in the single-bound form `Implements1` (`Spec/Implements1.lean`).

For each entry point `g : ByteArray → T` (`g xs := f xs constants…`, `f` compiled by `frontx_compile`):
`frontx_entry g` adds the program `g.prog` and its source-level theorem `g.exec`; `frontx_implements g` adds
`g.code` (through the standard entry point `rvF.compBF`) and

  `g.implements1 : Implements1With (fun xs => xs.data.toList) Res.enc g.code g (fun _ => 8 * (g.slots + 1) + 7)`.

Nothing in this file is proved by hand. -/
import Riscv.Frontx.Impl1
import Riscv.Frontx.ForExamples

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

end Proven.Frontx.Ex
