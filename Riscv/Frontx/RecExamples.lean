/- Non-tail recursion with real calls (`frontx_rec`, `RecCmd.lean`): the book's `NonTail.sum` and `NonTail.length`
(definitions in `ListExamples.lean`, verbatim, read through `frontx_view`), compiled WITHOUT the accumulator trick,
and a tree recursion with two calls (`fib`).  Each entry point has a generated `Implements1` theorem
(`g.implements1`, plain back end `compP` with stack frames; space `frame * (n + 1) + 32`). -/
import Riscv.Frontx.ListExamples
import Riscv.Frontx.RecCmd

namespace Proven.Frontx.BookList
open Proven Proven.Frontx

namespace NonTail
frontx_rec sum.view from sum.view.eq measure fun B i => B.size - i
frontx_rec length.view from length.view.eq measure fun B i => B.size - i
end NonTail

def nonTailSumRec (xs : ByteArray) : Nat := NonTail.sum (xs.data.toList.map UInt8.toNat)
theorem nonTailSumRec_eq (xs : ByteArray) : nonTailSumRec xs = NonTail.sum.view xs 0 := rfl
frontx_rec_entry nonTailSumRec from nonTailSumRec_eq

def nonTailLengthRec (xs : ByteArray) : Nat := NonTail.length xs.data.toList
theorem nonTailLengthRec_eq (xs : ByteArray) : nonTailLengthRec xs = NonTail.length.view xs 0 := rfl
frontx_rec_entry nonTailLengthRec from nonTailLengthRec_eq

end Proven.Frontx.BookList

namespace Proven.Frontx.RecEx
open Proven Proven.Frontx

/-- two non-tail calls (not from the book: the book has no such `Nat` function) -/
def fib (n : Nat) : Nat := if n < 2 then n else fib (n - 1) + fib (n - 2)
frontx_rec fib measure fun n => n

/-- `fib` of the input length -/
def fibLen (xs : ByteArray) : Nat := fib xs.size
frontx_rec_entry fibLen

end Proven.Frontx.RecEx
