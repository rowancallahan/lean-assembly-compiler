/- `frontx_compile` on ordinary tail-recursive definitions. -/
import Proven.Frontx.Translate

namespace Proven.Frontx.Ex
open Proven Proven.Frontx

def byteSum (xs : ByteArray) (i : Nat) (acc : UInt64) : UInt64 :=
  if h : i < xs.size then byteSum xs (i + 1) (acc + xs[i].toUInt64) else acc
termination_by xs.size - i

frontx_compile byteSum
#print byteSum.tree
#check @byteSum.runs
#check @byteSum.exec
#print axioms byteSum.exec

end Proven.Frontx.Ex
