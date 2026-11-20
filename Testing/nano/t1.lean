import Legacy.Nano.Elab
open Nano
def src := "def sq (x : UInt64) : UInt64 := x * x\ndef f (x y : UInt64) : UInt64 := let z := sq x + 3; z * y - 1 - sq (y - 2)"
#eval ((nanoElab src.toUTF8.toList).bind (·.eval [3,5]))
def sq (x : UInt64) : UInt64 := x * x
def f (x y : UInt64) : UInt64 := let z := sq x + 3; z * y - 1 - sq (y - 2)
#eval f 3 5
