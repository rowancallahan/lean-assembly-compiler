-- reverse: the input bytes in reverse order.
-- example: "stressed" -> "desserts"
-- input  (hex): 73 74 72 65 73 73 65 64
-- expect (hex): 64 65 73 73 65 72 74 73
def f : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
  | 0, x, i, o => o
  | n + 1, x, i, o => f n x (i - 1) (put o (rd x (i - 1)))
def m (x : List UInt8) : List UInt8 := f (len' x) x (len x) []
