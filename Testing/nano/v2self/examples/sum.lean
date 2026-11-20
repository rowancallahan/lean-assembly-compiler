-- sum: the sum of the input bytes mod 256, as one byte.
-- example: "abc" (61 62 63) -> 26
-- input  (hex): 61 62 63
-- expect (hex): 26
def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, x, i, a => a
  | n + 1, x, i, a => f n x (i + 1) (a + rd x i)
def m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0 0)
