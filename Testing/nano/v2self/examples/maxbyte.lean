-- maxbyte: the largest input byte, as one byte (00 on empty input).
-- example: "nano" (6e 61 6e 6f) -> 6f
-- input  (hex): 6e 61 6e 6f
-- expect (hex): 6f
def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, x, i, a => a
  | n + 1, x, i, a => if a < rd x i then f n x (i + 1) (rd x i) else f n x (i + 1) a
def m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0 0)
