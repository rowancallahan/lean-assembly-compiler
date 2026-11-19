-- rle: run-length encoding. Each run of equal bytes becomes two bytes: the run length (1..255), then the byte.
-- c is the length of the run that ends at position i.  e is 1 when the run continues at i + 1.
-- example: "aaabccdddd" -> 03 61 01 62 02 63 04 64
-- input  (hex): 61 61 61 62 63 63 64 64 64 64
-- expect (hex): 03 61 01 62 02 63 04 64
def e (x : List UInt8) (i c : UInt64) : UInt64 :=
  if i + 1 < len x then if rd x (i + 1) == rd x i then if c < 255 then 1 else 0 else 0 else 0
def f : Nat → List UInt8 → UInt64 → UInt64 → List UInt8 → List UInt8
  | 0, x, i, c, o => o
  | n + 1, x, i, c, o =>
    if e x i c == 1 then f n x (i + 1) (c + 1) o
    else f n x (i + 1) 1 (put (put o c) (rd x i))
def m (x : List UInt8) : List UInt8 := f (len' x) x 0 1 []
