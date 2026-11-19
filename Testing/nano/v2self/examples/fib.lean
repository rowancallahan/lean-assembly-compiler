-- fib: the Fibonacci number F(k) mod 2^64, k = the first input byte (0 on empty input), as 8 bytes, lowest byte first.
-- f has fuel 255 (the largest k) and leaves early when k reaches 0.  g writes the 8 bytes of v.
-- example: 0a (k = 10) -> 37 00 00 00 00 00 00 00   (F(10) = 55 = 0x37)
-- input  (hex): 0a
-- expect (hex): 37 00 00 00 00 00 00 00
def f : Nat → UInt64 → UInt64 → UInt64 → UInt64
  | 0, k, a, b => a
  | n + 1, k, a, b => if k == 0 then a else f n (k - 1) b (a + b)
def g : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
  | 0, x, v, o => o
  | n + 1, x, v, o => g n x (v >>> 8) (put o v)
def m (x : List UInt8) : List UInt8 := g 8 x (f 255 (rd x 0) 0 1) []
