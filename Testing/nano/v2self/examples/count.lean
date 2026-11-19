-- count: the number of input bytes, as one byte (mod 256).
-- example: "hello" (68 65 6c 6c 6f) -> 05
-- input  (hex): 68 65 6c 6c 6f
-- expect (hex): 05
def m (x : List UInt8) : List UInt8 := put [] (len x)
