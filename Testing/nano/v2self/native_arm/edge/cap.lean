def f : Nat → Buf → Buf
  | 0, b => b
  | n + 1, b => f n (bpush b 7)
def m (x : List UInt8) : List UInt8 := put [] (bsize (f 600000 bnew))
